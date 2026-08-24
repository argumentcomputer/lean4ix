import Batteries.Tactic.OpenPrivate
import Lean4Lean.Environment.Basic
import Lean4Lean.Expr
import Lean4Lean.Instantiate
import Lean4Lean.LocalContext

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

abbrev ExprBuildT (m) := ReaderT LocalContext <| ReaderT NameGenerator m

def ExprBuildT.run [Monad m] (x : ExprBuildT m α) : m α := x {} {}

instance : MonadLocalNameGenerator (ExprBuildT m) where
  withFreshId x c ngen := x ngen.curr c ngen.next

def checkEqType (env : Environment) : Except Exception Unit := do
  let fail {α} (s : String) : Except Exception α :=
    throw <| .other s!"failed to initialize quot module, {s}"
  let .inductInfo info ← env.get ``Eq | fail "environment does not have 'Eq' type"
  let [u] := info.levelParams | fail "unexpected number of universe params at 'Eq' type"
  let [eqRefl] := info.ctors | fail "unexpected number of constructors for 'Eq' type"
  ExprBuildT.run do
    withLocalDecl `α .implicit (.sort (.param u)) fun α => do
      if info.type != ((← read).mkForall #[α] <| .arrow α <| .arrow α .prop) then
        fail "'Eq' has an expected type"
    let info ← env.get eqRefl
    let [u] := info.levelParams
      | fail "unexpected number of universe params at 'Eq' type constructor"
    withLocalDecl `α .implicit (.sort (.param u)) fun α => do
      withLocalDecl `a .default α fun a => do
        if info.type != ((← read).mkForall #[α, a] <| mkApp3 (.const ``Eq [.param u]) α a a) then
        fail "unexpected type for 'Eq' type constructor"

/-!
The quotient constants have closed types.  Keeping those expressions explicit
avoids making verification replay the temporary free-variable contexts used by
the original builder.  The definitions below are alpha-equivalent to that
builder's output (and retain its binder names and binder information).
-/

def quotTypeExpr : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r
      (.forallE `a (.bvar 0)
        (.forallE `a (.bvar 1) .prop .default) .default)
      (.sort (.param `u)) .default) .implicit

def quotMkTypeExpr : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r
      (.forallE `a (.bvar 0)
        (.forallE `a (.bvar 1) .prop .default) .default)
      (.forallE `a (.bvar 1)
        (mkApp2 (.const ``Quot [.param `u]) (.bvar 2) (.bvar 1)) .default)
      .default) .implicit

def quotLiftTypeExpr : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r
      (.forallE `a (.bvar 0)
        (.forallE `a (.bvar 1) .prop .default) .default)
      (.forallE `β (.sort (.param `v))
        (.forallE `f
          (.forallE `a (.bvar 2) (.bvar 1) .default)
          (.forallE `a
            (.forallE `a (.bvar 3)
              (.forallE `b (.bvar 4)
                (.forallE `a
                  (mkApp2 (.bvar 4) (.bvar 1) (.bvar 0))
                  (mkApp3 (.const ``Eq [.param `v]) (.bvar 4)
                    (.app (.bvar 3) (.bvar 2))
                    (.app (.bvar 3) (.bvar 1))) .default)
                .default) .default)
            (.forallE `a
              (mkApp2 (.const ``Quot [.param `u]) (.bvar 4) (.bvar 3))
              (.bvar 3) .default) .default)
          .default) .implicit)
      .implicit) .implicit

def quotIndTypeExpr : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r
      (.forallE `a (.bvar 0)
        (.forallE `a (.bvar 1) .prop .default) .default)
      (.forallE `β
        (.forallE `a
          (mkApp2 (.const ``Quot [.param `u]) (.bvar 1) (.bvar 0))
          .prop .default)
        (.forallE `mk
          (.forallE `a (.bvar 2)
            (.app (.bvar 1)
              (mkApp3 (.const ``Quot.mk [.param `u])
                (.bvar 3) (.bvar 2) (.bvar 0))) .default)
          (.forallE `q
            (mkApp2 (.const ``Quot [.param `u]) (.bvar 3) (.bvar 2))
            (.app (.bvar 2) (.bvar 0)) .default)
          .default) .implicit)
      .implicit) .implicit

def quotTypeInfo : ConstantInfo := .quotInfo {
  name := ``Quot, kind := .type, levelParams := [`u], type := quotTypeExpr }

def quotMkInfo : ConstantInfo := .quotInfo {
  name := ``Quot.mk, kind := .ctor, levelParams := [`u], type := quotMkTypeExpr }

def quotLiftInfo : ConstantInfo := .quotInfo {
  name := ``Quot.lift, kind := .lift, levelParams := [`u, `v], type := quotLiftTypeExpr }

def quotIndInfo : ConstantInfo := .quotInfo {
  name := ``Quot.ind, kind := .ind, levelParams := [`u], type := quotIndTypeExpr }

def Environment.addQuot (env : Environment) : Except Exception Environment := do
  if env.quotInit then return env
  checkEqType env
  env.checkName ``Quot
  env.checkName ``Quot.mk
  env.checkName ``Quot.lift
  env.checkName ``Quot.ind
  let env := env.add quotTypeInfo
  let env := env.add quotMkInfo
  let env := env.add quotLiftInfo
  let env := env.add quotIndInfo
  return markQuotInit env

/-- Reduces the head application of a quotient eliminator as follows:

```
Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) :
  (∀ a b : α, r a b → f a = f b) → @Quot.{u} α r → β

Quot.lift f h (Quot.mk r a) ... ⟶ f a ...
```

```
Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : @Quot.{u} α r → Prop} :
  (∀ a : α, β (@Quot.mk.{u} α r a)) → ∀ q : @Quot.{u} α r, β q

Quot.ind p (Quot.mk r a) ... ⟶ p a ...
```
-/
def quotReduceRec [Monad m] (e : Expr) (whnf : Expr → m Expr) : m (Option Expr) := do
  let .const fn _ := e.getAppFn | return none
  let cont mkPos argPos := do
    let args := e.getAppArgs
    if h : mkPos < args.size then
      let mk ← whnf args[mkPos]
      if !mk.isAppOfArity ``Quot.mk 3 then return none
      let mut r := Expr.app args[argPos]! mk.appArg!
      let elimArity := mkPos + 1
      if elimArity < args.size then
        r := mkAppRange r elimArity args.size args
      return some r
    else return none
  if fn == ``Quot.lift then cont 5 3
  else if fn == ``Quot.ind then cont 4 3
  else return none
