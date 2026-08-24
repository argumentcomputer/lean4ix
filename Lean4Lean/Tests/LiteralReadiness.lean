import Lean4Lean.Theory.InductiveFixtures
import Lean4Lean.Theory.Literals
import Lean4Lean.Replay
import Lean4Lean.Verify.Typing.Lemmas

/-! # Literal readiness fixtures

These checks pin the consumer-neutral prelude descriptors used by
`VEnv.PreludeReady` to Lean's real compiled metadata, then exercise direct and
constructor-unfolded literals with notation-heavy values.
-/

namespace Lean4Lean.Tests.LiteralReadiness

open Lean

/-! The CLI deliberately does not import Verify's proof/axiom closure.  Pin
its closed-metadata translator to the deterministic `trExprS?` implementation
on every syntax boundary it supports, including let-binder depth and rejection
of malformed loose variables and projections. -/

private def differentialTranslation? (levelParams : List Name) (expr : Expr) :
    Option VExpr :=
  (Differential.exprToVExpr levelParams expr).toOption

private def binderTranslationFixture : Expr :=
  .lam `x (.sort (.succ (.param `u)))
    (.letE `y (.sort (.succ (.param `u))) (.bvar 0)
      (.app (.bvar 1) (.bvar 0)) false) .implicit

private def literalTranslationFixture : Expr :=
  .mdata {} <| .app (.const ``Nat.succ []) (.lit (.natVal 3))

#guard differentialTranslation? [`u] binderTranslationFixture ==
  trExprS? [`u] [] binderTranslationFixture
#guard differentialTranslation? [] literalTranslationFixture ==
  trExprS? [] [] literalTranslationFixture
#guard differentialTranslation? [] (.lit (.strVal "translation parity")) ==
  trExprS? [] [] (.lit (.strVal "translation parity"))
#guard differentialTranslation? [] (.bvar 0) == trExprS? [] [] (.bvar 0)
#guard differentialTranslation? [] (.proj ``Prod 0 (.const ``Unit.unit [])) ==
  trExprS? [] [] (.proj ``Prod 0 (.const ``Unit.unit []))
#guard differentialTranslation? [] (.sort (.param `unknown)) ==
  trExprS? [] [] (.sort (.param `unknown))

/-! The manual Theory descriptors are exactly the declarations already
checked against the kernel by `Theory.InductiveFixtures`. -/

example : LiteralPrelude.boolType = InductiveFixtures.boolType := rfl
example : LiteralPrelude.natType = InductiveFixtures.natType := rfl
example : LiteralPrelude.listType = InductiveFixtures.listType := rfl

example : LiteralPrelude.char = vconst(type_of% @Char) := rfl
example : LiteralPrelude.charOfNat = vconst(type_of% @Char.ofNat) := rfl
example : LiteralPrelude.string = vconst(type_of% @String) := rfl
example : LiteralPrelude.stringOfList = vconst(type_of% @String.ofList) := rfl

/-! The readiness contract's recursor and iota descriptors also agree
definitionally with the kernel declarations.  List's two universe parameters
use the same explicit occurrence-to-kernel permutation as the underlying
inductive adequacy fixture. -/

private def permC (ci : VConstant) (ls : List VLevel) : VConstant :=
  ⟨ci.uvars, ci.type.instL ls⟩

private def permE (df : VDefEq) (ls : List VLevel) : VDefEq :=
  ⟨df.uvars, df.lhs.instL ls, df.rhs.instL ls, df.type.instL ls⟩

example : LiteralPrelude.boolRec = vconst(type_of% @Bool.rec) := rfl
example : LiteralPrelude.boolIotas[0]? =
    some (vdefeq(motive f t => @Bool.rec motive f t .false ≡ f)) := rfl
example : LiteralPrelude.boolIotas[1]? =
    some (vdefeq(motive f t => @Bool.rec motive f t .true ≡ t)) := rfl

example : LiteralPrelude.natRec = vconst(type_of% @Nat.rec) := rfl
example : LiteralPrelude.natIotas[0]? =
    some (vdefeq(motive z s => @Nat.rec motive z s .zero ≡ z)) := rfl
example : LiteralPrelude.natIotas[1]? =
    some (vdefeq(motive z s n =>
      @Nat.rec motive z s (.succ n) ≡ s n (@Nat.rec motive z s n))) := rfl

example : LiteralPrelude.listRec =
    permC (vconst(type_of% @List.rec)) [.param 1, .param 0] := rfl
example : LiteralPrelude.listIotas[0]? =
    some (permE (vdefeq(α motive n c => @List.rec α motive n c (@List.nil α) ≡ n))
      [.param 1, .param 0]) := rfl
example : LiteralPrelude.listIotas[1]? =
    some (permE (vdefeq(α motive n c hd tl =>
        @List.rec α motive n c (@List.cons α hd tl) ≡
          c hd tl (@List.rec α motive n c tl)))
      [.param 1, .param 0]) := rfl

section

variable {env : VEnv} (ready : env.PreludeReady)

example {env' : VEnv} (henv : env ≤ env') (hordered : env'.Ordered) :
    env'.PreludeReady :=
  ready.mono henv hordered

example {env' : VEnv} (name : Name) (ci : VConstant) (hci : ci.WF env)
    (hadd : env.addConst name ci = some env') : env'.PreludeReady :=
  ready.addConst hci hadd

example (df : VDefEq) (hdf : df.WF env) :
    (env.addDefEq df).PreludeReady :=
  ready.addDefEq hdf

example : VExpr.WF env 0 [] (VExpr.trLiteral (.natVal 1_234_567)) :=
  ready.trLiteral_wf _ (ready.containsLits _)

example : VExpr.WF env 3 []
    (VExpr.trLiteral (.strVal "Lean 4: λ → ☃ — 12,345")) :=
  ready.trLiteral_wf _ (ready.containsLits _)

example (h : TrExprS env [] []
    (Literal.toConstructor (.strVal "constructor ↔ direct")) w) :
    w = VExpr.trLiteral (.strVal "constructor ↔ direct") ∧
      VExpr.WF env 0 [] w :=
  h.toConstructor_ready ready (ready.containsLits _)

example {l : Literal}
    (h : TrExprS env [] [] (Literal.toConstructor l) w) :
    w = VExpr.trLiteral l :=
  h.toConstructor_eq

end

end Lean4Lean.Tests.LiteralReadiness
