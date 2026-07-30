import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Basic

namespace Lean4Lean

deriving instance DecidableEq for VLevel
deriving instance DecidableEq for VExpr

/-- Syntactic underapproximation of `VLevel.IsNeverZero`,
mirroring `Lean.Level.isNeverZero`. -/
def VLevel.isNeverZero : VLevel → Bool
  | .zero | .param _ => false
  | .succ _ => true
  | .max l₁ l₂ => l₁.isNeverZero || l₂.isNeverZero
  | .imax _ l₂ => l₂.isNeverZero

instance VExpr.decClosedN : ∀ (e : VExpr) (k : Nat), Decidable (e.ClosedN k)
  | .bvar i, k => inferInstanceAs (Decidable (i < k))
  | .sort .., _ | .const .., _ => inferInstanceAs (Decidable True)
  | .app e1 e2, k => @instDecidableAnd _ _ (decClosedN e1 k) (decClosedN e2 k)
  | .lam e1 e2, k => @instDecidableAnd _ _ (decClosedN e1 k) (decClosedN e2 (k+1))
  | .forallE e1 e2, k => @instDecidableAnd _ _ (decClosedN e1 k) (decClosedN e2 (k+1))

def VExpr.hasConst (n : Name) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const c _ => c == n
  | .app e1 e2 | .lam e1 e2 | .forallE e1 e2 => e1.hasConst n || e2.hasConst n

def VExpr.appN (f : VExpr) : List VExpr → VExpr
  | [] => f
  | a :: as => (f.app a).appN as

/-- `[.bvar (off+m-1), ..., .bvar off]`: the spine referring to the last `m`
binders, skipping the innermost `off`. -/
def VExpr.bvarRevRange (off : Nat) : Nat → List VExpr
  | 0 => []
  | m+1 => .bvar (off + m) :: bvarRevRange off m

/-- Iterated lambda; the binder list is outermost first. -/
def VExpr.lamN : List VExpr → VExpr → VExpr
  | [], e => e
  | A :: As, e => .lam A (lamN As e)

/-- Iterated pi; the binder list is outermost first. -/
def VExpr.forallN : List VExpr → VExpr → VExpr
  | [], e => e
  | A :: As, e => .forallE A (forallN As e)

/-- Insert `n` binders below a telescope at depth `k`: the entry at depth
`j` within the telescope lifts by `n` at cutoff `k+j`. -/
def VExpr.liftTelN (n : Nat) : List VExpr → Nat → List VExpr
  | [], _ => []
  | A :: As, k => A.liftN n k :: liftTelN n As (k+1)

/-- The first `n` binder types of an iterated pi, outermost first. -/
def VExpr.telN : Nat → VExpr → List VExpr
  | 0, _ => []
  | n+1, .forallE A rest => A :: telN n rest
  | _+1, _ => []

/-- Strip `n` binders from an iterated pi. -/
def VExpr.dropN : Nat → VExpr → VExpr
  | 0, e => e
  | n+1, .forallE _ rest => dropN n rest
  | _+1, e => e

/-- The levels `[.param k, ..., .param (n+k-1)]`; `VLevel.params` shifted by `k`.
The recursor universe list is the elimination level (`.param 0`) followed by
the declaration's levels shifted by one, so declaration-world expressions
enter the recursor's universe context via `instL (params' n 1)`. -/
def VLevel.params' (n k : Nat) : List VLevel := (List.range n).map fun i => .param (i + k)

/-- Well-formedness of a binder telescope over a context. -/
def VEnv.OnTel (env : VEnv) (U : Nat) : List VExpr → List VExpr → Prop
  | _, [] => True
  | Γ, A :: As => env.IsType U Γ A ∧ OnTel env U (A :: Γ) As

namespace VInductDecl

variable (U : Nat) (T : Name) (np : Nat)

/-- The result sort of an inductive type past its parameters. -/
def sortLevel (ty : VInductiveType) : VLevel :=
  match VExpr.dropN np ty.type with
  | .sort l => l
  | _ => .zero

/-- Constructor field types, outermost first. -/
def ctorFields : VExpr → List VExpr
  | .forallE B rest => B :: ctorFields rest
  | _ => []

/-- The block type applied to its parameters, seen from `off` binders past
the parameter telescope (declaration universes). -/
def recApp (off : Nat) : VExpr :=
  VExpr.appN (.const T (VLevel.params U)) (VExpr.bvarRevRange off np)

/-- Positions of the directly recursive fields (`j` counts binders past the
parameters). -/
def recIdxs : List VExpr → (j : Nat := 0) → List Nat
  | [], _ => []
  | B :: Bs, j =>
    if B = recApp U T np j then j :: recIdxs Bs (j+1) else recIdxs Bs (j+1)

/-- Induction-hypothesis binder types for the recursive field positions
`rs`, at depth `p` past the `m` field binders (in context `[motive]`):
the `p`-th is `motive xⱼ` for `j = rs[p]`. -/
def ihsFrom (m : Nat) : List Nat → Nat → List VExpr
  | [], _ => []
  | j :: rs, p => .app (.bvar (m+p)) (.bvar (m-1-j+p)) :: ihsFrom m rs (p+1)

/-- A stage-2 field is either a direct recursive occurrence (exactly the
block's type constant applied to the parameters) or a type not mentioning
the block at all. This builds in strict positivity for the stage-2 class. -/
def stage2Field (j : Nat) (B : VExpr) : Bool :=
  B == recApp U T np j || !B.hasConst T

/-- Stage-2 constructor type past the parameters: a telescope of stage-2
fields ending in exactly the block's type constant applied to the
parameters. -/
def stage2Ctor : Nat → VExpr → Bool
  | j, .forallE B rest => stage2Field U T np j B && stage2Ctor (j+1) rest
  | j, e => e == recApp U T np j

/-- The stage-2 restriction: a single non-indexed inductive type, in a
syntactically never-zero sort (so large elimination is unconditional),
whose constructors share the type's parameter telescope syntactically and
whose fields are non-recursive types not mentioning the block, or direct
recursive occurrences. Later stages will widen this class; the public
entry points (`WF`, `addInduct`) are guarded by it rather than sorried for
the general case. -/
def stage2 : VInductDecl → Bool
  | ⟨U, np, [ty]⟩ =>
    ty.uvars == U &&
    (VExpr.telN np ty.type).length == np &&
    (match VExpr.dropN np ty.type with
      | .sort l => decide (l.WF U) && l.isNeverZero
      | _ => false) &&
    ty.ctors.all fun c => c.uvars == U &&
      VExpr.telN np c.type == VExpr.telN np ty.type &&
      stage2Ctor U ty.name np 0 (VExpr.dropN np c.type)
  | _ => false

/-- The parameter telescope in the recursor's universe context. -/
def paramsTel (ty : VInductiveType) : List VExpr :=
  (VExpr.telN np ty.type).map (VExpr.instL (VLevel.params' U 1))

/-- `recApp` in the recursor's universe context. -/
def recApp' (off : Nat) : VExpr :=
  VExpr.appN (.const T (VLevel.params' U 1)) (VExpr.bvarRevRange off np)

/-- `motive : T params → Sort u`, in context `params`. -/
def motiveType : VExpr :=
  .forallE (recApp' U T np 0) (.sort (.param 0))

/-- Constructor fields in the recursor's universe context (still at
parameter depth, no motive shift). -/
def ctorFieldsR (c : VConstVal) : List VExpr :=
  (ctorFields (VExpr.dropN np c.type)).map (VExpr.instL (VLevel.params' U 1))

/-- The minor premise for one constructor, in context `params ++ [motive]`:
`∀ fields, ∀ ihs, motive (ctor params fields)`, with one induction
hypothesis per directly recursive field. The fields shift by one for the
interposed motive. -/
def minorType (c : VConstVal) : VExpr :=
  let Bs := ctorFieldsR U np c
  let m := Bs.length
  let rs := recIdxs U T np (ctorFields (VExpr.dropN np c.type))
  let r := rs.length
  VExpr.forallN (VExpr.liftTelN 1 Bs 0)
    (VExpr.forallN (ihsFrom m rs 0)
      (.app (.bvar (m+r))
        (VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange (r+m+1) np ++ VExpr.bvarRevRange r m))))

/-- Minor premise types in position: the `i`-th lives under
`params ++ motive` and the previous `i` minors. -/
def minorTypes : List VConstVal → (i : Nat := 0) → List VExpr
  | [], _ => []
  | c :: cs, i => VExpr.liftN i (minorType U T np c) :: minorTypes cs (i+1)

/-- The recursor type
`∀ params, ∀ (motive : T params → Sort u) (minors..) (t : T params), motive t`. -/
def recType (ty : VInductiveType) : VExpr :=
  let k := ty.ctors.length
  VExpr.forallN (paramsTel U np ty) <|
    .forallE (motiveType U T np) <|
      VExpr.forallN (minorTypes U T np ty.ctors) <|
        .forallE (recApp' U T np (k+1)) (.app (.bvar (k+1)) (.bvar 0))

def recConst (ty : VInductiveType) : VConstant := ⟨U + 1, recType U T np ty⟩

/-- The iota rule for the `i`-th constructor, as a closed defeq between
lambda telescopes over `params ++ motive :: minors ++ fields` (the same
shape as `quotDefEq`, and the same telescope the kernel's
`RecursorRule.rhs` binds). The left body is the `SimplePattern.iota`
spine: the recursor applied to the parameters, motive and minors, with a
constructor-headed major. -/
def rule (ty : VInductiveType) (i : Nat) (c : VConstVal) : VDefEq :=
  let k := ty.ctors.length
  let Bs := ctorFieldsR U np c
  let m := Bs.length
  let rs := recIdxs U T np (ctorFields (VExpr.dropN np c.type))
  let binders := paramsTel U np ty ++ motiveType U T np :: minorTypes U T np ty.ctors ++
    VExpr.liftTelN (k+1) Bs 0
  let recBase := VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
    (VExpr.bvarRevRange m (np+k+1))
  let ctorApp := VExpr.appN (.const c.name (VLevel.params' U 1))
    (VExpr.bvarRevRange (m+k+1) np ++ VExpr.bvarRevRange 0 m)
  let ihs := rs.map fun j => recBase.app (.bvar (m-1-j))
  { uvars := U + 1
    lhs := VExpr.lamN binders (recBase.app ctorApp)
    rhs := VExpr.lamN binders
      (VExpr.appN (.bvar (k-1-i+m)) (VExpr.bvarRevRange 0 m ++ ihs))
    type := VExpr.forallN binders (.app (.bvar (k+m)) ctorApp) }

def rules (ty : VInductiveType) : List VDefEq :=
  ty.ctors.zipIdx.map fun (c, i) => rule U T np ty i c

/-- Semantic well-formedness of the stage-2 constructor fields over the
pre-environment, in the growing context (parameters first): each
non-recursive field is a type whose universe is bounded by the block's
result level (the kernel's `checkConstructors` universe condition).
Recursive fields refer to the block constant, which is not yet in `env`,
so they carry no side condition here; their typing is established inside
`addInduct_WF` after the type constant is added. -/
def fieldsWF (env : VEnv) (l : VLevel) : List VExpr → Nat → List VExpr → Prop
  | _, _, [] => True
  | Γ, j, B :: Bs =>
    (B = recApp U T np j ∨ ∃ u, env.HasType U Γ B (.sort u) ∧ u ≤ l) ∧
    fieldsWF env l (B :: Γ) (j+1) Bs

end VInductDecl

def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop :=
  decl.stage2 ∧
  ∀ ty ∈ decl.types,
    VEnv.OnTel env decl.uvars [] (VExpr.telN decl.nparams ty.type) ∧
    ∀ c ∈ ty.ctors,
      VInductDecl.fieldsWF decl.uvars ty.name decl.nparams env
        (VInductDecl.sortLevel decl.nparams ty)
        (VExpr.telN decl.nparams ty.type).reverse 0
        (VInductDecl.ctorFields (VExpr.dropN decl.nparams c.type))

def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv := do
  guard decl.stage2
  let [ty] := decl.types | none
  let env ← env.addConst ty.name ty.toVConstant
  let env ← ty.ctors.foldlM (fun env c => env.addConst c.name c.toVConstant) env
  let env ← env.addConst (.str ty.name "rec")
    (VInductDecl.recConst decl.uvars ty.name decl.nparams ty)
  return (VInductDecl.rules decl.uvars ty.name decl.nparams ty).foldl VEnv.addDefEq env
