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

/-- The levels `[.param k, ..., .param (n+k-1)]`; `VLevel.params` shifted by `k`.
The recursor universe list is the elimination level (`.param 0`) followed by
the declaration's levels shifted by one, so declaration-world expressions
enter the recursor's universe context via `instL (params' n 1)`. -/
def VLevel.params' (n k : Nat) : List VLevel := (List.range n).map fun i => .param (i + k)

namespace VInductDecl

/-- The result sort of an inductive type (stage 1 requires the type to be a
literal sort: no indices, no parameters). -/
def sortLevel (ty : VInductiveType) : VLevel :=
  match ty.type with
  | .sort l => l
  | _ => .zero

/-- Constructor field types, outermost first. -/
def ctorFields : VExpr → List VExpr
  | .forallE B rest => B :: ctorFields rest
  | _ => []

variable (U : Nat) (T : Name)

/-- Positions of the directly recursive fields. -/
def recIdxs : List VExpr → (j : Nat := 0) → List Nat
  | [], _ => []
  | B :: Bs, j =>
    if B = .const T (VLevel.params U) then j :: recIdxs Bs (j+1) else recIdxs Bs (j+1)

/-- A stage-1 field is either a direct recursive occurrence (exactly the
block's type constant at the identity levels) or a closed type not
mentioning the block at all. This builds in strict positivity for the
stage-1 class. -/
def stage1Field (B : VExpr) : Bool :=
  B == .const T (VLevel.params U) || (decide (B.ClosedN 0) && !B.hasConst T)

/-- Stage-1 constructor type: a non-dependent telescope of stage-1 fields
ending in exactly the block's type constant. -/
def stage1Ctor : VExpr → Bool
  | .forallE B rest => stage1Field U T B && stage1Ctor rest
  | e => e == .const T (VLevel.params U)

/-- The stage-1 restriction: a single non-indexed inductive type with no
parameters, in a syntactically never-zero sort (so large elimination is
unconditional), whose constructors take only closed non-recursive or
directly recursive arguments. Later stages will widen this class; the
public entry points (`WF`, `addInduct`) are guarded by it rather than
sorried for the general case. -/
def stage1 : VInductDecl → Bool
  | ⟨U, 0, [ty]⟩ =>
    ty.uvars == U &&
    (match ty.type with
      | .sort l => decide (l.WF U) && l.isNeverZero
      | _ => false) &&
    ty.ctors.all fun c => c.uvars == U && stage1Ctor U ty.name c.type
  | _ => false

/-- `motive : T → Sort u` in the recursor's universe context. -/
def motiveType : VExpr :=
  .forallE (.const T (VLevel.params' U 1)) (.sort (.param 0))

/-- The minor premise for one constructor, in context `[motive]`:
`∀ fields, ∀ ihs, motive (ctor fields)`, with one induction hypothesis per
directly recursive field. Field types are closed, so they need no lifting;
only the universe shift into the recursor context applies. -/
def minorType (c : VConstVal) : VExpr :=
  let Bs := ctorFields c.type
  let m := Bs.length
  let rs := recIdxs U T Bs
  let r := rs.length
  let ctorApp := VExpr.appN (.const c.name (VLevel.params' U 1)) (VExpr.bvarRevRange r m)
  let ihs := rs.zipIdx.map fun (j, p) => VExpr.app (.bvar (m+p)) (.bvar (m-1-j+p))
  VExpr.forallN (Bs.map (VExpr.instL (VLevel.params' U 1)))
    (VExpr.forallN ihs (.app (.bvar (m+r)) ctorApp))

/-- Minor premise types in position: the `i`-th lives under `motive` and the
previous `i` minors. -/
def minorTypes (ty : VInductiveType) : List VExpr :=
  ty.ctors.zipIdx.map fun (c, i) => VExpr.liftN i (minorType U T c)

/-- The recursor type
`∀ (motive : T → Sort u) (minors..) (t : T), motive t`. -/
def recType (ty : VInductiveType) : VExpr :=
  let k := ty.ctors.length
  .forallE (motiveType U T) <|
    VExpr.forallN (minorTypes U T ty) <|
      .forallE (.const T (VLevel.params' U 1)) (.app (.bvar (k+1)) (.bvar 0))

def recConst (ty : VInductiveType) : VConstant := ⟨U + 1, recType U T ty⟩

/-- The iota rule for the `i`-th constructor, as a closed defeq between
lambda telescopes over `motive :: minors ++ fields` (the same shape as
`quotDefEq`, and the same telescope the kernel's `RecursorRule.rhs` binds).
The left body is the `SimplePattern.iota` spine: the recursor applied to
`motive` and the minors, with a constructor-headed major. -/
def rule (ty : VInductiveType) (i : Nat) (c : VConstVal) : VDefEq :=
  let k := ty.ctors.length
  let Bs := ctorFields c.type
  let m := Bs.length
  let rs := recIdxs U T Bs
  let binders := motiveType U T :: minorTypes U T ty ++
    Bs.map (VExpr.instL (VLevel.params' U 1))
  let fieldArgs := VExpr.bvarRevRange 0 m
  let recBase := VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
    (.bvar (k+m) :: VExpr.bvarRevRange m k)
  let ctorApp := VExpr.appN (.const c.name (VLevel.params' U 1)) fieldArgs
  let ihs := rs.map fun j => recBase.app (.bvar (m-1-j))
  { uvars := U + 1
    lhs := VExpr.lamN binders (recBase.app ctorApp)
    rhs := VExpr.lamN binders (VExpr.appN (.bvar (k-1-i+m)) (fieldArgs ++ ihs))
    type := VExpr.forallN binders (.app (.bvar (k+m)) ctorApp) }

def rules (ty : VInductiveType) : List VDefEq :=
  ty.ctors.zipIdx.map fun (c, i) => rule U T ty i c

/-- Semantic well-formedness of one stage-1 constructor type over the
pre-environment: each non-recursive field is a type whose universe is
bounded by the block's result level (the kernel's
`checkConstructors` universe condition). Recursive fields refer to the
block constant, which is not yet in `env`, so they carry no side condition
here; their typing is established inside `addInduct_WF` after the type
constant is added. -/
def ctorWF (env : VEnv) (l : VLevel) : VExpr → Prop
  | .forallE B rest =>
    (B = .const T (VLevel.params U) ∨
      ∃ u, env.HasType U [] B (.sort u) ∧ u ≤ l) ∧ ctorWF env l rest
  | _ => True

end VInductDecl

def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop :=
  decl.stage1 ∧
  ∀ ty ∈ decl.types, ∀ c ∈ ty.ctors,
    VInductDecl.ctorWF decl.uvars ty.name env (VInductDecl.sortLevel ty) c.type

def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv := do
  guard decl.stage1
  let [ty] := decl.types | none
  let env ← env.addConst ty.name ty.toVConstant
  let env ← ty.ctors.foldlM (fun env c => env.addConst c.name c.toVConstant) env
  let env ← env.addConst (.str ty.name "rec") (VInductDecl.recConst decl.uvars ty.name ty)
  return (VInductDecl.rules decl.uvars ty.name ty).foldl VEnv.addDefEq env
