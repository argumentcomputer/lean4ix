import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Meta
import Lean4Lean.Theory.Typing.InductiveLemmas

/-! Adequacy fixtures for `VEnv.addInduct` (stage 1): run the generator on
hand-written declarations and check the output against the real kernel's
constants, translated by the `vconst`/`vdefeq` macros. A mismatch in
telescope order, universe conventions, or de Bruijn arithmetic fails these
`rfl`s. -/

namespace Lean4Lean
namespace InductiveFixtures
open VInductDecl

/-! ## Nat -/

def natType : VInductiveType where
  name := ``Nat
  uvars := 0
  type := vexpr(Type)
  ctors := [⟨vconst(type_of% @Nat.zero), ``Nat.zero⟩, ⟨vconst(type_of% @Nat.succ), ``Nat.succ⟩]

def natDecl : VInductDecl := ⟨0, 0, [natType]⟩

example : natDecl.stage1 = true := rfl

/-- The generated recursor is exactly the kernel's `Nat.rec`. -/
example : recConst 0 ``Nat natType = vconst(type_of% @Nat.rec) := rfl

/-- The generated iota rules are exactly the kernel's reduction rules for
`Nat.rec`, phrased as closed lambda-telescope defeqs like `quotDefEq`. -/
example : (rules 0 ``Nat natType)[0]? =
    some (vdefeq(motive z s => @Nat.rec motive z s .zero ≡ z)) := rfl

example : (rules 0 ``Nat natType)[1]? =
    some (vdefeq(motive z s n => @Nat.rec motive z s (.succ n) ≡ s n (@Nat.rec motive z s n))) :=
  rfl

example : (VEnv.empty.addInduct natDecl).isSome = true := rfl

example : (VEnv.empty.addInduct natDecl).map (·.constants ``Nat) =
    some (some natType.toVConstant) := rfl

example : (VEnv.empty.addInduct natDecl).map (·.constants ``Nat.rec) =
    some (some (recConst 0 ``Nat natType)) := rfl

/-- The successor iota rule is registered in the output environment. -/
example : ∀ env', VEnv.empty.addInduct natDecl = some env' →
    env'.defeqs (rule 0 ``Nat natType 1 ⟨vconst(type_of% @Nat.succ), ``Nat.succ⟩) := by
  rintro env' ⟨⟩; exact .inl rfl

/-! ## Bool -/

def boolType : VInductiveType where
  name := ``Bool
  uvars := 0
  type := vexpr(Type)
  ctors := [⟨vconst(type_of% @Bool.false), ``Bool.false⟩, ⟨vconst(type_of% @Bool.true), ``Bool.true⟩]

def boolDecl : VInductDecl := ⟨0, 0, [boolType]⟩

example : boolDecl.stage1 = true := rfl

example : recConst 0 ``Bool boolType = vconst(type_of% @Bool.rec) := rfl

example : (rules 0 ``Bool boolType)[0]? =
    some (vdefeq(motive f t => @Bool.rec motive f t .false ≡ f)) := rfl

example : (rules 0 ``Bool boolType)[1]? =
    some (vdefeq(motive f t => @Bool.rec motive f t .true ≡ t)) := rfl

/-! ## Conservativity: outside the stage-1 class `addInduct` refuses. -/

/-- `List` has a parameter, so stage 1 rejects it. -/
example :
    VEnv.empty.addInduct ⟨0, 1, [{
      name := ``List
      uvars := 0
      type := vexpr(Type → Type)
      ctors := [] }]⟩ = none := rfl

/-! ## The M1 axiom gate: `addInduct_WF` is proven without `sorry`. -/

/-- info: 'Lean4Lean.VEnv.addInduct_WF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms VEnv.addInduct_WF
