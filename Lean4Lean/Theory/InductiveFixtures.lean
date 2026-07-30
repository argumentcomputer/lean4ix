import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.Meta
import Lean4Lean.Theory.Typing.InductiveLemmas

/-! Adequacy fixtures for `VEnv.addInduct` (stage 2): run the generator on
hand-written declarations and check the output against the real kernel's
constants, translated by the `vconst`/`vdefeq` macros. A mismatch in
telescope order, universe conventions, or de Bruijn arithmetic fails these
`rfl`s. -/

namespace Lean4Lean
namespace InductiveFixtures
open VInductDecl

/-- Permute the universe parameters of a translated constant. The `vconst`
and `vdefeq` macros number universes by occurrence order (declaration
levels first), while the kernel's recursors put the elimination level
first; these fixtures compare via the explicit permutation. -/
private def permC (ci : VConstant) (ls : List VLevel) : VConstant :=
  ⟨ci.uvars, ci.type.instL ls⟩

private def permE (df : VDefEq) (ls : List VLevel) : VDefEq :=
  ⟨df.uvars, df.lhs.instL ls, df.rhs.instL ls, df.type.instL ls⟩

/-! ## Nat -/

def natType : VInductiveType where
  name := ``Nat
  uvars := 0
  type := vexpr(Type)
  ctors := [⟨vconst(type_of% @Nat.zero), ``Nat.zero⟩, ⟨vconst(type_of% @Nat.succ), ``Nat.succ⟩]

def natDecl : VInductDecl := ⟨0, 0, [natType]⟩

example : natDecl.stage2 = true := rfl

/-- The generated recursor is exactly the kernel's `Nat.rec`. -/
example : recConst 0 ``Nat 0 natType = vconst(type_of% @Nat.rec) := rfl

/-- The generated iota rules are exactly the kernel's reduction rules for
`Nat.rec`, phrased as closed lambda-telescope defeqs like `quotDefEq`. -/
example : (rules 0 ``Nat 0 natType)[0]? =
    some (vdefeq(motive z s => @Nat.rec motive z s .zero ≡ z)) := rfl

example : (rules 0 ``Nat 0 natType)[1]? =
    some (vdefeq(motive z s n => @Nat.rec motive z s (.succ n) ≡ s n (@Nat.rec motive z s n))) :=
  rfl

example : (VEnv.empty.addInduct natDecl).isSome = true := rfl

example : (VEnv.empty.addInduct natDecl).map (·.constants ``Nat) =
    some (some natType.toVConstant) := rfl

example : (VEnv.empty.addInduct natDecl).map (·.constants ``Nat.rec) =
    some (some (recConst 0 ``Nat 0 natType)) := rfl

/-- The successor iota rule is registered in the output environment. -/
example : ∀ env', VEnv.empty.addInduct natDecl = some env' →
    env'.defeqs (rule 0 ``Nat 0 natType 1 ⟨vconst(type_of% @Nat.succ), ``Nat.succ⟩) := by
  rintro env' ⟨⟩; exact .inl rfl

/-! ## Bool -/

def boolType : VInductiveType where
  name := ``Bool
  uvars := 0
  type := vexpr(Type)
  ctors := [⟨vconst(type_of% @Bool.false), ``Bool.false⟩, ⟨vconst(type_of% @Bool.true), ``Bool.true⟩]

def boolDecl : VInductDecl := ⟨0, 0, [boolType]⟩

example : boolDecl.stage2 = true := rfl

example : recConst 0 ``Bool 0 boolType = vconst(type_of% @Bool.rec) := rfl

example : (rules 0 ``Bool 0 boolType)[0]? =
    some (vdefeq(motive f t => @Bool.rec motive f t .false ≡ f)) := rfl

example : (rules 0 ``Bool 0 boolType)[1]? =
    some (vdefeq(motive f t => @Bool.rec motive f t .true ≡ t)) := rfl

/-! ## List: one parameter, a dependent field, direct recursion -/

def listType : VInductiveType where
  name := ``List
  uvars := 1
  type := vconst(type_of% @List).type
  ctors := [⟨vconst(type_of% @List.nil), ``List.nil⟩, ⟨vconst(type_of% @List.cons), ``List.cons⟩]

def listDecl : VInductDecl := ⟨1, 1, [listType]⟩

example : listDecl.stage2 = true := rfl

/-- The generated recursor is exactly the kernel's `List.rec`, with the
occurrence-ordered `vconst` universes permuted to the kernel's
elimination-level-first convention. -/
example : recConst 1 ``List 1 listType =
    permC (vconst(type_of% @List.rec)) [.param 1, .param 0] := rfl

example : (rules 1 ``List 1 listType)[0]? =
    some (permE (vdefeq(α motive n c => @List.rec α motive n c (@List.nil α) ≡ n))
      [.param 1, .param 0]) := rfl

example : (rules 1 ``List 1 listType)[1]? =
    some (permE (vdefeq(α motive n c hd tl =>
        @List.rec α motive n c (@List.cons α hd tl) ≡
          c hd tl (@List.rec α motive n c tl)))
      [.param 1, .param 0]) := rfl

example : (VEnv.empty.addInduct listDecl).isSome = true := rfl

/-! ## Prod: two parameters, no recursion -/

def prodType : VInductiveType where
  name := ``Prod
  uvars := 2
  type := vconst(type_of% @Prod).type
  ctors := [⟨vconst(type_of% @Prod.mk), ``Prod.mk⟩]

def prodDecl : VInductDecl := ⟨2, 2, [prodType]⟩

example : prodDecl.stage2 = true := rfl

example : recConst 2 ``Prod 2 prodType =
    permC (vconst(type_of% @Prod.rec)) [.param 1, .param 2, .param 0] := rfl

example : (rules 2 ``Prod 2 prodType)[0]? =
    some (permE (vdefeq(α β motive mk a b =>
        @Prod.rec α β motive mk (@Prod.mk α β a b) ≡ mk a b))
      [.param 1, .param 2, .param 0]) := rfl

/-! ## Option: one parameter, two constructors -/

def optionType : VInductiveType where
  name := ``Option
  uvars := 1
  type := vconst(type_of% @Option).type
  ctors := [⟨vconst(type_of% @Option.none), ``Option.none⟩,
    ⟨vconst(type_of% @Option.some), ``Option.some⟩]

def optionDecl : VInductDecl := ⟨1, 1, [optionType]⟩

example : optionDecl.stage2 = true := rfl

example : recConst 1 ``Option 1 optionType =
    permC (vconst(type_of% @Option.rec)) [.param 1, .param 0] := rfl

example : (rules 1 ``Option 1 optionType)[0]? =
    some (permE (vdefeq(α motive n s => @Option.rec α motive n s (@Option.none α) ≡ n))
      [.param 1, .param 0]) := rfl

example : (rules 1 ``Option 1 optionType)[1]? =
    some (permE (vdefeq(α motive n s a => @Option.rec α motive n s (@Option.some α a) ≡ s a))
      [.param 1, .param 0]) := rfl

/-! ## Conservativity: outside the stage-2 class `addInduct` refuses. -/

/-- `Eq` has an index, so stage 2 rejects it (the type is not a sort past
its two parameters, and the constructor's result is not the type constant
applied to exactly the parameters). -/
example :
    VEnv.empty.addInduct ⟨1, 2, [{
      name := ``Eq
      uvars := 1
      type := vconst(type_of% @Eq).type
      ctors := [⟨vconst(type_of% @Eq.refl), ``Eq.refl⟩] }]⟩ = none := rfl

/-! ## The M2 axiom gate: `addInduct_WF` is proven without `sorry`. -/

/-- info: 'Lean4Lean.VEnv.addInduct_WF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms VEnv.addInduct_WF
