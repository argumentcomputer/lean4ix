import Lean4Lean.Theory.InductiveFixtures

/-!
# Constructor-validity parity fixtures

Focused singleton declarations for L4L-05.  The positive declarations retain
real kernel metadata while remaining inside the already-supported large-
elimination and non-K fragment.  The failed declarations pin the nearest
Lean elaborator/kernel rejection for each neighboring positivity or universe
branch; `#guard_msgs` rolls every failed declaration back.
-/

namespace Lean4Lean
namespace InductiveFixtures
open VInductDecl

universe u

/-! ## Type-valued dependency and positivity matrix -/

/-- A source-ordered constructor covering the non-Prop universe boundary,
dependent proof fields, direct recursion, a recursive function, and an
independent/dependent suffix after both recursive outer fields. -/
inductive ConstructorValidityMatrix (α : Type u) (P : α → Prop) : Type u where
  | mk (x : α) (proof : P x)
      (direct : ConstructorValidityMatrix α P)
      (function : (y : α) → ConstructorValidityMatrix α P)
      (later : α) (laterProof : P later) :
      ConstructorValidityMatrix α P

def constructorValidityMatrixType : VInductiveType where
  name := ``ConstructorValidityMatrix
  uvars := 1
  type := vconst(type_of% @ConstructorValidityMatrix).type
  ctors := [⟨vconst(type_of% @ConstructorValidityMatrix.mk),
    ``ConstructorValidityMatrix.mk⟩]

def constructorValidityMatrixDecl : VInductDecl :=
  ⟨1, 2, [constructorValidityMatrixType]⟩

example : constructorValidityMatrixDecl.stage3 = true := rfl

def constructorValidityMatrixChecked : constructorValidityMatrixDecl.Checked :=
  constructorValidityMatrixDecl.checked?.get (by decide)

def constructorValidityMatrixGenerationChecked :
    GenerationChecked constructorValidityMatrixDecl :=
  (identityGeneration? constructorValidityMatrixDecl).get (by decide)

private def l4l05PermC (constant : VConstant)
    (levels : List VLevel) : VConstant :=
  ⟨constant.uvars, constant.type.instL levels⟩

example : constructorValidityMatrixGenerationChecked.recursor =
    l4l05PermC (vconst(type_of% @ConstructorValidityMatrix.rec))
      [.param 1, .param 0] := rfl

example : constructorValidityMatrixChecked.resultLevel =
    .succ (.param 0) := rfl

example : constructorValidityMatrixChecked.constructors[0].fields.length = 6 :=
  rfl

example : constructorValidityMatrixChecked.constructors[0].recursive.map
    (fun position => (position.fieldIndex, position.binders.length)) =
      [(2, 0), (3, 1)] := rfl

example :
    constructorValidityMatrixGenerationChecked.generatedRules.length = 1 :=
  rfl

/-! ## Prop-valued recursive-function universe boundary -/

/-- The ordinary field `a : α` reaches the impredicative-Prop constructor
universe branch.  The varying recursive target prevents parameter promotion,
and the single constructor remains a legitimate non-K large eliminator. -/
inductive PropRecursiveBoundary (α : Type u) : α → Prop where
  | mk (a : α) (next : (b : α) → PropRecursiveBoundary α b) :
      PropRecursiveBoundary α a

def propRecursiveBoundaryType : VInductiveType where
  name := ``PropRecursiveBoundary
  uvars := 1
  type := vconst(type_of% @PropRecursiveBoundary).type
  ctors := [⟨vconst(type_of% @PropRecursiveBoundary.mk),
    ``PropRecursiveBoundary.mk⟩]

def propRecursiveBoundaryDecl : VInductDecl :=
  ⟨1, 1, [propRecursiveBoundaryType]⟩

example : propRecursiveBoundaryDecl.stage3 = true := rfl

def propRecursiveBoundaryChecked : propRecursiveBoundaryDecl.Checked :=
  propRecursiveBoundaryDecl.checked?.get (by decide)

def propRecursiveBoundaryGenerationChecked :
    GenerationChecked propRecursiveBoundaryDecl :=
  (identityGeneration? propRecursiveBoundaryDecl).get (by decide)

example : propRecursiveBoundaryGenerationChecked.recursor =
    l4l05PermC (vconst(type_of% @PropRecursiveBoundary.rec))
      [.param 1, .param 0] := rfl

example : propRecursiveBoundaryChecked.resultLevel = .zero := rfl

example : propRecursiveBoundaryChecked.constructors[0].fields.length = 2 := rfl

example : propRecursiveBoundaryChecked.constructors[0].recursive.map
    (fun position => (position.fieldIndex, position.binders.length)) =
      [(1, 1)] := rfl

example : propRecursiveBoundaryGenerationChecked.generatedRules.length = 1 :=
  rfl

/-! ## Nearest-kernel rejection matrix -/

namespace KernelDifferential

opaque L4L05TypeBox : Type → Type
opaque L4L05ProofBox : Type → Prop
opaque L4L05DepProofBox (α : Type) : α → Prop

/--
error: (kernel) arg #1 of 'Lean4Lean.InductiveFixtures.KernelDifferential.L4L05NestedNegative.mk' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive L4L05NestedNegative : Type where
  | mk : ((L4L05NestedNegative → Prop) → L4L05NestedNegative) →
      L4L05NestedNegative

/--
error: (kernel) arg #1 of 'Lean4Lean.InductiveFixtures.KernelDifferential.L4L05FamilyNonrecursive.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive L4L05FamilyNonrecursive : Type where
  | mk : L4L05TypeBox L4L05FamilyNonrecursive → L4L05FamilyNonrecursive

/--
error: (kernel) arg #1 of 'Lean4Lean.InductiveFixtures.KernelDifferential.L4L05FamilyProof.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive L4L05FamilyProof : Type where
  | mk : L4L05ProofBox L4L05FamilyProof → L4L05FamilyProof

/--
error: (kernel) arg #2 of 'Lean4Lean.InductiveFixtures.KernelDifferential.L4L05RecursiveDependency.mk' contains a non valid occurrence of the datatypes being declared
-/
#guard_msgs in
inductive L4L05RecursiveDependency : Type where
  | mk (recursive : L4L05RecursiveDependency)
      (proof : L4L05DepProofBox L4L05RecursiveDependency recursive) :
      L4L05RecursiveDependency

/--
error: Invalid universe level in constructor `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05UniverseReject.mk`: Parameter `α` has type
  Type
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
-/
#guard_msgs in
inductive L4L05UniverseReject : Type where
  | mk (α : Type) : L4L05UniverseReject

end KernelDifferential
end InductiveFixtures
end Lean4Lean
