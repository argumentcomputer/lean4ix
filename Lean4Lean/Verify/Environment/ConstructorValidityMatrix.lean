import Lean4Lean.Theory.ConstructorValidityFixtures
import Lean4Lean.Verify.Environment.InductiveFixtures

/-!
# L4L-05 constructor-validity differential matrix

The positive half quotes real Lean metadata, runs the ordinary normalization
candidate producer, then runs both strengthened constructor gates at their
actual pre-family and post-family environments.  The negative half pairs each failed
source declaration in `Theory.ConstructorValidityFixtures` with hand-built
metadata at the nearest ordinary-producer phase.
-/

namespace Lean4Lean.InductiveReplayFixtures
open Lean Meta Elab Term
open Lean4Lean.InductiveFixtures

/-! ## Actual positive metadata -/

def constructorValidityMatrixInfo : ConstantInfo :=
  kernelInductInfo% ConstructorValidityMatrix

def constructorValidityMatrixMkInfo : ConstantInfo :=
  kernelCtorInfo% ConstructorValidityMatrix.mk

def constructorValidityMatrixRecInfo : ConstantInfo :=
  kernelRecInfo% ConstructorValidityMatrix.rec

def constructorValidityMatrixKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% ConstructorValidityMatrix.rec 0

def constructorValidityMatrixKernelCtor : Constructor where
  name := constructorValidityMatrixMkInfo.name
  type := constructorValidityMatrixMkInfo.type

def constructorValidityMatrixKernelType : InductiveType where
  name := constructorValidityMatrixInfo.name
  type := constructorValidityMatrixInfo.type
  ctors := [constructorValidityMatrixKernelCtor]

def propRecursiveBoundaryInfo : ConstantInfo :=
  kernelInductInfo% PropRecursiveBoundary

def propRecursiveBoundaryMkInfo : ConstantInfo :=
  kernelCtorInfo% PropRecursiveBoundary.mk

def propRecursiveBoundaryRecInfo : ConstantInfo :=
  kernelRecInfo% PropRecursiveBoundary.rec

def propRecursiveBoundaryKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% PropRecursiveBoundary.rec 0

def propRecursiveBoundaryKernelCtor : Constructor where
  name := propRecursiveBoundaryMkInfo.name
  type := propRecursiveBoundaryMkInfo.type

def propRecursiveBoundaryKernelType : InductiveType where
  name := propRecursiveBoundaryInfo.name
  type := propRecursiveBoundaryInfo.type
  ctors := [propRecursiveBoundaryKernelCtor]

theorem constructorValidityMatrix_kernel_shape :
    (match constructorValidityMatrixInfo with
    | .inductInfo info => (info.numParams, info.numIndices)
    | _ => (0, 0)) = (2, 0) ∧
      (match constructorValidityMatrixMkInfo with
      | .ctorInfo info => info.numFields
      | _ => 0) = 6 ∧
      (match constructorValidityMatrixRecInfo with
      | .recInfo info =>
        (info.numParams, info.numIndices, info.numMotives,
          info.numMinors, info.rules.length)
      | _ => (0, 0, 0, 0, 0)) = (2, 0, 1, 1, 1) := by
  exact ⟨rfl, rfl, rfl⟩

theorem constructorValidityMatrix_recursive_positions_exact :
    constructorValidityMatrixChecked.constructors[0].recursive.map
      (fun position => (position.fieldIndex, position.binders.length)) =
        [(2, 0), (3, 1)] := rfl

theorem constructorValidityMatrix_kernel_rule_exact :
    constructorValidityMatrixKernelRuleRhs =
      constructorValidityMatrixGenerationChecked.generatedRules[0].rhs := rfl

theorem propRecursiveBoundary_kernel_shape :
    (match propRecursiveBoundaryInfo with
    | .inductInfo info => (info.numParams, info.numIndices)
    | _ => (0, 0)) = (1, 1) ∧
      (match propRecursiveBoundaryMkInfo with
      | .ctorInfo info => info.numFields
      | _ => 0) = 2 ∧
      (match propRecursiveBoundaryRecInfo with
      | .recInfo info =>
        (info.numParams, info.numIndices, info.numMotives,
          info.numMinors, info.rules.length)
      | _ => (0, 0, 0, 0, 0)) = (1, 1, 1, 1, 1) := by
  exact ⟨rfl, rfl, rfl⟩

theorem propRecursiveBoundary_recursive_positions_exact :
    propRecursiveBoundaryChecked.constructors[0].recursive.map
      (fun position => (position.fieldIndex, position.binders.length)) =
        [(1, 1)] := rfl

theorem propRecursiveBoundary_kernel_rule_exact :
    propRecursiveBoundaryKernelRuleRhs =
      propRecursiveBoundaryGenerationChecked.generatedRules[0].rhs := rfl

/-! ## Positive ordinary and strengthened gates -/

def constructorValidityMatrixContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_constructorValidityMatrix
    ({} : ConstMap)
  lparams := [`u]
  safety := .safe
  allowPrimitive := false

def propRecursiveBoundaryContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_propRecursiveBoundary
    ({} : ConstMap)
  lparams := [`u]
  safety := .safe
  allowPrimitive := false

def singletonCandidateExact (nparams : Nat) (source : InductiveType)
    (context : AddInductive.Context) : Bool :=
  match AddInductive.buildNormalizationCandidate nparams [source] 0 false
      context with
  | .error _ => false
  | .ok candidate =>
      candidate.families.singleton.familyType.type.view.equal source.type &&
        candidate.families.singleton.constructors.toList
          (fun _ constructor => constructor.type.view) ==
            source.ctors.map (fun constructor => constructor.type)

def singletonPreFamilyAccepted (nparams : Nat) (source : InductiveType)
    (context : AddInductive.Context) : Bool :=
  match AddInductive.buildNormalizationCandidate nparams [source] 0 false
      context with
  | .error _ => false
  | .ok candidate =>
      match AddInductive.checkInductiveTypes nparams #[source]
          (fun stats =>
            AddInductive.checkConstructorPreFamilySafety stats
              candidate.families.singleton.familyType.type.view
              candidate.families.singleton.constructors) context with
      | .ok _ => true
      | .error _ => false

def singletonUniverseAccepted (nparams : Nat) (source : InductiveType)
    (context : AddInductive.Context) : Bool :=
  match AddInductive.checkInductiveTypes nparams #[source]
      (fun stats => do
        let familyEnv ← AddInductive.declareInductiveTypes stats nparams
          #[source] 0 false
        AddInductive.withEnv familyEnv do
          AddInductive.checkConstructorUniverseListSemantics stats
            source.ctors) context with
  | .ok _ => true
  | .error _ => false

#guard singletonCandidateExact 2 constructorValidityMatrixKernelType
  constructorValidityMatrixContext

#guard singletonPreFamilyAccepted 2 constructorValidityMatrixKernelType
  constructorValidityMatrixContext

#guard singletonUniverseAccepted 2 constructorValidityMatrixKernelType
  constructorValidityMatrixContext

#guard singletonCandidateExact 1 propRecursiveBoundaryKernelType
  propRecursiveBoundaryContext

#guard singletonPreFamilyAccepted 1 propRecursiveBoundaryKernelType
  propRecursiveBoundaryContext

#guard singletonUniverseAccepted 1 propRecursiveBoundaryKernelType
  propRecursiveBoundaryContext

/-! ## Matching ordinary-producer rejections -/

def l4l05TypeBoxName : Name :=
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05TypeBox

def l4l05ProofBoxName : Name :=
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05ProofBox

def l4l05DepProofBoxName : Name :=
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05DepProofBox

def l4l05TypeBoxInfo : ConstantInfo := .axiomInfo {
  name := l4l05TypeBoxName
  levelParams := []
  type := .forallE `α (.sort (.succ .zero))
    (.sort (.succ .zero)) .default
  isUnsafe := false }

def l4l05ProofBoxInfo : ConstantInfo := .axiomInfo {
  name := l4l05ProofBoxName
  levelParams := []
  type := .forallE `α (.sort (.succ .zero)) (.sort .zero) .default
  isUnsafe := false }

def l4l05DepProofBoxInfo : ConstantInfo := .axiomInfo {
  name := l4l05DepProofBoxName
  levelParams := []
  type := .forallE `α (.sort (.succ .zero))
    (.forallE `value (.bvar 0) (.sort .zero) .default) .implicit
  isUnsafe := false }

def l4l05NegativeMap : ConstMap :=
  ((({} : ConstMap).insert l4l05TypeBoxName l4l05TypeBoxInfo).insert
    l4l05ProofBoxName l4l05ProofBoxInfo).insert
      l4l05DepProofBoxName l4l05DepProofBoxInfo

def l4l05NegativeContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_l4l05Negative l4l05NegativeMap
  lparams := []
  safety := .safe
  allowPrimitive := false

def l4l05UnsafeNegativeContext : AddInductive.Context :=
  { l4l05NegativeContext with safety := .unsafe }

def l4l05NegativeType (name ctorName : Name) (ctorType : Expr) :
    InductiveType where
  name := name
  type := .sort (.succ .zero)
  ctors := [{ name := ctorName, type := ctorType }]

def l4l05NestedNegativeName : Name :=
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05NestedNegative

def l4l05NestedNegativeMkName : Name :=
  .str l4l05NestedNegativeName "mk"

def l4l05NestedNegativeConst : Expr :=
  .const l4l05NestedNegativeName []

def l4l05NestedNegativeField : Expr :=
  .forallE `_
    (.forallE `_ l4l05NestedNegativeConst (.sort .zero) .default)
    l4l05NestedNegativeConst .default

def l4l05NestedNegativeType : InductiveType :=
  l4l05NegativeType l4l05NestedNegativeName l4l05NestedNegativeMkName
    (.forallE `field l4l05NestedNegativeField
      l4l05NestedNegativeConst .default)

def l4l05FamilyNonrecursiveName : Name :=
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05FamilyNonrecursive

def l4l05FamilyNonrecursiveMkName : Name :=
  .str l4l05FamilyNonrecursiveName "mk"

def l4l05FamilyNonrecursiveConst : Expr :=
  .const l4l05FamilyNonrecursiveName []

def l4l05FamilyNonrecursiveType : InductiveType :=
  l4l05NegativeType l4l05FamilyNonrecursiveName
    l4l05FamilyNonrecursiveMkName
    (.forallE `field
      (.app (.const l4l05TypeBoxName []) l4l05FamilyNonrecursiveConst)
      l4l05FamilyNonrecursiveConst .default)

def l4l05FamilyProofName : Name :=
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05FamilyProof

def l4l05FamilyProofMkName : Name :=
  .str l4l05FamilyProofName "mk"

def l4l05FamilyProofConst : Expr :=
  .const l4l05FamilyProofName []

def l4l05FamilyProofType : InductiveType :=
  l4l05NegativeType l4l05FamilyProofName l4l05FamilyProofMkName
    (.forallE `proof
      (.app (.const l4l05ProofBoxName []) l4l05FamilyProofConst)
      l4l05FamilyProofConst .default)

def l4l05RecursiveDependencyName : Name :=
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05RecursiveDependency

def l4l05RecursiveDependencyMkName : Name :=
  .str l4l05RecursiveDependencyName "mk"

def l4l05RecursiveDependencyConst : Expr :=
  .const l4l05RecursiveDependencyName []

def l4l05RecursiveDependencyProof : Expr :=
  .app (.app (.const l4l05DepProofBoxName [])
    l4l05RecursiveDependencyConst) (.bvar 0)

def l4l05RecursiveDependencyType : InductiveType :=
  l4l05NegativeType l4l05RecursiveDependencyName
    l4l05RecursiveDependencyMkName
    (.forallE `recursive l4l05RecursiveDependencyConst
      (.forallE `proof l4l05RecursiveDependencyProof
        l4l05RecursiveDependencyConst .default) .default)

def l4l05UniverseRejectName : Name :=
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05UniverseReject

def l4l05UniverseRejectMkName : Name :=
  .str l4l05UniverseRejectName "mk"

def l4l05UniverseRejectConst : Expr :=
  .const l4l05UniverseRejectName []

def l4l05UniverseRejectType : InductiveType :=
  l4l05NegativeType l4l05UniverseRejectName l4l05UniverseRejectMkName
    (.forallE `α (.sort (.succ .zero)) l4l05UniverseRejectConst .default)

def l4l05CandidateError (source : InductiveType) : Option String :=
  match AddInductive.buildNormalizationCandidate 0 [source] 0 false
      l4l05NegativeContext with
  | .error (.other message) => some message
  | _ => none

#guard l4l05CandidateError l4l05NestedNegativeType = some
  "arg #1 of 'Lean4Lean.InductiveFixtures.KernelDifferential.L4L05NestedNegative.mk' has a non positive occurrence of the datatypes being declared"

#guard l4l05CandidateError l4l05FamilyNonrecursiveType = some
  "arg #1 of 'Lean4Lean.InductiveFixtures.KernelDifferential.L4L05FamilyNonrecursive.mk' has a non valid occurrence of the datatypes being declared"

#guard l4l05CandidateError l4l05FamilyProofType = some
  "arg #1 of 'Lean4Lean.InductiveFixtures.KernelDifferential.L4L05FamilyProof.mk' has a non valid occurrence of the datatypes being declared"

#guard l4l05CandidateError l4l05RecursiveDependencyType = some
  "arg #2 of 'Lean4Lean.InductiveFixtures.KernelDifferential.L4L05RecursiveDependency.mk' has a non valid occurrence of the datatypes being declared"

#guard l4l05CandidateError l4l05UniverseRejectType = some
  "universe level of type_of(arg #1) of 'Lean4Lean.InductiveFixtures.KernelDifferential.L4L05UniverseReject.mk' is too big for the corresponding inductive datatype"

def l4l05RecursiveDependencyPreFamilyError : Option String :=
  match AddInductive.buildNormalizationCandidate 0
      [l4l05RecursiveDependencyType] 0 true l4l05UnsafeNegativeContext with
  | .error _ => none
  | .ok candidate =>
      match AddInductive.checkInductiveTypes 0
          #[l4l05RecursiveDependencyType]
          (fun stats =>
            AddInductive.checkConstructorPreFamilySafety stats
              candidate.families.singleton.familyType.type.view
              candidate.families.singleton.constructors)
          l4l05UnsafeNegativeContext with
      | .error (.other message) => some message
      | _ => none

#guard l4l05RecursiveDependencyPreFamilyError =
  some "constructor depends on an omitted recursive local"

end Lean4Lean.InductiveReplayFixtures
