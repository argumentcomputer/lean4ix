import Lean4Lean.Verify.Environment.InductiveFixtures
import Lean4Lean.Verify.Environment.IndexedVecSemanticReplay
import Lean4Lean.Verify.Environment.NormalizationElimination
import Lean4Lean.Verify.Environment.NormalizationReadiness
import Lean4Lean.Theory.MutualInductiveFixtures

/-!
# Mutual generation, preservation, and environment replay

The real `Tree`/`TreeList` and indexed mutual fixtures instantiate the
arbitrary-block validator traces, generate one recursor per family with one
globally flattened minor/rule inventory, and compare every kernel metadata
record.  Their Theory transactions stage all families before constructors,
all constructors before recursors, and all recursors before rules, then replay
the same phases through `TrEnv'.inductBlock` into aligned Verify environments.
-/

namespace Lean4Lean.MutualInductiveReplayFixtures

open Lean Meta Elab Term
open Kernel
open AddInductive
open VInductDecl
open Lean4Lean.MutualInductiveFixtures
open Lean4Lean.InductiveReplayFixtures

local instance : Inhabited VEnv := ⟨.empty⟩

/-- Quote a kernel recursor type using the recursor metadata's own universe
parameter order. -/
syntax "kernelRecConstant08C%" ident : term
syntax "kernelConstVType08C%" ident : term

elab_rules : term
  | `(kernelRecConstant08C% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .recInfo info ← getConstInfo name
      | throwError "expected recursor metadata for {name}"
    let type ← Lean4Lean.Meta.expandExpr info.type
    let type ← Lean4Lean.Meta.ofExpr info.levelParams {} type
    return toExpr ({ uvars := info.levelParams.length, type } : VConstant)

/-- Quote a stored kernel metadata type in that record's own universe order.
Together with the explicit record-field checks below, this observes universe
permutations as well as the translated type expression. -/
elab_rules : term
  | `(kernelConstVType08C% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let info ← getConstInfo name
    let type ← Lean4Lean.Meta.expandExpr info.type
    let type ← Lean4Lean.Meta.ofExpr info.levelParams {} type
    return toExpr type

/-! ## Complete block metadata parity -/

/-- One block-wide comparison between the retained Theory generation and all
kernel inductive metadata.  The nested lists preserve family/constructor
ownership and split each recursor's local rules out of the globally flattened
Theory rule list. -/
structure MutualKernelBlockRow where
  source : VInductDecl
  generation : BlockGenerationChecked source
  inductInfos : List ConstantInfo
  ctorInfos : List (List ConstantInfo)
  recInfos : List ConstantInfo
  familyTypes : List VExpr
  ctorTypes : List (List VExpr)
  recTypes : List VExpr
  ruleRhs : List (List VExpr)

namespace MutualKernelBlockRow

def ctorMatches (row : MutualKernelBlockRow)
    (family : NormalizedFamily) (cidx : Nat) (info : ConstantInfo)
    (constructor : NormalizedCtor) (storedType : VExpr) : Bool :=
  match info with
  | .ctorInfo ctor =>
      ctor.name == constructor.raw.name &&
        ctor.levelParams.length == row.source.uvars &&
        ctor.induct == family.raw.name &&
        ctor.cidx == cidx &&
        ctor.numParams == row.source.nparams &&
        ctor.numFields == constructor.view.fields.length &&
        !ctor.isUnsafe && storedType == constructor.raw.type
  | _ => false

def ctorsMatch (row : MutualKernelBlockRow)
    (family : NormalizedFamily) :
    List ConstantInfo → List NormalizedCtor → List VExpr → Nat → Bool
  | [], [], [], _ => true
  | info :: infos, constructor :: constructors, storedType :: storedTypes,
      cidx =>
      row.ctorMatches family cidx info constructor storedType &&
        row.ctorsMatch family infos constructors storedTypes (cidx + 1)
  | _, _, _, _ => false

def recursorMatches (row : MutualKernelBlockRow)
    (family : NormalizedFamily) (offset : Nat)
    (info : ConstantInfo) (storedType : VExpr)
    (rhs : List VExpr) : Bool :=
  match info with
  | .recInfo rec =>
      rec.name == .str family.raw.name "rec" &&
        rec.levelParams.length == row.generation.recUvars &&
        rec.all == row.source.types.map (·.name) &&
        rec.numParams == row.source.nparams &&
        rec.numIndices == family.view.indices.length &&
        rec.numMotives == row.generation.familyCount &&
        rec.numMinors == row.generation.minorCount &&
        rec.k == row.generation.kTarget &&
        !rec.isUnsafe &&
        rec.rules.map (fun rule => (rule.ctor, rule.nfields)) ==
          family.ctorPairs.map (fun constructor =>
            (constructor.raw.name, constructor.view.fields.length)) &&
        storedType == (row.generation.recursor family).type &&
        rhs == ((row.generation.generatedRules.drop offset).take
          family.ctorPairs.length |>.map (·.rhs))
  | _ => false

def familiesMatch (row : MutualKernelBlockRow) :
    List NormalizedFamily → List ConstantInfo → List (List ConstantInfo) →
      List ConstantInfo → List VExpr → List (List VExpr) → List VExpr →
      List (List VExpr) → Nat → Bool
  | [], [], [], [], [], [], [], [], _ => true
  | family :: families, inductInfo :: inductInfos,
      ctorInfos :: ctorInfosTail, recInfo :: recInfos,
      familyType :: familyTypes, ctorTypes :: ctorTypesTail,
      recType :: recTypes, ruleRhs :: ruleRhsTail, offset =>
      (match inductInfo with
        | .inductInfo induct =>
            induct.name == family.raw.name &&
              induct.levelParams.length == row.source.uvars &&
              induct.numParams == row.source.nparams &&
              induct.numIndices == family.view.indices.length &&
              induct.all == row.source.types.map (·.name) &&
              induct.ctors == family.raw.ctors.map (·.name) &&
              induct.numNested == 0 &&
              induct.isRec == row.generation.isRec &&
              induct.isReflexive == row.generation.isReflexive &&
              !induct.isUnsafe &&
              familyType == family.raw.type
        | _ => false) &&
      row.ctorsMatch family ctorInfos family.ctorPairs ctorTypes 0 &&
      row.recursorMatches family offset recInfo recType ruleRhs &&
      row.familiesMatch families inductInfos ctorInfosTail recInfos
        familyTypes ctorTypesTail recTypes ruleRhsTail
        (offset + family.ctorPairs.length)
  | _, _, _, _, _, _, _, _, _ => false

/-- Every list must agree position-for-position; no truncated family,
constructor, recursor, or rule inventory can satisfy the comparison. -/
def agrees (row : MutualKernelBlockRow) : Bool :=
  row.familiesMatch row.generation.families row.inductInfos row.ctorInfos
    row.recInfos row.familyTypes row.ctorTypes row.recTypes row.ruleRhs 0

end MutualKernelBlockRow

def kernelRecursorInfo? : ConstantInfo → Option RecursorVal
  | .recInfo info => some info
  | _ => none

/-! ## Executable kernel validation -/

def treeKernelInfo : ConstantInfo := kernelInductInfo% Tree
def treeListKernelInfo : ConstantInfo := kernelInductInfo% TreeList
def treeLeafKernelInfo : ConstantInfo := kernelCtorInfo% Tree.leaf
def treeNodeKernelInfo : ConstantInfo := kernelCtorInfo% Tree.node
def treeBranchKernelInfo : ConstantInfo := kernelCtorInfo% Tree.branch
def treeListNilKernelInfo : ConstantInfo := kernelCtorInfo% TreeList.nil
def treeListConsKernelInfo : ConstantInfo := kernelCtorInfo% TreeList.cons
def treeRecKernelInfo : ConstantInfo := kernelRecInfo% Tree.rec
def treeListRecKernelInfo : ConstantInfo := kernelRecInfo% TreeList.rec
def treeRecKernelConstant : VConstant := kernelRecConstant08C% Tree.rec
def treeListRecKernelConstant : VConstant :=
  kernelRecConstant08C% TreeList.rec
def treeLeafKernelRuleRhs : VExpr := kernelRecRuleRhs% Tree.rec 0
def treeNodeKernelRuleRhs : VExpr := kernelRecRuleRhs% Tree.rec 1
def treeBranchKernelRuleRhs : VExpr := kernelRecRuleRhs% Tree.rec 2
def treeListNilKernelRuleRhs : VExpr := kernelRecRuleRhs% TreeList.rec 0
def treeListConsKernelRuleRhs : VExpr := kernelRecRuleRhs% TreeList.rec 1

example : treeRecKernelConstant =
    treeGeneration.recursors[0].toVConstant := rfl
example : treeListRecKernelConstant =
    treeGeneration.recursors[1].toVConstant := rfl
example : treeLeafKernelRuleRhs = treeGeneration.generatedRules[0].rhs := rfl
example : treeNodeKernelRuleRhs = treeGeneration.generatedRules[1].rhs := rfl
example : treeBranchKernelRuleRhs = treeGeneration.generatedRules[2].rhs := rfl
example : treeListNilKernelRuleRhs = treeGeneration.generatedRules[3].rhs := rfl
example : treeListConsKernelRuleRhs = treeGeneration.generatedRules[4].rhs := rfl

def treeKernelType : InductiveType where
  name := treeKernelInfo.name
  type := treeKernelInfo.type
  ctors := [
    ⟨treeLeafKernelInfo.name, treeLeafKernelInfo.type⟩,
    ⟨treeNodeKernelInfo.name, treeNodeKernelInfo.type⟩,
    ⟨treeBranchKernelInfo.name, treeBranchKernelInfo.type⟩]

def treeListKernelType : InductiveType where
  name := treeListKernelInfo.name
  type := treeListKernelInfo.type
  ctors := [
    ⟨treeListNilKernelInfo.name, treeListNilKernelInfo.type⟩,
    ⟨treeListConsKernelInfo.name, treeListConsKernelInfo.type⟩]

def treeKernelTypes : List InductiveType :=
  [treeKernelType, treeListKernelType]

def treeKernelContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_mutualTree ({} : ConstMap)
  lparams := [`u]
  safety := .safe
  allowPrimitive := false

def treeBlockGenerationShapeResult :=
  produceBlockGenerationShapeCandidate treeDecl treeKernelTypes 0 false
    treeKernelContext

theorem treeBlockGenerationShapeResult_isOk :
    treeBlockGenerationShapeResult.isOk = true := by
  native_decide

def treeProducedBlockGenerationShape :
    { produced // treeBlockGenerationShapeResult = .ok produced } :=
  match h : treeBlockGenerationShapeResult with
  | .ok produced => ⟨produced, rfl⟩
  | .error _ => by
      have hOk := treeBlockGenerationShapeResult_isOk
      rw [h] at hOk
      contradiction

def treeBlockGenerationShape := treeProducedBlockGenerationShape.val

/-- All later validation and generation fixtures consume the one detailed
execution retained by the strengthened block-shape producer. -/
def treeExecution := treeBlockGenerationShape.execution

/-- The detailed normalization execution owns the exact mutual-family
statistics and continuation context selected by its own successful family
validation phase. -/
theorem treeExecution_familyValidationResult_run :
    observeFamilyValidationBlock 1 treeKernelTypes treeKernelContext =
      .ok treeExecution.familyValidationResult := by
  exact treeBlockGenerationShape.familyValidationResult_run

/-- The generalized generation-shape gate accepts the complete unindexed
mutual block produced by the ordinary kernel-facing candidate pass. -/
theorem treeExecution_generationShape :
    normalizationCandidateBlockGenerationShape treeDecl
      treeExecution.candidate = true :=
  treeBlockGenerationShape.shape

/-- Strengthen the retained ordinary producer through constructor declaration
and the exact elimination-level and K-target decisions used by the kernel. -/
def treeBlockEliminationShapeResult :=
  produceBlockEliminationShapeCandidate treeDecl treeKernelTypes 0 false
    treeKernelContext

theorem treeBlockEliminationShapeResult_isOk :
    treeBlockEliminationShapeResult.isOk = true := by
  native_decide

def treeProducedBlockEliminationShape :
    { produced // treeBlockEliminationShapeResult = .ok produced } :=
  match h : treeBlockEliminationShapeResult with
  | .ok produced => ⟨produced, rfl⟩
  | .error _ => by
      have hOk := treeBlockEliminationShapeResult_isOk
      rw [h] at hOk
      contradiction

def treeBlockEliminationShape := treeProducedBlockEliminationShape.val

def treeEliminationExecution := treeBlockEliminationShape.execution

/-- The strengthened run starts with exactly the detailed normalization
execution already retained by the generation-shape producer. -/
theorem treeEliminationNormalization_eq :
    treeEliminationExecution.normalization = treeExecution := by
  apply Except.ok.inj
  exact (treeEliminationExecution.normalization_run
    treeBlockEliminationShape.producedExecution).symm.trans
      treeBlockGenerationShape.producedExecution

theorem treeBlockEliminationBase_eq :
    treeBlockEliminationShape.base = treeBlockGenerationShape := by
  apply ProducedBlockGenerationShapeCandidate.eq_of_execution_eq
  exact treeEliminationNormalization_eq

/-- The actual post-constructor decisions agree with every elimination field
consumed by the ordinary mutual Theory generation. -/
def treeBlockEliminationAlignment :
    CheckerBlockEliminationRun treeGeneration treeEliminationExecution :=
  (CheckerBlockEliminationRun.build? treeGeneration
    treeEliminationExecution).get (by native_decide)

/-- The same ordinary block execution continued through actual recursor
synthesis and declaration. -/
def treeBlockRecursorShapeResult :=
  produceBlockRecursorShapeCandidate treeDecl treeKernelTypes 0 false
    treeKernelContext rfl

theorem treeBlockRecursorShapeResult_isOk :
    treeBlockRecursorShapeResult.isOk = true := by
  native_decide

def treeProducedBlockRecursorShape :
    { produced // treeBlockRecursorShapeResult = .ok produced } :=
  match h : treeBlockRecursorShapeResult with
  | .ok produced => ⟨produced, rfl⟩
  | .error _ => by
      have hOk := treeBlockRecursorShapeResult_isOk
      rw [h] at hOk
      contradiction

def treeBlockRecursorShape := treeProducedBlockRecursorShape.val

def treeRecursorExecution := treeBlockRecursorShape.execution

theorem treeRecursorElimination_eq :
    treeRecursorExecution.eliminationExecution =
      treeEliminationExecution := by
  apply Except.ok.inj
  exact (treeRecursorExecution.prefix_run
    treeBlockRecursorShape.producedExecution).symm.trans
      treeBlockEliminationShape.producedExecution

theorem treeBlockRecursorEliminationBase_eq :
    treeBlockRecursorShape.eliminationBase =
      treeBlockEliminationShape := by
  apply ProducedBlockEliminationShapeCandidate.eq_of_execution_eq
  exact treeRecursorElimination_eq

/-- The records synthesized by the instrumented ordinary run are the complete
kernel recursor records, including their rule payloads. -/
theorem treeGeneratedRecursorInfos_match :
    List.beq (treeRecursorExecution.recursors.infos.map some)
      [kernelRecursorInfo? treeRecKernelInfo,
        kernelRecursorInfo? treeListRecKernelInfo] = true := by
  native_decide

/-- Stored kernel recursor records in the same family order as the ordinary
producer.  The preceding `Option`-valued comparison also checks that both
lookups really are recursor records. -/
def treeExpectedRecursorInfos : List RecursorVal :=
  [(kernelRecursorInfo? treeRecKernelInfo).get!,
    (kernelRecursorInfo? treeListRecKernelInfo).get!]

theorem treeGeneratedAddInductiveRun :
    AddInductive.run treeDecl.nparams treeKernelTypes 0 treeKernelContext =
      .ok treeRecursorExecution.recursors.env :=
  treeBlockRecursorShape.addInductiveRun

/-- A shortened raw family inventory cannot pass the complete block gate. -/
theorem treeExecution_shortGenerationShape_rejected :
    normalizationCandidateBlockGenerationShape
      { treeDecl with types := [treeType] } treeExecution.candidate = false := by
  native_decide

def treeFamilyValidationResult :=
  FamilyValidationBlockRun.buildExecution 1 treeKernelTypes treeKernelContext

theorem treeFamilyValidationResult_isOk :
    treeFamilyValidationResult.isOk = true := by
  native_decide

def treeProducedFamilyValidation :
    { run // treeFamilyValidationResult = .ok run } :=
  match h : treeFamilyValidationResult with
  | .ok run => ⟨run, rfl⟩
  | .error _ => by
      have hOk := treeFamilyValidationResult_isOk
      rw [h] at hOk
      contradiction

/-- The proof-carrying terminal family invariants come from the same detailed
execution as the block-generation shape.  The separately replayed result
above remains an independent executable parity check. -/
def treeFamilyValidation :
    FamilyValidationBlockRun 1 treeKernelTypes treeKernelContext :=
  treeBlockGenerationShape.familyValidation (by decide)

def treeConstructorContext : AddInductive.Context :=
  { treeExecution.validationContext with env := treeExecution.familyEnv }

def treeConstructorValidationResult :=
  ConstructorBlockValidationRun.buildExecution treeKernelTypes
    treeExecution.stats false treeConstructorContext

theorem treeConstructorValidationResult_isOk :
    treeConstructorValidationResult.isOk = true := by
  native_decide

def treeProducedConstructorValidation :
    { run // treeConstructorValidationResult = .ok run } :=
  match h : treeConstructorValidationResult with
  | .ok run => ⟨run, rfl⟩
  | .error _ => by
      have hOk := treeConstructorValidationResult_isOk
      rw [h] at hOk
      contradiction

/-- Constructor semantics are consumed from the exact successful validation
equation retained by the ordinary normalization execution. -/
def treeConstructorValidation :
    ConstructorBlockValidationRun treeKernelTypes treeExecution.stats false
      treeConstructorContext :=
  treeBlockGenerationShape.constructorValidation

/-- The real positivity traversal selects both sibling targets and records the
one Pi binder above `Tree.branch`'s recursive occurrence. -/
theorem treeConstructorTargets_exact :
    treeConstructorValidation.traces.targets =
      [
        [[none],
          [some { familyIdx := 1, binderDepth := 0 }],
          [some { familyIdx := 1, binderDepth := 1 }]],
        [[],
          [some { familyIdx := 0, binderDepth := 0 },
            some { familyIdx := 1, binderDepth := 0 }]]
      ] := by
  native_decide

example : treeFamilyValidation.parameters.size = 1 :=
  treeFamilyValidation.params_size

example : treeFamilyValidation.result.stats.nindices = #[0, 0] := by
  native_decide

#guard AddInductive.levelStructEq treeFamilyValidation.resultLevel
  (.succ (.param `u))

#guard AddInductive.levelStructEq treeExecution.stats.resultLevel
  (.succ (.param `u))

def indexedTreeKernelInfo : ConstantInfo := kernelInductInfo% IndexedTree
def indexedTreeListKernelInfo : ConstantInfo :=
  kernelInductInfo% IndexedTreeList
def indexedTreeLeafKernelInfo : ConstantInfo :=
  kernelCtorInfo% IndexedTree.leaf
def indexedTreeNodeKernelInfo : ConstantInfo :=
  kernelCtorInfo% IndexedTree.node
def indexedTreeListNilKernelInfo : ConstantInfo :=
  kernelCtorInfo% IndexedTreeList.nil
def indexedTreeListConsKernelInfo : ConstantInfo :=
  kernelCtorInfo% IndexedTreeList.cons
def indexedTreeRecKernelInfo : ConstantInfo :=
  kernelRecInfo% IndexedTree.rec
def indexedTreeListRecKernelInfo : ConstantInfo :=
  kernelRecInfo% IndexedTreeList.rec
def indexedTreeRecKernelConstant : VConstant :=
  kernelRecConstant08C% IndexedTree.rec
def indexedTreeListRecKernelConstant : VConstant :=
  kernelRecConstant08C% IndexedTreeList.rec
def indexedTreeLeafKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedTree.rec 0
def indexedTreeNodeKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedTree.rec 1
def indexedTreeListNilKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedTreeList.rec 0
def indexedTreeListConsKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedTreeList.rec 1

example : indexedTreeRecKernelConstant =
    indexedTreeGeneration.recursors[0].toVConstant := rfl
example : indexedTreeListRecKernelConstant =
    indexedTreeGeneration.recursors[1].toVConstant := rfl
example : indexedTreeLeafKernelRuleRhs =
    indexedTreeGeneration.generatedRules[0].rhs := rfl
example : indexedTreeNodeKernelRuleRhs =
    indexedTreeGeneration.generatedRules[1].rhs := rfl
example : indexedTreeListNilKernelRuleRhs =
    indexedTreeGeneration.generatedRules[2].rhs := rfl
example : indexedTreeListConsKernelRuleRhs =
    indexedTreeGeneration.generatedRules[3].rhs := rfl

/-- Complete kernel/Theory metadata row for the unindexed mutual block. -/
def treeKernelBlockRow : MutualKernelBlockRow where
  source := treeDecl
  generation := treeGeneration
  inductInfos := [treeKernelInfo, treeListKernelInfo]
  ctorInfos := [
    [treeLeafKernelInfo, treeNodeKernelInfo, treeBranchKernelInfo],
    [treeListNilKernelInfo, treeListConsKernelInfo]]
  recInfos := [treeRecKernelInfo, treeListRecKernelInfo]
  familyTypes := [kernelConstVType08C% Tree,
    kernelConstVType08C% TreeList]
  ctorTypes := [
    [kernelConstVType08C% Tree.leaf, kernelConstVType08C% Tree.node,
      kernelConstVType08C% Tree.branch],
    [kernelConstVType08C% TreeList.nil,
      kernelConstVType08C% TreeList.cons]]
  recTypes := [kernelConstVType08C% Tree.rec,
    kernelConstVType08C% TreeList.rec]
  ruleRhs := [
    [treeLeafKernelRuleRhs, treeNodeKernelRuleRhs,
      treeBranchKernelRuleRhs],
    [treeListNilKernelRuleRhs, treeListConsKernelRuleRhs]]

#guard treeKernelBlockRow.agrees

/-- Complete kernel/Theory metadata row for the indexed mutual block. -/
def indexedTreeKernelBlockRow : MutualKernelBlockRow where
  source := indexedTreeDecl
  generation := indexedTreeGeneration
  inductInfos := [indexedTreeKernelInfo, indexedTreeListKernelInfo]
  ctorInfos := [
    [indexedTreeLeafKernelInfo, indexedTreeNodeKernelInfo],
    [indexedTreeListNilKernelInfo, indexedTreeListConsKernelInfo]]
  recInfos := [indexedTreeRecKernelInfo, indexedTreeListRecKernelInfo]
  familyTypes := [kernelConstVType08C% IndexedTree,
    kernelConstVType08C% IndexedTreeList]
  ctorTypes := [
    [kernelConstVType08C% IndexedTree.leaf,
      kernelConstVType08C% IndexedTree.node],
    [kernelConstVType08C% IndexedTreeList.nil,
      kernelConstVType08C% IndexedTreeList.cons]]
  recTypes := [kernelConstVType08C% IndexedTree.rec,
    kernelConstVType08C% IndexedTreeList.rec]
  ruleRhs := [
    [indexedTreeLeafKernelRuleRhs, indexedTreeNodeKernelRuleRhs],
    [indexedTreeListNilKernelRuleRhs, indexedTreeListConsKernelRuleRhs]]

#guard indexedTreeKernelBlockRow.agrees

def indexedTreeKernelType : InductiveType where
  name := indexedTreeKernelInfo.name
  type := indexedTreeKernelInfo.type
  ctors := [
    ⟨indexedTreeLeafKernelInfo.name, indexedTreeLeafKernelInfo.type⟩,
    ⟨indexedTreeNodeKernelInfo.name, indexedTreeNodeKernelInfo.type⟩]

def indexedTreeListKernelType : InductiveType where
  name := indexedTreeListKernelInfo.name
  type := indexedTreeListKernelInfo.type
  ctors := [
    ⟨indexedTreeListNilKernelInfo.name, indexedTreeListNilKernelInfo.type⟩,
    ⟨indexedTreeListConsKernelInfo.name, indexedTreeListConsKernelInfo.type⟩]

def indexedTreeKernelTypes : List InductiveType :=
  [indexedTreeKernelType, indexedTreeListKernelType]

def indexedTreeKernelContext : AddInductive.Context where
  env := Kernel.Environment.ofConstants `_mutualIndexedTree natMap
  lparams := [`u]
  safety := .safe
  allowPrimitive := false

def indexedTreeBlockGenerationShapeResult :=
  produceBlockGenerationShapeCandidate indexedTreeDecl indexedTreeKernelTypes
    0 false indexedTreeKernelContext

theorem indexedTreeBlockGenerationShapeResult_isOk :
    indexedTreeBlockGenerationShapeResult.isOk = true := by
  native_decide

def indexedTreeProducedBlockGenerationShape :
    { produced // indexedTreeBlockGenerationShapeResult = .ok produced } :=
  match h : indexedTreeBlockGenerationShapeResult with
  | .ok produced => ⟨produced, rfl⟩
  | .error _ => by
      have hOk := indexedTreeBlockGenerationShapeResult_isOk
      rw [h] at hOk
      contradiction

def indexedTreeBlockGenerationShape :=
  indexedTreeProducedBlockGenerationShape.val

/-- The indexed block likewise uses the one detailed execution retained by
its successful shape producer. -/
def indexedTreeExecution := indexedTreeBlockGenerationShape.execution

/-- The indexed detailed execution retains the exact result of the family
validator which invoked its post-validation phases. -/
theorem indexedTreeExecution_familyValidationResult_run :
    observeFamilyValidationBlock 1 indexedTreeKernelTypes
      indexedTreeKernelContext =
      .ok indexedTreeExecution.familyValidationResult := by
  exact indexedTreeBlockGenerationShape.familyValidationResult_run

/-- The complete indexed mutual candidate also satisfies the generalized
source-ordered generation-shape gate. -/
theorem indexedTreeExecution_generationShape :
    normalizationCandidateBlockGenerationShape indexedTreeDecl
      indexedTreeExecution.candidate = true :=
  indexedTreeBlockGenerationShape.shape

/-- Indexed counterpart of the retained post-constructor elimination
execution. -/
def indexedTreeBlockEliminationShapeResult :=
  produceBlockEliminationShapeCandidate indexedTreeDecl indexedTreeKernelTypes
    0 false indexedTreeKernelContext

theorem indexedTreeBlockEliminationShapeResult_isOk :
    indexedTreeBlockEliminationShapeResult.isOk = true := by
  native_decide

def indexedTreeProducedBlockEliminationShape :
    { produced // indexedTreeBlockEliminationShapeResult = .ok produced } :=
  match h : indexedTreeBlockEliminationShapeResult with
  | .ok produced => ⟨produced, rfl⟩
  | .error _ => by
      have hOk := indexedTreeBlockEliminationShapeResult_isOk
      rw [h] at hOk
      contradiction

def indexedTreeBlockEliminationShape :=
  indexedTreeProducedBlockEliminationShape.val

def indexedTreeEliminationExecution :=
  indexedTreeBlockEliminationShape.execution

theorem indexedTreeEliminationNormalization_eq :
    indexedTreeEliminationExecution.normalization =
      indexedTreeExecution := by
  apply Except.ok.inj
  exact (indexedTreeEliminationExecution.normalization_run
    indexedTreeBlockEliminationShape.producedExecution).symm.trans
      indexedTreeBlockGenerationShape.producedExecution

theorem indexedTreeBlockEliminationBase_eq :
    indexedTreeBlockEliminationShape.base =
      indexedTreeBlockGenerationShape := by
  apply ProducedBlockGenerationShapeCandidate.eq_of_execution_eq
  exact indexedTreeEliminationNormalization_eq

def indexedTreeBlockEliminationAlignment :
    CheckerBlockEliminationRun indexedTreeGeneration
      indexedTreeEliminationExecution :=
  (CheckerBlockEliminationRun.build? indexedTreeGeneration
    indexedTreeEliminationExecution).get (by native_decide)

def indexedTreeBlockRecursorShapeResult :=
  produceBlockRecursorShapeCandidate indexedTreeDecl indexedTreeKernelTypes
    0 false indexedTreeKernelContext rfl

theorem indexedTreeBlockRecursorShapeResult_isOk :
    indexedTreeBlockRecursorShapeResult.isOk = true := by
  native_decide

def indexedTreeProducedBlockRecursorShape :
    { produced // indexedTreeBlockRecursorShapeResult = .ok produced } :=
  match h : indexedTreeBlockRecursorShapeResult with
  | .ok produced => ⟨produced, rfl⟩
  | .error _ => by
      have hOk := indexedTreeBlockRecursorShapeResult_isOk
      rw [h] at hOk
      contradiction

def indexedTreeBlockRecursorShape :=
  indexedTreeProducedBlockRecursorShape.val

def indexedTreeRecursorExecution := indexedTreeBlockRecursorShape.execution

theorem indexedTreeRecursorElimination_eq :
    indexedTreeRecursorExecution.eliminationExecution =
      indexedTreeEliminationExecution := by
  apply Except.ok.inj
  exact (indexedTreeRecursorExecution.prefix_run
    indexedTreeBlockRecursorShape.producedExecution).symm.trans
      indexedTreeBlockEliminationShape.producedExecution

theorem indexedTreeBlockRecursorEliminationBase_eq :
    indexedTreeBlockRecursorShape.eliminationBase =
      indexedTreeBlockEliminationShape := by
  apply ProducedBlockEliminationShapeCandidate.eq_of_execution_eq
  exact indexedTreeRecursorElimination_eq

theorem indexedTreeGeneratedRecursorInfos_match :
    List.beq (indexedTreeRecursorExecution.recursors.infos.map some)
      [kernelRecursorInfo? indexedTreeRecKernelInfo,
        kernelRecursorInfo? indexedTreeListRecKernelInfo] = true := by
  native_decide

def indexedTreeExpectedRecursorInfos : List RecursorVal :=
  [(kernelRecursorInfo? indexedTreeRecKernelInfo).get!,
    (kernelRecursorInfo? indexedTreeListRecKernelInfo).get!]

theorem indexedTreeGeneratedAddInductiveRun :
    AddInductive.run indexedTreeDecl.nparams indexedTreeKernelTypes 0
        indexedTreeKernelContext =
      .ok indexedTreeRecursorExecution.recursors.env :=
  indexedTreeBlockRecursorShape.addInductiveRun

def indexedTreeFamilyValidationResult :=
  FamilyValidationBlockRun.buildExecution 1 indexedTreeKernelTypes
    indexedTreeKernelContext

theorem indexedTreeFamilyValidationResult_isOk :
    indexedTreeFamilyValidationResult.isOk = true := by
  native_decide

def indexedTreeProducedFamilyValidation :
    { run // indexedTreeFamilyValidationResult = .ok run } :=
  match h : indexedTreeFamilyValidationResult with
  | .ok run => ⟨run, rfl⟩
  | .error _ => by
      have hOk := indexedTreeFamilyValidationResult_isOk
      rw [h] at hOk
      contradiction

/-- The indexed terminal family invariants are owned by the block producer's
single detailed execution; the standalone builder above remains a parity
check. -/
def indexedTreeFamilyValidation :
    FamilyValidationBlockRun 1 indexedTreeKernelTypes
      indexedTreeKernelContext :=
  indexedTreeBlockGenerationShape.familyValidation (by decide)

def indexedTreeConstructorContext : AddInductive.Context :=
  { indexedTreeExecution.validationContext with
    env := indexedTreeExecution.familyEnv }

def indexedTreeConstructorValidationResult :=
  ConstructorBlockValidationRun.buildExecution indexedTreeKernelTypes
    indexedTreeExecution.stats false indexedTreeConstructorContext

theorem indexedTreeConstructorValidationResult_isOk :
    indexedTreeConstructorValidationResult.isOk = true := by
  native_decide

def indexedTreeProducedConstructorValidation :
    { run // indexedTreeConstructorValidationResult = .ok run } :=
  match h : indexedTreeConstructorValidationResult with
  | .ok run => ⟨run, rfl⟩
  | .error _ => by
      have hOk := indexedTreeConstructorValidationResult_isOk
      rw [h] at hOk
      contradiction

/-- The indexed fixture likewise consumes the real execution's exact
constructor-validation equation rather than selecting a parallel trace. -/
def indexedTreeConstructorValidation :
    ConstructorBlockValidationRun indexedTreeKernelTypes
      indexedTreeExecution.stats false indexedTreeConstructorContext :=
  indexedTreeBlockGenerationShape.constructorValidation

/-- Indexed recursive fields retain sibling ordinals after the ordinary Nat
binder, while nonrecursive fields occupy explicit `none` slots. -/
theorem indexedTreeConstructorTargets_exact :
    indexedTreeConstructorValidation.traces.targets =
      [
        [[none],
          [none, some { familyIdx := 1, binderDepth := 0 }]],
        [[],
          [none,
            some { familyIdx := 0, binderDepth := 0 },
            some { familyIdx := 1, binderDepth := 0 }]]
      ] := by
  native_decide

example : indexedTreeFamilyValidation.parameters.size = 1 :=
  indexedTreeFamilyValidation.params_size

example : indexedTreeFamilyValidation.result.stats.nindices = #[1, 1] := by
  native_decide

#guard AddInductive.levelStructEq indexedTreeFamilyValidation.resultLevel
  (.succ (.param `u))

/-! ## Phase-specific failures -/

def treeParameterMismatchType : InductiveType :=
  { treeListKernelType with
    type := .forallE `α (.sort .zero) (.sort (.succ (.param `u))) .default }

#guard match observeFamilyValidationBlock 1
    [treeKernelType, treeParameterMismatchType] treeKernelContext with
  | .error (.other message) =>
      message == "parameters of all inductive datatypes must match"
  | _ => false

def treeResultUniverseMismatchType : InductiveType :=
  { treeListKernelType with
    type := .forallE `α (.sort (.succ (.param `u))) (.sort .zero) .default }

#guard match observeFamilyValidationBlock 1
    [treeKernelType, treeResultUniverseMismatchType] treeKernelContext with
  | .error (.other message) =>
      message == "mutually inductive types must live in the same universe"
  | _ => false

/-- Reusing the original family statistics after swapping source owners
reaches constructor validation and fails at the first now-misowned return. -/
def treeReorderedConstructorResult :=
  checkConstructors #[treeListKernelType, treeKernelType]
    treeExecution.stats false treeConstructorContext

#guard match treeReorderedConstructorResult with
  | .error (.other message) =>
      message ==
        "invalid return type for 'Lean4Lean.MutualInductiveFixtures.TreeList.nil'"
  | _ => false

def treeReorderedView : VInductDecl :=
  { treeDecl with types := [treeListType, treeType] }

/- Raw/view normalization rejects family reordering before semantic evidence
can be attached to the dependent candidate list. -/
#guard (normalization? treeDecl treeReorderedView).isNone

/-! The host elaborator diagnostics independently pin the corresponding
family-validation phases in Lean itself. -/

namespace KernelPhases

universe v

/--
error: Invalid mutually inductive types: Parameter `α` has type
  Prop
of sort `Type` but is expected to have type
  Type v
of sort `Type (v + 1)`
-/
#guard_msgs in
mutual
inductive ParamA (α : Type v) : Type v
inductive ParamB (α : Prop) : Type v
end

/--
error: Invalid mutually inductive types: The resulting type of this declaration
  Prop
differs from a preceding one
  Type v

Note: All inductive types declared in the same `mutual` block must belong to the same type universe
-/
#guard_msgs in
mutual
inductive UniverseA (α : Type v) : Type v
inductive UniverseB (α : Type v) : Prop
end

end KernelPhases

/-! ## Tree/TreeList Theory semantics -/

def treeBlockEnv : VEnv :=
  (VEnv.empty.stageInductiveTypes treeDecl.types).get!

theorem treeStage :
    VEnv.empty.stageInductiveTypes treeDecl.types = some treeBlockEnv := by
  rfl

theorem empty_le_treeBlockEnv : VEnv.empty ≤ treeBlockEnv where
  constants h := by simp [VEnv.empty] at h
  defeqs h := h.elim
  structEtas h := h.elim

theorem treeFamilyTypeWF (type : VInductiveType)
    (h : type = treeType ∨ type = treeListType) :
    type.type.WF VEnv.empty type.uvars [] := by
  rcases h with rfl | rfl <;>
    refine ⟨.sort (.imax (.succ (.succ (.param 0)))
      (.succ (.succ (.param 0)))), VEnv.HasType.forallE ?_ ?_⟩ <;>
    exact VEnv.HasType.sort (by decide)

theorem treeCtorWF (ctor : VConstVal)
    (h : ctor ∈ treeType.ctors ∨ ctor ∈ treeListType.ctors) :
    ctor.type.WF treeBlockEnv 1 [] := by
  have hTree : treeBlockEnv.constants ``Tree =
      some treeType.toVConstant := by rfl
  have hTreeList : treeBlockEnv.constants ``TreeList =
      some treeListType.toVConstant := by rfl
  rcases h with h | h
  · simp [treeType] at h
    rcases h with (rfl | rfl | rfl)
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, by type_tac⟩
  · simp [treeListType] at h
    rcases h with (rfl | rfl)
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, by type_tac⟩

theorem treeNormalizationBlockWF :
    (Normalization.identity treeDecl).BlockWF VEnv.empty treeBlockEnv := by
  refine ⟨treeStage, ?_⟩
  change List.Forall₂ _ [treeType, treeListType] [treeType, treeListType]
  apply List.Forall₂.cons
  · refine ⟨?_, ?_⟩
    · exact VEnv.IsDefEqU.refl (treeFamilyTypeWF treeType (.inl rfl))
    · apply List.Forall₂.rfl
      intro ctor h
      exact VEnv.IsDefEqU.refl (treeCtorWF ctor (.inl h))
  · apply List.Forall₂.cons
    · refine ⟨?_, ?_⟩
      · exact VEnv.IsDefEqU.refl (treeFamilyTypeWF treeListType (.inr rfl))
      · apply List.Forall₂.rfl
        intro ctor h
        exact VEnv.IsDefEqU.refl (treeCtorWF ctor (.inr h))
    · exact .nil

theorem treeLeafSemantic :
    let constructor := CheckedCtor.ofBlock treeDecl treeType.ctors[0]
    checkedBlockFieldsWF VEnv.empty 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      VEnv.empty.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[0]).fields =
      [.bvar 0] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[0]).recursiveAt =
      [none] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[0]).resultIndices =
      [] by rfl]
  exact ⟨⟨⟨.succ (.param 0), .bvar .zero,
    .inr (VLevel.le_refl _)⟩, trivial⟩, .nil⟩

theorem treeNodeSemantic :
    let constructor := CheckedCtor.ofBlock treeDecl treeType.ctors[1]
    checkedBlockFieldsWF VEnv.empty 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      VEnv.empty.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[1]).fields =
      [.app (.const ``TreeList [.param 0]) (.bvar 0)] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[1]).recursiveAt =
      [some ({
        fieldIndex := 0
        binders := []
        targetType := 1
        indices := [] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[1]).resultIndices =
      [] by rfl]
  exact ⟨⟨⟨rfl, trivial, .nil⟩, trivial⟩, .nil⟩

theorem treeBranchSemantic :
    let constructor := CheckedCtor.ofBlock treeDecl treeType.ctors[2]
    checkedBlockFieldsWF VEnv.empty 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      VEnv.empty.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[2]).fields =
      [.forallE (.bvar 0)
        (.app (.const ``TreeList [.param 0]) (.bvar 1))] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[2]).recursiveAt =
      [some ({
        fieldIndex := 0
        binders := [.bvar 0]
        targetType := 1
        indices := [] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeType.ctors[2]).resultIndices =
      [] by rfl]
  exact ⟨
    ⟨⟨rfl, ⟨⟨⟨.succ (.param 0), .bvar .zero⟩, trivial⟩, .nil⟩⟩,
      trivial⟩,
    .nil⟩

theorem treeListNilSemantic :
    let constructor := CheckedCtor.ofBlock treeDecl treeListType.ctors[0]
    checkedBlockFieldsWF VEnv.empty 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      VEnv.empty.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[0]).fields =
      [] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[0]).recursiveAt =
      [] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[0]).resultIndices =
      [] by rfl]
  exact ⟨trivial, .nil⟩

theorem treeListConsSemantic :
    let constructor := CheckedCtor.ofBlock treeDecl treeListType.ctors[1]
    checkedBlockFieldsWF VEnv.empty 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      VEnv.empty.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[1]).fields =
      [.app (.const ``Tree [.param 0]) (.bvar 0),
        .app (.const ``TreeList [.param 0]) (.bvar 1)] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[1]).recursiveAt =
      [some ({
          fieldIndex := 0
          binders := []
          targetType := 0
          indices := [] } : RecArg),
        some ({
          fieldIndex := 1
          binders := []
          targetType := 1
          indices := [] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock treeDecl treeListType.ctors[1]).resultIndices =
      [] by rfl]
  exact ⟨
    ⟨⟨rfl, trivial, .nil⟩,
      ⟨⟨rfl, trivial, .nil⟩, trivial⟩⟩,
    .nil⟩

theorem treeCheckedBlockWF :
    treeChecked.WF VEnv.empty (.succ (.param 0)) := by
  have hparams : treeChecked.params =
      [.sort (.succ (.param 0))] := rfl
  have hindices : treeChecked.families.indices = [[], []] := rfl
  have hlevels : treeChecked.families.resultLevels =
      [.succ (.param 0), .succ (.param 0)] := rfl
  have hconstructors : treeChecked.families.constructors =
      [treeType.ctors.map (CheckedCtor.ofBlock treeDecl),
        treeListType.ctors.map (CheckedCtor.ofBlock treeDecl)] := rfl
  rw [CheckedBlock.WF, hindices, hlevels, hconstructors]
  rw [hparams]
  simp only [checkedFamilyListsWF]
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
  · exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
  · intro ctor h
    simp [treeType] at h
    rcases h with rfl | rfl | rfl
    · exact treeLeafSemantic
    · exact treeNodeSemantic
    · exact treeBranchSemantic
  · exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
  · refine ⟨?_, trivial⟩
    intro ctor h
    simp [treeListType] at h
    rcases h with rfl | rfl
    · exact treeListNilSemantic
    · exact treeListConsSemantic

def treeNormalizedBlock : NormalizedCheckedBlock treeDecl where
  normalization := Normalization.identity treeDecl
  checked := treeChecked
  checked_eq := (Option.some_get (x := treeDecl.checkedBlock?)
    (by decide)).symm

def treeValidatedBlock : ValidatedBlock treeDecl where
  block := treeNormalizedBlock
  resultLevel := .succ (.param 0)

/-- Exact validation-only semantic package for the unindexed mutual block. -/
def treeValidationCertificate : ValidationCertificate treeDecl VEnv.empty where
  validated := treeValidatedBlock
  blockEnv := treeBlockEnv
  wf := ⟨treeNormalizationBlockWF, treeCheckedBlockWF⟩

/-! ## IndexedTree/IndexedTreeList Theory semantics -/

def indexedTreeBlockEnv : VEnv :=
  (natFinalEnv.stageInductiveTypes indexedTreeDecl.types).get!

theorem indexedTreeStage :
    natFinalEnv.stageInductiveTypes indexedTreeDecl.types =
      some indexedTreeBlockEnv := by
  rfl

theorem indexedTreeFamilyTypeWF (type : VInductiveType)
    (h : type = indexedTreeType ∨ type = indexedTreeListType) :
    type.type.WF natFinalEnv type.uvars [] := by
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  rcases h with rfl | rfl <;>
    exact ⟨_, by type_tac⟩

theorem indexedTreeCtorWF (ctor : VConstVal)
    (h : ctor ∈ indexedTreeType.ctors ∨
      ctor ∈ indexedTreeListType.ctors) :
    ctor.type.WF indexedTreeBlockEnv 1 [] := by
  have hNat : indexedTreeBlockEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := by rfl
  have hZero : indexedTreeBlockEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := by rfl
  have hSucc : indexedTreeBlockEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := by rfl
  have hTree : indexedTreeBlockEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := by rfl
  have hTreeList : indexedTreeBlockEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := by rfl
  rcases h with h | h
  · simp [indexedTreeType] at h
    rcases h with (rfl | rfl)
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, by type_tac⟩
  · simp [indexedTreeListType] at h
    rcases h with (rfl | rfl)
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, by type_tac⟩

theorem indexedTreeNormalizationBlockWF :
    (Normalization.identity indexedTreeDecl).BlockWF
      natFinalEnv indexedTreeBlockEnv := by
  refine ⟨indexedTreeStage, ?_⟩
  change List.Forall₂ _ [indexedTreeType, indexedTreeListType]
    [indexedTreeType, indexedTreeListType]
  apply List.Forall₂.cons
  · refine ⟨?_, ?_⟩
    · exact VEnv.IsDefEqU.refl
        (indexedTreeFamilyTypeWF indexedTreeType (.inl rfl))
    · apply List.Forall₂.rfl
      intro ctor h
      exact VEnv.IsDefEqU.refl (indexedTreeCtorWF ctor (.inl h))
  · apply List.Forall₂.cons
    · refine ⟨?_, ?_⟩
      · exact VEnv.IsDefEqU.refl
          (indexedTreeFamilyTypeWF indexedTreeListType (.inr rfl))
      · apply List.Forall₂.rfl
        intro ctor h
        exact VEnv.IsDefEqU.refl (indexedTreeCtorWF ctor (.inr h))
    · exact .nil

theorem indexedTreeLeafSemantic :
    let constructor := CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[0]
    checkedBlockFieldsWF natFinalEnv 1 (.succ (.param 0))
        [[.const ``Nat []], [.const ``Nat []]]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      natFinalEnv.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN
          (VExpr.liftTelN constructor.fields.length [.const ``Nat []] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[0]).fields = [.bvar 0] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[0]).recursiveAt = [none] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[0]).resultIndices = [.const ``Nat.zero []] by rfl]
  constructor
  · exact ⟨⟨.succ (.param 0), .bvar .zero,
      .inr (VLevel.le_refl _)⟩, trivial⟩
  · have hNat : natFinalEnv.constants ``Nat =
        some InductiveFixtures.natType.toVConstant := rfl
    have hZero : natFinalEnv.constants ``Nat.zero =
        some InductiveFixtures.natType.ctors[0].toVConstant := rfl
    exact .cons (by type_tac) .nil

theorem indexedTreeNodeSemantic :
    let constructor := CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[1]
    checkedBlockFieldsWF natFinalEnv 1 (.succ (.param 0))
        [[.const ``Nat []], [.const ``Nat []]]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      natFinalEnv.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN
          (VExpr.liftTelN constructor.fields.length [.const ``Nat []] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[1]).fields =
        [.const ``Nat [],
          (VExpr.const ``IndexedTreeList [.param 0]).app (.bvar 1)
            |>.app (.bvar 0)] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[1]).recursiveAt =
        [none, some ({
          fieldIndex := 1
          binders := []
          targetType := 1
          indices := [.bvar 0] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeType.ctors[1]).resultIndices =
        [(VExpr.const ``Nat.succ []).app (.bvar 1)] by rfl]
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hSucc : natFinalEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  refine ⟨?_, ?_⟩
  · refine ⟨⟨.succ .zero, (by type_tac),
        .inr (VLevel.succ_le_succ VLevel.zero_le)⟩, ?_⟩
    exact ⟨⟨rfl, trivial, .cons (by type_tac) .nil⟩, trivial⟩
  · exact .cons (by type_tac) .nil

theorem indexedTreeListNilSemantic :
    let constructor := CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[0]
    checkedBlockFieldsWF natFinalEnv 1 (.succ (.param 0))
        [[.const ``Nat []], [.const ``Nat []]]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      natFinalEnv.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN
          (VExpr.liftTelN constructor.fields.length [.const ``Nat []] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[0]).fields = [] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[0]).recursiveAt = [] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[0]).resultIndices =
        [.const ``Nat.zero []] by rfl]
  refine ⟨trivial, ?_⟩
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : natFinalEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  exact .cons (by type_tac) .nil

theorem indexedTreeListConsSemantic :
    let constructor := CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[1]
    checkedBlockFieldsWF natFinalEnv 1 (.succ (.param 0))
        [[.const ``Nat []], [.const ``Nat []]]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      natFinalEnv.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN
          (VExpr.liftTelN constructor.fields.length [.const ``Nat []] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[1]).fields =
        [.const ``Nat [],
          (VExpr.const ``IndexedTree [.param 0]).app (.bvar 1)
            |>.app (.bvar 0),
          (VExpr.const ``IndexedTreeList [.param 0]).app (.bvar 2)
            |>.app (.bvar 1)] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[1]).recursiveAt =
        [none,
          some ({
            fieldIndex := 1
            binders := []
            targetType := 0
            indices := [.bvar 0] } : RecArg),
          some ({
            fieldIndex := 2
            binders := []
            targetType := 1
            indices := [.bvar 1] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock indexedTreeDecl
      indexedTreeListType.ctors[1]).resultIndices =
        [(VExpr.const ``Nat.succ []).app (.bvar 2)] by rfl]
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hSucc : natFinalEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  refine ⟨?_, ?_⟩
  · refine ⟨⟨.succ .zero, (by type_tac),
        .inr (VLevel.succ_le_succ VLevel.zero_le)⟩, ?_⟩
    refine ⟨⟨rfl, trivial, .cons (by type_tac) .nil⟩, ?_⟩
    exact ⟨⟨rfl, trivial, .cons (by type_tac) .nil⟩, trivial⟩
  · exact .cons (by type_tac) .nil

theorem indexedTreeCheckedBlockWF :
    indexedTreeChecked.WF natFinalEnv (.succ (.param 0)) := by
  have hparams : indexedTreeChecked.params =
      [.sort (.succ (.param 0))] := rfl
  have hindices : indexedTreeChecked.families.indices =
      [[.const ``Nat []], [.const ``Nat []]] := rfl
  have hlevels : indexedTreeChecked.families.resultLevels =
      [.succ (.param 0), .succ (.param 0)] := rfl
  have hconstructors : indexedTreeChecked.families.constructors =
      [indexedTreeType.ctors.map (CheckedCtor.ofBlock indexedTreeDecl),
        indexedTreeListType.ctors.map
          (CheckedCtor.ofBlock indexedTreeDecl)] := rfl
  rw [CheckedBlock.WF, hindices, hlevels, hconstructors]
  rw [hparams]
  simp only [checkedFamilyListsWF]
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
  · exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩,
      ⟨⟨_, (by type_tac)⟩, trivial⟩⟩
  · intro ctor h
    simp [indexedTreeType] at h
    rcases h with rfl | rfl
    · exact indexedTreeLeafSemantic
    · exact indexedTreeNodeSemantic
  · exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩,
      ⟨⟨_, (by type_tac)⟩, trivial⟩⟩
  · refine ⟨?_, trivial⟩
    intro ctor h
    simp [indexedTreeListType] at h
    rcases h with rfl | rfl
    · exact indexedTreeListNilSemantic
    · exact indexedTreeListConsSemantic

def indexedTreeNormalizedBlock : NormalizedCheckedBlock indexedTreeDecl where
  normalization := Normalization.identity indexedTreeDecl
  checked := indexedTreeChecked
  checked_eq := (Option.some_get (x := indexedTreeDecl.checkedBlock?)
    (by decide)).symm

def indexedTreeValidatedBlock : ValidatedBlock indexedTreeDecl where
  block := indexedTreeNormalizedBlock
  resultLevel := .succ (.param 0)

/-- Exact validation-only semantic package for the indexed mutual block. -/
def indexedTreeValidationCertificate :
    ValidationCertificate indexedTreeDecl natFinalEnv where
  validated := indexedTreeValidatedBlock
  blockEnv := indexedTreeBlockEnv
  wf := ⟨indexedTreeNormalizationBlockWF, indexedTreeCheckedBlockWF⟩

/-! ## Certified block-generation semantics -/

theorem treeLeafGenerationWF :
    NormalizedBlockCtor.WF treeGeneration treeGeneration.flatCtors[0]
      treeBlockEnv := by
  refine {
    declaredTel := ?_
    declaredResult := ?_
    emittedTel := ?_
    emittedResult := ?_
    owner := ?_
    recursive := ?_
    resultSpine := ?_ }
  · change treeBlockEnv.TelDefEq 1 []
      [.sort (.succ (.param 0)), .bvar 0]
      [.sort (.succ (.param 0)), .bvar 0]
    exact (show treeBlockEnv.OnTel 1 []
      [.sort (.succ (.param 0)), .bvar 0] from by
        refine ⟨⟨_, VEnv.HasType.sort (by decide)⟩, ?_⟩
        exact ⟨⟨_, by type_tac⟩, trivial⟩).telDefEq_refl
  · change treeBlockEnv.IsDefEq 1
      [.bvar 0, .sort (.succ (.param 0))]
      (.app (.const ``Tree [.param 0]) (.bvar 1))
      (.app (.const ``Tree [.param 0]) (.bvar 1))
      (.sort (.succ (.param 0)))
    have hTree : treeBlockEnv.constants ``Tree =
        some treeType.toVConstant := rfl
    apply VEnv.HasType.app
      (A := .sort (.succ (.param 0)))
      (B := .sort (.succ (.param 0)))
    · exact VEnv.HasType.const hTree (by simp [VLevel.WF]) rfl
    · exact VEnv.HasType.bvar (.succ .zero)
  · change treeBlockEnv.TelDefEq 1 []
      [.sort (.succ (.param 0)), .bvar 0]
      [.sort (.succ (.param 0)), .bvar 0]
    exact (show treeBlockEnv.OnTel 1 []
      [.sort (.succ (.param 0)), .bvar 0] from by
        refine ⟨⟨_, VEnv.HasType.sort (by decide)⟩, ?_⟩
        exact ⟨⟨_, by type_tac⟩, trivial⟩).telDefEq_refl
  · change treeBlockEnv.IsDefEq 1
      [.bvar 0, .sort (.succ (.param 0))]
      (.app (.const ``Tree [.param 0]) (.bvar 1))
      (.app (.const ``Tree [.param 0]) (.bvar 1))
      (.sort (.succ (.param 0)))
    have hTree : treeBlockEnv.constants ``Tree =
        some treeType.toVConstant := rfl
    apply VEnv.HasType.app
      (A := .sort (.succ (.param 0)))
      (B := .sort (.succ (.param 0)))
    · exact VEnv.HasType.const hTree (by simp [VLevel.WF]) rfl
    · exact VEnv.HasType.bvar (.succ .zero)
  · refine ⟨treeGeneration.families[0], ?_, rfl, rfl, rfl⟩
    exact .head _
  · intro recursive hrecursive
    change recursive ∈ [] at hrecursive
    nomatch hrecursive
  · exact treeLeafSemantic.2.mono empty_le_treeBlockEnv

theorem treeNodeGenerationWF :
    NormalizedBlockCtor.WF treeGeneration treeGeneration.flatCtors[1]
      treeBlockEnv := by
  have hTree : treeBlockEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeBlockEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  have hbinders : treeBlockEnv.OnTel 1 []
      [.sort (.succ (.param 0)),
        .app (.const ``TreeList [.param 0]) (.bvar 0)] := by
    refine ⟨⟨_, VEnv.HasType.sort (by decide)⟩, ?_⟩
    refine ⟨⟨.succ (.param 0), ?_⟩, trivial⟩
    apply VEnv.HasType.app
      (A := .sort (.succ (.param 0)))
      (B := .sort (.succ (.param 0)))
    · exact VEnv.HasType.const hTreeList (by simp [VLevel.WF]) rfl
    · exact VEnv.HasType.bvar .zero
  have hresult : treeBlockEnv.HasType 1
      [.app (.const ``TreeList [.param 0]) (.bvar 0),
        .sort (.succ (.param 0))]
      (.app (.const ``Tree [.param 0]) (.bvar 1))
      (.sort (.succ (.param 0))) := by
    apply VEnv.HasType.app
      (A := .sort (.succ (.param 0)))
      (B := .sort (.succ (.param 0)))
    · exact VEnv.HasType.const hTree (by simp [VLevel.WF]) rfl
    · exact VEnv.HasType.bvar (.succ .zero)
  refine {
    declaredTel := ?_
    declaredResult := ?_
    emittedTel := ?_
    emittedResult := ?_
    owner := ?_
    recursive := ?_
    resultSpine := ?_ }
  · exact hbinders.telDefEq_refl
  · exact hresult
  · exact hbinders.telDefEq_refl
  · exact hresult
  · refine ⟨treeGeneration.families[0], ?_, rfl, rfl, rfl⟩
    exact .head _
  · intro recursive hrecursive
    change recursive ∈ [{
      fieldIndex := 0
      binders := []
      targetType := 1
      indices := [] }] at hrecursive
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrecursive
    subst recursive
    refine ⟨treeGeneration.families[1], ?_, rfl, ?_, ?_⟩
    · exact .tail _ (.head _)
    · exact ⟨.app (.const ``TreeList [.param 0]) (.bvar 0), rfl, rfl⟩
    · exact ⟨trivial, .nil⟩
  · exact treeNodeSemantic.2.mono empty_le_treeBlockEnv

theorem treeBranchGenerationWF :
    NormalizedBlockCtor.WF treeGeneration treeGeneration.flatCtors[2]
      treeBlockEnv := by
  have hTree : treeBlockEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeBlockEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  have hbinders : treeBlockEnv.OnTel 1 []
      [.sort (.succ (.param 0)),
        .forallE (.bvar 0)
          (.app (.const ``TreeList [.param 0]) (.bvar 1))] := by
    refine ⟨⟨_, VEnv.HasType.sort (by decide)⟩, ?_⟩
    refine ⟨⟨.imax (.succ (.param 0)) (.succ (.param 0)), ?_⟩,
      trivial⟩
    apply VEnv.HasType.forallE
    · exact VEnv.HasType.bvar .zero
    · apply VEnv.HasType.app
        (A := .sort (.succ (.param 0)))
        (B := .sort (.succ (.param 0)))
      · exact VEnv.HasType.const hTreeList (by simp [VLevel.WF]) rfl
      · exact VEnv.HasType.bvar (.succ .zero)
  have hresult : treeBlockEnv.HasType 1
      [.forallE (.bvar 0)
          (.app (.const ``TreeList [.param 0]) (.bvar 1)),
        .sort (.succ (.param 0))]
      (.app (.const ``Tree [.param 0]) (.bvar 1))
      (.sort (.succ (.param 0))) := by
    apply VEnv.HasType.app
      (A := .sort (.succ (.param 0)))
      (B := .sort (.succ (.param 0)))
    · exact VEnv.HasType.const hTree (by simp [VLevel.WF]) rfl
    · exact VEnv.HasType.bvar (.succ .zero)
  refine {
    declaredTel := hbinders.telDefEq_refl
    declaredResult := hresult
    emittedTel := hbinders.telDefEq_refl
    emittedResult := hresult
    owner := ?_
    recursive := ?_
    resultSpine := treeBranchSemantic.2.mono empty_le_treeBlockEnv }
  · refine ⟨treeGeneration.families[0], ?_, rfl, rfl, rfl⟩
    exact .head _
  · intro recursive hrecursive
    change recursive ∈ [{
      fieldIndex := 0
      binders := [.bvar 0]
      targetType := 1
      indices := [] }] at hrecursive
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrecursive
    subst recursive
    refine ⟨treeGeneration.families[1], ?_, rfl, ?_, ?_⟩
    · exact .tail _ (.head _)
    · exact ⟨.forallE (.bvar 0)
        (.app (.const ``TreeList [.param 0]) (.bvar 1)), rfl, rfl⟩
    · exact ⟨⟨⟨_, VEnv.HasType.bvar .zero⟩, trivial⟩, .nil⟩

theorem treeListNilGenerationWF :
    NormalizedBlockCtor.WF treeGeneration treeGeneration.flatCtors[3]
      treeBlockEnv := by
  have hTreeList : treeBlockEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  have hbinders : treeBlockEnv.OnTel 1 []
      [.sort (.succ (.param 0))] :=
    ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
  have hresult : treeBlockEnv.HasType 1
      [.sort (.succ (.param 0))]
      (.app (.const ``TreeList [.param 0]) (.bvar 0))
      (.sort (.succ (.param 0))) := by
    apply VEnv.HasType.app
      (A := .sort (.succ (.param 0)))
      (B := .sort (.succ (.param 0)))
    · exact VEnv.HasType.const hTreeList (by simp [VLevel.WF]) rfl
    · exact VEnv.HasType.bvar .zero
  refine {
    declaredTel := hbinders.telDefEq_refl
    declaredResult := hresult
    emittedTel := hbinders.telDefEq_refl
    emittedResult := hresult
    owner := ?_
    recursive := ?_
    resultSpine := treeListNilSemantic.2.mono empty_le_treeBlockEnv }
  · refine ⟨treeGeneration.families[1], ?_, rfl, rfl, rfl⟩
    exact .tail _ (.head _)
  · intro recursive hrecursive
    change recursive ∈ [] at hrecursive
    nomatch hrecursive

theorem treeListConsGenerationWF :
    NormalizedBlockCtor.WF treeGeneration treeGeneration.flatCtors[4]
      treeBlockEnv := by
  have hTree : treeBlockEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeBlockEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  have hbinders : treeBlockEnv.OnTel 1 []
      [.sort (.succ (.param 0)),
        .app (.const ``Tree [.param 0]) (.bvar 0),
        .app (.const ``TreeList [.param 0]) (.bvar 1)] := by
    refine ⟨⟨_, VEnv.HasType.sort (by decide)⟩, ?_⟩
    refine ⟨⟨.succ (.param 0), ?_⟩, ?_⟩
    · apply VEnv.HasType.app
        (A := .sort (.succ (.param 0)))
        (B := .sort (.succ (.param 0)))
      · exact VEnv.HasType.const hTree (by simp [VLevel.WF]) rfl
      · exact VEnv.HasType.bvar .zero
    · refine ⟨⟨.succ (.param 0), ?_⟩, trivial⟩
      apply VEnv.HasType.app
        (A := .sort (.succ (.param 0)))
        (B := .sort (.succ (.param 0)))
      · exact VEnv.HasType.const hTreeList (by simp [VLevel.WF]) rfl
      · exact VEnv.HasType.bvar (.succ .zero)
  have hresult : treeBlockEnv.HasType 1
      [.app (.const ``TreeList [.param 0]) (.bvar 1),
        .app (.const ``Tree [.param 0]) (.bvar 0),
        .sort (.succ (.param 0))]
      (.app (.const ``TreeList [.param 0]) (.bvar 2))
      (.sort (.succ (.param 0))) := by
    apply VEnv.HasType.app
      (A := .sort (.succ (.param 0)))
      (B := .sort (.succ (.param 0)))
    · exact VEnv.HasType.const hTreeList (by simp [VLevel.WF]) rfl
    · exact VEnv.HasType.bvar (.succ (.succ .zero))
  refine {
    declaredTel := hbinders.telDefEq_refl
    declaredResult := hresult
    emittedTel := hbinders.telDefEq_refl
    emittedResult := hresult
    owner := ?_
    recursive := ?_
    resultSpine := treeListConsSemantic.2.mono empty_le_treeBlockEnv }
  · refine ⟨treeGeneration.families[1], ?_, rfl, rfl, rfl⟩
    exact .tail _ (.head _)
  · intro recursive hrecursive
    change recursive ∈ [{
      fieldIndex := 0
      binders := []
      targetType := 0
      indices := [] }, {
      fieldIndex := 1
      binders := []
      targetType := 1
      indices := [] }] at hrecursive
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrecursive
    rcases hrecursive with rfl | rfl
    · refine ⟨treeGeneration.families[0], ?_, rfl, ?_, ?_⟩
      · exact .head _
      · exact ⟨.app (.const ``Tree [.param 0]) (.bvar 0), rfl, rfl⟩
      · exact ⟨trivial, .nil⟩
    · refine ⟨treeGeneration.families[1], ?_, rfl, ?_, ?_⟩
      · exact .tail _ (.head _)
      · exact ⟨.app (.const ``TreeList [.param 0]) (.bvar 1), rfl, rfl⟩
      · exact ⟨trivial, .nil⟩

theorem treeBlockGenerationWF :
    treeGeneration.WF VEnv.empty treeBlockEnv := by
  refine {
    blockWF := treeValidationCertificate.wf
    resultLevelWF := by decide
    paramsTel := ?_
    families := ?_
    constructors := ?_ }
  · change VEnv.empty.TelDefEq 1 []
      [.sort (.succ (.param 0))] [.sort (.succ (.param 0))]
    exact (show VEnv.empty.OnTel 1 []
      [.sort (.succ (.param 0))] from
        ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩).telDefEq_refl
  · intro family hfamily
    have hfamilies : treeGeneration.families =
        [treeGeneration.families[0], treeGeneration.families[1]] := rfl
    rw [hfamilies] at hfamily
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfamily
    rcases hfamily with rfl | rfl
    · constructor
      · change VEnv.empty.TelDefEq 1 []
          [.sort (.succ (.param 0))] [.sort (.succ (.param 0))]
        exact (show VEnv.empty.OnTel 1 []
          [.sort (.succ (.param 0))] from
            ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩).telDefEq_refl
      · change VEnv.empty.IsDefEq 1 [.sort (.succ (.param 0))]
          (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
          (.sort (.succ (.succ (.param 0))))
        exact .sortDF (by decide) (by decide) rfl
    · constructor
      · change VEnv.empty.TelDefEq 1 []
          [.sort (.succ (.param 0))] [.sort (.succ (.param 0))]
        exact (show VEnv.empty.OnTel 1 []
          [.sort (.succ (.param 0))] from
            ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩).telDefEq_refl
      · change VEnv.empty.IsDefEq 1 [.sort (.succ (.param 0))]
          (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
          (.sort (.succ (.succ (.param 0))))
        exact .sortDF (by decide) (by decide) rfl
  · intro constructor hconstructor
    have hconstructors : treeGeneration.flatCtors =
        [treeGeneration.flatCtors[0], treeGeneration.flatCtors[1],
          treeGeneration.flatCtors[2], treeGeneration.flatCtors[3],
          treeGeneration.flatCtors[4]] := rfl
    rw [hconstructors] at hconstructor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hconstructor
    rcases hconstructor with rfl | rfl | rfl | rfl | rfl
    · exact treeLeafGenerationWF
    · exact treeNodeGenerationWF
    · exact treeBranchGenerationWF
    · exact treeListNilGenerationWF
    · exact treeListConsGenerationWF

theorem indexedTreeBlock_le : natFinalEnv ≤ indexedTreeBlockEnv := by
  have hfold : indexedTreeDecl.blockTypeConstants.foldlM
      (fun env type => env.addConst type.name type.toVConstant) natFinalEnv =
        some indexedTreeBlockEnv := by
    rw [blockTypeConstants_foldlM_eq_stageInductiveTypes]
    exact indexedTreeStage
  exact (VInductDecl.ctorFold_spec indexedTreeDecl.blockTypeConstants hfold).1

theorem indexedTreeLeafGenerationWF :
    NormalizedBlockCtor.WF indexedTreeGeneration
      indexedTreeGeneration.flatCtors[0] indexedTreeBlockEnv := by
  have hTree : indexedTreeBlockEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hZero : indexedTreeBlockEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hbinders : indexedTreeBlockEnv.OnTel 1 []
      [.sort (.succ (.param 0)), .bvar 0] := by
    refine ⟨⟨_, VEnv.HasType.sort (by decide)⟩, ?_⟩
    exact ⟨⟨_, VEnv.HasType.bvar .zero⟩, trivial⟩
  have hresult : indexedTreeBlockEnv.HasType 1
      [.bvar 0, .sort (.succ (.param 0))]
      (.app
        (.app (.const ``IndexedTree [.param 0]) (.bvar 1))
        (.const ``Nat.zero []))
      (.sort (.succ (.param 0))) := by
    apply VEnv.HasType.app
      (A := .const ``Nat [])
      (B := .sort (.succ (.param 0)))
    · apply VEnv.HasType.app
        (A := .sort (.succ (.param 0)))
        (B := .forallE (.const ``Nat []) (.sort (.succ (.param 0))))
      · exact VEnv.HasType.const hTree (by simp [VLevel.WF]) rfl
      · exact VEnv.HasType.bvar (.succ .zero)
    · exact VEnv.HasType.const hZero (by simp) rfl
  refine {
    declaredTel := hbinders.telDefEq_refl
    declaredResult := hresult
    emittedTel := hbinders.telDefEq_refl
    emittedResult := hresult
    owner := ?_
    recursive := ?_
    resultSpine := indexedTreeLeafSemantic.2.mono indexedTreeBlock_le }
  · refine ⟨indexedTreeGeneration.families[0], ?_, rfl, rfl, rfl⟩
    exact .head _
  · intro recursive hrecursive
    change recursive ∈ [] at hrecursive
    nomatch hrecursive

theorem indexedTreeListNilGenerationWF :
    NormalizedBlockCtor.WF indexedTreeGeneration
      indexedTreeGeneration.flatCtors[2] indexedTreeBlockEnv := by
  have hTreeList : indexedTreeBlockEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  have hZero : indexedTreeBlockEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hbinders : indexedTreeBlockEnv.OnTel 1 []
      [.sort (.succ (.param 0))] :=
    ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
  have hresult : indexedTreeBlockEnv.HasType 1
      [.sort (.succ (.param 0))]
      (.app
        (.app (.const ``IndexedTreeList [.param 0]) (.bvar 0))
        (.const ``Nat.zero []))
      (.sort (.succ (.param 0))) := by
    apply VEnv.HasType.app
      (A := .const ``Nat [])
      (B := .sort (.succ (.param 0)))
    · apply VEnv.HasType.app
        (A := .sort (.succ (.param 0)))
        (B := .forallE (.const ``Nat []) (.sort (.succ (.param 0))))
      · exact VEnv.HasType.const hTreeList (by simp [VLevel.WF]) rfl
      · exact VEnv.HasType.bvar .zero
    · exact VEnv.HasType.const hZero (by simp) rfl
  refine {
    declaredTel := hbinders.telDefEq_refl
    declaredResult := hresult
    emittedTel := hbinders.telDefEq_refl
    emittedResult := hresult
    owner := ?_
    recursive := ?_
    resultSpine := indexedTreeListNilSemantic.2.mono
      indexedTreeBlock_le }
  · refine ⟨indexedTreeGeneration.families[1], ?_, rfl, rfl, rfl⟩
    exact .tail _ (.head _)
  · intro recursive hrecursive
    change recursive ∈ [] at hrecursive
    nomatch hrecursive

theorem indexedTreeNodeGenerationWF :
    NormalizedBlockCtor.WF indexedTreeGeneration
      indexedTreeGeneration.flatCtors[1] indexedTreeBlockEnv := by
  have hNat : indexedTreeBlockEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hSucc : indexedTreeBlockEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedTreeBlockEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedTreeBlockEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  have hbinders : indexedTreeBlockEnv.OnTel 1 []
      [.sort (.succ (.param 0)), .const ``Nat [],
        .app
          (.app (.const ``IndexedTreeList [.param 0]) (.bvar 1))
          (.bvar 0)] := by
    refine ⟨⟨_, VEnv.HasType.sort (by decide)⟩, ?_⟩
    refine ⟨⟨.succ .zero, VEnv.HasType.const hNat (by simp) rfl⟩, ?_⟩
    refine ⟨⟨.succ (.param 0), ?_⟩, trivial⟩
    apply VEnv.HasType.app
      (A := .const ``Nat [])
      (B := .sort (.succ (.param 0)))
    · apply VEnv.HasType.app
        (A := .sort (.succ (.param 0)))
        (B := .forallE (.const ``Nat []) (.sort (.succ (.param 0))))
      · exact VEnv.HasType.const hTreeList (by simp [VLevel.WF]) rfl
      · exact VEnv.HasType.bvar (.succ .zero)
    · exact VEnv.HasType.bvar .zero
  have hresult : indexedTreeBlockEnv.HasType 1
      [.app
          (.app (.const ``IndexedTreeList [.param 0]) (.bvar 1))
          (.bvar 0),
        .const ``Nat [], .sort (.succ (.param 0))]
      (.app
        (.app (.const ``IndexedTree [.param 0]) (.bvar 2))
        (.app (.const ``Nat.succ []) (.bvar 1)))
      (.sort (.succ (.param 0))) := by
    apply VEnv.HasType.app
      (A := .const ``Nat [])
      (B := .sort (.succ (.param 0)))
    · apply VEnv.HasType.app
        (A := .sort (.succ (.param 0)))
        (B := .forallE (.const ``Nat []) (.sort (.succ (.param 0))))
      · exact VEnv.HasType.const hTree (by simp [VLevel.WF]) rfl
      · exact VEnv.HasType.bvar (.succ (.succ .zero))
    · apply VEnv.HasType.app
        (A := .const ``Nat []) (B := .const ``Nat [])
      · exact VEnv.HasType.const hSucc (by simp) rfl
      · exact VEnv.HasType.bvar (.succ .zero)
  refine {
    declaredTel := hbinders.telDefEq_refl
    declaredResult := hresult
    emittedTel := hbinders.telDefEq_refl
    emittedResult := hresult
    owner := ?_
    recursive := ?_
    resultSpine := indexedTreeNodeSemantic.2.mono
      indexedTreeBlock_le }
  · refine ⟨indexedTreeGeneration.families[0], ?_, rfl, rfl, rfl⟩
    exact .head _
  · intro recursive hrecursive
    change recursive ∈ [{
      fieldIndex := 1
      binders := []
      targetType := 1
      indices := [.bvar 0] }] at hrecursive
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrecursive
    subst recursive
    refine ⟨indexedTreeGeneration.families[1], ?_, rfl, ?_, ?_⟩
    · exact .tail _ (.head _)
    · exact ⟨.app
        (.app (.const ``IndexedTreeList [.param 0]) (.bvar 1))
        (.bvar 0), rfl, rfl⟩
    · refine ⟨trivial, ?_⟩
      exact .cons (VEnv.HasType.bvar .zero) .nil

theorem indexedTreeListConsGenerationWF :
    NormalizedBlockCtor.WF indexedTreeGeneration
      indexedTreeGeneration.flatCtors[3] indexedTreeBlockEnv := by
  have hNat : indexedTreeBlockEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hSucc : indexedTreeBlockEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedTreeBlockEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedTreeBlockEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  have hbinders : indexedTreeBlockEnv.OnTel 1 []
      [.sort (.succ (.param 0)), .const ``Nat [],
        .app
          (.app (.const ``IndexedTree [.param 0]) (.bvar 1))
          (.bvar 0),
        .app
          (.app (.const ``IndexedTreeList [.param 0]) (.bvar 2))
          (.bvar 1)] := by
    refine ⟨⟨_, VEnv.HasType.sort (by decide)⟩, ?_⟩
    refine ⟨⟨.succ .zero, VEnv.HasType.const hNat (by simp) rfl⟩, ?_⟩
    refine ⟨⟨.succ (.param 0), ?_⟩, ?_⟩
    · apply VEnv.HasType.app
        (A := .const ``Nat [])
        (B := .sort (.succ (.param 0)))
      · apply VEnv.HasType.app
          (A := .sort (.succ (.param 0)))
          (B := .forallE (.const ``Nat []) (.sort (.succ (.param 0))))
        · exact VEnv.HasType.const hTree (by simp [VLevel.WF]) rfl
        · exact VEnv.HasType.bvar (.succ .zero)
      · exact VEnv.HasType.bvar .zero
    · refine ⟨⟨.succ (.param 0), ?_⟩, trivial⟩
      apply VEnv.HasType.app
        (A := .const ``Nat [])
        (B := .sort (.succ (.param 0)))
      · apply VEnv.HasType.app
          (A := .sort (.succ (.param 0)))
          (B := .forallE (.const ``Nat []) (.sort (.succ (.param 0))))
        · exact VEnv.HasType.const hTreeList (by simp [VLevel.WF]) rfl
        · exact VEnv.HasType.bvar (.succ (.succ .zero))
      · exact VEnv.HasType.bvar (.succ .zero)
  have hresult : indexedTreeBlockEnv.HasType 1
      [.app
          (.app (.const ``IndexedTreeList [.param 0]) (.bvar 2))
          (.bvar 1),
        .app
          (.app (.const ``IndexedTree [.param 0]) (.bvar 1))
          (.bvar 0),
        .const ``Nat [], .sort (.succ (.param 0))]
      (.app
        (.app (.const ``IndexedTreeList [.param 0]) (.bvar 3))
        (.app (.const ``Nat.succ []) (.bvar 2)))
      (.sort (.succ (.param 0))) := by
    apply VEnv.HasType.app
      (A := .const ``Nat [])
      (B := .sort (.succ (.param 0)))
    · apply VEnv.HasType.app
        (A := .sort (.succ (.param 0)))
        (B := .forallE (.const ``Nat []) (.sort (.succ (.param 0))))
      · exact VEnv.HasType.const hTreeList (by simp [VLevel.WF]) rfl
      · exact VEnv.HasType.bvar (.succ (.succ (.succ .zero)))
    · apply VEnv.HasType.app
        (A := .const ``Nat []) (B := .const ``Nat [])
      · exact VEnv.HasType.const hSucc (by simp) rfl
      · exact VEnv.HasType.bvar (.succ (.succ .zero))
  refine {
    declaredTel := hbinders.telDefEq_refl
    declaredResult := hresult
    emittedTel := hbinders.telDefEq_refl
    emittedResult := hresult
    owner := ?_
    recursive := ?_
    resultSpine := indexedTreeListConsSemantic.2.mono
      indexedTreeBlock_le }
  · refine ⟨indexedTreeGeneration.families[1], ?_, rfl, rfl, rfl⟩
    exact .tail _ (.head _)
  · intro recursive hrecursive
    change recursive ∈ [{
      fieldIndex := 1
      binders := []
      targetType := 0
      indices := [.bvar 0] }, {
      fieldIndex := 2
      binders := []
      targetType := 1
      indices := [.bvar 1] }] at hrecursive
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrecursive
    rcases hrecursive with rfl | rfl
    · refine ⟨indexedTreeGeneration.families[0], ?_, rfl, ?_, ?_⟩
      · exact .head _
      · exact ⟨.app
          (.app (.const ``IndexedTree [.param 0]) (.bvar 1))
          (.bvar 0), rfl, rfl⟩
      · refine ⟨trivial, ?_⟩
        exact .cons (VEnv.HasType.bvar .zero) .nil
    · refine ⟨indexedTreeGeneration.families[1], ?_, rfl, ?_, ?_⟩
      · exact .tail _ (.head _)
      · exact ⟨.app
          (.app (.const ``IndexedTreeList [.param 0]) (.bvar 2))
          (.bvar 1), rfl, rfl⟩
      · refine ⟨trivial, ?_⟩
        exact .cons (VEnv.HasType.bvar (.succ .zero)) .nil

theorem indexedTreeBlockGenerationWF :
    indexedTreeGeneration.WF natFinalEnv indexedTreeBlockEnv := by
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hparams : natFinalEnv.OnTel 1 []
      [.sort (.succ (.param 0))] :=
    ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
  have hfamilyTel : natFinalEnv.OnTel 1 []
      [.sort (.succ (.param 0)), .const ``Nat []] :=
    ⟨⟨_, VEnv.HasType.sort (by decide)⟩,
      ⟨⟨.succ .zero, VEnv.HasType.const hNat (by simp) rfl⟩, trivial⟩⟩
  refine {
    blockWF := indexedTreeValidationCertificate.wf
    resultLevelWF := by decide
    paramsTel := hparams.telDefEq_refl
    families := ?_
    constructors := ?_ }
  · intro family hfamily
    have hfamilies : indexedTreeGeneration.families =
        [indexedTreeGeneration.families[0],
          indexedTreeGeneration.families[1]] := rfl
    rw [hfamilies] at hfamily
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfamily
    rcases hfamily with rfl | rfl
    · constructor
      · exact hfamilyTel.telDefEq_refl
      · change natFinalEnv.IsDefEq 1
          [.const ``Nat [], .sort (.succ (.param 0))]
          (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
          (.sort (.succ (.succ (.param 0))))
        exact .sortDF (by decide) (by decide) rfl
    · constructor
      · exact hfamilyTel.telDefEq_refl
      · change natFinalEnv.IsDefEq 1
          [.const ``Nat [], .sort (.succ (.param 0))]
          (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
          (.sort (.succ (.succ (.param 0))))
        exact .sortDF (by decide) (by decide) rfl
  · intro constructor hconstructor
    have hconstructors : indexedTreeGeneration.flatCtors =
        [indexedTreeGeneration.flatCtors[0],
          indexedTreeGeneration.flatCtors[1],
          indexedTreeGeneration.flatCtors[2],
          indexedTreeGeneration.flatCtors[3]] := rfl
    rw [hconstructors] at hconstructor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hconstructor
    rcases hconstructor with rfl | rfl | rfl | rfl
    · exact indexedTreeLeafGenerationWF
    · exact indexedTreeNodeGenerationWF
    · exact indexedTreeListNilGenerationWF
    · exact indexedTreeListConsGenerationWF

/-- Proof-carrying block generation for `Tree`/`TreeList`. -/
def treeGenerationCertificate :
    treeDecl.BlockGenerationCertificate VEnv.empty where
  generation := treeGeneration
  blockEnv := treeBlockEnv
  wf := treeBlockGenerationWF

/-- Proof-carrying block generation for the indexed mutual fixture. -/
def indexedTreeGenerationCertificate :
    indexedTreeDecl.BlockGenerationCertificate natFinalEnv where
  generation := indexedTreeGeneration
  blockEnv := indexedTreeBlockEnv
  wf := indexedTreeBlockGenerationWF

/-- Final Theory environment produced by the certified unindexed block
transaction. -/
def treeFinalEnv : VEnv :=
  (VEnv.empty.addInductBlockCertified treeGenerationCertificate).get
    (by decide)

theorem tree_addInductBlockCertified :
    VEnv.empty.addInductBlockCertified treeGenerationCertificate =
      some treeFinalEnv := by
  rfl

/-- The raw public transaction selects the same retained block descriptor and
produces the same final Theory environment. -/
theorem tree_addInduct :
    VEnv.empty.addInduct treeDecl = some treeFinalEnv := by
  rfl

theorem tree_addInduct_success :
    VEnv.AddInductSuccess VEnv.empty treeFinalEnv treeDecl :=
  VEnv.addInduct_success tree_addInduct

/-- Exact four-phase trace for the certified unindexed block transaction. -/
theorem treeCertifiedTrace :
    Nonempty (VEnv.AddInductBlockGenerationTrace
      VEnv.empty treeFinalEnv treeGeneration) :=
  VEnv.addInductBlockCertified_trace tree_addInductBlockCertified

theorem treeFinalEnv_ordered : treeFinalEnv.Ordered :=
  VEnv.addInduct_WF .empty rfl treeBlockGenerationWF tree_addInduct

theorem treeFinalEnv_family_lookup {type : VInductiveType}
    (htype : type ∈ treeDecl.types) :
    treeFinalEnv.constants type.name = some type.toVConstant := by
  obtain ⟨trace⟩ := treeCertifiedTrace
  exact trace.family_lookup htype

theorem treeFinalEnv_ctor_lookup {constructor : VConstVal}
    (hconstructor : constructor ∈ treeDecl.blockConstructorConstants) :
    treeFinalEnv.constants constructor.name =
      some constructor.toVConstant := by
  obtain ⟨trace⟩ := treeCertifiedTrace
  exact trace.ctor_lookup hconstructor

theorem treeFinalEnv_rec_lookup {recursor : VConstVal}
    (hrecursor : recursor ∈ treeGeneration.recursors) :
    treeFinalEnv.constants recursor.name =
      some recursor.toVConstant := by
  obtain ⟨trace⟩ := treeCertifiedTrace
  exact trace.rec_lookup hrecursor

theorem treeFinalEnv_rule_mem {rule : VDefEq}
    (hrule : rule ∈ treeGeneration.generatedRules) :
    treeFinalEnv.defeqs rule := by
  obtain ⟨trace⟩ := treeCertifiedTrace
  exact trace.rule_mem hrule

/-- Final Theory environment produced by the certified indexed block
transaction. -/
def indexedTreeFinalEnv : VEnv :=
  (natFinalEnv.addInductBlockCertified indexedTreeGenerationCertificate).get
    (by decide)

theorem indexedTree_addInductBlockCertified :
    natFinalEnv.addInductBlockCertified indexedTreeGenerationCertificate =
      some indexedTreeFinalEnv := by
  rfl

/-- The indexed mutual block also runs through the same raw public entry
point once its ordinary `Nat` dependency is present. -/
theorem indexedTree_addInduct :
    natFinalEnv.addInduct indexedTreeDecl = some indexedTreeFinalEnv := by
  rfl

theorem indexedTree_addInduct_success :
    VEnv.AddInductSuccess natFinalEnv indexedTreeFinalEnv indexedTreeDecl :=
  VEnv.addInduct_success indexedTree_addInduct

/-- Exact four-phase trace for the certified indexed block transaction. -/
theorem indexedTreeCertifiedTrace :
    Nonempty (VEnv.AddInductBlockGenerationTrace
      natFinalEnv indexedTreeFinalEnv indexedTreeGeneration) :=
  VEnv.addInductBlockCertified_trace indexedTree_addInductBlockCertified

theorem indexedTreeFinalEnv_ordered : indexedTreeFinalEnv.Ordered :=
  VEnv.addInduct_WF natFinalEnv_ordered rfl indexedTreeBlockGenerationWF
    indexedTree_addInduct

theorem indexedTreeFinalEnv_family_lookup {type : VInductiveType}
    (htype : type ∈ indexedTreeDecl.types) :
    indexedTreeFinalEnv.constants type.name = some type.toVConstant := by
  obtain ⟨trace⟩ := indexedTreeCertifiedTrace
  exact trace.family_lookup htype

theorem indexedTreeFinalEnv_ctor_lookup {constructor : VConstVal}
    (hconstructor :
      constructor ∈ indexedTreeDecl.blockConstructorConstants) :
    indexedTreeFinalEnv.constants constructor.name =
      some constructor.toVConstant := by
  obtain ⟨trace⟩ := indexedTreeCertifiedTrace
  exact trace.ctor_lookup hconstructor

theorem indexedTreeFinalEnv_rec_lookup {recursor : VConstVal}
    (hrecursor : recursor ∈ indexedTreeGeneration.recursors) :
    indexedTreeFinalEnv.constants recursor.name =
      some recursor.toVConstant := by
  obtain ⟨trace⟩ := indexedTreeCertifiedTrace
  exact trace.rec_lookup hrecursor

theorem indexedTreeFinalEnv_rule_mem {rule : VDefEq}
    (hrule : rule ∈ indexedTreeGeneration.generatedRules) :
    indexedTreeFinalEnv.defeqs rule := by
  obtain ⟨trace⟩ := indexedTreeCertifiedTrace
  exact trace.rule_mem hrule

/-! ## Verification-environment block replay -/

/-! ## Unindexed Verify block replay -/

def treeReplayFirstTypeEnv : VEnv :=
  (VEnv.empty.addConst treeType.name treeType.toVConstant).get!

def treeReplayTypeEnv : VEnv :=
  (treeReplayFirstTypeEnv.addConst treeListType.name
    treeListType.toVConstant).get!

def treeReplayLeafEnv : VEnv :=
  (treeReplayTypeEnv.addConst treeType.ctors[0].name
    treeType.ctors[0].toVConstant).get!

def treeReplayNodeEnv : VEnv :=
  (treeReplayLeafEnv.addConst treeType.ctors[1].name
    treeType.ctors[1].toVConstant).get!

def treeReplayBranchEnv : VEnv :=
  (treeReplayNodeEnv.addConst treeType.ctors[2].name
    treeType.ctors[2].toVConstant).get!

def treeReplayNilEnv : VEnv :=
  (treeReplayBranchEnv.addConst treeListType.ctors[0].name
    treeListType.ctors[0].toVConstant).get!

def treeReplayCtorEnv : VEnv :=
  (treeReplayNilEnv.addConst treeListType.ctors[1].name
    treeListType.ctors[1].toVConstant).get!

def treeReplayFirstRecEnv : VEnv :=
  (treeReplayCtorEnv.addConst treeGeneration.recursors[0].name
    treeGeneration.recursors[0].toVConstant).get!

def treeReplayRecEnv : VEnv :=
  (treeReplayFirstRecEnv.addConst treeGeneration.recursors[1].name
    treeGeneration.recursors[1].toVConstant).get!

example : treeReplayTypeEnv = treeBlockEnv := rfl

theorem treeReplay_addFirstType :
    VEnv.empty.addConst treeType.name treeType.toVConstant =
      some treeReplayFirstTypeEnv := rfl

theorem treeReplay_addSecondType :
    treeReplayFirstTypeEnv.addConst treeListType.name
      treeListType.toVConstant = some treeReplayTypeEnv := rfl

theorem treeReplay_addLeaf :
    treeReplayTypeEnv.addConst treeType.ctors[0].name
      treeType.ctors[0].toVConstant = some treeReplayLeafEnv := rfl

theorem treeReplay_addNode :
    treeReplayLeafEnv.addConst treeType.ctors[1].name
      treeType.ctors[1].toVConstant = some treeReplayNodeEnv := rfl

theorem treeReplay_addBranch :
    treeReplayNodeEnv.addConst treeType.ctors[2].name
      treeType.ctors[2].toVConstant = some treeReplayBranchEnv := rfl

theorem treeReplay_addNil :
    treeReplayBranchEnv.addConst treeListType.ctors[0].name
      treeListType.ctors[0].toVConstant = some treeReplayNilEnv := rfl

theorem treeReplay_addCons :
    treeReplayNilEnv.addConst treeListType.ctors[1].name
      treeListType.ctors[1].toVConstant = some treeReplayCtorEnv := rfl

theorem treeReplay_addFirstRec :
    treeReplayCtorEnv.addConst treeGeneration.recursors[0].name
      treeGeneration.recursors[0].toVConstant =
        some treeReplayFirstRecEnv := rfl

theorem treeReplay_addSecondRec :
    treeReplayFirstRecEnv.addConst treeGeneration.recursors[1].name
      treeGeneration.recursors[1].toVConstant =
        some treeReplayRecEnv := rfl

theorem treeTypeConstantWF : treeType.toVConstant.WF VEnv.empty := by
  exact treeBlockGenerationWF.rawFamily_isType (.head _)

theorem treeListTypeConstantWF :
    treeListType.toVConstant.WF VEnv.empty := by
  exact treeBlockGenerationWF.rawFamily_isType (.tail _ (.head _))

theorem treeLeafConstantWF :
    treeType.ctors[0].toVConstant.WF treeReplayTypeEnv := by
  exact treeBlockGenerationWF.rawCtor_isType (.head _)

theorem treeNodeConstantWF :
    treeType.ctors[1].toVConstant.WF treeReplayTypeEnv := by
  exact treeBlockGenerationWF.rawCtor_isType (.tail _ (.head _))

theorem treeBranchConstantWF :
    treeType.ctors[2].toVConstant.WF treeReplayTypeEnv := by
  exact treeBlockGenerationWF.rawCtor_isType
    (.tail _ (.tail _ (.head _)))

theorem treeNilConstantWF :
    treeListType.ctors[0].toVConstant.WF treeReplayTypeEnv := by
  exact treeBlockGenerationWF.rawCtor_isType
    (.tail _ (.tail _ (.tail _ (.head _))))

theorem treeConsConstantWF :
    treeListType.ctors[1].toVConstant.WF treeReplayTypeEnv := by
  exact treeBlockGenerationWF.rawCtor_isType
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

theorem treeReplayFirstTypeEnv_ordered :
    treeReplayFirstTypeEnv.Ordered := by
  exact .const .empty treeTypeConstantWF treeReplay_addFirstType

theorem treeReplayTypeEnv_ordered : treeReplayTypeEnv.Ordered := by
  refine .const treeReplayFirstTypeEnv_ordered ?_
    treeReplay_addSecondType
  exact treeListTypeConstantWF.mono
    (VEnv.addConst_le treeReplay_addFirstType)

theorem treeReplayTypeEnv_le_leafEnv :
    treeReplayTypeEnv ≤ treeReplayLeafEnv :=
  VEnv.addConst_le treeReplay_addLeaf

theorem treeReplayLeafEnv_ordered : treeReplayLeafEnv.Ordered := by
  exact .const treeReplayTypeEnv_ordered treeLeafConstantWF
    treeReplay_addLeaf

theorem treeReplayLeafEnv_le_nodeEnv :
    treeReplayLeafEnv ≤ treeReplayNodeEnv :=
  VEnv.addConst_le treeReplay_addNode

theorem treeReplayNodeEnv_ordered : treeReplayNodeEnv.Ordered := by
  refine .const treeReplayLeafEnv_ordered ?_ treeReplay_addNode
  exact treeNodeConstantWF.mono
    treeReplayTypeEnv_le_leafEnv

theorem treeReplayNodeEnv_le_branchEnv :
    treeReplayNodeEnv ≤ treeReplayBranchEnv :=
  VEnv.addConst_le treeReplay_addBranch

theorem treeReplayBranchEnv_ordered : treeReplayBranchEnv.Ordered := by
  refine .const treeReplayNodeEnv_ordered ?_ treeReplay_addBranch
  exact treeBranchConstantWF.mono
    (treeReplayTypeEnv_le_leafEnv.trans treeReplayLeafEnv_le_nodeEnv)

theorem treeReplayBranchEnv_le_nilEnv :
    treeReplayBranchEnv ≤ treeReplayNilEnv :=
  VEnv.addConst_le treeReplay_addNil

theorem treeReplayNilEnv_ordered : treeReplayNilEnv.Ordered := by
  refine .const treeReplayBranchEnv_ordered ?_ treeReplay_addNil
  exact treeNilConstantWF.mono
      (treeReplayTypeEnv_le_leafEnv.trans
        (treeReplayLeafEnv_le_nodeEnv.trans
          treeReplayNodeEnv_le_branchEnv))

theorem treeReplayNilEnv_le_ctorEnv :
    treeReplayNilEnv ≤ treeReplayCtorEnv :=
  VEnv.addConst_le treeReplay_addCons

theorem treeReplayCtorEnv_ordered : treeReplayCtorEnv.Ordered := by
  refine .const treeReplayNilEnv_ordered ?_ treeReplay_addCons
  exact treeConsConstantWF.mono
      (treeReplayTypeEnv_le_leafEnv.trans
        (treeReplayLeafEnv_le_nodeEnv.trans
          (treeReplayNodeEnv_le_branchEnv.trans
            treeReplayBranchEnv_le_nilEnv)))

theorem treeReplayInput_le_ctorEnv : VEnv.empty ≤ treeReplayCtorEnv := by
  exact (VEnv.addConst_le treeReplay_addFirstType).trans
    ((VEnv.addConst_le treeReplay_addSecondType).trans
      (treeReplayTypeEnv_le_leafEnv.trans
        (treeReplayLeafEnv_le_nodeEnv.trans
          (treeReplayNodeEnv_le_branchEnv.trans
            (treeReplayBranchEnv_le_nilEnv.trans
              treeReplayNilEnv_le_ctorEnv)))))

theorem treeReplayBlock_le_ctorEnv : treeBlockEnv ≤ treeReplayCtorEnv := by
  exact treeReplayTypeEnv_le_leafEnv.trans
    (treeReplayLeafEnv_le_nodeEnv.trans
      (treeReplayNodeEnv_le_branchEnv.trans
        (treeReplayBranchEnv_le_nilEnv.trans
          treeReplayNilEnv_le_ctorEnv)))

theorem treeReplayGenerationEnv :
    BlockGenerationEnv treeGeneration treeReplayCtorEnv := by
  apply treeBlockGenerationWF.toBlockGenerationEnv
    treeReplayInput_le_ctorEnv treeReplayBlock_le_ctorEnv
    treeReplayCtorEnv_ordered
  · intro family hfamily
    have hfamilies : treeGeneration.families =
        [treeGeneration.families[0], treeGeneration.families[1]] := rfl
    rw [hfamilies] at hfamily
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfamily
    rcases hfamily with rfl | rfl <;> rfl
  · intro constructor hconstructor
    have hconstructors : treeGeneration.flatCtors =
        [treeGeneration.flatCtors[0], treeGeneration.flatCtors[1],
          treeGeneration.flatCtors[2], treeGeneration.flatCtors[3],
          treeGeneration.flatCtors[4]] := rfl
    rw [hconstructors] at hconstructor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hconstructor
    rcases hconstructor with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem treeReplayFirstRecEnv_ordered :
    treeReplayFirstRecEnv.Ordered := by
  refine .const treeReplayCtorEnv_ordered ?_ treeReplay_addFirstRec
  exact treeReplayGenerationEnv.recursor_wf (.head _)

theorem treeReplayCtorEnv_le_firstRecEnv :
    treeReplayCtorEnv ≤ treeReplayFirstRecEnv :=
  VEnv.addConst_le treeReplay_addFirstRec

theorem treeReplayRecEnv_ordered : treeReplayRecEnv.Ordered := by
  refine .const treeReplayFirstRecEnv_ordered ?_ treeReplay_addSecondRec
  exact (treeReplayGenerationEnv.recursor_wf
    (.tail _ (.head _))).mono treeReplayCtorEnv_le_firstRecEnv

theorem treeKernelInfo_tr :
    TrConstVal .safe VEnv.empty treeKernelInfo treeType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr VEnv.empty treeKernelInfo.levelParams []
      treeKernelInfo.type treeType.type := by tr_type_expr_tac
  exact hshape.to_trExprS .empty trivial
    (treeFamilyTypeWF treeType (.inl rfl))

theorem treeListKernelInfo_tr :
    TrConstVal .safe treeReplayFirstTypeEnv treeListKernelInfo
      treeListType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr treeReplayFirstTypeEnv
      treeListKernelInfo.levelParams [] treeListKernelInfo.type
      treeListType.type := by tr_type_expr_tac
  exact hshape.to_trExprS treeReplayFirstTypeEnv_ordered trivial
    ((treeFamilyTypeWF treeListType (.inr rfl)).mono
      (VEnv.addConst_le (by rfl)))

theorem treeLeafKernelInfo_tr :
    TrConstVal .safe treeReplayTypeEnv treeLeafKernelInfo
      treeType.ctors[0] := by
  have hTree : treeReplayTypeEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeReplayTypeEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr treeReplayTypeEnv
      treeLeafKernelInfo.levelParams [] treeLeafKernelInfo.type
      treeType.ctors[0].type := by tr_type_expr_tac
  exact hshape.to_trExprS treeReplayTypeEnv_ordered trivial
    (treeCtorWF treeType.ctors[0] (.inl (by simp [treeType])))

theorem treeNodeKernelInfo_tr :
    TrConstVal .safe treeReplayLeafEnv treeNodeKernelInfo
      treeType.ctors[1] := by
  have hTree : treeReplayLeafEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeReplayLeafEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr treeReplayLeafEnv
      treeNodeKernelInfo.levelParams [] treeNodeKernelInfo.type
      treeType.ctors[1].type := by tr_type_expr_tac
  exact hshape.to_trExprS treeReplayLeafEnv_ordered trivial
    ((treeCtorWF treeType.ctors[1] (.inl (by simp [treeType]))).mono
      treeReplayTypeEnv_le_leafEnv)

theorem treeBranchKernelInfo_tr :
    TrConstVal .safe treeReplayNodeEnv treeBranchKernelInfo
      treeType.ctors[2] := by
  have hTree : treeReplayNodeEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeReplayNodeEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr treeReplayNodeEnv
      treeBranchKernelInfo.levelParams [] treeBranchKernelInfo.type
      treeType.ctors[2].type := by tr_type_expr_tac
  exact hshape.to_trExprS treeReplayNodeEnv_ordered trivial
    ((treeCtorWF treeType.ctors[2] (.inl (by simp [treeType]))).mono
      (treeReplayTypeEnv_le_leafEnv.trans treeReplayLeafEnv_le_nodeEnv))

theorem treeListNilKernelInfo_tr :
    TrConstVal .safe treeReplayBranchEnv treeListNilKernelInfo
      treeListType.ctors[0] := by
  have hTree : treeReplayBranchEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeReplayBranchEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr treeReplayBranchEnv
      treeListNilKernelInfo.levelParams [] treeListNilKernelInfo.type
      treeListType.ctors[0].type := by tr_type_expr_tac
  exact hshape.to_trExprS treeReplayBranchEnv_ordered trivial
    ((treeCtorWF treeListType.ctors[0]
      (.inr (by simp [treeListType]))).mono
        (treeReplayTypeEnv_le_leafEnv.trans
          (treeReplayLeafEnv_le_nodeEnv.trans
            treeReplayNodeEnv_le_branchEnv)))

theorem treeListConsKernelInfo_tr :
    TrConstVal .safe treeReplayNilEnv treeListConsKernelInfo
      treeListType.ctors[1] := by
  have hTree : treeReplayNilEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeReplayNilEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr treeReplayNilEnv
      treeListConsKernelInfo.levelParams [] treeListConsKernelInfo.type
      treeListType.ctors[1].type := by tr_type_expr_tac
  exact hshape.to_trExprS treeReplayNilEnv_ordered trivial
    ((treeCtorWF treeListType.ctors[1]
      (.inr (by simp [treeListType]))).mono
        (treeReplayTypeEnv_le_leafEnv.trans
          (treeReplayLeafEnv_le_nodeEnv.trans
            (treeReplayNodeEnv_le_branchEnv.trans
              treeReplayBranchEnv_le_nilEnv))))

/-! ## Exact ordinary-candidate block generation -/

/-- Minimal verifier family used at the ordinary candidate's pre-family
kernel environment. -/
def treeCandidateVEnvs : VEnvs where
  venv _ := VEnv.empty

theorem treeCandidateHasPrimitives : VEnv.HasPrimitives VEnv.empty := by
  apply VEnv.HasPrimitives.of_avoids
  intro name membership
  rfl

theorem treeCandidateSafePrimitives :
    treeKernelContext.env.find? name = some info →
      Environment.primitives.contains name →
      info.safety = .safe ∧ info.levelParams = [] := by
  intro found primitive
  change ({} : ConstMap).find?' name = some info at found
  rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at found
  simp [SMap.find?] at found

theorem treeCandidateVEnvsWF :
    treeCandidateVEnvs.WF treeKernelContext.env where
  tr := by
    intro safety
    change TrEnv' safety ({} : ConstMap) false VEnv.empty
    exact .empty
  hasPrimitives := treeCandidateHasPrimitives
  safePrimitives := treeCandidateSafePrimitives
  mono := fun _ => .rfl
  projectionReady := ProjectionReady.of_no_ctorInfo <| by
    intro name info found
    change ({} : ConstMap).find?' name = some (.ctorInfo info) at found
    rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at found
    simp [SMap.find?] at found
  structureEtaReady := StructureEtaReady.of_no_ctorInfo <| by
    intro name info found
    change ({} : ConstMap).find?' name = some (.ctorInfo info) at found
    rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at found
    simp [SMap.find?] at found

theorem treeCandidateNamePrefixNe :
    treeKernelContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def treeCandidatePreContextRun :
    TypeChecker.CandidateContextRun { treeKernelContext with lctx := {} } :=
  TypeChecker.CandidateContextRun.root treeCandidateVEnvsWF rfl
    treeCandidateNamePrefixNe

def treeCandidatePreStage : TypeChecker.CandidateSemanticStage
    { treeKernelContext with lctx := {} } VEnv.empty [`u] where
  contextRun := treeCandidatePreContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

theorem treeKernelLevelParams : treeKernelInfo.levelParams = [`u] := by
  native_decide

theorem treeListKernelLevelParams :
    treeListKernelInfo.levelParams = [`u] := by
  native_decide

theorem treeLeafKernelLevelParams :
    treeLeafKernelInfo.levelParams = [`u] := by
  native_decide

theorem treeNodeKernelLevelParams :
    treeNodeKernelInfo.levelParams = [`u] := by
  native_decide

theorem treeBranchKernelLevelParams :
    treeBranchKernelInfo.levelParams = [`u] := by
  native_decide

theorem treeListNilKernelLevelParams :
    treeListNilKernelInfo.levelParams = [`u] := by
  native_decide

theorem treeListConsKernelLevelParams :
    treeListConsKernelInfo.levelParams = [`u] := by
  native_decide

theorem treeReplayTypeEnv_eq_blockEnv : treeReplayTypeEnv = treeBlockEnv := rfl

theorem treeCandidateValidationEnv_eq :
    treeExecution.validationContext.env = treeKernelContext.env := by
  exact treeExecution.validationContext_env
    treeBlockGenerationShape.producedExecution (by decide)

theorem treeFamilySourceTr :
    TrExprS VEnv.empty [`u] [] treeKernelType.type treeType.type := by
  simpa only [treeKernelType, treeKernelLevelParams] using
    treeKernelInfo_tr.1.2.2

theorem treeListFamilySourceTr :
    TrExprS VEnv.empty [`u] [] treeListKernelType.type treeListType.type := by
  have shape : TrTypeExpr VEnv.empty treeListKernelInfo.levelParams []
      treeListKernelInfo.type treeListType.type := by
    tr_type_expr_tac
  rw [treeListKernelLevelParams] at shape
  simpa [treeListKernelType] using shape.to_trExprS
    (show VEnv.empty.Ordered from .empty) trivial
    (treeFamilyTypeWF treeListType (.inr rfl))

def treeCandidateFamilySources : CandidateBlockFamilyTypeSourceListInput
    VEnv.empty [`u] treeKernelTypes treeDecl.types :=
  .cons {
      name_eq := rfl
      uvars_eq := rfl
      source_tr := treeFamilySourceTr }
    (.cons {
      name_eq := rfl
      uvars_eq := rfl
      source_tr := treeListFamilySourceTr } .nil)

theorem treeCandidateBlockEnvOrdered : treeBlockEnv.Ordered :=
  treeReplayTypeEnv_ordered

theorem treeLeafSourceTr :
    TrExprS treeBlockEnv [`u] [] treeKernelType.ctors[0].type
      treeType.ctors[0].type := by
  simpa [treeKernelType, treeLeafKernelLevelParams,
    treeReplayTypeEnv_eq_blockEnv] using treeLeafKernelInfo_tr.1.2.2

theorem treeNodeSourceTr :
    TrExprS treeBlockEnv [`u] [] treeKernelType.ctors[1].type
      treeType.ctors[1].type := by
  have hTree : treeBlockEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeBlockEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  have shape : TrTypeExpr treeBlockEnv treeNodeKernelInfo.levelParams []
      treeNodeKernelInfo.type treeType.ctors[1].type := by
    tr_type_expr_tac
  rw [treeNodeKernelLevelParams] at shape
  simpa [treeKernelType] using shape.to_trExprS
    treeCandidateBlockEnvOrdered trivial
    (treeCtorWF treeType.ctors[1] (.inl (by simp [treeType])))

theorem treeBranchSourceTr :
    TrExprS treeBlockEnv [`u] [] treeKernelType.ctors[2].type
      treeType.ctors[2].type := by
  have hTree : treeBlockEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeBlockEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  have shape : TrTypeExpr treeBlockEnv treeBranchKernelInfo.levelParams []
      treeBranchKernelInfo.type treeType.ctors[2].type := by
    tr_type_expr_tac
  rw [treeBranchKernelLevelParams] at shape
  simpa [treeKernelType] using shape.to_trExprS
    treeCandidateBlockEnvOrdered trivial
    (treeCtorWF treeType.ctors[2] (.inl (by simp [treeType])))

theorem treeListNilSourceTr :
    TrExprS treeBlockEnv [`u] [] treeListKernelType.ctors[0].type
      treeListType.ctors[0].type := by
  have hTree : treeBlockEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeBlockEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  have shape : TrTypeExpr treeBlockEnv treeListNilKernelInfo.levelParams []
      treeListNilKernelInfo.type treeListType.ctors[0].type := by
    tr_type_expr_tac
  rw [treeListNilKernelLevelParams] at shape
  simpa [treeListKernelType] using shape.to_trExprS
    treeCandidateBlockEnvOrdered trivial
    (treeCtorWF treeListType.ctors[0] (.inr (by simp [treeListType])))

theorem treeListConsSourceTr :
    TrExprS treeBlockEnv [`u] [] treeListKernelType.ctors[1].type
      treeListType.ctors[1].type := by
  have hTree : treeBlockEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeBlockEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  have shape : TrTypeExpr treeBlockEnv treeListConsKernelInfo.levelParams []
      treeListConsKernelInfo.type treeListType.ctors[1].type := by
    tr_type_expr_tac
  rw [treeListConsKernelLevelParams] at shape
  simpa [treeListKernelType] using shape.to_trExprS
    treeCandidateBlockEnvOrdered trivial
    (treeCtorWF treeListType.ctors[1] (.inr (by simp [treeListType])))

theorem treeCandidateFamilyEnvNoCtorInfo :
    ∀ name info, treeExecution.familyEnv.find? name ≠
      some (.ctorInfo info) := by
  intro name info
  have initialWF : treeExecution.validationContext.env.constants.WF := by
    rw [treeCandidateValidationEnv_eq]
    exact SMap.WF.empty
  have finalWF := declarationTraceConstantsWF treeExecution.declareTrace
    initialWF
  intro found
  change treeExecution.familyEnv.constants.find?' name =
    some (.ctorInfo info) at found
  rw [finalWF.find?'_eq_find?] at found
  exact declarationTraceNoCtorInfo treeExecution.declareTrace initialWF
    (by
      intro n i h
      rw [treeCandidateValidationEnv_eq] at h
      simp [treeKernelContext, Kernel.Environment.ofConstants,
        SMap.find?] at h) name info found

/-- The exact shared family stage derived from the ordinary mutual candidate
execution and its family-only declaration trace. -/
def treeCandidateStaging : NormalizationCandidateBlockStagingInput
    treeKernelContext treeExecution VEnv.empty treeBlockEnv [`u] treeDecl where
  uvars_eq := rfl
  preFamily := treeCandidatePreStage
  familyTypes := treeCandidateFamilySources.staged
    treeExecution.candidate.families (by
      change CandidateFamilyTypeListProduced _
        treeExecution.families.candidates.familyTypes
      rw [treeExecution.families.produced.familyTypes_eq]
      exact treeExecution.familyTypes.produced) 9999 rfl
  terminals := CandidateBlockFamilyTerminalSortList.of_check
    treeExecution.candidate.families (by native_decide)
  stage := treeStage
  nindices_size := treeFamilyValidation.nindices_size
  validation_env_eq := treeCandidateValidationEnv_eq
  validation_lparams_eq := by native_decide
  context_safety_eq := rfl
  isUnsafe_eq := rfl
  preMapWF := SMap.WF.empty
  names_not_primitive := by
    intro raw member
    simp [treeDecl] at member
    rcases member with rfl | rfl
    · constructor
      · simp [treeType, VEnv.reflectedPrimitiveNames]
      · simp [treeType, Kernel.Environment.primitives, NameSet.ofList,
          NameSet.contains]
    · constructor
      · simp [treeListType, VEnv.reflectedPrimitiveNames]
      · simp [treeListType, Kernel.Environment.primitives, NameSet.ofList,
          NameSet.contains]
  projectionReady := ProjectionReady.of_no_ctorInfo <| by
    intro name info found
    exact treeCandidateFamilyEnvNoCtorInfo name info found
  structureEtaReady := StructureEtaReady.of_no_ctorInfo <| by
    intro name info found
    exact treeCandidateFamilyEnvNoCtorInfo name info found

def treeCandidateConstructorSources :
    CandidateBlockConstructorSourceListInput treeBlockEnv [`u]
      treeKernelTypes treeDecl.types :=
  .cons
    (.cons {
        name_eq := rfl
        uvars_eq := rfl
        source_tr := treeLeafSourceTr }
      (.cons {
          name_eq := rfl
          uvars_eq := rfl
          source_tr := treeNodeSourceTr }
        (.cons {
            name_eq := rfl
            uvars_eq := rfl
            source_tr := treeBranchSourceTr }
          .nil)))
    (.cons
      (.cons {
          name_eq := rfl
          uvars_eq := rfl
          source_tr := treeListNilSourceTr }
        (.cons {
            name_eq := rfl
            uvars_eq := rfl
            source_tr := treeListConsSourceTr }
          .nil))
      .nil)

def treeCandidateConstructors : CandidateBlockConstructorStagedListInput
    treeCandidateStaging.postFamily treeExecution.candidate.families
      treeDecl.types :=
  treeCandidateConstructorSources.staged treeExecution.candidate.families
    treeExecution.families.produced.constructorLists 9999 rfl

/-- Complete pre/post-family staged owner for the ordinary mutual candidate. -/
def treeStagedCandidateSemantic :
    StagedNormalizationCandidateBlockSemanticInput treeCandidateStaging where
  postFamily := treeCandidateStaging.postFamily
  constructors := treeCandidateConstructors

/-- Identity-specialized semantic interpretation of the exact ordinary
candidate hierarchy. -/
def treeCandidateIdentitySemantic : NormalizationCandidateBlockSemanticRun
    VEnv.empty treeBlockEnv [`u] treeExecution.candidate treeDecl :=
  treeStagedCandidateSemantic.semanticRunOfIdentity (by native_decide)

theorem treeCandidateIdentityNormalization :
    treeCandidateIdentitySemantic.normalization =
      Normalization.identity treeDecl := by
  simpa only [treeCandidateIdentitySemantic] using
    treeStagedCandidateSemantic.semanticRunOfIdentity_normalization
      (by native_decide)

theorem treeCandidateIdentityAnalysis :
    treeCandidateIdentitySemantic.normalization.checkBlock? =
      some treeGeneration.block := by
  rw [treeCandidateIdentityNormalization]
  rfl

def treeProducedCandidateIdentitySemantic :
    ProducedNormalizationCandidateBlockSemanticRun
      { treeKernelContext with lctx := {} }
      { treeKernelContext with env := treeExecution.familyEnv, lctx := {} }
      VEnv.empty treeBlockEnv [`u] treeExecution.candidate treeDecl where
  semantic := treeCandidateIdentitySemantic
  familyTypesProduced := by
    change CandidateFamilyTypeListProduced _
      treeExecution.families.candidates.familyTypes
    rw [treeExecution.families.produced.familyTypes_eq]
    exact treeExecution.familyTypes.produced
  familiesProduced := treeExecution.families.produced.reindex

/-- Exact dependent closure from the ordinary kernel-facing producer through
the generic block-generation assembler. -/
def treeExactProducedBlockGeneration : ExactProducedBlockGenerationRun
    VEnv.empty treeBlockEnv [`u] treeBlockGenerationShape treeGeneration where
  producedSemantic := treeProducedCandidateIdentitySemantic
  analysis := treeCandidateIdentityAnalysis
  checked := treeCheckedBlockWF
  resultLevelWF := by decide

/-- The ordinary exact semantic run paired with the constructor environment,
elimination level, recursor universe layout, and K decision from the same
strengthened kernel execution. -/
def treeExactProducedBlockElimination : ExactProducedBlockEliminationRun
    VEnv.empty treeBlockEnv [`u] treeBlockEliminationShape treeGeneration where
  block := by
    rw [treeBlockEliminationBase_eq]
    exact treeExactProducedBlockGeneration
  elimination := treeBlockEliminationAlignment
  isUnsafe_eq := rfl
  validation_lparams_eq := by
    change treeEliminationExecution.normalization.validationContext.lparams =
      [`u]
    rw [treeEliminationNormalization_eq]
    exact treeCandidateStaging.validation_lparams_eq

/-- Exact semantic generation indexed by the ordinary run that has already
synthesized and installed both mutual recursors. -/
def treeExactProducedBlockRecursor : ExactProducedBlockRecursorRun
    VEnv.empty treeBlockEnv [`u] treeBlockRecursorShape treeGeneration where
  elimination := by
    rw [treeBlockRecursorEliminationBase_eq]
    exact treeExactProducedBlockElimination

/-- Reindex the already-derived family staging input onto the normalization
execution retained by the stronger producer. -/
def treeExactEliminationStaging : NormalizationCandidateBlockStagingInput
    treeKernelContext treeEliminationExecution.normalization
      VEnv.empty treeBlockEnv [`u] treeDecl := by
  rw [treeEliminationNormalization_eq]
  exact treeCandidateStaging

/-- Reindex the same semantic staging data onto the stronger execution that
continues through actual recursor synthesis. -/
def treeExactRecursorStaging : NormalizationCandidateBlockStagingInput
    treeKernelContext
      treeBlockRecursorShape.execution.eliminationExecution.normalization
      VEnv.empty treeBlockEnv [`u] treeDecl := by
  change NormalizationCandidateBlockStagingInput treeKernelContext
    treeRecursorExecution.eliminationExecution.normalization
      VEnv.empty treeBlockEnv [`u] treeDecl
  rw [treeRecursorElimination_eq]
  exact treeExactEliminationStaging

/-- One exact owner of both declaration phases preceding recursor synthesis. -/
noncomputable def treeExactDeclarationRun :
    ExactProducedBlockDeclarationRun treeExactProducedBlockElimination :=
  treeExactProducedBlockElimination.declarationRun
    treeExactEliminationStaging

/-- The identical family/constructor prefix, now indexed by the execution
that owns the generated recursor records. -/
noncomputable def treeExactRecursorDeclarationRun :=
  treeExactProducedBlockRecursor.elimination.declarationRun
    treeExactRecursorStaging

/-- Exact paired family declaration underlying the shared constructor
checker context. -/
noncomputable def treeExactFamilyDeclaration :
    FamilyDeclarationStagingRun
      treeExecution.validationContext.allowPrimitive
      treeExecution.validationContext.env treeExecution.familyEnv
      treeExecution.declaredInfos VEnv.empty treeBlockEnv
      treeDecl.blockTypeConstants treeExecution.validationContext.env.quotInit := by
  rw [← treeEliminationNormalization_eq]
  exact treeExactDeclarationRun.families

theorem treeExactFamilyDeclaration_fold :
    treeDecl.blockTypeConstants.foldlM
      (fun env family => env.addConst family.name family.toVConstant)
      VEnv.empty = some treeBlockEnv :=
  treeExactFamilyDeclaration.addTypes.to_foldlM

/-- The retained ordinary constructor declaration interpreted directly as a
kernel/Theory staging run.  Its map is the real post-constructor kernel map,
and its Theory environment is constructed from the exact raw constructor
inventory rather than the replay fixture below. -/
noncomputable def treeExactConstructorDeclaration :
    ConstructorDeclarationStagingRun
      treeEliminationExecution.constructorContext.allowPrimitive
      treeEliminationExecution.normalization.familyEnv
      treeEliminationExecution.constructorEnv
      treeEliminationExecution.declaredConstructorInfos
      treeBlockEnv treeDecl.blockConstructorConstants
      treeEliminationExecution.normalization.validationContext.env.quotInit :=
  treeExactDeclarationRun.constructors

theorem treeExactConstructorDeclaration_fold :
    treeDecl.blockConstructorConstants.foldlM
      (fun env constructor =>
        env.addConst constructor.name constructor.toVConstant)
      treeBlockEnv = some treeExactConstructorDeclaration.ctorEnv :=
  treeExactConstructorDeclaration.addCtors.to_foldlM

/-- The Theory environment constructed from the recursor-owning execution is
the existing post-constructor replay boundary. -/
theorem treeExactRecursorConstructorEnv_eq :
    (treeExactProducedBlockRecursor.elimination.declarationRun
      treeExactRecursorStaging).constructors.ctorEnv =
        treeReplayCtorEnv := by
  have replay : treeDecl.blockConstructorConstants.foldlM
      (fun env constructor =>
        env.addConst constructor.name constructor.toVConstant)
      treeBlockEnv = some treeReplayCtorEnv := by rfl
  rw [(treeExactProducedBlockRecursor.elimination.declarationRun
    treeExactRecursorStaging).constructors.addCtors.to_foldlM] at replay
  exact Option.some.inj replay

/-- The real mutual block's generation certificate can be reconstructed from
the ordinary normalization execution without fixture-selected family or
constructor inventories. -/
theorem treeBlockGenerationWF_fromCandidate :
    treeGeneration.WF VEnv.empty treeBlockEnv :=
  treeExactProducedBlockGeneration.blockGenerationRun.wf

theorem treeRecKernelInfo_tr :
    TrConstVal .safe treeReplayCtorEnv treeRecKernelInfo
      treeGeneration.recursors[0] := by
  have hTree : treeReplayCtorEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeReplayCtorEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  have hLeaf : treeReplayCtorEnv.constants ``Tree.leaf =
      some treeType.ctors[0].toVConstant := rfl
  have hNode : treeReplayCtorEnv.constants ``Tree.node =
      some treeType.ctors[1].toVConstant := rfl
  have hBranch : treeReplayCtorEnv.constants ``Tree.branch =
      some treeType.ctors[2].toVConstant := rfl
  have hNil : treeReplayCtorEnv.constants ``TreeList.nil =
      some treeListType.ctors[0].toVConstant := rfl
  have hCons : treeReplayCtorEnv.constants ``TreeList.cons =
      some treeListType.ctors[1].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr treeReplayCtorEnv
      treeRecKernelInfo.levelParams [] treeRecKernelInfo.type
      treeGeneration.recursors[0].type := by tr_type_expr_tac
  obtain ⟨u, hrec⟩ :=
    treeReplayGenerationEnv.recursor_wf (.head _)
  exact hshape.to_trExprS treeReplayCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

theorem treeListRecKernelInfo_tr_atCtor :
    TrConstVal .safe treeReplayCtorEnv treeListRecKernelInfo
      treeGeneration.recursors[1] := by
  have hTree : treeReplayCtorEnv.constants ``Tree =
      some treeType.toVConstant := rfl
  have hTreeList : treeReplayCtorEnv.constants ``TreeList =
      some treeListType.toVConstant := rfl
  have hLeaf : treeReplayCtorEnv.constants ``Tree.leaf =
      some treeType.ctors[0].toVConstant := rfl
  have hNode : treeReplayCtorEnv.constants ``Tree.node =
      some treeType.ctors[1].toVConstant := rfl
  have hBranch : treeReplayCtorEnv.constants ``Tree.branch =
      some treeType.ctors[2].toVConstant := rfl
  have hNil : treeReplayCtorEnv.constants ``TreeList.nil =
      some treeListType.ctors[0].toVConstant := rfl
  have hCons : treeReplayCtorEnv.constants ``TreeList.cons =
      some treeListType.ctors[1].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr treeReplayCtorEnv
      treeListRecKernelInfo.levelParams [] treeListRecKernelInfo.type
      treeGeneration.recursors[1].type := by tr_type_expr_tac
  obtain ⟨u, hrec⟩ :=
    treeReplayGenerationEnv.recursor_wf (.tail _ (.head _))
  exact hshape.to_trExprS treeReplayCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

theorem treeListRecKernelInfo_tr :
    TrConstVal .safe treeReplayFirstRecEnv treeListRecKernelInfo
      treeGeneration.recursors[1] :=
  treeListRecKernelInfo_tr_atCtor.mono treeReplayCtorEnv_le_firstRecEnv

/-- Semantic translations of the stored kernel recursor records at their
shared post-constructor boundary. -/
theorem treeExpectedRecursorEvidence : List.Forall₂
    (fun info raw =>
      TrConstVal .safe treeReplayCtorEnv (.recInfo info) raw)
    treeExpectedRecursorInfos treeGeneration.recursors := by
  have hrecs : treeGeneration.recursors =
      [treeGeneration.recursors[0], treeGeneration.recursors[1]] := rfl
  rw [hrecs]
  exact .cons
    (by
      simpa [treeExpectedRecursorInfos, treeRecKernelInfo,
        kernelRecursorInfo?] using treeRecKernelInfo_tr)
    (.cons
      (by
        simpa [treeExpectedRecursorInfos, treeListRecKernelInfo,
          kernelRecursorInfo?] using treeListRecKernelInfo_tr_atCtor)
      .nil)

/-- Translation evidence for the records synthesized by the actual ordinary
run, obtained from full stored-record parity without asserting propositional
equality of opaque kernel expressions. -/
theorem treeGeneratedRecursorEvidence : List.Forall₂
    (fun info raw => TrConstVal .safe
      (treeExactProducedBlockRecursor.elimination.declarationRun
        treeExactRecursorStaging).constructors.ctorEnv
      (.recInfo info) raw)
    treeBlockRecursorShape.execution.recursors.infos
      treeGeneration.recursors := by
  rw [treeExactRecursorConstructorEnv_eq]
  apply recursorInfoTranslationList_of_option_beq
    (expected := treeExpectedRecursorInfos)
  · simpa [treeRecursorExecution, treeExpectedRecursorInfos,
      treeRecKernelInfo, treeListRecKernelInfo,
      kernelRecursorInfo?] using treeGeneratedRecursorInfos_match
  · exact treeExpectedRecursorEvidence

theorem treeGeneratedRecursorsWF :
    ∀ raw ∈ treeGeneration.recursors,
      raw.toVConstant.WF
        (treeExactProducedBlockRecursor.elimination.declarationRun
          treeExactRecursorStaging).constructors.ctorEnv := by
  intro raw member
  rw [treeExactRecursorConstructorEnv_eq]
  simp only [BlockGenerationChecked.recursors, List.mem_map] at member
  obtain ⟨family, hfamily, rfl⟩ := member
  exact treeReplayGenerationEnv.recursor_wf hfamily

/-- The ordinary mutual fixture now consumes the actual synthesized recursor
inventory in the same exact family/constructor/recursor staging prefix. -/
noncomputable def treeExactMetadataPrefixRun :
    ExactProducedBlockMetadataPrefixRun treeExactProducedBlockRecursor :=
  treeExactProducedBlockRecursor.metadataPrefix treeExactRecursorStaging
    treeGeneratedRecursorEvidence treeGeneratedRecursorsWF

def treeReplayFirstTypeMap : ConstMap :=
  ({} : ConstMap).insert ``Tree treeKernelInfo

def treeReplayTypeMap : ConstMap :=
  treeReplayFirstTypeMap.insert ``TreeList treeListKernelInfo

def treeReplayLeafMap : ConstMap :=
  treeReplayTypeMap.insert ``Tree.leaf treeLeafKernelInfo

def treeReplayNodeMap : ConstMap :=
  treeReplayLeafMap.insert ``Tree.node treeNodeKernelInfo

def treeReplayBranchMap : ConstMap :=
  treeReplayNodeMap.insert ``Tree.branch treeBranchKernelInfo

def treeReplayNilMap : ConstMap :=
  treeReplayBranchMap.insert ``TreeList.nil treeListNilKernelInfo

def treeReplayCtorMap : ConstMap :=
  treeReplayNilMap.insert ``TreeList.cons treeListConsKernelInfo

def treeReplayFirstRecMap : ConstMap :=
  treeReplayCtorMap.insert ``Tree.rec treeRecKernelInfo

def treeReplayMap : ConstMap :=
  treeReplayFirstRecMap.insert ``TreeList.rec treeListRecKernelInfo

theorem treeReplayFirstType_fresh :
    ({} : ConstMap).find? ``Tree = none := by
  simp [SMap.find?]

theorem treeReplayFirstTypeMap_wf : treeReplayFirstTypeMap.WF :=
  SMap.WF.empty.insert _ _ treeReplayFirstType_fresh

theorem treeReplaySecondType_fresh :
    treeReplayFirstTypeMap.find? ``TreeList = none := by
  rw [treeReplayFirstTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem treeReplayTypeMap_wf : treeReplayTypeMap.WF :=
  treeReplayFirstTypeMap_wf.insert _ _ treeReplaySecondType_fresh

theorem treeReplayLeaf_fresh :
    treeReplayTypeMap.find? ``Tree.leaf = none := by
  rw [treeReplayTypeMap, treeReplayFirstTypeMap_wf.find?_insert,
    treeReplayFirstTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem treeReplayLeafMap_wf : treeReplayLeafMap.WF :=
  treeReplayTypeMap_wf.insert _ _ treeReplayLeaf_fresh

theorem treeReplayNode_fresh :
    treeReplayLeafMap.find? ``Tree.node = none := by
  rw [treeReplayLeafMap, treeReplayTypeMap_wf.find?_insert,
    treeReplayTypeMap, treeReplayFirstTypeMap_wf.find?_insert,
    treeReplayFirstTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem treeReplayNodeMap_wf : treeReplayNodeMap.WF :=
  treeReplayLeafMap_wf.insert _ _ treeReplayNode_fresh

theorem treeReplayBranch_fresh :
    treeReplayNodeMap.find? ``Tree.branch = none := by
  rw [treeReplayNodeMap, treeReplayLeafMap_wf.find?_insert,
    treeReplayLeafMap, treeReplayTypeMap_wf.find?_insert,
    treeReplayTypeMap, treeReplayFirstTypeMap_wf.find?_insert,
    treeReplayFirstTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem treeReplayBranchMap_wf : treeReplayBranchMap.WF :=
  treeReplayNodeMap_wf.insert _ _ treeReplayBranch_fresh

theorem treeReplayNil_fresh :
    treeReplayBranchMap.find? ``TreeList.nil = none := by
  rw [treeReplayBranchMap, treeReplayNodeMap_wf.find?_insert,
    treeReplayNodeMap, treeReplayLeafMap_wf.find?_insert,
    treeReplayLeafMap, treeReplayTypeMap_wf.find?_insert,
    treeReplayTypeMap, treeReplayFirstTypeMap_wf.find?_insert,
    treeReplayFirstTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem treeReplayNilMap_wf : treeReplayNilMap.WF :=
  treeReplayBranchMap_wf.insert _ _ treeReplayNil_fresh

theorem treeReplayCons_fresh :
    treeReplayNilMap.find? ``TreeList.cons = none := by
  rw [treeReplayNilMap, treeReplayBranchMap_wf.find?_insert,
    treeReplayBranchMap, treeReplayNodeMap_wf.find?_insert,
    treeReplayNodeMap, treeReplayLeafMap_wf.find?_insert,
    treeReplayLeafMap, treeReplayTypeMap_wf.find?_insert,
    treeReplayTypeMap, treeReplayFirstTypeMap_wf.find?_insert,
    treeReplayFirstTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem treeReplayCtorMap_wf : treeReplayCtorMap.WF :=
  treeReplayNilMap_wf.insert _ _ treeReplayCons_fresh

theorem treeReplayFirstRec_fresh :
    treeReplayCtorMap.find? ``Tree.rec = none := by
  rw [treeReplayCtorMap, treeReplayNilMap_wf.find?_insert,
    treeReplayNilMap, treeReplayBranchMap_wf.find?_insert,
    treeReplayBranchMap, treeReplayNodeMap_wf.find?_insert,
    treeReplayNodeMap, treeReplayLeafMap_wf.find?_insert,
    treeReplayLeafMap, treeReplayTypeMap_wf.find?_insert,
    treeReplayTypeMap, treeReplayFirstTypeMap_wf.find?_insert,
    treeReplayFirstTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem treeReplayFirstRecMap_wf : treeReplayFirstRecMap.WF :=
  treeReplayCtorMap_wf.insert _ _ treeReplayFirstRec_fresh

theorem treeReplaySecondRec_fresh :
    treeReplayFirstRecMap.find? ``TreeList.rec = none := by
  rw [treeReplayFirstRecMap, treeReplayCtorMap_wf.find?_insert,
    treeReplayCtorMap, treeReplayNilMap_wf.find?_insert,
    treeReplayNilMap, treeReplayBranchMap_wf.find?_insert,
    treeReplayBranchMap, treeReplayNodeMap_wf.find?_insert,
    treeReplayNodeMap, treeReplayLeafMap_wf.find?_insert,
    treeReplayLeafMap, treeReplayTypeMap_wf.find?_insert,
    treeReplayTypeMap, treeReplayFirstTypeMap_wf.find?_insert,
    treeReplayFirstTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem treeReplayMap_wf : treeReplayMap.WF :=
  treeReplayFirstRecMap_wf.insert _ _ treeReplaySecondRec_fresh

theorem treeReplay_treeRec_lookup :
    treeReplayMap.find? ``Tree.rec = some treeRecKernelInfo := by
  rw [treeReplayMap, treeReplayFirstRecMap_wf.find?_insert,
    treeReplayFirstRecMap, treeReplayCtorMap_wf.find?_insert]
  rfl

theorem treeReplay_treeListRec_lookup :
    treeReplayMap.find? ``TreeList.rec = some treeListRecKernelInfo := by
  rw [treeReplayMap, treeReplayFirstRecMap_wf.find?_insert]
  rfl

def treeAddInductBlockTrace :
    AddInductBlockTrace ({} : ConstMap) VEnv.empty treeDecl
      treeReplayMap treeFinalEnv where
  generation := treeGeneration
  blockEnv := treeBlockEnv
  generation_wf := treeBlockGenerationWF
  typeMap := treeReplayTypeMap
  typeEnv := treeReplayTypeEnv
  ctorMap := treeReplayCtorMap
  ctorEnv := treeReplayCtorEnv
  recEnv := treeReplayRecEnv
  addTypes := .cons {
      info := treeKernelInfo
      kind_eq := by simp [treeKernelInfo, InductConstantKind.Matches]
      tr := treeKernelInfo_tr
      map_fresh := treeReplayFirstType_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := treeListKernelInfo
      kind_eq := by simp [treeListKernelInfo, InductConstantKind.Matches]
      tr := treeListKernelInfo_tr
      map_fresh := treeReplaySecondType_fresh
      env_add := rfl
      map_add := rfl } .nil)
  addCtors := .cons {
      info := treeLeafKernelInfo
      kind_eq := by simp [treeLeafKernelInfo, InductConstantKind.Matches]
      tr := treeLeafKernelInfo_tr
      map_fresh := treeReplayLeaf_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := treeNodeKernelInfo
      kind_eq := by simp [treeNodeKernelInfo, InductConstantKind.Matches]
      tr := treeNodeKernelInfo_tr
      map_fresh := treeReplayNode_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := treeBranchKernelInfo
      kind_eq := by simp [treeBranchKernelInfo, InductConstantKind.Matches]
      tr := treeBranchKernelInfo_tr
      map_fresh := treeReplayBranch_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := treeListNilKernelInfo
      kind_eq := by simp [treeListNilKernelInfo, InductConstantKind.Matches]
      tr := treeListNilKernelInfo_tr
      map_fresh := treeReplayNil_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := treeListConsKernelInfo
      kind_eq := by simp [treeListConsKernelInfo, InductConstantKind.Matches]
      tr := treeListConsKernelInfo_tr
      map_fresh := treeReplayCons_fresh
      env_add := rfl
      map_add := rfl } .nil))))
  addRecs := .cons {
      info := treeRecKernelInfo
      kind_eq := by simp [treeRecKernelInfo, InductConstantKind.Matches]
      tr := treeRecKernelInfo_tr
      map_fresh := treeReplayFirstRec_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := treeListRecKernelInfo
      kind_eq := by simp [treeListRecKernelInfo, InductConstantKind.Matches]
      tr := treeListRecKernelInfo_tr
      map_fresh := treeReplaySecondRec_fresh
      env_add := rfl
      map_add := rfl } .nil)
  recK := by
    intro recursor hrecursor
    have hrecs : treeGeneration.recursors =
        [treeGeneration.recursors[0], treeGeneration.recursors[1]] := rfl
    rw [hrecs] at hrecursor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrecursor
    rcases hrecursor with rfl | rfl
    · exact ⟨treeRecKernelInfo, treeReplay_treeRec_lookup, by decide⟩
    · exact ⟨treeListRecKernelInfo, treeReplay_treeListRec_lookup,
        by decide⟩
  addRules := ⟨rfl⟩

theorem treeAddInductBlock :
    AddInductBlock ({} : ConstMap) VEnv.empty treeDecl
      treeReplayMap treeFinalEnv :=
  ⟨treeAddInductBlockTrace⟩

/-- The Theory recursor fold constructed from the actual synthesized records
has the same endpoint as the independently replayed raw-constant fold. -/
theorem treeExactProducedRecEnv_eq :
    treeExactMetadataPrefixRun.recursors.recEnv = treeReplayRecEnv := by
  have ctorEnvEq :
      treeExactMetadataPrefixRun.declarations.constructors.ctorEnv =
        treeReplayCtorEnv := by
    change (treeExactProducedBlockRecursor.elimination.declarationRun
      treeExactRecursorStaging).constructors.ctorEnv = treeReplayCtorEnv
    exact treeExactRecursorConstructorEnv_eq
  have exactFold := treeExactMetadataPrefixRun.recursors.addRecs.to_foldlM
  have replayFold : treeGeneration.recursors.foldlM
      (fun env recursor => env.addConst recursor.name recursor.toVConstant)
      treeReplayCtorEnv = some treeReplayRecEnv := by rfl
  have folds := congrArg
    (fun start => treeGeneration.recursors.foldlM
      (fun env recursor => env.addConst recursor.name recursor.toVConstant)
      start) ctorEnvEq
  rw [exactFold, replayFold] at folds
  exact Option.some.inj folds

/-- The ordinary exact transaction now ends in the actual synthesized kernel
map.  Family, constructor, recursor, and K evidence all come from the retained
producer; only the deterministic Theory rule fold closes the transaction. -/
noncomputable def treeExactProducedBlockMetadataTrace :
    AddInductBlockTrace
      treeRecursorExecution.eliminationExecution.normalization.validationContext.env.constants
      VEnv.empty treeDecl
      treeRecursorExecution.recursors.env.constants treeFinalEnv :=
  treeExactMetadataPrefixRun.addInductBlockTrace (env₂ := treeFinalEnv) ⟨by
    rw [treeExactProducedRecEnv_eq]
    rfl⟩

theorem treeExactProducedBlockMetadata :
    AddInductBlock
      treeRecursorExecution.eliminationExecution.normalization.validationContext.env.constants
      VEnv.empty treeDecl
      treeRecursorExecution.recursors.env.constants treeFinalEnv :=
  ⟨treeExactProducedBlockMetadataTrace⟩

theorem tree_trEnv' : TrEnv' .safe treeReplayMap false treeFinalEnv :=
  .inductBlock treeAddInductBlock .empty

theorem tree_verify_env_wf : treeFinalEnv.WF := tree_trEnv'.wf

theorem tree_verify_aligned :
    Aligned .safe treeReplayMap treeFinalEnv := tree_trEnv'.aligned

/-! ## Indexed Verify block replay -/

def indexedReplayFirstTypeEnv : VEnv :=
  (natFinalEnv.addConst indexedTreeType.name
    indexedTreeType.toVConstant).get!

def indexedReplayTypeEnv : VEnv :=
  (indexedReplayFirstTypeEnv.addConst indexedTreeListType.name
    indexedTreeListType.toVConstant).get!

def indexedReplayLeafEnv : VEnv :=
  (indexedReplayTypeEnv.addConst indexedTreeType.ctors[0].name
    indexedTreeType.ctors[0].toVConstant).get!

def indexedReplayNodeEnv : VEnv :=
  (indexedReplayLeafEnv.addConst indexedTreeType.ctors[1].name
    indexedTreeType.ctors[1].toVConstant).get!

def indexedReplayNilEnv : VEnv :=
  (indexedReplayNodeEnv.addConst indexedTreeListType.ctors[0].name
    indexedTreeListType.ctors[0].toVConstant).get!

def indexedReplayCtorEnv : VEnv :=
  (indexedReplayNilEnv.addConst indexedTreeListType.ctors[1].name
    indexedTreeListType.ctors[1].toVConstant).get!

def indexedReplayFirstRecEnv : VEnv :=
  (indexedReplayCtorEnv.addConst
    indexedTreeGeneration.recursors[0].name
    indexedTreeGeneration.recursors[0].toVConstant).get!

def indexedReplayRecEnv : VEnv :=
  (indexedReplayFirstRecEnv.addConst
    indexedTreeGeneration.recursors[1].name
    indexedTreeGeneration.recursors[1].toVConstant).get!

example : indexedReplayTypeEnv = indexedTreeBlockEnv := rfl

theorem indexedReplay_addFirstType :
    natFinalEnv.addConst indexedTreeType.name
      indexedTreeType.toVConstant = some indexedReplayFirstTypeEnv := rfl

theorem indexedReplay_addSecondType :
    indexedReplayFirstTypeEnv.addConst indexedTreeListType.name
      indexedTreeListType.toVConstant = some indexedReplayTypeEnv := rfl

theorem indexedReplay_addLeaf :
    indexedReplayTypeEnv.addConst indexedTreeType.ctors[0].name
      indexedTreeType.ctors[0].toVConstant =
        some indexedReplayLeafEnv := rfl

theorem indexedReplay_addNode :
    indexedReplayLeafEnv.addConst indexedTreeType.ctors[1].name
      indexedTreeType.ctors[1].toVConstant =
        some indexedReplayNodeEnv := rfl

theorem indexedReplay_addNil :
    indexedReplayNodeEnv.addConst indexedTreeListType.ctors[0].name
      indexedTreeListType.ctors[0].toVConstant =
        some indexedReplayNilEnv := rfl

theorem indexedReplay_addCons :
    indexedReplayNilEnv.addConst indexedTreeListType.ctors[1].name
      indexedTreeListType.ctors[1].toVConstant =
        some indexedReplayCtorEnv := rfl

theorem indexedReplay_addFirstRec :
    indexedReplayCtorEnv.addConst
      indexedTreeGeneration.recursors[0].name
      indexedTreeGeneration.recursors[0].toVConstant =
        some indexedReplayFirstRecEnv := rfl

theorem indexedReplay_addSecondRec :
    indexedReplayFirstRecEnv.addConst
      indexedTreeGeneration.recursors[1].name
      indexedTreeGeneration.recursors[1].toVConstant =
        some indexedReplayRecEnv := rfl

theorem indexedTreeTypeConstantWF :
    indexedTreeType.toVConstant.WF natFinalEnv := by
  exact indexedTreeBlockGenerationWF.rawFamily_isType (.head _)

theorem indexedTreeListTypeConstantWF :
    indexedTreeListType.toVConstant.WF natFinalEnv := by
  exact indexedTreeBlockGenerationWF.rawFamily_isType
    (.tail _ (.head _))

theorem indexedTreeLeafConstantWF :
    indexedTreeType.ctors[0].toVConstant.WF indexedReplayTypeEnv := by
  exact indexedTreeBlockGenerationWF.rawCtor_isType (.head _)

theorem indexedTreeNodeConstantWF :
    indexedTreeType.ctors[1].toVConstant.WF indexedReplayTypeEnv := by
  exact indexedTreeBlockGenerationWF.rawCtor_isType
    (.tail _ (.head _))

theorem indexedTreeNilConstantWF :
    indexedTreeListType.ctors[0].toVConstant.WF
      indexedReplayTypeEnv := by
  exact indexedTreeBlockGenerationWF.rawCtor_isType
    (.tail _ (.tail _ (.head _)))

theorem indexedTreeConsConstantWF :
    indexedTreeListType.ctors[1].toVConstant.WF
      indexedReplayTypeEnv := by
  exact indexedTreeBlockGenerationWF.rawCtor_isType
    (.tail _ (.tail _ (.tail _ (.head _))))

theorem indexedReplayFirstTypeEnv_ordered :
    indexedReplayFirstTypeEnv.Ordered := by
  exact .const natFinalEnv_ordered indexedTreeTypeConstantWF
    indexedReplay_addFirstType

theorem indexedReplayTypeEnv_ordered : indexedReplayTypeEnv.Ordered := by
  refine .const indexedReplayFirstTypeEnv_ordered ?_
    indexedReplay_addSecondType
  exact indexedTreeListTypeConstantWF.mono
    (VEnv.addConst_le indexedReplay_addFirstType)

theorem indexedReplayTypeEnv_le_leafEnv :
    indexedReplayTypeEnv ≤ indexedReplayLeafEnv :=
  VEnv.addConst_le indexedReplay_addLeaf

theorem indexedReplayLeafEnv_ordered : indexedReplayLeafEnv.Ordered := by
  exact .const indexedReplayTypeEnv_ordered indexedTreeLeafConstantWF
    indexedReplay_addLeaf

theorem indexedReplayLeafEnv_le_nodeEnv :
    indexedReplayLeafEnv ≤ indexedReplayNodeEnv :=
  VEnv.addConst_le indexedReplay_addNode

theorem indexedReplayNodeEnv_ordered : indexedReplayNodeEnv.Ordered := by
  refine .const indexedReplayLeafEnv_ordered ?_ indexedReplay_addNode
  exact indexedTreeNodeConstantWF.mono indexedReplayTypeEnv_le_leafEnv

theorem indexedReplayNodeEnv_le_nilEnv :
    indexedReplayNodeEnv ≤ indexedReplayNilEnv :=
  VEnv.addConst_le indexedReplay_addNil

theorem indexedReplayNilEnv_ordered : indexedReplayNilEnv.Ordered := by
  refine .const indexedReplayNodeEnv_ordered ?_ indexedReplay_addNil
  exact indexedTreeNilConstantWF.mono
    (indexedReplayTypeEnv_le_leafEnv.trans
      indexedReplayLeafEnv_le_nodeEnv)

theorem indexedReplayNilEnv_le_ctorEnv :
    indexedReplayNilEnv ≤ indexedReplayCtorEnv :=
  VEnv.addConst_le indexedReplay_addCons

theorem indexedReplayCtorEnv_ordered : indexedReplayCtorEnv.Ordered := by
  refine .const indexedReplayNilEnv_ordered ?_ indexedReplay_addCons
  exact indexedTreeConsConstantWF.mono
    (indexedReplayTypeEnv_le_leafEnv.trans
      (indexedReplayLeafEnv_le_nodeEnv.trans
        indexedReplayNodeEnv_le_nilEnv))

theorem indexedReplayInput_le_ctorEnv :
    natFinalEnv ≤ indexedReplayCtorEnv := by
  exact (VEnv.addConst_le indexedReplay_addFirstType).trans
    ((VEnv.addConst_le indexedReplay_addSecondType).trans
      (indexedReplayTypeEnv_le_leafEnv.trans
        (indexedReplayLeafEnv_le_nodeEnv.trans
          (indexedReplayNodeEnv_le_nilEnv.trans
            indexedReplayNilEnv_le_ctorEnv))))

theorem indexedReplayBlock_le_ctorEnv :
    indexedTreeBlockEnv ≤ indexedReplayCtorEnv := by
  exact indexedReplayTypeEnv_le_leafEnv.trans
    (indexedReplayLeafEnv_le_nodeEnv.trans
      (indexedReplayNodeEnv_le_nilEnv.trans
        indexedReplayNilEnv_le_ctorEnv))

theorem indexedReplayGenerationEnv :
    BlockGenerationEnv indexedTreeGeneration indexedReplayCtorEnv := by
  apply indexedTreeBlockGenerationWF.toBlockGenerationEnv
    indexedReplayInput_le_ctorEnv indexedReplayBlock_le_ctorEnv
    indexedReplayCtorEnv_ordered
  · intro family hfamily
    have hfamilies : indexedTreeGeneration.families =
        [indexedTreeGeneration.families[0],
          indexedTreeGeneration.families[1]] := rfl
    rw [hfamilies] at hfamily
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfamily
    rcases hfamily with rfl | rfl <;> rfl
  · intro constructor hconstructor
    have hconstructors : indexedTreeGeneration.flatCtors =
        [indexedTreeGeneration.flatCtors[0],
          indexedTreeGeneration.flatCtors[1],
          indexedTreeGeneration.flatCtors[2],
          indexedTreeGeneration.flatCtors[3]] := rfl
    rw [hconstructors] at hconstructor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hconstructor
    rcases hconstructor with rfl | rfl | rfl | rfl <;> rfl

theorem indexedReplayFirstRecEnv_ordered :
    indexedReplayFirstRecEnv.Ordered := by
  refine .const indexedReplayCtorEnv_ordered ?_
    indexedReplay_addFirstRec
  exact indexedReplayGenerationEnv.recursor_wf (.head _)

theorem indexedReplayCtorEnv_le_firstRecEnv :
    indexedReplayCtorEnv ≤ indexedReplayFirstRecEnv :=
  VEnv.addConst_le indexedReplay_addFirstRec

theorem indexedReplayRecEnv_ordered : indexedReplayRecEnv.Ordered := by
  refine .const indexedReplayFirstRecEnv_ordered ?_
    indexedReplay_addSecondRec
  exact (indexedReplayGenerationEnv.recursor_wf
    (.tail _ (.head _))).mono indexedReplayCtorEnv_le_firstRecEnv

theorem indexedTreeKernelInfo_tr :
    TrConstVal .safe natFinalEnv indexedTreeKernelInfo
      indexedTreeType.toVConstVal := by
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr natFinalEnv indexedTreeKernelInfo.levelParams []
      indexedTreeKernelInfo.type indexedTreeType.type := by
    tr_type_expr_tac
  exact hshape.to_trExprS natFinalEnv_ordered trivial
    (indexedTreeFamilyTypeWF indexedTreeType (.inl rfl))

theorem indexedTreeListKernelInfo_tr :
    TrConstVal .safe indexedReplayFirstTypeEnv indexedTreeListKernelInfo
      indexedTreeListType.toVConstVal := by
  have hNat : indexedReplayFirstTypeEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedReplayFirstTypeEnv
      indexedTreeListKernelInfo.levelParams [] indexedTreeListKernelInfo.type
      indexedTreeListType.type := by tr_type_expr_tac
  exact hshape.to_trExprS indexedReplayFirstTypeEnv_ordered trivial
    ((indexedTreeFamilyTypeWF indexedTreeListType (.inr rfl)).mono
      (VEnv.addConst_le indexedReplay_addFirstType))

theorem indexedTreeLeafKernelInfo_tr :
    TrConstVal .safe indexedReplayTypeEnv indexedTreeLeafKernelInfo
      indexedTreeType.ctors[0] := by
  have hNat : indexedReplayTypeEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : indexedReplayTypeEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hSucc : indexedReplayTypeEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedReplayTypeEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedReplayTypeEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedReplayTypeEnv
      indexedTreeLeafKernelInfo.levelParams [] indexedTreeLeafKernelInfo.type
      indexedTreeType.ctors[0].type := by tr_type_expr_tac
  exact hshape.to_trExprS indexedReplayTypeEnv_ordered trivial
    (indexedTreeCtorWF indexedTreeType.ctors[0]
      (.inl (by simp [indexedTreeType])))

theorem indexedTreeNodeKernelInfo_tr :
    TrConstVal .safe indexedReplayLeafEnv indexedTreeNodeKernelInfo
      indexedTreeType.ctors[1] := by
  have hNat : indexedReplayLeafEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : indexedReplayLeafEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hSucc : indexedReplayLeafEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedReplayLeafEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedReplayLeafEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedReplayLeafEnv
      indexedTreeNodeKernelInfo.levelParams [] indexedTreeNodeKernelInfo.type
      indexedTreeType.ctors[1].type := by tr_type_expr_tac
  exact hshape.to_trExprS indexedReplayLeafEnv_ordered trivial
    ((indexedTreeCtorWF indexedTreeType.ctors[1]
      (.inl (by simp [indexedTreeType]))).mono
        indexedReplayTypeEnv_le_leafEnv)

theorem indexedTreeListNilKernelInfo_tr :
    TrConstVal .safe indexedReplayNodeEnv indexedTreeListNilKernelInfo
      indexedTreeListType.ctors[0] := by
  have hNat : indexedReplayNodeEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : indexedReplayNodeEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hSucc : indexedReplayNodeEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedReplayNodeEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedReplayNodeEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedReplayNodeEnv
      indexedTreeListNilKernelInfo.levelParams []
      indexedTreeListNilKernelInfo.type indexedTreeListType.ctors[0].type := by
    tr_type_expr_tac
  exact hshape.to_trExprS indexedReplayNodeEnv_ordered trivial
    ((indexedTreeCtorWF indexedTreeListType.ctors[0]
      (.inr (by simp [indexedTreeListType]))).mono
        (indexedReplayTypeEnv_le_leafEnv.trans
          indexedReplayLeafEnv_le_nodeEnv))

theorem indexedTreeListConsKernelInfo_tr :
    TrConstVal .safe indexedReplayNilEnv indexedTreeListConsKernelInfo
      indexedTreeListType.ctors[1] := by
  have hNat : indexedReplayNilEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : indexedReplayNilEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hSucc : indexedReplayNilEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedReplayNilEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedReplayNilEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedReplayNilEnv
      indexedTreeListConsKernelInfo.levelParams []
      indexedTreeListConsKernelInfo.type indexedTreeListType.ctors[1].type := by
    tr_type_expr_tac
  exact hshape.to_trExprS indexedReplayNilEnv_ordered trivial
    ((indexedTreeCtorWF indexedTreeListType.ctors[1]
      (.inr (by simp [indexedTreeListType]))).mono
        (indexedReplayTypeEnv_le_leafEnv.trans
          (indexedReplayLeafEnv_le_nodeEnv.trans
            indexedReplayNodeEnv_le_nilEnv)))

/-! ## Exact indexed-candidate block generation -/

/-- The indexed candidate reuses the exact Nat model and readiness
certificate, transported across the fixture-specific kernel module header. -/
def indexedTreeCandidateVEnvs : VEnvs :=
  indexedVecSemanticNatVEnvs

theorem indexedTreeCandidateKernelConstants_eq :
    indexedVecKernelEnv.constants = indexedTreeKernelContext.env.constants :=
  rfl

theorem indexedTreeCandidateVEnvsWF :
    indexedTreeCandidateVEnvs.WF indexedTreeKernelContext.env where
  tr := by
    intro safety
    change TrEnv' safety natMap false natFinalEnv
    exact nat_trEnv'
  hasPrimitives := indexedVecSemanticNatHasPrimitives
  safePrimitives := by
    intro name info found primitive
    exact indexedVecSemanticNatSafePrimitives found primitive
  mono := fun _ => .rfl
  projectionReady :=
    indexedVecSemanticNatVEnvsWF.projectionReady.of_constants_eq
      indexedTreeCandidateKernelConstants_eq
  structureEtaReady :=
    indexedVecSemanticNatVEnvsWF.structureEtaReady.of_constants_eq
      indexedTreeCandidateKernelConstants_eq

theorem indexedTreeCandidateNamePrefixNe :
    indexedTreeKernelContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def indexedTreeCandidatePreContextRun :
    TypeChecker.CandidateContextRun
      { indexedTreeKernelContext with lctx := {} } :=
  TypeChecker.CandidateContextRun.root indexedTreeCandidateVEnvsWF rfl
    indexedTreeCandidateNamePrefixNe

def indexedTreeCandidatePreStage : TypeChecker.CandidateSemanticStage
    { indexedTreeKernelContext with lctx := {} } natFinalEnv [`u] where
  contextRun := indexedTreeCandidatePreContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

theorem indexedTreeKernelLevelParams :
    indexedTreeKernelInfo.levelParams = [`u] := by
  native_decide

theorem indexedTreeListKernelLevelParams :
    indexedTreeListKernelInfo.levelParams = [`u] := by
  native_decide

theorem indexedTreeLeafKernelLevelParams :
    indexedTreeLeafKernelInfo.levelParams = [`u] := by
  native_decide

theorem indexedTreeNodeKernelLevelParams :
    indexedTreeNodeKernelInfo.levelParams = [`u] := by
  native_decide

theorem indexedTreeListNilKernelLevelParams :
    indexedTreeListNilKernelInfo.levelParams = [`u] := by
  native_decide

theorem indexedTreeListConsKernelLevelParams :
    indexedTreeListConsKernelInfo.levelParams = [`u] := by
  native_decide

theorem indexedTreeCandidateValidationEnv_eq :
    indexedTreeExecution.validationContext.env =
      indexedTreeKernelContext.env := by
  exact indexedTreeExecution.validationContext_env
    indexedTreeBlockGenerationShape.producedExecution (by decide)

theorem indexedTreeFamilySourceTr :
    TrExprS natFinalEnv [`u] [] indexedTreeKernelType.type
      indexedTreeType.type := by
  simpa only [indexedTreeKernelType, indexedTreeKernelLevelParams] using
    indexedTreeKernelInfo_tr.1.2.2

theorem indexedTreeListFamilySourceTr :
    TrExprS natFinalEnv [`u] [] indexedTreeListKernelType.type
      indexedTreeListType.type := by
  have hNat : natFinalEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have shape : TrTypeExpr natFinalEnv indexedTreeListKernelInfo.levelParams []
      indexedTreeListKernelInfo.type indexedTreeListType.type := by
    tr_type_expr_tac
  rw [indexedTreeListKernelLevelParams] at shape
  simpa [indexedTreeListKernelType] using shape.to_trExprS
    natFinalEnv_ordered trivial
    (indexedTreeFamilyTypeWF indexedTreeListType (.inr rfl))

def indexedTreeCandidateFamilySources :
    CandidateBlockFamilyTypeSourceListInput natFinalEnv [`u]
      indexedTreeKernelTypes indexedTreeDecl.types :=
  .cons {
      name_eq := rfl
      uvars_eq := rfl
      source_tr := indexedTreeFamilySourceTr }
    (.cons {
      name_eq := rfl
      uvars_eq := rfl
      source_tr := indexedTreeListFamilySourceTr } .nil)

theorem indexedTreeCandidateBlockEnvOrdered :
    indexedTreeBlockEnv.Ordered :=
  indexedReplayTypeEnv_ordered

theorem indexedTreeLeafSourceTr :
    TrExprS indexedTreeBlockEnv [`u] []
      indexedTreeKernelType.ctors[0].type
      indexedTreeType.ctors[0].type := by
  rw [show indexedTreeBlockEnv = indexedReplayTypeEnv by rfl]
  simpa [indexedTreeKernelType, indexedTreeLeafKernelLevelParams] using
    indexedTreeLeafKernelInfo_tr.1.2.2

theorem indexedTreeNodeSourceTr :
    TrExprS indexedTreeBlockEnv [`u] []
      indexedTreeKernelType.ctors[1].type
      indexedTreeType.ctors[1].type := by
  have hNat : indexedTreeBlockEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : indexedTreeBlockEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hSucc : indexedTreeBlockEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedTreeBlockEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedTreeBlockEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  have shape : TrTypeExpr indexedTreeBlockEnv
      indexedTreeNodeKernelInfo.levelParams [] indexedTreeNodeKernelInfo.type
      indexedTreeType.ctors[1].type := by
    tr_type_expr_tac
  rw [indexedTreeNodeKernelLevelParams] at shape
  simpa [indexedTreeKernelType] using shape.to_trExprS
    indexedTreeCandidateBlockEnvOrdered trivial
    (indexedTreeCtorWF indexedTreeType.ctors[1]
      (.inl (by simp [indexedTreeType])))

theorem indexedTreeListNilSourceTr :
    TrExprS indexedTreeBlockEnv [`u] []
      indexedTreeListKernelType.ctors[0].type
      indexedTreeListType.ctors[0].type := by
  have hNat : indexedTreeBlockEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : indexedTreeBlockEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hSucc : indexedTreeBlockEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedTreeBlockEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedTreeBlockEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  have shape : TrTypeExpr indexedTreeBlockEnv
      indexedTreeListNilKernelInfo.levelParams []
      indexedTreeListNilKernelInfo.type indexedTreeListType.ctors[0].type := by
    tr_type_expr_tac
  rw [indexedTreeListNilKernelLevelParams] at shape
  simpa [indexedTreeListKernelType] using shape.to_trExprS
    indexedTreeCandidateBlockEnvOrdered trivial
    (indexedTreeCtorWF indexedTreeListType.ctors[0]
      (.inr (by simp [indexedTreeListType])))

theorem indexedTreeListConsSourceTr :
    TrExprS indexedTreeBlockEnv [`u] []
      indexedTreeListKernelType.ctors[1].type
      indexedTreeListType.ctors[1].type := by
  have hNat : indexedTreeBlockEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : indexedTreeBlockEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hSucc : indexedTreeBlockEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedTreeBlockEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedTreeBlockEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  have shape : TrTypeExpr indexedTreeBlockEnv
      indexedTreeListConsKernelInfo.levelParams []
      indexedTreeListConsKernelInfo.type indexedTreeListType.ctors[1].type := by
    tr_type_expr_tac
  rw [indexedTreeListConsKernelLevelParams] at shape
  simpa [indexedTreeListKernelType] using shape.to_trExprS
    indexedTreeCandidateBlockEnvOrdered trivial
    (indexedTreeCtorWF indexedTreeListType.ctors[1]
      (.inr (by simp [indexedTreeListType])))

def indexedTreeCandidateFamilyTypes :
    CandidateBlockFamilyTypeStagedListInput indexedTreeCandidatePreStage
      indexedTreeExecution.candidate.families indexedTreeDecl.types :=
  indexedTreeCandidateFamilySources.staged
    indexedTreeExecution.candidate.families (by
      change CandidateFamilyTypeListProduced _
        indexedTreeExecution.families.candidates.familyTypes
      rw [indexedTreeExecution.families.produced.familyTypes_eq]
      exact indexedTreeExecution.familyTypes.produced) 9999 rfl

theorem indexedTreeCandidateTerminals :
    CandidateBlockFamilyTerminalSortList
      indexedTreeExecution.candidate.families :=
  CandidateBlockFamilyTerminalSortList.of_check
    indexedTreeExecution.candidate.families (by native_decide)

theorem indexedTreeCandidateDeclaredInfosMulti :
    ∀ info ∈ indexedTreeExecution.declaredInfos,
      info.ctors.length ≠ 1 := by
  native_decide

theorem indexedTreeCandidateNindicesSize :
    indexedTreeExecution.stats.nindices.size =
      indexedTreeKernelTypes.length := by
  have sizes := indexedTreeExecution.familyValidationResult.sizes_of_run
    (by decide) indexedTreeExecution_familyValidationResult_run
  simpa only [AddInductive.NormalizationCandidateExecution.familyValidationResult]
    using sizes.2.1

/-- The exact family declaration trace transports the Nat-backed projection
and eta certificate across both multi-constructor indexed families. -/
theorem indexedTreeCandidatePostReadiness :
    ProjectionReady indexedTreeExecution.familyEnv indexedTreeBlockEnv ∧
      StructureEtaReady indexedTreeExecution.familyEnv
        indexedTreeBlockEnv := by
  have metadata : List.Forall₂
      (fun indType info => ∃ numIndices,
        info = AddInductive.declaredInductiveInfo indexedTreeExecution.stats
          indexedTreeDecl.nparams indexedTreeKernelTypes.toArray indType
            numIndices 0 false indexedTreeExecution.validationContext)
      indexedTreeKernelTypes indexedTreeExecution.declaredInfos := by
    simpa only [AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray] using
      AddInductive.declaredInductiveInfos_matches indexedTreeExecution.stats
        indexedTreeDecl.nparams indexedTreeKernelTypes.toArray 0 false
        indexedTreeExecution.validationContext
        indexedTreeCandidateNindicesSize
  have evidenceFull := indexedTreeCandidateFamilyTypes.declarationEvidence
    metadata indexedTreeCandidateTerminals (show false = false from rfl)
      (by native_decide)
  have evidence : List.Forall₂
      (fun _ raw => raw.toVConstant.WF natFinalEnv)
      indexedTreeExecution.declaredInfos indexedTreeDecl.types :=
    Lean4Lean.List.Forall₂.imp (h := evidenceFull) fun _ _ h => h.2
  apply declarationTraceMultiConstructorReadiness
    indexedTreeExecution.declareTrace indexedTreeStage evidence
    indexedTreeCandidateDeclaredInfosMulti
  · rw [indexedTreeCandidateValidationEnv_eq]
    exact natMap_wf
  · exact natFinalEnv_ordered
  · rw [indexedTreeCandidateValidationEnv_eq]
    simpa [indexedTreeCandidateVEnvs,
      indexedVecSemanticNatVEnvs] using
      indexedTreeCandidateVEnvsWF.projectionReady (safety := .safe)
  · rw [indexedTreeCandidateValidationEnv_eq]
    simpa [indexedTreeCandidateVEnvs,
      indexedVecSemanticNatVEnvs] using
      indexedTreeCandidateVEnvsWF.structureEtaReady (safety := .safe)

/-- Exact shared family stage derived from the indexed mutual candidate and
its retained family-only declaration trace. -/
def indexedTreeCandidateStaging : NormalizationCandidateBlockStagingInput
    indexedTreeKernelContext indexedTreeExecution natFinalEnv
      indexedTreeBlockEnv [`u] indexedTreeDecl where
  uvars_eq := rfl
  preFamily := indexedTreeCandidatePreStage
  familyTypes := indexedTreeCandidateFamilyTypes
  terminals := indexedTreeCandidateTerminals
  stage := indexedTreeStage
  nindices_size := indexedTreeCandidateNindicesSize
  validation_env_eq := indexedTreeCandidateValidationEnv_eq
  validation_lparams_eq := by native_decide
  context_safety_eq := rfl
  isUnsafe_eq := rfl
  preMapWF := natMap_wf
  names_not_primitive := by
    intro raw member
    simp [indexedTreeDecl] at member
    rcases member with rfl | rfl
    · constructor
      · simp [indexedTreeType, VEnv.reflectedPrimitiveNames]
      · simp [indexedTreeType, Kernel.Environment.primitives,
          NameSet.ofList, NameSet.contains]
    · constructor
      · simp [indexedTreeListType, VEnv.reflectedPrimitiveNames]
      · simp [indexedTreeListType, Kernel.Environment.primitives,
          NameSet.ofList, NameSet.contains]
  projectionReady := indexedTreeCandidatePostReadiness.1
  structureEtaReady := indexedTreeCandidatePostReadiness.2

def indexedTreeCandidateConstructorSources :
    CandidateBlockConstructorSourceListInput indexedTreeBlockEnv [`u]
      indexedTreeKernelTypes indexedTreeDecl.types :=
  .cons
    (.cons {
        name_eq := rfl
        uvars_eq := rfl
        source_tr := indexedTreeLeafSourceTr }
      (.cons {
          name_eq := rfl
          uvars_eq := rfl
          source_tr := indexedTreeNodeSourceTr }
        .nil))
    (.cons
      (.cons {
          name_eq := rfl
          uvars_eq := rfl
          source_tr := indexedTreeListNilSourceTr }
        (.cons {
            name_eq := rfl
            uvars_eq := rfl
            source_tr := indexedTreeListConsSourceTr }
          .nil))
      .nil)

def indexedTreeCandidateConstructors :
    CandidateBlockConstructorStagedListInput
      indexedTreeCandidateStaging.postFamily
      indexedTreeExecution.candidate.families indexedTreeDecl.types :=
  indexedTreeCandidateConstructorSources.staged
    indexedTreeExecution.candidate.families
    indexedTreeExecution.families.produced.constructorLists 9999 rfl

/-- Complete pre/post-family staged owner for the indexed mutual candidate. -/
def indexedTreeStagedCandidateSemantic :
    StagedNormalizationCandidateBlockSemanticInput
      indexedTreeCandidateStaging where
  postFamily := indexedTreeCandidateStaging.postFamily
  constructors := indexedTreeCandidateConstructors

/-- Identity-specialized interpretation of the exact indexed candidate
hierarchy. -/
def indexedTreeCandidateIdentitySemantic :
    NormalizationCandidateBlockSemanticRun natFinalEnv indexedTreeBlockEnv
      [`u] indexedTreeExecution.candidate indexedTreeDecl :=
  indexedTreeStagedCandidateSemantic.semanticRunOfIdentity (by native_decide)

theorem indexedTreeCandidateIdentityNormalization :
    indexedTreeCandidateIdentitySemantic.normalization =
      Normalization.identity indexedTreeDecl := by
  simpa only [indexedTreeCandidateIdentitySemantic] using
    indexedTreeStagedCandidateSemantic.semanticRunOfIdentity_normalization
      (by native_decide)

theorem indexedTreeCandidateIdentityAnalysis :
    indexedTreeCandidateIdentitySemantic.normalization.checkBlock? =
      some indexedTreeGeneration.block := by
  rw [indexedTreeCandidateIdentityNormalization]
  rfl

def indexedTreeProducedCandidateIdentitySemantic :
    ProducedNormalizationCandidateBlockSemanticRun
      { indexedTreeKernelContext with lctx := {} }
      { indexedTreeKernelContext with
        env := indexedTreeExecution.familyEnv, lctx := {} }
      natFinalEnv indexedTreeBlockEnv [`u] indexedTreeExecution.candidate
        indexedTreeDecl where
  semantic := indexedTreeCandidateIdentitySemantic
  familyTypesProduced := by
    change CandidateFamilyTypeListProduced _
      indexedTreeExecution.families.candidates.familyTypes
    rw [indexedTreeExecution.families.produced.familyTypes_eq]
    exact indexedTreeExecution.familyTypes.produced
  familiesProduced := indexedTreeExecution.families.produced.reindex

/-- Exact dependent closure from the indexed kernel-facing producer through
the generic block-generation assembler. -/
def indexedTreeExactProducedBlockGeneration :
    ExactProducedBlockGenerationRun natFinalEnv indexedTreeBlockEnv [`u]
      indexedTreeBlockGenerationShape indexedTreeGeneration where
  producedSemantic := indexedTreeProducedCandidateIdentitySemantic
  analysis := indexedTreeCandidateIdentityAnalysis
  checked := indexedTreeCheckedBlockWF
  resultLevelWF := by decide

/-- Indexed exact semantic generation paired with its retained ordinary
post-constructor elimination decisions. -/
def indexedTreeExactProducedBlockElimination :
    ExactProducedBlockEliminationRun natFinalEnv indexedTreeBlockEnv [`u]
      indexedTreeBlockEliminationShape indexedTreeGeneration where
  block := by
    rw [indexedTreeBlockEliminationBase_eq]
    exact indexedTreeExactProducedBlockGeneration
  elimination := indexedTreeBlockEliminationAlignment
  isUnsafe_eq := rfl
  validation_lparams_eq := by
    change indexedTreeEliminationExecution.normalization.validationContext.lparams =
      [`u]
    rw [indexedTreeEliminationNormalization_eq]
    exact indexedTreeCandidateStaging.validation_lparams_eq

def indexedTreeExactProducedBlockRecursor : ExactProducedBlockRecursorRun
    natFinalEnv indexedTreeBlockEnv [`u] indexedTreeBlockRecursorShape
      indexedTreeGeneration where
  elimination := by
    rw [indexedTreeBlockRecursorEliminationBase_eq]
    exact indexedTreeExactProducedBlockElimination

/-- Indexed staging input reindexed onto the retained elimination execution. -/
def indexedTreeExactEliminationStaging :
    NormalizationCandidateBlockStagingInput indexedTreeKernelContext
      indexedTreeEliminationExecution.normalization natFinalEnv
      indexedTreeBlockEnv [`u] indexedTreeDecl := by
  rw [indexedTreeEliminationNormalization_eq]
  exact indexedTreeCandidateStaging

def indexedTreeExactRecursorStaging :
    NormalizationCandidateBlockStagingInput indexedTreeKernelContext
      indexedTreeBlockRecursorShape.execution.eliminationExecution.normalization
      natFinalEnv indexedTreeBlockEnv [`u] indexedTreeDecl := by
  change NormalizationCandidateBlockStagingInput indexedTreeKernelContext
    indexedTreeRecursorExecution.eliminationExecution.normalization
      natFinalEnv indexedTreeBlockEnv [`u] indexedTreeDecl
  rw [indexedTreeRecursorElimination_eq]
  exact indexedTreeExactEliminationStaging

/-- Exact indexed owner of the family and constructor declaration prefix. -/
noncomputable def indexedTreeExactDeclarationRun :
    ExactProducedBlockDeclarationRun
      indexedTreeExactProducedBlockElimination :=
  indexedTreeExactProducedBlockElimination.declarationRun
    indexedTreeExactEliminationStaging

noncomputable def indexedTreeExactRecursorDeclarationRun :=
  indexedTreeExactProducedBlockRecursor.elimination.declarationRun
    indexedTreeExactRecursorStaging

/-- Exact indexed family declaration paired with its Theory staging fold. -/
noncomputable def indexedTreeExactFamilyDeclaration :
    FamilyDeclarationStagingRun
      indexedTreeExecution.validationContext.allowPrimitive
      indexedTreeExecution.validationContext.env indexedTreeExecution.familyEnv
      indexedTreeExecution.declaredInfos natFinalEnv indexedTreeBlockEnv
      indexedTreeDecl.blockTypeConstants
      indexedTreeExecution.validationContext.env.quotInit := by
  rw [← indexedTreeEliminationNormalization_eq]
  exact indexedTreeExactDeclarationRun.families

theorem indexedTreeExactFamilyDeclaration_fold :
    indexedTreeDecl.blockTypeConstants.foldlM
      (fun env family => env.addConst family.name family.toVConstant)
      natFinalEnv = some indexedTreeBlockEnv :=
  indexedTreeExactFamilyDeclaration.addTypes.to_foldlM

/-- Indexed counterpart of the exact constructor declaration interpreter;
all four raw constructors and their source order come from the retained
ordinary execution. -/
noncomputable def indexedTreeExactConstructorDeclaration :
    ConstructorDeclarationStagingRun
      indexedTreeEliminationExecution.constructorContext.allowPrimitive
      indexedTreeEliminationExecution.normalization.familyEnv
      indexedTreeEliminationExecution.constructorEnv
      indexedTreeEliminationExecution.declaredConstructorInfos
      indexedTreeBlockEnv indexedTreeDecl.blockConstructorConstants
      indexedTreeEliminationExecution.normalization.validationContext.env.quotInit :=
  indexedTreeExactDeclarationRun.constructors

theorem indexedTreeExactConstructorDeclaration_fold :
    indexedTreeDecl.blockConstructorConstants.foldlM
      (fun env constructor =>
        env.addConst constructor.name constructor.toVConstant)
      indexedTreeBlockEnv =
        some indexedTreeExactConstructorDeclaration.ctorEnv :=
  indexedTreeExactConstructorDeclaration.addCtors.to_foldlM

theorem indexedTreeExactRecursorConstructorEnv_eq :
    (indexedTreeExactProducedBlockRecursor.elimination.declarationRun
      indexedTreeExactRecursorStaging).constructors.ctorEnv =
        indexedReplayCtorEnv := by
  have replay : indexedTreeDecl.blockConstructorConstants.foldlM
      (fun env constructor =>
        env.addConst constructor.name constructor.toVConstant)
      indexedTreeBlockEnv = some indexedReplayCtorEnv := by rfl
  rw [(indexedTreeExactProducedBlockRecursor.elimination.declarationRun
    indexedTreeExactRecursorStaging).constructors.addCtors.to_foldlM] at replay
  exact Option.some.inj replay

/-- The indexed mutual block's generation certificate is reconstructed from
the retained normalization execution, with no fixture-selected inventories. -/
theorem indexedTreeBlockGenerationWF_fromCandidate :
    indexedTreeGeneration.WF natFinalEnv indexedTreeBlockEnv :=
  indexedTreeExactProducedBlockGeneration.blockGenerationRun.wf

theorem indexedTreeRecKernelInfo_tr :
    TrConstVal .safe indexedReplayCtorEnv indexedTreeRecKernelInfo
      indexedTreeGeneration.recursors[0] := by
  have hNat : indexedReplayCtorEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : indexedReplayCtorEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hSucc : indexedReplayCtorEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedReplayCtorEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedReplayCtorEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  have hLeaf : indexedReplayCtorEnv.constants ``IndexedTree.leaf =
      some indexedTreeType.ctors[0].toVConstant := rfl
  have hNode : indexedReplayCtorEnv.constants ``IndexedTree.node =
      some indexedTreeType.ctors[1].toVConstant := rfl
  have hNil : indexedReplayCtorEnv.constants ``IndexedTreeList.nil =
      some indexedTreeListType.ctors[0].toVConstant := rfl
  have hCons : indexedReplayCtorEnv.constants ``IndexedTreeList.cons =
      some indexedTreeListType.ctors[1].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedReplayCtorEnv
      indexedTreeRecKernelInfo.levelParams [] indexedTreeRecKernelInfo.type
      indexedTreeGeneration.recursors[0].type := by tr_type_expr_tac
  obtain ⟨u, hrec⟩ := indexedReplayGenerationEnv.recursor_wf (.head _)
  exact hshape.to_trExprS indexedReplayCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

theorem indexedTreeListRecKernelInfo_tr_atCtor :
    TrConstVal .safe indexedReplayCtorEnv indexedTreeListRecKernelInfo
      indexedTreeGeneration.recursors[1] := by
  have hNat : indexedReplayCtorEnv.constants ``Nat =
      some InductiveFixtures.natType.toVConstant := rfl
  have hZero : indexedReplayCtorEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := rfl
  have hSucc : indexedReplayCtorEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant := rfl
  have hTree : indexedReplayCtorEnv.constants ``IndexedTree =
      some indexedTreeType.toVConstant := rfl
  have hTreeList : indexedReplayCtorEnv.constants ``IndexedTreeList =
      some indexedTreeListType.toVConstant := rfl
  have hLeaf : indexedReplayCtorEnv.constants ``IndexedTree.leaf =
      some indexedTreeType.ctors[0].toVConstant := rfl
  have hNode : indexedReplayCtorEnv.constants ``IndexedTree.node =
      some indexedTreeType.ctors[1].toVConstant := rfl
  have hNil : indexedReplayCtorEnv.constants ``IndexedTreeList.nil =
      some indexedTreeListType.ctors[0].toVConstant := rfl
  have hCons : indexedReplayCtorEnv.constants ``IndexedTreeList.cons =
      some indexedTreeListType.ctors[1].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedReplayCtorEnv
      indexedTreeListRecKernelInfo.levelParams []
      indexedTreeListRecKernelInfo.type
      indexedTreeGeneration.recursors[1].type := by tr_type_expr_tac
  obtain ⟨u, hrec⟩ := indexedReplayGenerationEnv.recursor_wf
    (.tail _ (.head _))
  exact hshape.to_trExprS indexedReplayCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

theorem indexedTreeListRecKernelInfo_tr :
    TrConstVal .safe indexedReplayFirstRecEnv indexedTreeListRecKernelInfo
      indexedTreeGeneration.recursors[1] :=
  indexedTreeListRecKernelInfo_tr_atCtor.mono
    indexedReplayCtorEnv_le_firstRecEnv

theorem indexedTreeExpectedRecursorEvidence : List.Forall₂
    (fun info raw =>
      TrConstVal .safe indexedReplayCtorEnv (.recInfo info) raw)
    indexedTreeExpectedRecursorInfos indexedTreeGeneration.recursors := by
  have hrecs : indexedTreeGeneration.recursors =
      [indexedTreeGeneration.recursors[0],
        indexedTreeGeneration.recursors[1]] := rfl
  rw [hrecs]
  exact .cons
    (by
      simpa [indexedTreeExpectedRecursorInfos,
        indexedTreeRecKernelInfo, kernelRecursorInfo?] using
          indexedTreeRecKernelInfo_tr)
    (.cons
      (by
        simpa [indexedTreeExpectedRecursorInfos,
          indexedTreeListRecKernelInfo, kernelRecursorInfo?] using
            indexedTreeListRecKernelInfo_tr_atCtor)
      .nil)

theorem indexedTreeGeneratedRecursorEvidence : List.Forall₂
    (fun info raw => TrConstVal .safe
      (indexedTreeExactProducedBlockRecursor.elimination.declarationRun
        indexedTreeExactRecursorStaging).constructors.ctorEnv
      (.recInfo info) raw)
    indexedTreeBlockRecursorShape.execution.recursors.infos
      indexedTreeGeneration.recursors := by
  rw [indexedTreeExactRecursorConstructorEnv_eq]
  apply recursorInfoTranslationList_of_option_beq
    (expected := indexedTreeExpectedRecursorInfos)
  · simpa [indexedTreeRecursorExecution,
      indexedTreeExpectedRecursorInfos, indexedTreeRecKernelInfo,
      indexedTreeListRecKernelInfo, kernelRecursorInfo?] using
        indexedTreeGeneratedRecursorInfos_match
  · exact indexedTreeExpectedRecursorEvidence

theorem indexedTreeGeneratedRecursorsWF :
    ∀ raw ∈ indexedTreeGeneration.recursors,
      raw.toVConstant.WF
        (indexedTreeExactProducedBlockRecursor.elimination.declarationRun
          indexedTreeExactRecursorStaging).constructors.ctorEnv := by
  intro raw member
  rw [indexedTreeExactRecursorConstructorEnv_eq]
  simp only [BlockGenerationChecked.recursors, List.mem_map] at member
  obtain ⟨family, hfamily, rfl⟩ := member
  exact indexedReplayGenerationEnv.recursor_wf hfamily

noncomputable def indexedTreeExactMetadataPrefixRun :
    ExactProducedBlockMetadataPrefixRun
      indexedTreeExactProducedBlockRecursor :=
  indexedTreeExactProducedBlockRecursor.metadataPrefix
    indexedTreeExactRecursorStaging indexedTreeGeneratedRecursorEvidence
      indexedTreeGeneratedRecursorsWF

def indexedReplayFirstTypeMap : ConstMap :=
  natMap.insert ``IndexedTree indexedTreeKernelInfo

def indexedReplayTypeMap : ConstMap :=
  indexedReplayFirstTypeMap.insert ``IndexedTreeList
    indexedTreeListKernelInfo

def indexedReplayLeafMap : ConstMap :=
  indexedReplayTypeMap.insert ``IndexedTree.leaf indexedTreeLeafKernelInfo

def indexedReplayNodeMap : ConstMap :=
  indexedReplayLeafMap.insert ``IndexedTree.node indexedTreeNodeKernelInfo

def indexedReplayNilMap : ConstMap :=
  indexedReplayNodeMap.insert ``IndexedTreeList.nil
    indexedTreeListNilKernelInfo

def indexedReplayCtorMap : ConstMap :=
  indexedReplayNilMap.insert ``IndexedTreeList.cons
    indexedTreeListConsKernelInfo

def indexedReplayFirstRecMap : ConstMap :=
  indexedReplayCtorMap.insert ``IndexedTree.rec indexedTreeRecKernelInfo

def indexedReplayMap : ConstMap :=
  indexedReplayFirstRecMap.insert ``IndexedTreeList.rec
    indexedTreeListRecKernelInfo

theorem indexedReplayFirstType_fresh :
    natMap.find? ``IndexedTree = none := by
  rw [natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedReplayFirstTypeMap_wf : indexedReplayFirstTypeMap.WF :=
  nat_aligned.map_wf.insert _ _ indexedReplayFirstType_fresh

theorem indexedReplaySecondType_fresh :
    indexedReplayFirstTypeMap.find? ``IndexedTreeList = none := by
  rw [indexedReplayFirstTypeMap, nat_aligned.map_wf.find?_insert,
    natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedReplayTypeMap_wf : indexedReplayTypeMap.WF :=
  indexedReplayFirstTypeMap_wf.insert _ _ indexedReplaySecondType_fresh

theorem indexedReplayLeaf_fresh :
    indexedReplayTypeMap.find? ``IndexedTree.leaf = none := by
  rw [indexedReplayTypeMap, indexedReplayFirstTypeMap_wf.find?_insert,
    indexedReplayFirstTypeMap, nat_aligned.map_wf.find?_insert,
    natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedReplayLeafMap_wf : indexedReplayLeafMap.WF :=
  indexedReplayTypeMap_wf.insert _ _ indexedReplayLeaf_fresh

theorem indexedReplayNode_fresh :
    indexedReplayLeafMap.find? ``IndexedTree.node = none := by
  rw [indexedReplayLeafMap, indexedReplayTypeMap_wf.find?_insert,
    indexedReplayTypeMap, indexedReplayFirstTypeMap_wf.find?_insert,
    indexedReplayFirstTypeMap, nat_aligned.map_wf.find?_insert,
    natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedReplayNodeMap_wf : indexedReplayNodeMap.WF :=
  indexedReplayLeafMap_wf.insert _ _ indexedReplayNode_fresh

theorem indexedReplayNil_fresh :
    indexedReplayNodeMap.find? ``IndexedTreeList.nil = none := by
  rw [indexedReplayNodeMap, indexedReplayLeafMap_wf.find?_insert,
    indexedReplayLeafMap, indexedReplayTypeMap_wf.find?_insert,
    indexedReplayTypeMap, indexedReplayFirstTypeMap_wf.find?_insert,
    indexedReplayFirstTypeMap, nat_aligned.map_wf.find?_insert,
    natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedReplayNilMap_wf : indexedReplayNilMap.WF :=
  indexedReplayNodeMap_wf.insert _ _ indexedReplayNil_fresh

theorem indexedReplayCons_fresh :
    indexedReplayNilMap.find? ``IndexedTreeList.cons = none := by
  rw [indexedReplayNilMap, indexedReplayNodeMap_wf.find?_insert,
    indexedReplayNodeMap, indexedReplayLeafMap_wf.find?_insert,
    indexedReplayLeafMap, indexedReplayTypeMap_wf.find?_insert,
    indexedReplayTypeMap, indexedReplayFirstTypeMap_wf.find?_insert,
    indexedReplayFirstTypeMap, nat_aligned.map_wf.find?_insert,
    natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedReplayCtorMap_wf : indexedReplayCtorMap.WF :=
  indexedReplayNilMap_wf.insert _ _ indexedReplayCons_fresh

theorem indexedReplayFirstRec_fresh :
    indexedReplayCtorMap.find? ``IndexedTree.rec = none := by
  rw [indexedReplayCtorMap, indexedReplayNilMap_wf.find?_insert,
    indexedReplayNilMap, indexedReplayNodeMap_wf.find?_insert,
    indexedReplayNodeMap, indexedReplayLeafMap_wf.find?_insert,
    indexedReplayLeafMap, indexedReplayTypeMap_wf.find?_insert,
    indexedReplayTypeMap, indexedReplayFirstTypeMap_wf.find?_insert,
    indexedReplayFirstTypeMap, nat_aligned.map_wf.find?_insert,
    natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedReplayFirstRecMap_wf : indexedReplayFirstRecMap.WF :=
  indexedReplayCtorMap_wf.insert _ _ indexedReplayFirstRec_fresh

theorem indexedReplaySecondRec_fresh :
    indexedReplayFirstRecMap.find? ``IndexedTreeList.rec = none := by
  rw [indexedReplayFirstRecMap, indexedReplayCtorMap_wf.find?_insert,
    indexedReplayCtorMap, indexedReplayNilMap_wf.find?_insert,
    indexedReplayNilMap, indexedReplayNodeMap_wf.find?_insert,
    indexedReplayNodeMap, indexedReplayLeafMap_wf.find?_insert,
    indexedReplayLeafMap, indexedReplayTypeMap_wf.find?_insert,
    indexedReplayTypeMap, indexedReplayFirstTypeMap_wf.find?_insert,
    indexedReplayFirstTypeMap, nat_aligned.map_wf.find?_insert,
    natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedReplayMap_wf : indexedReplayMap.WF :=
  indexedReplayFirstRecMap_wf.insert _ _ indexedReplaySecondRec_fresh

theorem indexedReplay_treeRec_lookup :
    indexedReplayMap.find? ``IndexedTree.rec =
      some indexedTreeRecKernelInfo := by
  rw [indexedReplayMap, indexedReplayFirstRecMap_wf.find?_insert,
    indexedReplayFirstRecMap, indexedReplayCtorMap_wf.find?_insert]
  rfl

theorem indexedReplay_treeListRec_lookup :
    indexedReplayMap.find? ``IndexedTreeList.rec =
      some indexedTreeListRecKernelInfo := by
  rw [indexedReplayMap, indexedReplayFirstRecMap_wf.find?_insert]
  rfl

def indexedTreeAddInductBlockTrace :
    AddInductBlockTrace natMap natFinalEnv indexedTreeDecl
      indexedReplayMap indexedTreeFinalEnv where
  generation := indexedTreeGeneration
  blockEnv := indexedTreeBlockEnv
  generation_wf := indexedTreeBlockGenerationWF
  typeMap := indexedReplayTypeMap
  typeEnv := indexedReplayTypeEnv
  ctorMap := indexedReplayCtorMap
  ctorEnv := indexedReplayCtorEnv
  recEnv := indexedReplayRecEnv
  addTypes := .cons {
      info := indexedTreeKernelInfo
      kind_eq := by simp [indexedTreeKernelInfo,
        InductConstantKind.Matches]
      tr := indexedTreeKernelInfo_tr
      map_fresh := indexedReplayFirstType_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := indexedTreeListKernelInfo
      kind_eq := by simp [indexedTreeListKernelInfo,
        InductConstantKind.Matches]
      tr := indexedTreeListKernelInfo_tr
      map_fresh := indexedReplaySecondType_fresh
      env_add := rfl
      map_add := rfl } .nil)
  addCtors := .cons {
      info := indexedTreeLeafKernelInfo
      kind_eq := by simp [indexedTreeLeafKernelInfo,
        InductConstantKind.Matches]
      tr := indexedTreeLeafKernelInfo_tr
      map_fresh := indexedReplayLeaf_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := indexedTreeNodeKernelInfo
      kind_eq := by simp [indexedTreeNodeKernelInfo,
        InductConstantKind.Matches]
      tr := indexedTreeNodeKernelInfo_tr
      map_fresh := indexedReplayNode_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := indexedTreeListNilKernelInfo
      kind_eq := by simp [indexedTreeListNilKernelInfo,
        InductConstantKind.Matches]
      tr := indexedTreeListNilKernelInfo_tr
      map_fresh := indexedReplayNil_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := indexedTreeListConsKernelInfo
      kind_eq := by simp [indexedTreeListConsKernelInfo,
        InductConstantKind.Matches]
      tr := indexedTreeListConsKernelInfo_tr
      map_fresh := indexedReplayCons_fresh
      env_add := rfl
      map_add := rfl } .nil)))
  addRecs := .cons {
      info := indexedTreeRecKernelInfo
      kind_eq := by simp [indexedTreeRecKernelInfo,
        InductConstantKind.Matches]
      tr := indexedTreeRecKernelInfo_tr
      map_fresh := indexedReplayFirstRec_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := indexedTreeListRecKernelInfo
      kind_eq := by simp [indexedTreeListRecKernelInfo,
        InductConstantKind.Matches]
      tr := indexedTreeListRecKernelInfo_tr
      map_fresh := indexedReplaySecondRec_fresh
      env_add := rfl
      map_add := rfl } .nil)
  recK := by
    intro recursor hrecursor
    have hrecs : indexedTreeGeneration.recursors =
        [indexedTreeGeneration.recursors[0],
          indexedTreeGeneration.recursors[1]] := rfl
    rw [hrecs] at hrecursor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrecursor
    rcases hrecursor with rfl | rfl
    · exact ⟨indexedTreeRecKernelInfo,
        indexedReplay_treeRec_lookup, by decide⟩
    · exact ⟨indexedTreeListRecKernelInfo,
        indexedReplay_treeListRec_lookup, by decide⟩
  addRules := ⟨rfl⟩

theorem indexedTreeAddInductBlock :
    AddInductBlock natMap natFinalEnv indexedTreeDecl
      indexedReplayMap indexedTreeFinalEnv :=
  ⟨indexedTreeAddInductBlockTrace⟩

/-- The indexed producer-constructed recursor fold agrees with the independent
raw Theory replay endpoint. -/
theorem indexedTreeExactProducedRecEnv_eq :
    indexedTreeExactMetadataPrefixRun.recursors.recEnv =
      indexedReplayRecEnv := by
  have ctorEnvEq :
      indexedTreeExactMetadataPrefixRun.declarations.constructors.ctorEnv =
        indexedReplayCtorEnv := by
    change (indexedTreeExactProducedBlockRecursor.elimination.declarationRun
      indexedTreeExactRecursorStaging).constructors.ctorEnv =
        indexedReplayCtorEnv
    exact indexedTreeExactRecursorConstructorEnv_eq
  have exactFold :=
    indexedTreeExactMetadataPrefixRun.recursors.addRecs.to_foldlM
  have replayFold : indexedTreeGeneration.recursors.foldlM
      (fun env recursor => env.addConst recursor.name recursor.toVConstant)
      indexedReplayCtorEnv = some indexedReplayRecEnv := by rfl
  have folds := congrArg
    (fun start => indexedTreeGeneration.recursors.foldlM
      (fun env recursor => env.addConst recursor.name recursor.toVConstant)
      start) ctorEnvEq
  rw [exactFold, replayFold] at folds
  exact Option.some.inj folds

/-- Indexed exact transaction through the actual synthesized kernel map. -/
noncomputable def indexedTreeExactProducedBlockMetadataTrace :
    AddInductBlockTrace
      indexedTreeRecursorExecution.eliminationExecution.normalization.validationContext.env.constants
      natFinalEnv indexedTreeDecl
      indexedTreeRecursorExecution.recursors.env.constants
      indexedTreeFinalEnv :=
  indexedTreeExactMetadataPrefixRun.addInductBlockTrace
    (env₂ := indexedTreeFinalEnv) ⟨by
      rw [indexedTreeExactProducedRecEnv_eq]
      rfl⟩

theorem indexedTreeExactProducedBlockMetadata :
    AddInductBlock
      indexedTreeRecursorExecution.eliminationExecution.normalization.validationContext.env.constants
      natFinalEnv indexedTreeDecl
      indexedTreeRecursorExecution.recursors.env.constants
      indexedTreeFinalEnv :=
  ⟨indexedTreeExactProducedBlockMetadataTrace⟩

theorem indexedTree_trEnv' :
    TrEnv' .safe indexedReplayMap false indexedTreeFinalEnv :=
  .inductBlock indexedTreeAddInductBlock nat_trEnv'

theorem indexedTree_verify_env_wf : indexedTreeFinalEnv.WF :=
  indexedTree_trEnv'.wf

theorem indexedTree_verify_aligned :
    Aligned .safe indexedReplayMap indexedTreeFinalEnv :=
  indexedTree_trEnv'.aligned



/-! ## Trust-boundary manifests -/

/- The semantic generation and raw public transaction remain inside the
accepted Theory trust baseline. -/
/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.treeBlockGenerationWF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeBlockGenerationWF

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.indexedTreeBlockGenerationWF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms indexedTreeBlockGenerationWF

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.treeFinalEnv_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeFinalEnv_ordered

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.indexedTreeFinalEnv_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms indexedTreeFinalEnv_ordered

/- The implementation metadata replay is now `sorryAx`-free and inherits only
the already classified persistent-map contracts; fixture-local native-decision
axioms are deliberately absent. -/
/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.treeAddInductBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms treeAddInductBlock

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.indexedTreeAddInductBlock' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedTreeAddInductBlock

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.tree_verify_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms tree_verify_aligned

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.indexedTree_verify_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedTree_verify_aligned

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.treeCheckedBlockWF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms treeCheckedBlockWF

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.indexedTreeCheckedBlockWF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms indexedTreeCheckedBlockWF

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.treeNormalizationBlockWF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeNormalizationBlockWF

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.indexedTreeNormalizationBlockWF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms indexedTreeNormalizationBlockWF

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.treeValidationCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms treeValidationCertificate

/--
info: 'Lean4Lean.MutualInductiveReplayFixtures.indexedTreeValidationCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms indexedTreeValidationCertificate

end Lean4Lean.MutualInductiveReplayFixtures
