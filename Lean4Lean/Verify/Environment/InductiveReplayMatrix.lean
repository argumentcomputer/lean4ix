import Lean4Lean.Theory.Typing.InductiveCertificate
import Lean4Lean.Verify.Environment.MutualInductiveFixtures
import Lean4Lean.Verify.Environment.DeepNestedReplay

/-!
# Complete inductive replay matrix

This module puts the singleton, mutual, and nested replay rows behind one
uniform completion interface.  A row is accepted only when it carries its
real implementation map, its explicit dependency environment, an exact
Theory transaction, and final alignment.  The generic metadata facts below
then check the family role, every constructor role, and every recursor role
at the final map rather than at an intermediate insertion phase.

The mutual and nested packages retain data-bearing traces.  Consequently a
consumer-neutral `BlockCertificate` (or `NestedBlockCertificate`) is built
from the exact replay data, without selecting a second generation or asking
the consumer for a semantic oracle.
-/

namespace Lean4Lean

open Lean
open VInductDecl

/-- One final implementation-map entry, with its exact inductive role and
translation into the final Theory environment. -/
def FinalTranslatedMetadata
    (kind : InductConstantKind) (map : ConstMap) (env : VEnv)
    (constant : VConstVal) : Prop :=
  ∃ info, map.find? constant.name = some info ∧
    kind.Matches info ∧ TrConstVal .safe env info constant

/-- Final recursor metadata together with the public exact-lookup uniqueness
contract required by consumers. -/
def FinalRecursorMetadata
    (map : ConstMap) (env : VEnv) (recursor : VConstVal) : Prop :=
  FinalTranslatedMetadata .recursor map env recursor ∧
    ∀ {left right : ConstantInfo},
      map.find? recursor.name = some left →
      map.find? recursor.name = some right → left = right

namespace FinalTranslatedMetadata

/-- A final metadata lookup cannot name two different implementation
records.  This is the lookup-uniqueness fact used for every recursor row. -/
theorem lookup_unique {map : ConstMap} {constant : VConstVal}
    {left right : ConstantInfo}
    (leftLookup : map.find? constant.name = some left)
    (rightLookup : map.find? constant.name = some right) :
    left = right :=
  Option.some.inj (leftLookup.symm.trans rightLookup)

/-- Promote an exact translated recursor lookup to the complete public
recursor contract. -/
theorem recursor_complete {map : ConstMap} {env : VEnv}
    {recursor : VConstVal}
    (metadata : FinalTranslatedMetadata .recursor map env recursor) :
    FinalRecursorMetadata map env recursor := by
  refine ⟨metadata, ?_⟩
  intro left right leftLookup rightLookup
  exact lookup_unique leftLookup rightLookup

end FinalTranslatedMetadata

namespace InductiveReplayFixtures

/-- Proof-only completion package recovered from a singleton replay.  The
generation, semantic certificate, successful Theory transaction, and all
three metadata roles are selected by the same data-bearing replay witness. -/
def SingletonReplayCompletion
    (artifact : SingletonReplayArtifact) : Prop :=
  ∃ generation : artifact.source.GenerationChecked,
    artifact.source.types = [generation.block.sourceType] ∧
    generation.WF artifact.inputEnv ∧
    artifact.inputEnv.addInductGeneration generation =
      some artifact.outputEnv ∧
    FinalTranslatedMetadata .induct artifact.outputMap artifact.outputEnv
      generation.block.sourceType.toVConstVal ∧
    (∀ {constructor : VConstVal},
      constructor ∈ generation.block.sourceType.ctors →
        FinalTranslatedMetadata .ctor artifact.outputMap artifact.outputEnv
          constructor) ∧
    FinalRecursorMetadata artifact.outputMap artifact.outputEnv
      (inductGenerationRecVal generation)

/-- Automatically recover the complete singleton package from the retained
transaction; no `Classical.choice` is used at this boundary. -/
theorem SingletonReplayArtifact.completion
    (artifact : SingletonReplayArtifact) :
    SingletonReplayCompletion artifact := by
  rcases artifact.transaction with ⟨trace⟩
  refine ⟨trace.generation, trace.generation.block.source_types_eq,
    trace.generation_wf, trace.to_addInductGeneration, ?_, ?_, ?_⟩
  · obtain ⟨info, lookup, role, translated⟩ :=
      trace.type_translated_lookup artifact.inputMapWF
    exact ⟨info, lookup, role, translated⟩
  · intro constructor hconstructor
    obtain ⟨info, lookup, role, translated⟩ :=
      trace.constructor_translated_lookup artifact.inputMapWF hconstructor
    exact ⟨info, lookup, role, translated⟩
  · obtain ⟨info, lookup, role, translated⟩ :=
      trace.recursor_translated_lookup artifact.inputMapWF
    exact FinalTranslatedMetadata.recursor_complete
      ⟨info, lookup, role, translated⟩

end InductiveReplayFixtures

namespace CompleteInductiveReplay

open InductiveReplayFixtures
open MutualInductiveReplayFixtures
open MutualInductiveFixtures
open InductiveFixtures
open NestedReplayFixtures
open NestedRepresentation
open DeepNestedReplayFixtures

/-- The real kernel metadata and dependency map from which one singleton
candidate is reconstructed.  The replay artifact is retained in the same
value, so candidate construction and environment replay cannot drift into
parallel inventories. -/
structure SingletonCandidateInput where
  replay : SingletonReplayArtifact
  inductInfo : ConstantInfo
  ctorInfos : List ConstantInfo

namespace SingletonCandidateInput

private def metadataStored (map : ConstMap) (info : ConstantInfo) : Bool :=
  match map.find? info.name with
  | some stored => ptrEqConstantInfo stored info
  | none => false

private def constructor? : ConstantInfo → Option Constructor
  | .ctorInfo constructor =>
      some { name := constructor.name, type := constructor.type }
  | _ => none

def kernelType? (input : SingletonCandidateInput) : Option InductiveType := do
  let .inductInfo family := input.inductInfo | none
  let constructors ← input.ctorInfos.mapM constructor?
  return { name := family.name, type := family.type, ctors := constructors }

def context (input : SingletonCandidateInput) : AddInductive.Context where
  env := Kernel.Environment.ofConstants
    (.str `_completeSingletonReplay input.replay.label.toString)
    input.replay.inputMap
  lparams := input.inductInfo.levelParams
  safety := .safe
  allowPrimitive := input.replay.source.types.any fun family =>
    family.name == ``Nat || family.name == ``Bool

end SingletonCandidateInput

/-- The data-bearing result of the ordinary singleton candidate constructor,
including exact source-order agreement. -/
structure ProducedSingletonCandidate (input : SingletonCandidateInput) where
  kernelType : InductiveType
  execution : AddInductive.NormalizationCandidateExecution
    input.replay.source.nparams [kernelType] 0 false input.context
  kernelType_eq : input.kernelType? = some kernelType
  produced : AddInductive.buildNormalizationCandidateExecution
    input.replay.source.nparams [kernelType] 0 false input.context =
      .ok execution
  familyNames : [kernelType.name] = input.replay.source.types.map (·.name)
  constructorNames : kernelType.ctors.map (·.name) =
    input.replay.source.blockConstructorConstants.map (·.name)
  familyMetadataStored : SingletonCandidateInput.metadataStored
    input.replay.outputMap input.inductInfo = true
  constructorMetadataStored : input.ctorInfos.all fun info =>
    SingletonCandidateInput.metadataStored input.replay.outputMap info

namespace SingletonCandidateInput

/-- Execute and package one candidate automatically.  Failed metadata shape,
ordinary candidate rejection, or source-order mismatch all return `none`. -/
def producedCandidate? (input : SingletonCandidateInput) :
    Option (ProducedSingletonCandidate input) :=
  match htype : input.kernelType? with
  | none => none
  | some kernelType =>
      match hproduced : AddInductive.buildNormalizationCandidateExecution
          input.replay.source.nparams [kernelType] 0 false input.context with
      | .error _ => none
      | .ok execution =>
          if hfamilies : [kernelType.name] =
              input.replay.source.types.map (·.name) then
            if hconstructors : kernelType.ctors.map (·.name) =
                input.replay.source.blockConstructorConstants.map (·.name) then
              if hfamilyStored : SingletonCandidateInput.metadataStored
                  input.replay.outputMap input.inductInfo then
                if hconstructorsStored : input.ctorInfos.all fun info =>
                    SingletonCandidateInput.metadataStored
                      input.replay.outputMap info then
                  some {
                    kernelType := kernelType
                    execution := execution
                    kernelType_eq := htype
                    produced := hproduced
                    familyNames := hfamilies
                    constructorNames := hconstructors
                    familyMetadataStored := hfamilyStored
                    constructorMetadataStored := hconstructorsStored }
                else none
              else none
            else none
          else none

end SingletonCandidateInput

/-- One inseparable singleton candidate/replay package. -/
structure SingletonCandidateReplayArtifact where
  input : SingletonCandidateInput
  candidate : ProducedSingletonCandidate input

namespace SingletonCandidateInput

def complete? (input : SingletonCandidateInput) :
    Option SingletonCandidateReplayArtifact := do
  let candidate ← input.producedCandidate?
  return { input, candidate }

end SingletonCandidateInput

/-! The complete singleton metadata matrix, now with data-bearing ordinary
candidate executions rather than Boolean acceptance witnesses. -/

def singletonCandidateInputs : List SingletonCandidateInput :=
  [ { replay := natReplay07
      inductInfo := natInfo
      ctorInfos := [natZeroInfo, natSuccInfo] },
    { replay := boolReplay07
      inductInfo := boolInfo07
      ctorInfos := [boolFalseInfo07, boolTrueInfo07] },
    { replay := listReplay07
      inductInfo := listInfo07
      ctorInfos := [listNilInfo07, listConsInfo07] },
    { replay := optionReplay07
      inductInfo := optionInfo07
      ctorInfos := [optionNoneInfo07, optionSomeInfo07] },
    { replay := prodReplay07
      inductInfo := prodInfo07
      ctorInfos := [prodMkInfo07] },
    { replay := punitReplay07
      inductInfo := punitInfo06C
      ctorInfos := [punitCtorInfo06C] },
    { replay := emptyReplay07
      inductInfo := emptyInfo06C
      ctorInfos := [] },
    { replay := orReplay07
      inductInfo := orInfo06
      ctorInfos := [orInlInfo06, orInrInfo06] },
    { replay := andReplay07
      inductInfo := andInfo06
      ctorInfos := [andIntroInfo06] },
    { replay := eqReplay07
      inductInfo := eqInfo
      ctorInfos := [eqReflInfo] },
    { replay := heqReplay07
      inductInfo := heqInfo07
      ctorInfos := [heqReflInfo07] },
    { replay := finReplay07
      inductInfo := finInfo07
      ctorInfos := [finMkInfo07] },
    { replay := vectorReplay07
      inductInfo := vectorInfo07
      ctorInfos := [vectorMkInfo07] },
    { replay := accReplay07
      inductInfo := accInfo
      ctorInfos := [accIntroInfo] },
    { replay := aliasFormerReplay07
      inductInfo := aliasFormerInfo
      ctorInfos := [aliasFormerMkInfo] },
    { replay := aliasRecReplay07
      inductInfo := aliasRecInfo
      ctorInfos := [aliasRecMkInfo] },
    { replay := normalizationMatrixReplay07
      inductInfo := normalizationMatrixInfo
      ctorInfos := [normalizationMatrixMkInfo] },
    { replay := annotatedPiReplay07
      inductInfo := annotatedPiInfo
      ctorInfos := [annotatedPiMkInfo] },
    { replay := annotatedParamReplay07
      inductInfo := annotatedParamInfo
      ctorInfos := [annotatedParamMkInfo] },
    { replay := biBoxReplay
      inductInfo := biBoxInfo
      ctorInfos := [biBoxMkInfo] } ]

def singletonCandidateReplayMatrix? :
    Option (List SingletonCandidateReplayArtifact) :=
  singletonCandidateInputs.mapM (·.complete?)

#guard singletonCandidateReplayMatrix?.isSome

/-- All 20 singleton packages selected from the actual executable results,
including the two-parameter dependency used by the deep nested row. -/
def singletonCandidateReplayMatrix :
    List SingletonCandidateReplayArtifact :=
  singletonCandidateReplayMatrix?.get (by native_decide)

example : singletonCandidateInputs.map (·.replay) =
    singletonReplayMatrix ++ [biBoxReplay] := rfl
example : singletonCandidateInputs.length = 20 := rfl
example : singletonCandidateReplayMatrix.length = 20 := by native_decide

/-- Provenance for the implementation's ordinary mutual-block candidate
constructor.  This data deliberately stays on the Verify side: the exported
Theory certificate below retains only the translated declaration and its
semantic transaction. -/
structure ProducedBlockCandidate (source : VInductDecl) where
  nparams : Nat
  kernelTypes : List InductiveType
  numNested : Nat
  isUnsafe : Bool
  context : AddInductive.Context
  execution : AddInductive.NormalizationCandidateExecution nparams
    kernelTypes numNested isUnsafe context
  produced :
    AddInductive.buildNormalizationCandidateExecution nparams kernelTypes
      numNested isUnsafe context = .ok execution
  familyNames : kernelTypes.map (·.name) = source.types.map (·.name)
  constructorNames :
    kernelTypes.flatMap (fun family => family.ctors.map (·.name)) =
      source.blockConstructorConstants.map (·.name)

/-- One non-nested arbitrary-block replay package.  Its trace owns the exact
generation and every implementation metadata insertion; `inputWF` supplies
the explicit dependency history needed to export a Theory certificate. -/
structure BlockReplayArtifact where
  label : Name
  source : VInductDecl
  inputMap : ConstMap
  inputEnv : VEnv
  outputMap : ConstMap
  outputEnv : VEnv
  inputMapWF : inputMap.WF
  inputWF : inputEnv.WF
  candidate : ProducedBlockCandidate source
  trace : AddInductBlockTrace inputMap inputEnv source outputMap outputEnv
  generationProduced :
    source.identityBlockGeneration? = some trace.generation
  aligned : Aligned .safe outputMap outputEnv

namespace BlockReplayArtifact

/-- Erase implementation metadata and retain the consumer-neutral completed
block certificate. -/
def certificate (artifact : BlockReplayArtifact) :
    artifact.source.BlockCertificate artifact.inputEnv artifact.outputEnv where
  semantic := {
    generation := artifact.trace.generation
    blockEnv := artifact.trace.blockEnv
    wf := artifact.trace.generation_wf }
  success := by
    simpa [VEnv.addInductBlockCertified] using
      artifact.trace.to_addInductBlockGeneration
  beforeWF := artifact.inputWF

/-- The concrete replay succeeds through the ordinary raw entry point, not
only through its proof-carrying block helper. -/
theorem addInduct (artifact : BlockReplayArtifact) :
    artifact.inputEnv.addInduct artifact.source = some artifact.outputEnv :=
  artifact.certificate.addInduct artifact.generationProduced

/-- The concrete block replay grows its explicit dependency environment. -/
theorem addInduct_le (artifact : BlockReplayArtifact) :
    artifact.inputEnv ≤ artifact.outputEnv :=
  artifact.certificate.addInduct_le

/-- The concrete block replay preserves environment well-formedness. -/
theorem addInduct_WF (artifact : BlockReplayArtifact) :
    artifact.outputEnv.WF :=
  artifact.certificate.addInduct_WF

theorem familyMetadata (artifact : BlockReplayArtifact)
    {family : VInductiveType} (hfamily : family ∈ artifact.source.types) :
    FinalTranslatedMetadata .induct artifact.outputMap artifact.outputEnv
      family.toVConstVal := by
  obtain ⟨info, lookup, role, translated⟩ :=
    artifact.trace.family_translated_lookup artifact.inputMapWF hfamily
  exact ⟨info, lookup, role, translated⟩

theorem constructorMetadata (artifact : BlockReplayArtifact)
    {constructor : VConstVal}
    (hconstructor :
      constructor ∈ artifact.source.blockConstructorConstants) :
    FinalTranslatedMetadata .ctor artifact.outputMap artifact.outputEnv
      constructor := by
  obtain ⟨info, lookup, role, translated⟩ :=
    artifact.trace.constructor_translated_lookup artifact.inputMapWF
      hconstructor
  exact ⟨info, lookup, role, translated⟩

theorem recursorMetadata (artifact : BlockReplayArtifact)
    {recursor : VConstVal}
    (hrecursor : recursor ∈ artifact.trace.generation.recursors) :
    FinalTranslatedMetadata .recursor artifact.outputMap artifact.outputEnv
      recursor := by
  obtain ⟨info, lookup, role, translated⟩ :=
    artifact.trace.recursor_translated_lookup artifact.inputMapWF hrecursor
  exact ⟨info, lookup, role, translated⟩

theorem recursorMetadataComplete (artifact : BlockReplayArtifact)
    {recursor : VConstVal}
    (hrecursor : recursor ∈ artifact.trace.generation.recursors) :
    FinalRecursorMetadata artifact.outputMap artifact.outputEnv recursor :=
  (artifact.recursorMetadata hrecursor).recursor_complete

/-- All implementation metadata roles are complete for this exact block. -/
def MetadataComplete (artifact : BlockReplayArtifact) : Prop :=
  (∀ family ∈ artifact.source.types, FinalTranslatedMetadata .induct
    artifact.outputMap artifact.outputEnv family.toVConstVal) ∧
  (∀ constructor ∈ artifact.source.blockConstructorConstants,
    FinalTranslatedMetadata .ctor artifact.outputMap artifact.outputEnv
      constructor) ∧
  (∀ recursor ∈ artifact.trace.generation.recursors,
    FinalRecursorMetadata artifact.outputMap artifact.outputEnv recursor)

theorem metadataComplete (artifact : BlockReplayArtifact) :
    artifact.MetadataComplete := by
  refine ⟨?_, ?_, ?_⟩
  · intro family hfamily
    exact artifact.familyMetadata hfamily
  · intro constructor hconstructor
    exact artifact.constructorMetadata hconstructor
  · intro recursor hrecursor
    exact artifact.recursorMetadataComplete hrecursor

end BlockReplayArtifact

/-- Provenance for the environment-free nested analyzer.  As above, target
copies and analyzer output remain a Verify artifact and do not cross the
Theory certificate boundary. -/
structure ProducedNestedCandidate (source : VInductDecl) where
  targets : List NestedTargetBlock
  nested : source.NestedBlockChecked
  produced : nestedBlockChecked? targets source = some nested

/-- One completed nested replay package.  Only restored source metadata is
present in the trace and output map; auxiliary flattening constants therefore
cannot be smuggled through this public inventory. -/
structure NestedReplayArtifact where
  label : Name
  source : VInductDecl
  inputMap : ConstMap
  inputEnv : VEnv
  outputMap : ConstMap
  outputEnv : VEnv
  inputMapWF : inputMap.WF
  inputWF : inputEnv.WF
  candidate : ProducedNestedCandidate source
  trace : AddInductNestedTrace inputMap inputEnv source outputMap outputEnv
  candidateAgrees : candidate.nested = trace.nested
  aligned : Aligned .safe outputMap outputEnv

namespace NestedReplayArtifact

/-- Erase implementation metadata and retain the consumer-neutral nested
completion certificate. -/
def certificate (artifact : NestedReplayArtifact) :
    artifact.source.NestedBlockCertificate artifact.inputEnv
      artifact.outputEnv where
  nested := artifact.trace.nested
  semantic := artifact.trace.nested_wf
  success := artifact.trace.to_addInductNested
  beforeWF := artifact.inputWF

/-- The concrete analyzer-produced nested transaction succeeds exactly. -/
theorem addInductNested (artifact : NestedReplayArtifact) :
    artifact.inputEnv.addInductNested artifact.trace.nested =
      some artifact.outputEnv :=
  artifact.certificate.success

/-- The concrete nested replay grows its explicit dependency environment. -/
theorem addInduct_le (artifact : NestedReplayArtifact) :
    artifact.inputEnv ≤ artifact.outputEnv :=
  artifact.certificate.addInduct_le

/-- The concrete nested replay preserves environment well-formedness. -/
theorem addInduct_WF (artifact : NestedReplayArtifact) :
    artifact.outputEnv.WF :=
  artifact.certificate.addInduct_WF

theorem familyMetadata (artifact : NestedReplayArtifact)
    {family : VInductiveType} (hfamily : family ∈ artifact.source.types) :
    FinalTranslatedMetadata .induct artifact.outputMap artifact.outputEnv
      family.toVConstVal := by
  obtain ⟨info, lookup, role, translated⟩ :=
    artifact.trace.family_translated_lookup artifact.inputMapWF hfamily
  exact ⟨info, lookup, role, translated⟩

theorem constructorMetadata (artifact : NestedReplayArtifact)
    {constructor : VConstVal}
    (hconstructor :
      constructor ∈ artifact.source.blockConstructorConstants) :
    FinalTranslatedMetadata .ctor artifact.outputMap artifact.outputEnv
      constructor := by
  obtain ⟨info, lookup, role, translated⟩ :=
    artifact.trace.constructor_translated_lookup artifact.inputMapWF
      hconstructor
  exact ⟨info, lookup, role, translated⟩

theorem recursorMetadata (artifact : NestedReplayArtifact)
    {recursor : VConstVal}
    (hrecursor : recursor ∈ artifact.trace.nested.recursors) :
    FinalTranslatedMetadata .recursor artifact.outputMap artifact.outputEnv
      recursor := by
  obtain ⟨info, lookup, role, translated⟩ :=
    artifact.trace.recursor_translated_lookup artifact.inputMapWF hrecursor
  exact ⟨info, lookup, role, translated⟩

theorem recursorMetadataComplete (artifact : NestedReplayArtifact)
    {recursor : VConstVal}
    (hrecursor : recursor ∈ artifact.trace.nested.recursors) :
    FinalRecursorMetadata artifact.outputMap artifact.outputEnv recursor :=
  (artifact.recursorMetadata hrecursor).recursor_complete

def MetadataComplete (artifact : NestedReplayArtifact) : Prop :=
  (∀ family ∈ artifact.source.types, FinalTranslatedMetadata .induct
    artifact.outputMap artifact.outputEnv family.toVConstVal) ∧
  (∀ constructor ∈ artifact.source.blockConstructorConstants,
    FinalTranslatedMetadata .ctor artifact.outputMap artifact.outputEnv
      constructor) ∧
  (∀ recursor ∈ artifact.trace.nested.recursors,
    FinalRecursorMetadata artifact.outputMap artifact.outputEnv recursor)

theorem metadataComplete (artifact : NestedReplayArtifact) :
    artifact.MetadataComplete := by
  refine ⟨?_, ?_, ?_⟩
  · intro family hfamily
    exact artifact.familyMetadata hfamily
  · intro constructor hconstructor
    exact artifact.constructorMetadata hconstructor
  · intro recursor hrecursor
    exact artifact.recursorMetadataComplete hrecursor

end NestedReplayArtifact

/-! ## Actual mutual and nested rows -/

def treeReplay11 : BlockReplayArtifact where
  label := ``Tree
  source := treeDecl
  inputMap := {}
  inputEnv := .empty
  outputMap := treeReplayMap
  outputEnv := treeFinalEnv
  inputMapWF := SMap.WF.empty
  inputWF := ⟨[], .empty⟩
  candidate := {
    nparams := 1
    kernelTypes := treeKernelTypes
    numNested := 0
    isUnsafe := false
    context := treeKernelContext
    execution := treeExecution
    produced := treeBlockGenerationShape.producedExecution
    familyNames := rfl
    constructorNames := rfl }
  generationProduced := rfl
  trace := treeAddInductBlockTrace
  aligned := tree_verify_aligned

def indexedTreeReplay11 : BlockReplayArtifact where
  label := ``IndexedTree
  source := indexedTreeDecl
  inputMap := natMap
  inputEnv := natFinalEnv
  outputMap := indexedReplayMap
  outputEnv := indexedTreeFinalEnv
  inputMapWF := nat_aligned.map_wf
  inputWF := (nat_trEnv' (safety := .safe)).wf
  candidate := {
    nparams := 1
    kernelTypes := indexedTreeKernelTypes
    numNested := 0
    isUnsafe := false
    context := indexedTreeKernelContext
    execution := indexedTreeExecution
    produced := indexedTreeBlockGenerationShape.producedExecution
    familyNames := rfl
    constructorNames := rfl }
  generationProduced := rfl
  trace := indexedTreeAddInductBlockTrace
  aligned := indexedTree_verify_aligned

def mutualReplayMatrix : List BlockReplayArtifact :=
  [treeReplay11, indexedTreeReplay11]

def roseReplay11 : NestedReplayArtifact where
  label := ``RoseTree
  source := roseSourceV
  inputMap := listMap07
  inputEnv := listFinalEnv07
  outputMap := roseMap09
  outputEnv := roseFinalEnv09
  inputMapWF := listTrEnv07.map_wf
  inputWF := listTrEnv07.wf
  candidate := {
    targets := [NestedInductiveFixtures.listTarget]
    nested := roseNestedC
    produced := by
      exact (Option.some_get (x := roseNestedC?)
        (of_decide_eq_true
          Lean4Lean.NestedReplayFixtures.roseNestedC._native.native_decide.ax_1)).symm }
  candidateAgrees := rfl
  trace := roseTrace09
  aligned := roseTrEnv09.aligned

def nestedIndexedReplay11 : NestedReplayArtifact where
  label := ``NVTree
  source := nvSourceV
  inputMap := pvecCtorMap09
  inputEnv := pvecCtorEnv09
  outputMap := nvMap09
  outputEnv := nvFinalEnv09
  inputMapWF := pvecTrEnv09.map_wf
  inputWF := pvecTrEnv09.wf
  candidate := {
    targets := [NestedTransformation.pvecStoredTarget]
    nested := nvNestedC
    produced := by
      exact (Option.some_get (x := nvNestedC?)
        (of_decide_eq_true
          Lean4Lean.NestedReplayFixtures.nvNestedC._native.native_decide.ax_1)).symm }
  candidateAgrees := rfl
  trace := nvTrace09
  aligned := nvTrEnv09.aligned

/-- A two-parameter target with a second nested occurrence discovered while
processing the first auxiliary constructor.  The explicit input is the full
replay of `BiBox`, and all three restored recursors are inserted from actual
kernel metadata. -/
def deepNestedReplay11 : NestedReplayArtifact where
  label := ``DeepBi
  source := deepSourceV
  inputMap := biBoxMap
  inputEnv := biBoxFinalEnv
  outputMap := deepMap
  outputEnv := deepFinalEnv
  inputMapWF := biBoxMapWF
  inputWF := biBoxFinalWF
  candidate := {
    targets := [biBoxTarget]
    nested := deepNestedC
    produced := deepNestedC_produced }
  candidateAgrees := rfl
  trace := deepTrace
  aligned := deepTrEnv.aligned

def nestedReplayMatrix : List NestedReplayArtifact :=
  [roseReplay11, nestedIndexedReplay11, deepNestedReplay11]

/-- The three supported transaction modes in one consumer-facing inventory. -/
inductive ReplayArtifact where
  | singleton (artifact : SingletonCandidateReplayArtifact)
  | block (artifact : BlockReplayArtifact)
  | nested (artifact : NestedReplayArtifact)

namespace ReplayArtifact

def MetadataComplete : ReplayArtifact → Prop
  | .singleton artifact => SingletonReplayCompletion artifact.input.replay
  | .block artifact => artifact.MetadataComplete
  | .nested artifact => artifact.MetadataComplete

theorem metadataComplete : ∀ artifact : ReplayArtifact,
    artifact.MetadataComplete
  | .singleton artifact => artifact.input.replay.completion
  | .block artifact => artifact.metadataComplete
  | .nested artifact => artifact.metadataComplete

end ReplayArtifact

/-- Complete actual-metadata matrix: all 20 singleton rows, both mutual rows,
and all three nested rows, with dependency environments retained per row. -/
def completeReplayMatrix : List ReplayArtifact :=
  singletonCandidateReplayMatrix.map .singleton ++
    mutualReplayMatrix.map .block ++ nestedReplayMatrix.map .nested

example : singletonReplayMatrix.length = 19 := rfl
example : singletonCandidateReplayMatrix.length = 20 := by native_decide
example : mutualReplayMatrix.length = 2 := rfl
example : nestedReplayMatrix.length = 3 := rfl
example : completeReplayMatrix.length = 25 := by native_decide

theorem completeReplayMatrix_metadataComplete :
    ∀ artifact ∈ completeReplayMatrix, artifact.MetadataComplete := by
  intro artifact _
  exact artifact.metadataComplete

end CompleteInductiveReplay

end Lean4Lean

/-! ## Exact trust manifests -/

/--
info: 'Lean4Lean.CompleteInductiveReplay.BlockReplayArtifact.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.CompleteInductiveReplay.BlockReplayArtifact.certificate

/--
info: 'Lean4Lean.CompleteInductiveReplay.NestedReplayArtifact.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.CompleteInductiveReplay.NestedReplayArtifact.certificate

/--
info: 'Lean4Lean.CompleteInductiveReplay.completeReplayMatrix_metadataComplete' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Lean4Lean.ptrEqConstantInfo_eq,
 Lean4Lean.ptrEqExpr_eq,
 Quot.sound,
 Lean.Expr.abstractRange_eq,
 Lean.Expr.abstract_eq,
 Lean.Expr.eqv_eq,
 Lean.Expr.hasLooseBVar_eq,
 Lean.Expr.instantiate1_eq,
 Lean.Expr.instantiateRange_eq,
 Lean.Expr.instantiateRevRange_eq,
 Lean.Expr.instantiateRev_eq,
 Lean.Expr.instantiate_eq,
 Lean.Expr.looseBVarRange_eq,
 Lean.Expr.lowerLooseBVars_eq,
 Lean.Expr.mkAppData_eq,
 Lean.Expr.mkData_eq,
 Lean.Expr.replace_eq,
 Lean.Level.hasMVar_eq,
 Lean.Level.hasParam_eq,
 Lean.Level.instLawfulBEqLevel,
 Lean.Level.isExplicitSubsumedAux_eq,
 Lean.Level.normalize_eq,
 Lean.PersistentArray.toList'_push,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.Syntax.structEq_eq,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.CompleteInductiveReplay.singletonCandidateReplayMatrix._native.native_decide.ax_1,
 Lean4Lean.DeepNestedReplayFixtures.biBoxObservedShape._native.native_decide.ax_1_1,
 Lean4Lean.DeepNestedReplayFixtures.deepKTarget._native.native_decide.ax_1_1,
 Lean4Lean.DeepNestedReplayFixtures.deepNestedC_some._native.native_decide.ax_1_1,
 Lean4Lean.DeepNestedReplayFixtures.deepRecursors_eq._native.native_decide.ax_1_1,
 Lean4Lean.DeepNestedReplayFixtures.deepRules_eq._native.native_decide.ax_1_1,
 Lean4Lean.MutualInductiveReplayFixtures.indexedTreeBlockGenerationShapeResult_isOk._native.native_decide.ax_1_1,
 Lean4Lean.MutualInductiveReplayFixtures.treeBlockGenerationShapeResult_isOk._native.native_decide.ax_1_1,
 Lean4Lean.NestedReplayFixtures.nvKTarget09._native.native_decide.ax_1_1,
 Lean4Lean.NestedReplayFixtures.nvNestedC._native.native_decide.ax_1,
 Lean4Lean.NestedReplayFixtures.nvRecursors_eq._native.native_decide.ax_1_1,
 Lean4Lean.NestedReplayFixtures.nvRules_eq._native.native_decide.ax_1_1,
 Lean4Lean.NestedReplayFixtures.roseKTarget09._native.native_decide.ax_1_1,
 Lean4Lean.NestedReplayFixtures.roseNestedC._native.native_decide.ax_1,
 Lean4Lean.NestedReplayFixtures.roseRecursors_eq._native.native_decide.ax_1_1,
 Lean4Lean.NestedReplayFixtures.roseRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Lean4Lean.CompleteInductiveReplay.completeReplayMatrix_metadataComplete
