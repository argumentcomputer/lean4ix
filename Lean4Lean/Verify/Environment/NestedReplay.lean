import Lean4Lean.Verify.Environment.SingletonParityReplay
import Lean4Lean.Verify.Environment.NestedTransformation
import Lean4Lean.Verify.Environment.NormalizationElimination
import Lean4Lean.Verify.Environment.Readiness
import Lean4Lean.Verify.Environment.RecursorReduction
import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Theory.Typing.NestedTransport

/-!
# Nested environment replay (L4L-09C)

Both ladder fixtures replayed from real stored metadata: the rose tree
over the completed `List` environment and the nested-indexed family over
a staged `PVec` boundary.  Each inserts its stored constants through
`AddInductNestedTrace`, proves the `NestedBlockChecked.WF` package by
direct concrete typing derivations over the exact phase environments,
and drives the final map and environment through `TrEnv'.inductNested`,
with `Ordered` derived and the transitional closures guarded.
-/

namespace Lean4Lean.NestedReplayFixtures

open Lean
open private Lean.Kernel.Environment.add from Lean.Environment
open Lean4Lean.InductiveReplayFixtures
open Lean4Lean.NestedRepresentation
open Lean4Lean.NestedInductiveFixtures
open Lean4Lean.TypeChecker.Inner
open VInductDecl

local instance : Inhabited VEnv := ⟨.empty⟩
local instance : Inhabited VConstVal := ⟨⟨⟨0, .sort .zero⟩, .anonymous⟩⟩

/-! ## The completed List replay as the input boundary -/

theorem listTrEnv07 : TrEnv' .safe listMap07 false listFinalEnv07 :=
  .induct listAddInduct07 .empty

theorem listFinalOrdered07 : listFinalEnv07.Ordered :=
  listTrEnv07.wf.ordered

/-! ## The translated rose source and its nested artifact -/

def roseSourceV : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := ``RoseTree
       uvars := 1
       type := nestedConstVType09A% RoseTree
       ctors :=
         [⟨⟨1, nestedConstVType09A% RoseTree.node⟩, ``RoseTree.node⟩] }]

def roseNestedC? : Option (NestedBlockChecked roseSourceV) :=
  nestedBlockChecked? [listTarget] roseSourceV

#guard roseNestedC?.isSome

def roseNestedC : NestedBlockChecked roseSourceV :=
  roseNestedC?.get (by native_decide)

/-! ## Stored metadata and phase maps/environments -/

def roseInfo09 : ConstantInfo := kernelInductInfo% RoseTree
def roseNodeInfo09 : ConstantInfo := kernelCtorInfo% RoseTree.node
def roseRecInfo09 : ConstantInfo := kernelRecInfo% RoseTree.rec
def roseRec1Info09 : ConstantInfo := kernelRecInfo% RoseTree.rec_1

/-- Kernel source payload and dependency-only environment for a concrete run
of the retained outer inductive execution. -/
def roseKernelType09 : InductiveType where
  name := ``RoseTree
  type := roseInfo09.type
  ctors := [⟨roseNodeInfo09.name, roseNodeInfo09.type⟩]

def roseInputKernelEnv09 : Kernel.Environment :=
  Kernel.Environment.ofConstants `_roseOuterExecution09 listMap07

def roseKernelDeclaration09 : Declaration :=
  .inductDecl [`u] 1 [roseKernelType09] false

theorem rosePrimitiveInductive09 :
    Environment.checkPrimitiveInductive roseInputKernelEnv09 [`u] 1
      [roseKernelType09]
      false = .ok false := by
  rfl

def roseEnvironmentInductiveExecutionResult :=
  AddInductive.EnvironmentInductiveExecution.buildExecution
    roseInputKernelEnv09 [`u] 1 [roseKernelType09] false false

theorem roseEnvironmentInductiveExecutionResult_isOk :
    roseEnvironmentInductiveExecutionResult.isOk = true := by
  native_decide

/-- The concrete rose-tree run owns prechecking, flattening, actual ordinary
recursor synthesis, restoration, and the auxiliary-value typecheck in one
dependent execution. -/
def roseEnvironmentInductiveExecution :=
  match h : roseEnvironmentInductiveExecutionResult with
  | .ok produced => produced
  | .error _ => by
      have hOk := roseEnvironmentInductiveExecutionResult_isOk
      rw [h] at hOk
      contradiction

theorem roseEnvironmentInductiveExecution_addInductive :
    Environment.addInductive roseInputKernelEnv09 [`u] 1 [roseKernelType09]
      false false = .ok roseEnvironmentInductiveExecution.1 :=
  roseEnvironmentInductiveExecution.2.addInductiveRun

theorem roseEnvironmentInductiveExecution_addDecl :
    addDecl roseInputKernelEnv09 roseKernelDeclaration09 =
      .ok roseEnvironmentInductiveExecution.1 := by
  simpa [roseKernelDeclaration09] using
    roseEnvironmentInductiveExecution.2.addDeclRun rosePrimitiveInductive09

theorem roseEnvironmentInductiveExecution_numNested :
    roseEnvironmentInductiveExecution.2.nested.aux2nested.size = 1 := by
  native_decide

/-- Theory's flattened RoseTree block retains the public declaration's
parameter count. -/
theorem roseFlatNparams : roseNestedC.elim.flat.nparams = 1 := by
  native_decide

/-- The normalization candidate selected inside the real outer execution
satisfies the complete generation-shape gate for Theory's exact flattened
RoseTree block. -/
theorem roseFlatGenerationShape :
    normalizationCandidateBlockGenerationShape roseNestedC.elim.flat
      roseEnvironmentInductiveExecution.2.flattened.candidate = true := by
  native_decide

/-- The real outer nested execution, reindexed as the exact ordinary
recursor-producing execution for its Theory flattened block. -/
def roseFlatRecursorShapeCandidate :
    ProducedBlockRecursorShapeCandidate roseNestedC.elim.flat
      roseEnvironmentInductiveExecution.2.nested.types
      roseEnvironmentInductiveExecution.2.nested.aux2nested.size false
      (AddInductive.Context.forInductive roseInputKernelEnv09 [`u] false false
        {}) :=
  ProducedBlockRecursorShapeCandidate.ofExecution
    roseEnvironmentInductiveExecution.2.flattened
    roseEnvironmentInductiveExecution.2.flattenedRun
    roseEnvironmentInductiveExecution.2.nested.types_nonempty
    roseFlatNparams roseFlatGenerationShape

/-- The retained post-constructor decisions agree with the Theory flattened
generation's elimination mode, K target, and recursor universe layout. -/
def roseFlatEliminationAlignment :
    AddInductive.CheckerBlockEliminationRun roseNestedC.generation
      roseFlatRecursorShapeCandidate.execution.eliminationExecution :=
  (AddInductive.CheckerBlockEliminationRun.build? roseNestedC.generation
    roseFlatRecursorShapeCandidate.execution.eliminationExecution).get
      (by native_decide)

/-- The retained flattened validation context uses the source universe
parameter order expected by the Theory block. -/
theorem roseFlatValidationLparams :
    (roseFlatRecursorShapeCandidate.execution.eliminationExecution.normalization).validationContext.lparams =
      [`u] := by
  native_decide

/-- The generated common result level is well formed in the flattened
source's universe context. -/
theorem roseFlatResultLevelWF :
    roseNestedC.generation.validated.resultLevel.WF
      roseNestedC.elim.flat.uvars := by
  native_decide

/-- Once the flattened semantic generation run is supplied, every later
ordinary producer alignment comes from the retained outer execution.  This
isolates the remaining producer work from elimination/K/universe bookkeeping. -/
def roseFlatExactRecursorOfGeneration
    {blockEnv : VEnv}
    (block : ExactProducedBlockGenerationRun listFinalEnv07 blockEnv [`u]
      roseFlatRecursorShapeCandidate.eliminationBase.base
      roseNestedC.generation) :
    ExactProducedBlockRecursorRun listFinalEnv07 blockEnv [`u]
      roseFlatRecursorShapeCandidate roseNestedC.generation where
  elimination := {
    block := block
    elimination := roseFlatEliminationAlignment
    isUnsafe_eq := rfl
    validation_lparams_eq := roseFlatValidationLparams }

private theorem roseEnvironmentInductiveExecution_restoration_exists :
    ∃ restoration : NestedRestorationResult
        roseEnvironmentInductiveExecution.2.nested
        roseEnvironmentInductiveExecution.2.flattened.recursors.env
        roseInputKernelEnv09 [roseKernelType09] false .safe [`u] {},
      restoreNestedEnvironment roseEnvironmentInductiveExecution.2.nested
          roseEnvironmentInductiveExecution.2.flattened.recursors.env
          roseInputKernelEnv09 [roseKernelType09] false .safe [`u] {} =
        .ok restoration ∧
      roseEnvironmentInductiveExecution.1 = restoration.env :=
  roseEnvironmentInductiveExecution.2.restoration_of_numNested_ne (by
    rw [roseEnvironmentInductiveExecution_numNested]
    decide)

/-- The exact restoration object selected by the full rose-tree execution. -/
noncomputable def roseEnvironmentInductiveRestoration :=
  Classical.choose roseEnvironmentInductiveExecution_restoration_exists

theorem roseEnvironmentInductiveRestoration_run :
    restoreNestedEnvironment roseEnvironmentInductiveExecution.2.nested
        roseEnvironmentInductiveExecution.2.flattened.recursors.env
        roseInputKernelEnv09 [roseKernelType09] false .safe [`u] {} =
      .ok roseEnvironmentInductiveRestoration :=
  (Classical.choose_spec
    roseEnvironmentInductiveExecution_restoration_exists).1

theorem roseEnvironmentInductiveExecution_finalEnv_eq :
    roseEnvironmentInductiveExecution.1 =
      roseEnvironmentInductiveRestoration.env :=
  (Classical.choose_spec
    roseEnvironmentInductiveExecution_restoration_exists).2

/-- Typed decomposition of the restored inventory for a singleton source
family with one constructor and one auxiliary recursor. -/
structure SingletonNestedRestoredInfoRun (infos : List ConstantInfo) where
  family : InductiveVal
  constructor : ConstructorVal
  recursor : RecursorVal
  auxiliaryRecursor : RecursorVal
  infos_eq : infos =
    [.inductInfo family, .ctorInfo constructor, .recInfo recursor,
      .recInfo auxiliaryRecursor]

def SingletonNestedRestoredInfoRun.build? (infos : List ConstantInfo) :
    Option (SingletonNestedRestoredInfoRun infos) :=
  match infos with
  | [.inductInfo family, .ctorInfo constructor, .recInfo recursor,
      .recInfo auxiliaryRecursor] =>
    some { family, constructor, recursor, auxiliaryRecursor, infos_eq := rfl }
  | _ => none

def roseProducedRestoredInfos09 : List ConstantInfo :=
  restoredNestedInfos roseEnvironmentInductiveExecution.2.nested
    roseEnvironmentInductiveExecution.2.flattened.recursors.env
    [roseKernelType09]

def roseProducedRestoredInfoRun? :=
  SingletonNestedRestoredInfoRun.build? roseProducedRestoredInfos09

theorem roseProducedRestoredInfoRun_isSome :
    roseProducedRestoredInfoRun?.isSome = true := by
  native_decide

/-- For the singleton-source rose block, the operational restoration order is
already family, constructor, main recursor, auxiliary recursor. -/
def roseProducedRestoredInfoRun :
    SingletonNestedRestoredInfoRun roseProducedRestoredInfos09 :=
  roseProducedRestoredInfoRun?.get roseProducedRestoredInfoRun_isSome

abbrev roseProducedRestoredFamilyInfo09 : InductiveVal :=
  roseProducedRestoredInfoRun.family

abbrev roseProducedRestoredCtorInfo09 : ConstructorVal :=
  roseProducedRestoredInfoRun.constructor

abbrev roseProducedRestoredRecInfo09 : RecursorVal :=
  roseProducedRestoredInfoRun.recursor

abbrev roseProducedRestoredAuxRecInfo09 : RecursorVal :=
  roseProducedRestoredInfoRun.auxiliaryRecursor

def roseFamilyV : VConstVal := roseSourceV.types[0].toVConstVal
def roseNodeV : VConstVal := roseSourceV.types[0].ctors[0]
def roseRecV : VConstVal := roseNestedC.recursors[0]!
def roseRec1V : VConstVal := roseNestedC.recursors[1]!

#guard roseRecV.name == ``RoseTree.rec
#guard roseRec1V.name == `Lean4Lean.NestedRepresentation.RoseTree.rec_1

def roseTypeMap09 : ConstMap := listMap07.insert ``RoseTree roseInfo09
def roseCtorMap09 : ConstMap := roseTypeMap09.insert ``RoseTree.node roseNodeInfo09
def roseRecMap09 : ConstMap := roseCtorMap09.insert ``RoseTree.rec roseRecInfo09
def roseMap09 : ConstMap :=
  roseRecMap09.insert `Lean4Lean.NestedRepresentation.RoseTree.rec_1 roseRec1Info09

def roseTypeEnv09 : VEnv :=
  (listFinalEnv07.addConst roseFamilyV.name roseFamilyV.toVConstant).get!
def roseCtorEnv09 : VEnv :=
  (roseTypeEnv09.addConst roseNodeV.name roseNodeV.toVConstant).get!
-- the recursor and rule phase environments are defined below, over the
-- printed literal inventories


/-! ## Printed artifact literals

The restored recursor types and rule components, printed from the
computed artifact and tied back to it below; the concrete typing
derivations are stated over these literals. -/

/-- Printed image of `roseNestedC.recursors[0]!.type`. -/
def roseRecTypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.app (.bvar 5) (.bvar 0))))))))

def roseRec1TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.app
                  (.const `List [.param 1])
                  (.app
                    (.const
                      `Lean4Lean.NestedRepresentation.RoseTree
                      [.param 1])
                    (.bvar 5)))
                (.app (.bvar 4) (.bvar 0))))))))

def roseRule0LhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.bvar 5)
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree.rec
                                  [.param 0, .param 1])
                                (.bvar 7))
                              (.bvar 6))
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.app
                      (.app
                        (.app
                          (.const
                            `Lean4Lean.NestedRepresentation.RoseTree.node
                            [.param 1])
                          (.bvar 7))
                        (.bvar 1))
                      (.bvar 0))))))))))

def roseRule0RhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.bvar 5)
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app (.bvar 4) (.bvar 1))
                      (.bvar 0))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.const
                                    `Lean4Lean.NestedRepresentation.RoseTree.rec_1
                                    [.param 0, .param 1])
                                  (.bvar 7))
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 2))
                      (.bvar 0))))))))))

def roseRule0TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.bvar 5)
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.bvar 6)
                    (.app
                      (.app
                        (.app
                          (.const
                            `Lean4Lean.NestedRepresentation.RoseTree.node
                            [.param 1])
                          (.bvar 7))
                        (.bvar 1))
                      (.bvar 0))))))))))

def roseRule1LhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.app
                (.app
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.const
                              `Lean4Lean.NestedRepresentation.RoseTree.rec_1
                              [.param 0, .param 1])
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.bvar 1))
                  (.bvar 0))
                (.app
                  (.const `List.nil [.param 1])
                  (.app
                    (.const
                      `Lean4Lean.NestedRepresentation.RoseTree
                      [.param 1])
                    (.bvar 5)))))))))

def roseRule1RhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.bvar 1))))))

def roseRule1TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.app
                (.bvar 3)
                (.app
                  (.const `List.nil [.param 1])
                  (.app
                    (.const
                      `Lean4Lean.NestedRepresentation.RoseTree
                      [.param 1])
                    (.bvar 5)))))))))

def roseRule2LhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree.rec_1
                                  [.param 0, .param 1])
                                (.bvar 7))
                              (.bvar 6))
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.app
                      (.app
                        (.app
                          (.const `List.cons [.param 1])
                          (.app
                            (.const
                              `Lean4Lean.NestedRepresentation.RoseTree
                              [.param 1])
                            (.bvar 7)))
                        (.bvar 1))
                      (.bvar 0))))))))))

def roseRule2RhsL : VExpr :=
  .lam
    (.sort (.succ (.param 1)))
    (.lam
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.lam
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.lam
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.lam
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.lam
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.lam
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.lam
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.app
                      (.app
                        (.app (.bvar 2) (.bvar 1))
                        (.bvar 0))
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.app
                                    (.const
                                      `Lean4Lean.NestedRepresentation.RoseTree.rec
                                      [.param 0, .param 1])
                                    (.bvar 7))
                                  (.bvar 6))
                                (.bvar 5))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))
                        (.bvar 1)))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.const
                                    `Lean4Lean.NestedRepresentation.RoseTree.rec_1
                                    [.param 0, .param 1])
                                  (.bvar 7))
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 2))
                      (.bvar 0))))))))))

def roseRule2TypeL : VExpr :=
  .forallE
    (.sort (.succ (.param 1)))
    (.forallE
      (.forallE
        (.app
          (.const
            `Lean4Lean.NestedRepresentation.RoseTree
            [.param 1])
          (.bvar 0))
        (.sort (.param 0)))
      (.forallE
        (.forallE
          (.app
            (.const `List [.param 1])
            (.app
              (.const
                `Lean4Lean.NestedRepresentation.RoseTree
                [.param 1])
              (.bvar 1)))
          (.sort (.param 0)))
        (.forallE
          (.forallE
            (.bvar 2)
            (.forallE
              (.app
                (.const `List [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3)))
              (.forallE
                (.app (.bvar 2) (.bvar 0))
                (.app
                  (.bvar 4)
                  (.app
                    (.app
                      (.app
                        (.const
                          `Lean4Lean.NestedRepresentation.RoseTree.node
                          [.param 1])
                        (.bvar 5))
                      (.bvar 2))
                    (.bvar 1))))))
          (.forallE
            (.app
              (.bvar 1)
              (.app
                (.const `List.nil [.param 1])
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 3))))
            (.forallE
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 4))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 5)))
                  (.forallE
                    (.app (.bvar 5) (.bvar 1))
                    (.forallE
                      (.app (.bvar 5) (.bvar 1))
                      (.app
                        (.bvar 6)
                        (.app
                          (.app
                            (.app
                              (.const `List.cons [.param 1])
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.RoseTree
                                  [.param 1])
                                (.bvar 8)))
                            (.bvar 3))
                          (.bvar 2)))))))
              (.forallE
                (.app
                  (.const
                    `Lean4Lean.NestedRepresentation.RoseTree
                    [.param 1])
                  (.bvar 5))
                (.forallE
                  (.app
                    (.const `List [.param 1])
                    (.app
                      (.const
                        `Lean4Lean.NestedRepresentation.RoseTree
                        [.param 1])
                      (.bvar 6)))
                  (.app
                    (.bvar 5)
                    (.app
                      (.app
                        (.app
                          (.const `List.cons [.param 1])
                          (.app
                            (.const
                              `Lean4Lean.NestedRepresentation.RoseTree
                              [.param 1])
                            (.bvar 7)))
                        (.bvar 1))
                      (.bvar 0))))))))))

#guard roseRecV.type == roseRecTypeL
#guard roseRec1V.type == roseRec1TypeL
#guard roseNestedC.generatedRules.map (fun df => (df.uvars, df.lhs, df.rhs, df.type)) ==
  [(2, roseRule0LhsL, roseRule0RhsL, roseRule0TypeL),
   (2, roseRule1LhsL, roseRule1RhsL, roseRule1TypeL),
   (2, roseRule2LhsL, roseRule2RhsL, roseRule2TypeL)]
#guard roseRecV.uvars == 2 && roseRec1V.uvars == 2


/-! ## Literal inventories -/

def roseRecVL : VConstVal := ⟨⟨2, roseRecTypeL⟩, ``RoseTree.rec⟩
def roseRec1VL : VConstVal :=
  ⟨⟨2, roseRec1TypeL⟩, `Lean4Lean.NestedRepresentation.RoseTree.rec_1⟩

def roseRulesL : List VDefEq :=
  [⟨2, roseRule0LhsL, roseRule0RhsL, roseRule0TypeL⟩,
   ⟨2, roseRule1LhsL, roseRule1RhsL, roseRule1TypeL⟩,
   ⟨2, roseRule2LhsL, roseRule2RhsL, roseRule2TypeL⟩]

theorem roseRecursors_eq : roseNestedC.recursors = [roseRecVL, roseRec1VL] := by
  native_decide

theorem roseRules_eq : roseNestedC.generatedRules = roseRulesL := by
  native_decide

def roseRecEnv09 : VEnv :=
  (roseCtorEnv09.addConst roseRecVL.name roseRecVL.toVConstant).get!
def roseRec1Env09 : VEnv :=
  (roseRecEnv09.addConst roseRec1VL.name roseRec1VL.toVConstant).get!
def roseFinalEnv09 : VEnv :=
  roseRulesL.foldl VEnv.addDefEq roseRec1Env09

/-! ## Concrete constant well-formedness -/

theorem roseFamilyWF09 : roseFamilyV.toVConstant.WF listFinalEnv07 :=
  ⟨_, by type_tac⟩

theorem roseTypeEnv09_eq :
    listFinalEnv07.addConst roseFamilyV.name roseFamilyV.toVConstant =
      some roseTypeEnv09 := rfl

theorem roseTypeOrdered09 : roseTypeEnv09.Ordered :=
  .const listFinalOrdered07 roseFamilyWF09 roseTypeEnv09_eq

theorem roseNodeWF09 : roseNodeV.toVConstant.WF roseTypeEnv09 := by
  have hList : roseTypeEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseTypeEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  exact ⟨_, by type_tac⟩


theorem roseCtorEnv09_eq :
    roseTypeEnv09.addConst roseNodeV.name roseNodeV.toVConstant =
      some roseCtorEnv09 := rfl

theorem roseCtorOrdered09 : roseCtorEnv09.Ordered :=
  .const roseTypeOrdered09 roseNodeWF09 roseCtorEnv09_eq

set_option maxRecDepth 4000 in
theorem roseRecWF09 : (⟨2, roseRecTypeL⟩ : VConstant).WF roseCtorEnv09 := by
  have hList : roseCtorEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseCtorEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseCtorEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseCtorEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseCtorEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  exact ⟨_, by type_tac⟩


theorem roseRecEnv09_eq :
    roseCtorEnv09.addConst roseRecVL.name roseRecVL.toVConstant =
      some roseRecEnv09 := rfl

theorem roseRecOrdered09 : roseRecEnv09.Ordered :=
  .const roseCtorOrdered09 roseRecWF09 roseRecEnv09_eq

set_option maxRecDepth 4000 in
theorem roseRec1WF09 : (⟨2, roseRec1TypeL⟩ : VConstant).WF roseRecEnv09 := by
  have hList : roseRecEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseRecEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseRecEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseRecEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseRecEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  exact ⟨_, by type_tac⟩

theorem roseRec1Env09_eq :
    roseRecEnv09.addConst roseRec1VL.name roseRec1VL.toVConstant =
      some roseRec1Env09 := rfl

theorem roseRec1Ordered09 : roseRec1Env09.Ordered :=
  .const roseRecOrdered09 roseRec1WF09 roseRec1Env09_eq


/-! ## Rule well-formedness at the rule-phase environment -/

section RuleWF

set_option maxRecDepth 8000

/-- The lookup hypotheses shared by every rule component derivation; the
environment argument is any `addDefEq` extension of `roseRec1Env09`, whose
constants agree definitionally. -/
macro "rose_rule_hyps" e:term : tactic => `(tactic| (
  have hList : VEnv.constants $e ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : VEnv.constants $e ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : VEnv.constants $e ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : VEnv.constants $e ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : VEnv.constants $e ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  have hRec : VEnv.constants $e ``RoseTree.rec =
      some ⟨2, roseRecTypeL⟩ := rfl
  have hRec1 : VEnv.constants $e
      `Lean4Lean.NestedRepresentation.RoseTree.rec_1 =
      some ⟨2, roseRec1TypeL⟩ := rfl))

def roseRuleEnv1 : VEnv := roseRec1Env09.addDefEq roseRulesL[0]
def roseRuleEnv2 : VEnv := roseRuleEnv1.addDefEq roseRulesL[1]

theorem roseRule0WF09 : roseRulesL[0].WF roseRec1Env09 := by
  constructor
  · rose_rule_hyps roseRec1Env09; type_tac
  · rose_rule_hyps roseRec1Env09; type_tac

theorem roseRule1WF09 : roseRulesL[1].WF roseRuleEnv1 := by
  constructor
  · rose_rule_hyps roseRuleEnv1; type_tac
  · rose_rule_hyps roseRuleEnv1; type_tac

theorem roseRule2WF09 : roseRulesL[2].WF roseRuleEnv2 := by
  constructor
  · rose_rule_hyps roseRuleEnv2; type_tac
  · rose_rule_hyps roseRuleEnv2; type_tac

end RuleWF


/-! ## The semantic package -/

theorem roseTypesFold_eq :
    roseSourceV.blockTypeConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) listFinalEnv07 =
      some roseTypeEnv09 := rfl

theorem roseCtorsFold_eq :
    roseSourceV.blockConstructorConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) roseTypeEnv09 =
      some roseCtorEnv09 := rfl

theorem roseRecsFold_eq :
    roseNestedC.recursors.foldlM
      (fun env c => env.addConst c.name c.toVConstant) roseCtorEnv09 =
      some roseRec1Env09 := by
  rw [roseRecursors_eq]; rfl

theorem roseNestedWF09 : roseNestedC.WF listFinalEnv07 := by
  refine ⟨⟨roseFamilyWF09, fun env' h => ?_⟩, fun {typeEnv} h => ?_,
    fun {typeEnv ctorEnv} hT hC => ?_, fun {typeEnv ctorEnv recEnv} hT hC hR => ?_⟩
  · cases Option.some.inj (roseTypeEnv09_eq.symm.trans h)
    exact trivial
  · cases Option.some.inj (roseTypesFold_eq.symm.trans h)
    exact ⟨roseNodeWF09, fun env' h' => by
      cases Option.some.inj (roseCtorEnv09_eq.symm.trans h')
      exact trivial⟩
  · cases Option.some.inj (roseTypesFold_eq.symm.trans hT)
    cases Option.some.inj (roseCtorsFold_eq.symm.trans hC)
    rw [roseRecursors_eq]
    exact ⟨roseRecWF09, fun env' h' => by
      cases Option.some.inj (roseRecEnv09_eq.symm.trans h')
      exact ⟨roseRec1WF09, fun env'' h'' => by
        cases Option.some.inj (roseRec1Env09_eq.symm.trans h'')
        exact trivial⟩⟩
  · cases Option.some.inj (roseTypesFold_eq.symm.trans hT)
    cases Option.some.inj (roseCtorsFold_eq.symm.trans hC)
    cases Option.some.inj (roseRecsFold_eq.symm.trans hR)
    rw [roseRules_eq]
    exact ⟨roseRule0WF09, roseRule1WF09, roseRule2WF09, trivial⟩


/-! ## Freshness of the stored insertions -/

theorem listMapWF07 : listMap07.WF :=
  listCtorMapWF07.insert _ _ listRecFresh07

theorem roseTypeFresh09 : listMap07.find? ``RoseTree = none := by
  rw [listMap07, listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem roseTypeMapWF09 : roseTypeMap09.WF :=
  listMapWF07.insert _ _ roseTypeFresh09

theorem roseNodeFresh09 : roseTypeMap09.find? ``RoseTree.node = none := by
  rw [roseTypeMap09, listMapWF07.find?_insert, listMap07,
    listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem roseCtorMapWF09 : roseCtorMap09.WF :=
  roseTypeMapWF09.insert _ _ roseNodeFresh09

theorem roseRecFresh09 : roseCtorMap09.find? ``RoseTree.rec = none := by
  rw [roseCtorMap09, roseTypeMapWF09.find?_insert, roseTypeMap09,
    listMapWF07.find?_insert, listMap07,
    listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem roseRecMapWF09 : roseRecMap09.WF :=
  roseCtorMapWF09.insert _ _ roseRecFresh09

theorem roseRec1Fresh09 :
    roseRecMap09.find? `Lean4Lean.NestedRepresentation.RoseTree.rec_1 = none := by
  rw [roseRecMap09, roseCtorMapWF09.find?_insert, roseCtorMap09,
    roseTypeMapWF09.find?_insert, roseTypeMap09,
    listMapWF07.find?_insert, listMap07,
    listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

/-! ## Exact flattened RoseTree inventory -/

/-- The auxiliary family name selected by the real nested elimination. -/
def roseFlatAuxName09 : Name := `_nested.List_1

/-- Raw flattened constructor replacing the nested `List` field by the
generated auxiliary family. -/
def roseFlatNode09 : VConstVal :=
  ⟨⟨1,
    .forallE (.sort (.succ (.param 0)))
      (.forallE (.bvar 0)
        (.forallE
          (.app (.const roseFlatAuxName09 [.param 0]) (.bvar 1))
          (.app (.const ``RoseTree [.param 0]) (.bvar 2))))⟩,
    ``RoseTree.node⟩

/-- Raw nil constructor of the generated auxiliary family. -/
def roseFlatNil09 : VConstVal :=
  ⟨⟨1,
    .forallE (.sort (.succ (.param 0)))
      (.app (.const roseFlatAuxName09 [.param 0]) (.bvar 0))⟩,
    roseFlatAuxName09 ++ `nil⟩

/-- Raw cons constructor of the generated auxiliary family. -/
def roseFlatCons09 : VConstVal :=
  ⟨⟨1,
    .forallE (.sort (.succ (.param 0)))
      (.forallE (.app (.const ``RoseTree [.param 0]) (.bvar 0))
        (.forallE
          (.app (.const roseFlatAuxName09 [.param 0]) (.bvar 1))
          (.app (.const roseFlatAuxName09 [.param 0]) (.bvar 2))))⟩,
    roseFlatAuxName09 ++ `cons⟩

/-- Source family as it occurs in the flattened ordinary block. -/
def roseFlatFamily09 : VInductiveType where
  name := ``RoseTree
  uvars := 1
  type := .forallE (.sort (.succ (.param 0)))
    (.sort (.succ (.param 0)))
  ctors := [roseFlatNode09]

/-- Generated auxiliary family representing `List (RoseTree α)`. -/
def roseFlatAuxFamily09 : VInductiveType where
  name := roseFlatAuxName09
  uvars := 1
  type := .forallE (.sort (.succ (.param 0)))
    (.sort (.succ (.param 0)))
  ctors := [roseFlatNil09, roseFlatCons09]

/-- Concrete printable image of the Theory declaration selected by the real
outer nested execution. -/
def roseFlatDecl09 : VInductDecl where
  uvars := 1
  nparams := 1
  types := [roseFlatFamily09, roseFlatAuxFamily09]

theorem roseFlatDecl09_eq : roseNestedC.elim.flat = roseFlatDecl09 := by
  native_decide

/-- First family-only insertion boundary for the flattened declaration. -/
def roseFlatFirstTypeEnv09 : VEnv :=
  (listFinalEnv07.addConst roseFlatFamily09.name
    roseFlatFamily09.toVConstant).get!

/-- Shared post-family environment in which all three flattened constructor
types are interpreted. -/
def roseFlatBlockEnv09 : VEnv :=
  (roseFlatFirstTypeEnv09.addConst roseFlatAuxFamily09.name
    roseFlatAuxFamily09.toVConstant).get!

theorem roseFlatFamilyWF09 :
    roseFlatFamily09.toVConstant.WF listFinalEnv07 :=
  ⟨_, by type_tac⟩

theorem roseFlatFirstTypeEnv09_eq :
    listFinalEnv07.addConst roseFlatFamily09.name
      roseFlatFamily09.toVConstant = some roseFlatFirstTypeEnv09 :=
  rfl

theorem roseFlatFirstTypeOrdered09 : roseFlatFirstTypeEnv09.Ordered :=
  .const listFinalOrdered07 roseFlatFamilyWF09
    roseFlatFirstTypeEnv09_eq

theorem roseFlatAuxFamilyWF09 :
    roseFlatAuxFamily09.toVConstant.WF roseFlatFirstTypeEnv09 :=
  ⟨_, by type_tac⟩

theorem roseFlatAuxFamilyPreWF09 :
    roseFlatAuxFamily09.toVConstant.WF listFinalEnv07 :=
  ⟨_, by type_tac⟩

theorem roseFlatBlockEnv09_eq :
    roseFlatFirstTypeEnv09.addConst roseFlatAuxFamily09.name
      roseFlatAuxFamily09.toVConstant = some roseFlatBlockEnv09 :=
  rfl

theorem roseFlatBlockEnvOrdered09 : roseFlatBlockEnv09.Ordered :=
  .const roseFlatFirstTypeOrdered09 roseFlatAuxFamilyWF09
    roseFlatBlockEnv09_eq

/-- The exact all-family staging fold consumed by the candidate semantic
hierarchy. -/
theorem roseFlatStage09 :
    listFinalEnv07.stageInductiveTypes roseFlatDecl09.types =
      some roseFlatBlockEnv09 :=
  rfl

theorem roseFlatNodeWF09 :
    roseFlatNode09.toVConstant.WF roseFlatBlockEnv09 := by
  have hRose : roseFlatBlockEnv09.constants ``RoseTree =
      some roseFlatFamily09.toVConstant := rfl
  have hAux : roseFlatBlockEnv09.constants roseFlatAuxName09 =
      some roseFlatAuxFamily09.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem roseFlatNilWF09 :
    roseFlatNil09.toVConstant.WF roseFlatBlockEnv09 := by
  have hRose : roseFlatBlockEnv09.constants ``RoseTree =
      some roseFlatFamily09.toVConstant := rfl
  have hAux : roseFlatBlockEnv09.constants roseFlatAuxName09 =
      some roseFlatAuxFamily09.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem roseFlatConsWF09 :
    roseFlatCons09.toVConstant.WF roseFlatBlockEnv09 := by
  have hRose : roseFlatBlockEnv09.constants ``RoseTree =
      some roseFlatFamily09.toVConstant := rfl
  have hAux : roseFlatBlockEnv09.constants roseFlatAuxName09 =
      some roseFlatAuxFamily09.toVConstant := rfl
  exact ⟨_, by type_tac⟩

/-! ### Exact flattened analyzer semantics -/

theorem roseFlatNodeSemantic09 :
    let constructor := CheckedCtor.ofBlock roseFlatDecl09 roseFlatNode09
    checkedBlockFieldsWF listFinalEnv07 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      listFinalEnv07.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock roseFlatDecl09 roseFlatNode09).fields =
      [.bvar 0,
        .app (.const roseFlatAuxName09 [.param 0]) (.bvar 1)] by rfl]
  rw [show (CheckedCtor.ofBlock roseFlatDecl09 roseFlatNode09).recursiveAt =
      [none, some ({
        fieldIndex := 1
        binders := []
        targetType := 1
        indices := [] } : RecArg)] by rfl]
  rw [show (CheckedCtor.ofBlock roseFlatDecl09 roseFlatNode09).resultIndices =
      [] by rfl]
  exact ⟨
    ⟨⟨.succ (.param 0), .bvar .zero, .inr (VLevel.le_refl _)⟩,
      ⟨⟨rfl, trivial, .nil⟩, trivial⟩⟩,
    .nil⟩

theorem roseFlatNilSemantic09 :
    let constructor := CheckedCtor.ofBlock roseFlatDecl09 roseFlatNil09
    checkedBlockFieldsWF listFinalEnv07 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      listFinalEnv07.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock roseFlatDecl09 roseFlatNil09).fields =
      [] by rfl]
  rw [show (CheckedCtor.ofBlock roseFlatDecl09 roseFlatNil09).recursiveAt =
      [] by rfl]
  rw [show (CheckedCtor.ofBlock roseFlatDecl09 roseFlatNil09).resultIndices =
      [] by rfl]
  exact ⟨trivial, .nil⟩

theorem roseFlatConsSemantic09 :
    let constructor := CheckedCtor.ofBlock roseFlatDecl09 roseFlatCons09
    checkedBlockFieldsWF listFinalEnv07 1 (.succ (.param 0)) [[], []]
        constructor.fields constructor.recursiveAt
        [.sort (.succ (.param 0))] 0 ∧
      listFinalEnv07.SpineWF 1
        (constructor.fields.reverse ++ [.sort (.succ (.param 0))])
        (VExpr.forallN (VExpr.liftTelN constructor.fields.length [] 0)
          (.sort (.succ (.param 0))))
        constructor.resultIndices (.sort (.succ (.param 0))) := by
  dsimp only
  rw [show (CheckedCtor.ofBlock roseFlatDecl09 roseFlatCons09).fields =
      [.app (.const ``RoseTree [.param 0]) (.bvar 0),
        .app (.const roseFlatAuxName09 [.param 0]) (.bvar 1)] by rfl]
  rw [show (CheckedCtor.ofBlock roseFlatDecl09 roseFlatCons09).recursiveAt =
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
  rw [show (CheckedCtor.ofBlock roseFlatDecl09 roseFlatCons09).resultIndices =
      [] by rfl]
  exact ⟨
    ⟨⟨rfl, trivial, .nil⟩,
      ⟨⟨rfl, trivial, .nil⟩, trivial⟩⟩,
    .nil⟩

/-- The exact analyzer selected inside the real flattened execution is
semantically valid in the original List model. -/
theorem roseFlatCheckedBlockWF09 :
    roseNestedC.generation.block.checked.WF listFinalEnv07
      roseNestedC.generation.validated.resultLevel := by
  have hresult : roseNestedC.generation.validated.resultLevel =
      .succ (.param 0) := by native_decide
  have hparams : roseNestedC.generation.block.checked.params =
      [.sort (.succ (.param 0))] := by native_decide
  have hindices :
      roseNestedC.generation.block.checked.families.indices =
        [[], []] := by native_decide
  have hlevels :
      roseNestedC.generation.block.checked.families.resultLevels =
        [.succ (.param 0), .succ (.param 0)] := by native_decide
  have hconstructors :
      roseNestedC.generation.block.checked.families.constructors =
        [roseFlatFamily09.ctors.map
            (CheckedCtor.ofBlock roseFlatDecl09),
          roseFlatAuxFamily09.ctors.map
            (CheckedCtor.ofBlock roseFlatDecl09)] := by native_decide
  have huvars :
      roseNestedC.generation.block.normalization.view.uvars = 1 := by
    native_decide
  unfold CheckedBlock.WF checkedFamilyListsWF
  rw [hresult, hindices, hlevels, hconstructors]
  simp only [checkedFamilyListsWF]
  rw [huvars, hparams]
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
  · exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
  · intro constructor member
    simp [roseFlatFamily09] at member
    rcases member with rfl
    exact roseFlatNodeSemantic09
  · exact ⟨⟨_, VEnv.HasType.sort (by decide)⟩, trivial⟩
  · refine ⟨?_, trivial⟩
    intro constructor member
    simp [roseFlatAuxFamily09] at member
    rcases member with rfl | rfl
    · exact roseFlatNilSemantic09
    · exact roseFlatConsSemantic09

/-! ### Kernel-source translations for the retained flat candidate -/

/-- First source family emitted by the implementation's real nested
flattening pass. -/
abbrev roseFlatKernelFamily09 : InductiveType :=
  roseEnvironmentInductiveExecution.2.nested.types[0]!

/-- Generated auxiliary source family emitted by that same pass. -/
abbrev roseFlatKernelAuxFamily09 : InductiveType :=
  roseEnvironmentInductiveExecution.2.nested.types[1]!

abbrev roseFlatKernelNode09 : Constructor :=
  roseFlatKernelFamily09.ctors[0]!

abbrev roseFlatKernelNil09 : Constructor :=
  roseFlatKernelAuxFamily09.ctors[0]!

abbrev roseFlatKernelCons09 : Constructor :=
  roseFlatKernelAuxFamily09.ctors[1]!

/-- Specialize the concrete source node's nested `List (RoseTree α)` field
while preserving its exact kernel binder names and binder information. -/
def roseFlatSpecializeNode09 : Expr → Expr
  | .forallE alphaName alphaType
      (.forallE valueName valueType
        (.forallE nestedName _ result nestedBinderInfo) valueBinderInfo)
      alphaBinderInfo =>
    .forallE alphaName alphaType
      (.forallE valueName valueType
        (.forallE nestedName
          (.app (.const roseFlatAuxName09 [.param `u]) (.bvar 1))
          result nestedBinderInfo)
        valueBinderInfo)
      alphaBinderInfo
  | expr => expr

/-- Rename the result family of the concrete auxiliary nil constructor. -/
def roseFlatSpecializeNil09 : Expr → Expr
  | .forallE alphaName alphaType _ alphaBinderInfo =>
      .forallE alphaName alphaType
        (.app (.const roseFlatAuxName09 [.param `u]) (.bvar 0))
        alphaBinderInfo
  | expr => expr

/-- Specialize the generic `List.cons` element domain to `RoseTree α` while
preserving its exact kernel binder names and binder information. -/
def roseFlatSpecializeCons09 : Expr → Expr
  | .forallE alphaName alphaType
      (.forallE headName _
        (.forallE tailName _ _ tailBinderInfo) headBinderInfo)
      alphaBinderInfo =>
    .forallE alphaName alphaType
      (.forallE headName
        (.app (.const ``RoseTree [.param `u]) (.bvar 0))
        (.forallE tailName
          (.app (.const roseFlatAuxName09 [.param `u]) (.bvar 1))
          (.app (.const roseFlatAuxName09 [.param `u]) (.bvar 2))
          tailBinderInfo)
        headBinderInfo)
      alphaBinderInfo
  | expr => expr

def roseFlatImplicitFamily09 : Expr → Expr
  | .forallE name type body _ =>
      .forallE name type body .implicit
  | expr => expr

private def roseFlatBinderInfoEq : BinderInfo → BinderInfo → Bool
  | .default, .default
  | .implicit, .implicit
  | .strictImplicit, .strictImplicit
  | .instImplicit, .instImplicit => true
  | _, _ => false

private theorem roseFlatBinderInfoEq_sound
    (left right : BinderInfo)
    (h : roseFlatBinderInfoEq left right = true) : left = right := by
  cases left <;> cases right <;> simp_all [roseFlatBinderInfoEq]

/-- Sound structural equality for the metadata-free kernel expressions in
the retained flattened inventory. -/
private def roseFlatExprEq : Expr → Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i, .fvar j => i == j
  | .mvar i, .mvar j => i == j
  | .sort u, .sort v => u == v
  | .const n us, .const n' us' => n == n' && us == us'
  | .app f a, .app f' a' => roseFlatExprEq f f' && roseFlatExprEq a a'
  | .lam n t b bi, .lam n' t' b' bi' =>
      n == n' && roseFlatExprEq t t' && roseFlatExprEq b b' &&
        roseFlatBinderInfoEq bi bi'
  | .forallE n t b bi, .forallE n' t' b' bi' =>
      n == n' && roseFlatExprEq t t' && roseFlatExprEq b b' &&
        roseFlatBinderInfoEq bi bi'
  | .letE n t v b nd, .letE n' t' v' b' nd' =>
      n == n' && roseFlatExprEq t t' && roseFlatExprEq v v' &&
        roseFlatExprEq b b' && nd == nd'
  | .lit a, .lit b => a == b
  | .proj n i s, .proj n' i' s' =>
      n == n' && i == i' && roseFlatExprEq s s'
  | _, _ => false

private theorem roseFlatExprEq_sound :
    ∀ left right, roseFlatExprEq left right = true → left = right := by
  intro left right h
  induction left generalizing right with
  | bvar i =>
      cases right <;> simp_all [roseFlatExprEq, beq_iff_eq]
  | fvar i =>
      cases right <;> simp_all [roseFlatExprEq, beq_iff_eq]
  | mvar i =>
      cases right <;> simp_all [roseFlatExprEq, beq_iff_eq]
  | sort u =>
      cases right <;> simp_all [roseFlatExprEq, beq_iff_eq]
  | const n us =>
      cases right <;> simp_all [roseFlatExprEq, beq_iff_eq]
  | app fn arg fnIH argIH =>
      cases right with
      | app fn' arg' =>
          simp only [roseFlatExprEq, Bool.and_eq_true] at h
          rw [fnIH fn' h.1, argIH arg' h.2]
      | _ => simp_all [roseFlatExprEq]
  | lam name type body binderInfo typeIH bodyIH =>
      cases right with
      | lam name' type' body' binderInfo' =>
          simp only [roseFlatExprEq, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1.1.1, typeIH type' h.1.1.2, bodyIH body' h.1.2,
            roseFlatBinderInfoEq_sound _ _ h.2]
      | _ => simp_all [roseFlatExprEq]
  | forallE name type body binderInfo typeIH bodyIH =>
      cases right with
      | forallE name' type' body' binderInfo' =>
          simp only [roseFlatExprEq, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1.1.1, typeIH type' h.1.1.2, bodyIH body' h.1.2,
            roseFlatBinderInfoEq_sound _ _ h.2]
      | _ => simp_all [roseFlatExprEq]
  | letE name type value body nondep typeIH valueIH bodyIH =>
      cases right with
      | letE name' type' value' body' nondep' =>
          simp only [roseFlatExprEq, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1.1.1.1, typeIH type' h.1.1.1.2,
            valueIH value' h.1.1.2, bodyIH body' h.1.2, h.2]
      | _ => simp_all [roseFlatExprEq]
  | lit literal =>
      cases right <;> simp_all [roseFlatExprEq, beq_iff_eq]
  | mdata data expr exprIH =>
      cases right <;> simp_all [roseFlatExprEq]
  | proj typeName idx struct structIH =>
      cases right with
      | proj typeName' idx' struct' =>
          simp only [roseFlatExprEq, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1.1, h.1.2, structIH struct' h.2]
      | _ => simp_all [roseFlatExprEq]

private def roseFlatConstructorEq (left right : Constructor) : Bool :=
  left.name == right.name && roseFlatExprEq left.type right.type

private theorem roseFlatConstructorEq_sound
    (left right : Constructor)
    (h : roseFlatConstructorEq left right = true) : left = right := by
  cases left with
  | mk leftName leftType =>
    cases right with
    | mk rightName rightType =>
      simp only [roseFlatConstructorEq, Bool.and_eq_true,
        beq_iff_eq] at h
      rw [h.1, roseFlatExprEq_sound _ _ h.2]

private def roseFlatConstructorListEq :
    List Constructor → List Constructor → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      roseFlatConstructorEq left right &&
        roseFlatConstructorListEq lefts rights
  | _, _ => false

private theorem roseFlatConstructorListEq_sound :
    ∀ left right, roseFlatConstructorListEq left right = true →
      left = right := by
  intro left right h
  induction left generalizing right with
  | nil => cases right <;> simp_all [roseFlatConstructorListEq]
  | cons head tail ih =>
      cases right with
      | nil => simp [roseFlatConstructorListEq] at h
      | cons head' tail' =>
        simp only [roseFlatConstructorListEq, Bool.and_eq_true] at h
        rw [roseFlatConstructorEq_sound _ _ h.1, ih tail' h.2]

private def roseFlatInductiveTypeEq
    (left right : InductiveType) : Bool :=
  left.name == right.name && roseFlatExprEq left.type right.type &&
    roseFlatConstructorListEq left.ctors right.ctors

private theorem roseFlatInductiveTypeEq_sound
    (left right : InductiveType)
    (h : roseFlatInductiveTypeEq left right = true) : left = right := by
  cases left with
  | mk leftName leftType leftCtors =>
    cases right with
    | mk rightName rightType rightCtors =>
      simp only [roseFlatInductiveTypeEq, Bool.and_eq_true,
        beq_iff_eq] at h
      rw [h.1.1, roseFlatExprEq_sound _ _ h.1.2,
        roseFlatConstructorListEq_sound _ _ h.2]

private def roseFlatInductiveTypeListEq :
    List InductiveType → List InductiveType → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      roseFlatInductiveTypeEq left right &&
        roseFlatInductiveTypeListEq lefts rights
  | _, _ => false

private theorem roseFlatInductiveTypeListEq_sound :
    ∀ left right, roseFlatInductiveTypeListEq left right = true →
      left = right := by
  intro left right h
  induction left generalizing right with
  | nil => cases right <;> simp_all [roseFlatInductiveTypeListEq]
  | cons head tail ih =>
      cases right with
      | nil => simp [roseFlatInductiveTypeListEq] at h
      | cons head' tail' =>
        simp only [roseFlatInductiveTypeListEq, Bool.and_eq_true] at h
        rw [roseFlatInductiveTypeEq_sound _ _ h.1, ih tail' h.2]

theorem roseFlatKernelFamilyType09_eq :
    roseFlatKernelFamily09.type = roseInfo09.type := by
  apply roseFlatExprEq_sound
  native_decide

theorem roseFlatKernelAuxFamilyType09_eq :
    roseFlatKernelAuxFamily09.type =
      roseFlatImplicitFamily09 listInfo07.type := by
  apply roseFlatExprEq_sound
  native_decide

theorem roseFlatKernelNodeType09_eq :
    roseFlatKernelNode09.type =
      roseFlatSpecializeNode09 roseNodeInfo09.type := by
  apply roseFlatExprEq_sound
  native_decide

theorem roseFlatKernelNilType09_eq :
    roseFlatKernelNil09.type =
      roseFlatSpecializeNil09 listNilInfo07.type := by
  apply roseFlatExprEq_sound
  native_decide

theorem roseFlatKernelConsType09_eq :
    roseFlatKernelCons09.type =
      roseFlatSpecializeCons09 listConsInfo07.type := by
  apply roseFlatExprEq_sound
  native_decide

theorem roseFlatKernelTypes09_eq :
    roseEnvironmentInductiveExecution.2.nested.types =
      [roseFlatKernelFamily09, roseFlatKernelAuxFamily09] := by
  apply roseFlatInductiveTypeListEq_sound
  native_decide

theorem roseFlatKernelFamilyCtors09_eq :
    roseFlatKernelFamily09.ctors = [roseFlatKernelNode09] := by
  apply roseFlatConstructorListEq_sound
  native_decide

theorem roseFlatKernelAuxFamilyCtors09_eq :
    roseFlatKernelAuxFamily09.ctors =
      [roseFlatKernelNil09, roseFlatKernelCons09] := by
  apply roseFlatConstructorListEq_sound
  native_decide

theorem roseFlatFamilySourceTr09 :
    TrExprS listFinalEnv07 [`u] [] roseFlatKernelFamily09.type
      roseFlatFamily09.type := by
  rw [roseFlatKernelFamilyType09_eq]
  have shape : TrTypeExpr listFinalEnv07
      [`u] [] roseInfo09.type
      roseFlatFamily09.type := by
    tr_type_expr_tac
  obtain ⟨_, familyWF⟩ := roseFlatFamilyWF09
  exact shape.to_trExprS listFinalOrdered07 trivial ⟨_, familyWF⟩

theorem roseFlatAuxFamilySourceTr09 :
    TrExprS listFinalEnv07 [`u] [] roseFlatKernelAuxFamily09.type
      roseFlatAuxFamily09.type := by
  rw [roseFlatKernelAuxFamilyType09_eq]
  have shape : TrTypeExpr listFinalEnv07
      [`u] []
      (roseFlatImplicitFamily09 listInfo07.type)
      roseFlatAuxFamily09.type := by
    tr_type_expr_tac
  obtain ⟨_, familyWF⟩ := roseFlatAuxFamilyPreWF09
  exact shape.to_trExprS listFinalOrdered07 trivial
    ⟨_, familyWF⟩

theorem roseFlatNodeSourceTr09 :
    TrExprS roseFlatBlockEnv09 [`u] [] roseFlatKernelNode09.type
      roseFlatNode09.type := by
  rw [roseFlatKernelNodeType09_eq]
  have hRose : roseFlatBlockEnv09.constants ``RoseTree =
      some roseFlatFamily09.toVConstant := rfl
  have hAux : roseFlatBlockEnv09.constants roseFlatAuxName09 =
      some roseFlatAuxFamily09.toVConstant := rfl
  have shape : TrTypeExpr roseFlatBlockEnv09
      [`u] [] (roseFlatSpecializeNode09 roseNodeInfo09.type)
      roseFlatNode09.type := by
    dsimp [roseNodeInfo09, roseFlatSpecializeNode09]
    tr_type_expr_tac
  obtain ⟨_, nodeWF⟩ := roseFlatNodeWF09
  exact shape.to_trExprS roseFlatBlockEnvOrdered09 trivial ⟨_, nodeWF⟩

theorem roseFlatNilSourceTr09 :
    TrExprS roseFlatBlockEnv09 [`u] [] roseFlatKernelNil09.type
      roseFlatNil09.type := by
  rw [roseFlatKernelNilType09_eq]
  have hRose : roseFlatBlockEnv09.constants ``RoseTree =
      some roseFlatFamily09.toVConstant := rfl
  have hAux : roseFlatBlockEnv09.constants roseFlatAuxName09 =
      some roseFlatAuxFamily09.toVConstant := rfl
  have shape : TrTypeExpr roseFlatBlockEnv09
      [`u] [] (roseFlatSpecializeNil09 listNilInfo07.type)
      roseFlatNil09.type := by
    dsimp [listNilInfo07, roseFlatSpecializeNil09]
    tr_type_expr_tac
  obtain ⟨_, nilWF⟩ := roseFlatNilWF09
  exact shape.to_trExprS roseFlatBlockEnvOrdered09 trivial ⟨_, nilWF⟩

theorem roseFlatConsSourceTr09 :
    TrExprS roseFlatBlockEnv09 [`u] [] roseFlatKernelCons09.type
      roseFlatCons09.type := by
  rw [roseFlatKernelConsType09_eq]
  have hRose : roseFlatBlockEnv09.constants ``RoseTree =
      some roseFlatFamily09.toVConstant := rfl
  have hAux : roseFlatBlockEnv09.constants roseFlatAuxName09 =
      some roseFlatAuxFamily09.toVConstant := rfl
  have shape : TrTypeExpr roseFlatBlockEnv09
      [`u] [] (roseFlatSpecializeCons09 listConsInfo07.type)
      roseFlatCons09.type := by
    simp only [listConsInfo07]
    simp only [roseFlatSpecializeCons09]
    tr_type_expr_tac
  obtain ⟨_, consWF⟩ := roseFlatConsWF09
  exact shape.to_trExprS roseFlatBlockEnvOrdered09 trivial ⟨_, consWF⟩

/-- Candidate-independent family roots for the exact source order retained
by the real flattened execution. -/
def roseFlatCandidateFamilySources09 :
    CandidateBlockFamilyTypeSourceListInput listFinalEnv07 [`u]
      roseEnvironmentInductiveExecution.2.nested.types
      roseNestedC.elim.flat.types := by
  rw [roseFlatKernelTypes09_eq, roseFlatDecl09_eq]
  exact .cons {
      name_eq := by native_decide
      uvars_eq := rfl
      source_tr := roseFlatFamilySourceTr09 }
    (.cons {
      name_eq := by native_decide
      uvars_eq := rfl
      source_tr := roseFlatAuxFamilySourceTr09 } .nil)

/-- Candidate-independent constructor roots for both flattened families,
interpreted in the exact environment after both family headers are staged. -/
def roseFlatFamilyConstructorSources09 :
    CandidateConstructorSourceListInput roseFlatBlockEnv09 [`u]
      roseFlatKernelFamily09.ctors roseFlatFamily09.ctors := by
  rw [roseFlatKernelFamilyCtors09_eq]
  exact .cons {
    name_eq := by native_decide
    uvars_eq := rfl
    source_tr := roseFlatNodeSourceTr09 } .nil

def roseFlatAuxConstructorSources09 :
    CandidateConstructorSourceListInput roseFlatBlockEnv09 [`u]
      roseFlatKernelAuxFamily09.ctors roseFlatAuxFamily09.ctors := by
  rw [roseFlatKernelAuxFamilyCtors09_eq]
  exact .cons {
      name_eq := by native_decide
      uvars_eq := rfl
      source_tr := roseFlatNilSourceTr09 }
    (.cons {
      name_eq := by native_decide
      uvars_eq := rfl
      source_tr := roseFlatConsSourceTr09 } .nil)

def roseFlatCandidateConstructorSources09 :
    CandidateBlockConstructorSourceListInput roseFlatBlockEnv09 [`u]
      roseEnvironmentInductiveExecution.2.nested.types
      roseNestedC.elim.flat.types := by
  rw [roseFlatKernelTypes09_eq, roseFlatDecl09_eq]
  exact .cons roseFlatFamilyConstructorSources09
    (.cons roseFlatAuxConstructorSources09 .nil)

/-! ## Retained flattened candidate semantics -/

/-- The source context of the real outer RoseTree execution. -/
abbrev roseFlatCandidateContext09 :=
  AddInductive.Context.forInductive roseInputKernelEnv09 [`u] false false {}

/-- The normalization execution retained below the produced recursor-shape
candidate. -/
abbrev roseFlatNormalizationExecution09 :=
  roseFlatRecursorShapeCandidate.execution.eliminationExecution.normalization

/-- The producer hierarchy immediately above flattened block generation. -/
abbrev roseFlatProducedGeneration09 :=
  roseFlatRecursorShapeCandidate.eliminationBase.base

/-- The exact residual readiness boundary for the flattened RoseTree
candidate.  All current-model and host-staging obligations are derived below;
only the positional `List` constructor invariant over arbitrary future Theory
extensions remains explicit. -/
structure RoseFlatCandidateReadiness09 where
  constructorNumParams_mono :
    ∀ {venv' : VEnv}, listFinalEnv07 ≤ venv' →
      ∀ (view : VStructureView) (info : ConstructorVal),
        view.WF venv' →
        view.fields ≠ [] →
        roseInputKernelEnv09.find? view.constructorName =
          some (.ctorInfo info) →
        info.numParams = view.nparams

theorem roseFlatValidationEnv09 :
    roseFlatNormalizationExecution09.validationContext.env =
      roseFlatCandidateContext09.env := by
  exact roseFlatNormalizationExecution09.validationContext_env
    roseFlatProducedGeneration09.producedExecution (by native_decide)

/-! ### Completed `List` readiness decomposition -/

theorem roseInputKernelEnvNoProjectionReady09 (name : Name) :
    roseInputKernelEnv09.isProjectionReadyStructure name = false := by
  simp only [roseInputKernelEnv09,
    Kernel.Environment.isProjectionReadyStructure,
    Kernel.Environment.ofConstants]
  simp only [listMapWF07.find?'_eq_find?]
  simp only [listMap07, listCtorMapWF07.find?_insert]
  simp only [listCtorMap07, listNilMapWF07.find?_insert]
  simp only [listNilMap07, listTypeMapWF07.find?_insert]
  simp only [listTypeMap07, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  by_cases hRec : ``List.rec = name
  · subst name
    simp [listRecInfo07]
  · by_cases hCons : ``List.cons = name
    · subst name
      simp [hRec, listConsInfo07]
    · by_cases hNil : ``List.nil = name
      · subst name
        simp [hRec, hCons, listNilInfo07]
      · by_cases hList : ``List = name
        · subst name
          simp [hRec, hCons, hNil, listInfo07]
        · simp [hRec, hCons, hNil, hList, SMap.find?]

theorem roseInputKernelEnvNoStructureEta09 (name : Name) :
    roseInputKernelEnv09.isNonRecStructure name = false := by
  simp only [roseInputKernelEnv09, Kernel.Environment.isNonRecStructure,
    Kernel.Environment.ofConstants, Kernel.Environment.find?]
  simp only [listMapWF07.find?'_eq_find?]
  simp only [listMap07, listCtorMapWF07.find?_insert]
  simp only [listCtorMap07, listNilMapWF07.find?_insert]
  simp only [listNilMap07, listTypeMapWF07.find?_insert]
  simp only [listTypeMap07, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  by_cases hRec : ``List.rec = name
  · subst name
    simp [listRecInfo07]
  · by_cases hCons : ``List.cons = name
    · subst name
      simp [hRec, listConsInfo07]
    · by_cases hNil : ``List.nil = name
      · subst name
        simp [hRec, hCons, listNilInfo07]
      · by_cases hList : ``List = name
        · subst name
          simp [hRec, hCons, hNil, listInfo07]
        · simp [hRec, hCons, hNil, hList, SMap.find?]

theorem roseListHasPrimitives09 : VEnv.HasPrimitives listFinalEnv07 := by
  apply VEnv.HasPrimitives.of_avoids
  intro name member
  simp only [VEnv.reflectedPrimitiveNames, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> rfl

theorem roseListSafePrimitives09 :
    roseInputKernelEnv09.find? name = some info →
      Kernel.Environment.primitives.contains name →
      info.safety = .safe ∧ info.levelParams = [] := by
  intro hfind hprimitive
  change listMap07.find?' name = some info at hfind
  rw [listMapWF07.find?'_eq_find?, listMap07,
    listCtorMapWF07.find?_insert] at hfind
  split at hfind
  · rename_i heq
    have : name = ``List.rec := (LawfulBEq.eq_of_beq heq).symm
    subst name
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprimitive
    simp +decide [NameSet.contains] at hprimitive
  · rw [listCtorMap07, listNilMapWF07.find?_insert] at hfind
    split at hfind
    · rename_i heq
      have : name = ``List.cons := (LawfulBEq.eq_of_beq heq).symm
      subst name
      simp [Kernel.Environment.primitives, NameSet.ofList] at hprimitive
      simp +decide [NameSet.contains] at hprimitive
    · rw [listNilMap07, listTypeMapWF07.find?_insert] at hfind
      split at hfind
      · rename_i heq
        have : name = ``List.nil := (LawfulBEq.eq_of_beq heq).symm
        subst name
        simp [Kernel.Environment.primitives, NameSet.ofList] at hprimitive
        simp +decide [NameSet.contains] at hprimitive
      · rw [listTypeMap07,
          SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
          at hfind
        split at hfind
        · rename_i heq
          have : name = ``List := (LawfulBEq.eq_of_beq heq).symm
          subst name
          simp [Kernel.Environment.primitives, NameSet.ofList] at hprimitive
          simp +decide [NameSet.contains] at hprimitive
        · simp [SMap.find?] at hfind

theorem RoseFlatCandidateReadiness09.listProjectionReady
    (self : RoseFlatCandidateReadiness09) :
    ProjectionReady roseInputKernelEnv09 listFinalEnv07 where
  infer name _info _hfind hready := by
    rw [roseInputKernelEnvNoProjectionReady09 name] at hready
    contradiction
  constructorHead name info hfind := by
    change listMap07.find?' name = some (.ctorInfo info) at hfind
    rw [listMapWF07.find?'_eq_find?] at hfind
    exact listMapConstructorHead07 hfind
  constructorNumParams view info hview hfields hfind :=
    self.constructorNumParams_mono VEnv.LE.rfl view info hview hfields
      hfind
  constructorNumParams_mono := self.constructorNumParams_mono

theorem roseListStructureEtaReady09 :
    StructureEtaReady roseInputKernelEnv09 listFinalEnv07 :=
  StructureEtaReady.of_no_nonRecStructure
    roseInputKernelEnvNoStructureEta09

def roseListVEnvs09 : VEnvs where
  venv _ := listFinalEnv07

theorem RoseFlatCandidateReadiness09.listVEnvsWF
    (self : RoseFlatCandidateReadiness09) :
    roseListVEnvs09.WF roseInputKernelEnv09 where
  tr := by
    intro safety
    change TrEnv' safety listMap07 false listFinalEnv07
    exact .induct listAddInduct07 .empty
  hasPrimitives := roseListHasPrimitives09
  safePrimitives := roseListSafePrimitives09
  mono := fun _ => .rfl
  projectionReady := self.listProjectionReady
  structureEtaReady := roseListStructureEtaReady09

def RoseFlatCandidateReadiness09.preFamily
    (self : RoseFlatCandidateReadiness09) :
    TypeChecker.CandidateSemanticStage
      { roseFlatCandidateContext09 with lctx := {} } listFinalEnv07 [`u] where
  contextRun := TypeChecker.CandidateContextRun.root self.listVEnvsWF rfl
    (by native_decide)
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

abbrev roseFlatMainInfo09 : InductiveVal :=
  roseFlatNormalizationExecution09.declaredInfos[0]!

abbrev roseFlatAuxInfo09 : InductiveVal :=
  roseFlatNormalizationExecution09.declaredInfos[1]!

private theorem list_eq_get_pair_of_length_two09 [Inhabited α]
    (xs : List α) (length_eq : xs.length = 2) :
    xs = [xs[0]!, xs[1]!] := by
  cases xs with
  | nil => simp at length_eq
  | cons x xs =>
    cases xs with
    | nil => simp at length_eq
    | cons y xs =>
      cases xs with
      | nil => rfl
      | cons z xs => simp at length_eq

theorem roseFlatDeclaredInfos09 :
    roseFlatNormalizationExecution09.declaredInfos =
      [roseFlatMainInfo09, roseFlatAuxInfo09] := by
  apply list_eq_get_pair_of_length_two09
  native_decide

theorem roseFlatMainInfoName09 : roseFlatMainInfo09.name = ``RoseTree := by
  native_decide

theorem roseFlatMainInfoShape09 :
    roseFlatMainInfo09.numIndices = 0 ∧
      roseFlatMainInfo09.ctors = [``RoseTree.node] := by
  native_decide

theorem roseFlatMainInfoIsRec09 : roseFlatMainInfo09.isRec = true := by
  native_decide

theorem roseFlatAuxInfoName09 :
    roseFlatAuxInfo09.name = roseFlatAuxName09 := by
  native_decide

theorem roseFlatAuxInfoShape09 :
    roseFlatAuxInfo09.numIndices = 0 ∧
      roseFlatAuxInfo09.ctors =
        [roseFlatAuxName09 ++ `nil, roseFlatAuxName09 ++ `cons] := by
  native_decide

def roseFlatHostFirstFamilyMap09 : ConstMap :=
  listMap07.insert roseFlatMainInfo09.name (.inductInfo roseFlatMainInfo09)

def roseFlatHostFamilyMap09 : ConstMap :=
  roseFlatHostFirstFamilyMap09.insert roseFlatAuxInfo09.name
    (.inductInfo roseFlatAuxInfo09)

theorem roseFlatMainInfoFresh09 :
    listMap07.find? roseFlatMainInfo09.name = none := by
  rw [roseFlatMainInfoName09]
  exact roseTypeFresh09

theorem roseFlatHostFirstFamilyMapWF09 :
    roseFlatHostFirstFamilyMap09.WF :=
  listMapWF07.insert _ _ roseFlatMainInfoFresh09

theorem roseFlatAuxInfoFresh09 :
    roseFlatHostFirstFamilyMap09.find? roseFlatAuxInfo09.name = none := by
  rw [roseFlatHostFirstFamilyMap09, listMapWF07.find?_insert,
    roseFlatMainInfoName09, roseFlatAuxInfoName09,
    listMap07, listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [roseFlatAuxName09, SMap.find?]

theorem roseFlatHostFamilyMapWF09 : roseFlatHostFamilyMap09.WF :=
  roseFlatHostFirstFamilyMapWF09.insert _ _ roseFlatAuxInfoFresh09

theorem roseFlatFamilyEnvConstants09 :
    roseFlatNormalizationExecution09.familyEnv.constants =
      roseFlatHostFamilyMap09 := by
  rw [roseFlatNormalizationExecution09.familyEnv_constants,
    roseFlatDeclaredInfos09, roseFlatValidationEnv09]
  rfl

def roseFlatHostFirstFamilyEnv09 : Kernel.Environment :=
  roseInputKernelEnv09.add (.inductInfo roseFlatMainInfo09)

def roseFlatHostFamilyEnv09 : Kernel.Environment :=
  roseFlatHostFirstFamilyEnv09.add (.inductInfo roseFlatAuxInfo09)

theorem roseFlatMainInfoHostFresh09 :
    roseInputKernelEnv09.find? roseFlatMainInfo09.name = none := by
  change listMap07.find?' roseFlatMainInfo09.name = none
  rw [listMapWF07.find?'_eq_find?]
  exact roseFlatMainInfoFresh09

theorem roseFlatAuxInfoHostFresh09 :
    roseFlatHostFirstFamilyEnv09.find? roseFlatAuxInfo09.name = none := by
  change roseFlatHostFirstFamilyMap09.find?' roseFlatAuxInfo09.name = none
  rw [roseFlatHostFirstFamilyMapWF09.find?'_eq_find?]
  exact roseFlatAuxInfoFresh09

theorem roseFlatHostFirstFamilyEnvMapWF09 :
    roseFlatHostFirstFamilyEnv09.constants.WF := by
  change roseFlatHostFirstFamilyMap09.WF
  exact roseFlatHostFirstFamilyMapWF09

theorem roseFlatHostFamilyEnvConstants09 :
    roseFlatHostFamilyEnv09.constants = roseFlatHostFamilyMap09 := rfl

theorem roseFlatMainCtorHostFresh09 :
    roseInputKernelEnv09.find? ``RoseTree.node = none := by
  change listMap07.find?' ``RoseTree.node = none
  rw [listMapWF07.find?'_eq_find?, listMap07,
    listCtorMapWF07.find?_insert, listCtorMap07,
    listNilMapWF07.find?_insert, listNilMap07,
    listTypeMapWF07.find?_insert, listTypeMap07,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem roseFlatFamilyEnvNoProjectionReady09 (name : Name) :
    roseFlatNormalizationExecution09.familyEnv.isProjectionReadyStructure
      name = false := by
  have constants_eq :
      roseFlatNormalizationExecution09.familyEnv.constants =
        roseFlatHostFamilyEnv09.constants := by
    rw [roseFlatFamilyEnvConstants09, roseFlatHostFamilyEnvConstants09]
  suffices roseFlatHostFamilyEnv09.isProjectionReadyStructure name = false by
    simpa only [Kernel.Environment.isProjectionReadyStructure, constants_eq]
  change (roseFlatHostFirstFamilyEnv09.add
    (.inductInfo roseFlatAuxInfo09)).isProjectionReadyStructure name = false
  by_cases hAux : roseFlatAuxInfo09.name = name
  · subst name
    apply Environment.isProjectionReadyStructure_add_inductInfo_self
      roseFlatHostFirstFamilyEnvMapWF09 roseFlatAuxInfo09
      roseFlatAuxInfoHostFresh09
    rw [roseFlatAuxInfoShape09.2]
    decide
  · rw [Environment.isProjectionReadyStructure_add_inductInfo
      roseFlatHostFirstFamilyEnvMapWF09 roseFlatAuxInfo09
      roseFlatAuxInfoHostFresh09 hAux]
    change (roseInputKernelEnv09.add
      (.inductInfo roseFlatMainInfo09)).isProjectionReadyStructure name =
        false
    by_cases hMain : roseFlatMainInfo09.name = name
    · subst name
      apply Environment.isProjectionReadyStructure_add_inductInfo_self_of_ctor_absent
        listMapWF07 roseFlatMainInfo09 roseFlatMainInfoHostFresh09
        ``RoseTree.node roseFlatMainInfoShape09.2
        roseFlatMainCtorHostFresh09
    · rw [Environment.isProjectionReadyStructure_add_inductInfo
        listMapWF07 roseFlatMainInfo09 roseFlatMainInfoHostFresh09 hMain]
      exact roseInputKernelEnvNoProjectionReady09 name

theorem roseFlatFamilyEnvNoStructureEta09 (name : Name) :
    roseFlatNormalizationExecution09.familyEnv.isNonRecStructure name =
      false := by
  have constants_eq :
      roseFlatNormalizationExecution09.familyEnv.constants =
        roseFlatHostFamilyEnv09.constants := by
    rw [roseFlatFamilyEnvConstants09, roseFlatHostFamilyEnvConstants09]
  suffices roseFlatHostFamilyEnv09.isNonRecStructure name = false by
    simpa only [Kernel.Environment.isNonRecStructure,
      Kernel.Environment.find?, constants_eq]
  change (roseFlatHostFirstFamilyEnv09.add
    (.inductInfo roseFlatAuxInfo09)).isNonRecStructure name = false
  by_cases hAux : roseFlatAuxInfo09.name = name
  · subst name
    apply Environment.isNonRecStructure_add_inductInfo_self
      roseFlatHostFirstFamilyEnvMapWF09 roseFlatAuxInfo09
      roseFlatAuxInfoHostFresh09
    rw [roseFlatAuxInfoShape09.2]
    decide
  · rw [Environment.isNonRecStructure_add_inductInfo
      roseFlatHostFirstFamilyEnvMapWF09 roseFlatAuxInfo09
      roseFlatAuxInfoHostFresh09 hAux]
    change (roseInputKernelEnv09.add
      (.inductInfo roseFlatMainInfo09)).isNonRecStructure name = false
    by_cases hMain : roseFlatMainInfo09.name = name
    · subst name
      exact Environment.isNonRecStructure_add_inductInfo_self_of_isRec
        listMapWF07 roseFlatMainInfo09 roseFlatMainInfoHostFresh09
        roseFlatMainInfoIsRec09
    · rw [Environment.isNonRecStructure_add_inductInfo listMapWF07
        roseFlatMainInfo09 roseFlatMainInfoHostFresh09 hMain]
      exact roseInputKernelEnvNoStructureEta09 name

theorem roseFlatFamilyEnvCtorFind09
    (hfind : roseFlatNormalizationExecution09.familyEnv.find? name =
      some (.ctorInfo info)) :
    roseInputKernelEnv09.find? name = some (.ctorInfo info) := by
  have constants_eq :
      roseFlatNormalizationExecution09.familyEnv.constants =
        roseFlatHostFamilyEnv09.constants := by
    rw [roseFlatFamilyEnvConstants09, roseFlatHostFamilyEnvConstants09]
  have hfind' : roseFlatHostFamilyEnv09.find? name =
      some (.ctorInfo info) := by
    change roseFlatHostFamilyEnv09.constants.find?' name = _
    change roseFlatNormalizationExecution09.familyEnv.constants.find?'
      name = _ at hfind
    rw [← constants_eq]
    exact hfind
  change (roseFlatHostFirstFamilyEnv09.add
    (.inductInfo roseFlatAuxInfo09)).find? name =
      some (.ctorInfo info) at hfind'
  rw [Environment.find?_add_eq roseFlatHostFirstFamilyEnvMapWF09
    (.inductInfo roseFlatAuxInfo09) roseFlatAuxInfoHostFresh09] at hfind'
  split at hfind'
  · cases hfind'
  · change (roseInputKernelEnv09.add
      (.inductInfo roseFlatMainInfo09)).find? name =
        some (.ctorInfo info) at hfind'
    rw [Environment.find?_add_eq listMapWF07
      (.inductInfo roseFlatMainInfo09) roseFlatMainInfoHostFresh09] at hfind'
    split at hfind'
    · cases hfind'
    · exact hfind'

theorem roseListFinalToFlatBlock09 :
    listFinalEnv07 ≤ roseFlatBlockEnv09 :=
  (VEnv.addConst_le roseFlatFirstTypeEnv09_eq).trans
    (VEnv.addConst_le roseFlatBlockEnv09_eq)

theorem RoseFlatCandidateReadiness09.projectionReady
    (self : RoseFlatCandidateReadiness09) :
    ProjectionReady roseFlatNormalizationExecution09.familyEnv
      roseFlatBlockEnv09 where
  infer name _info _hfind hready := by
    rw [roseFlatFamilyEnvNoProjectionReady09 name] at hready
    contradiction
  constructorHead name info hfind := by
    have hold := roseFlatFamilyEnvCtorFind09 hfind
    change listMap07.find?' name = some (.ctorInfo info) at hold
    rw [listMapWF07.find?'_eq_find?] at hold
    exact (listMapConstructorHead07 hold).mono roseListFinalToFlatBlock09
  constructorNumParams view info hview hfields hfind :=
    self.constructorNumParams_mono roseListFinalToFlatBlock09 view info
      hview hfields (roseFlatFamilyEnvCtorFind09 hfind)
  constructorNumParams_mono hle view info hview hfields hfind :=
    self.constructorNumParams_mono (roseListFinalToFlatBlock09.trans hle)
      view info hview hfields (roseFlatFamilyEnvCtorFind09 hfind)

theorem RoseFlatCandidateReadiness09.structureEtaReady
    (_self : RoseFlatCandidateReadiness09) :
    StructureEtaReady roseFlatNormalizationExecution09.familyEnv
      roseFlatBlockEnv09 :=
  StructureEtaReady.of_no_nonRecStructure
    roseFlatFamilyEnvNoStructureEta09

/-- The exact two-stage semantic owner reconstructed from the retained outer
normalization hierarchy and the source-indexed flattened translations. -/
def roseFlatCandidateStaging09 (readiness : RoseFlatCandidateReadiness09) :
    NormalizationCandidateBlockStagingInput roseFlatCandidateContext09
      roseFlatNormalizationExecution09 listFinalEnv07 roseFlatBlockEnv09 [`u]
      roseNestedC.elim.flat where
  uvars_eq := by native_decide
  preFamily := readiness.preFamily
  familyTypes := roseFlatCandidateFamilySources09.staged
    roseFlatNormalizationExecution09.candidate.families (by
      change AddInductive.CandidateFamilyTypeListProduced _
        roseFlatNormalizationExecution09.families.candidates.familyTypes
      rw [roseFlatNormalizationExecution09.families.produced.familyTypes_eq]
      exact roseFlatNormalizationExecution09.familyTypes.produced) 9999 rfl
  terminals := CandidateBlockFamilyTerminalSortList.of_check
    roseFlatNormalizationExecution09.candidate.families (by native_decide)
  stage := by
    rw [roseFlatDecl09_eq]
    exact roseFlatStage09
  nindices_size := by native_decide
  validation_env_eq := roseFlatValidationEnv09
  validation_lparams_eq := roseFlatValidationLparams
  context_safety_eq := rfl
  isUnsafe_eq := rfl
  preMapWF := by
    change listMap07.WF
    exact listMapWF07
  names_not_primitive := by
    intro raw member
    rw [roseFlatDecl09_eq] at member
    simp [roseFlatDecl09] at member
    rcases member with rfl | rfl
    · constructor
      · simp [roseFlatFamily09, VEnv.reflectedPrimitiveNames]
      · simp [roseFlatFamily09, Kernel.Environment.primitives,
          NameSet.ofList]
        simp +decide [NameSet.contains]
    · constructor
      · simp [roseFlatAuxFamily09, roseFlatAuxName09,
          VEnv.reflectedPrimitiveNames]
      · simp [roseFlatAuxFamily09, roseFlatAuxName09,
          Kernel.Environment.primitives, NameSet.ofList]
        simp +decide [NameSet.contains]
  projectionReady := readiness.projectionReady
  structureEtaReady := readiness.structureEtaReady

def roseFlatCandidateConstructors09
    (readiness : RoseFlatCandidateReadiness09) :
    CandidateBlockConstructorStagedListInput
      (roseFlatCandidateStaging09 readiness).postFamily
      roseFlatNormalizationExecution09.candidate.families
      roseNestedC.elim.flat.types :=
  roseFlatCandidateConstructorSources09.staged
    roseFlatNormalizationExecution09.candidate.families
    roseFlatNormalizationExecution09.families.produced.constructorLists
    9999 rfl

def roseFlatStagedCandidateSemantic09
    (readiness : RoseFlatCandidateReadiness09) :
    StagedNormalizationCandidateBlockSemanticInput
      (roseFlatCandidateStaging09 readiness) where
  postFamily := (roseFlatCandidateStaging09 readiness).postFamily
  constructors := roseFlatCandidateConstructors09 readiness

/-- All retained family and constructor traces normalize by recursive
identity.  The candidate-only form of the check erases the open readiness
proofs before native evaluation. -/
theorem roseFlatCandidateIdentityCheck09
    (readiness : RoseFlatCandidateReadiness09) :
    (roseFlatStagedCandidateSemantic09 readiness).identityCheck = true := by
  change (roseFlatCandidateStaging09 readiness).familyTypes.identityCheck
    (roseFlatCandidateConstructors09 readiness) = true
  rw [CandidateBlockFamilyTypeStagedListInput.identityCheck_eq_candidate]
  native_decide

def roseFlatCandidateIdentitySemantic09
    (readiness : RoseFlatCandidateReadiness09) :
    NormalizationCandidateBlockSemanticRun listFinalEnv07
      roseFlatBlockEnv09 [`u] roseFlatNormalizationExecution09.candidate
      roseNestedC.elim.flat :=
  (roseFlatStagedCandidateSemantic09 readiness).semanticRunOfIdentity
    (roseFlatCandidateIdentityCheck09 readiness)

theorem roseFlatCandidateIdentityNormalization09
    (readiness : RoseFlatCandidateReadiness09) :
    (roseFlatCandidateIdentitySemantic09 readiness).normalization =
      Normalization.identity roseNestedC.elim.flat := by
  simpa only [roseFlatCandidateIdentitySemantic09] using
    StagedNormalizationCandidateBlockSemanticInput.semanticRunOfIdentity_normalization
      (roseFlatStagedCandidateSemantic09 readiness)
      (roseFlatCandidateIdentityCheck09 readiness)

/-- The semantic interpretation returns the exact analyzer block already
owned by the accepted nested artifact, rather than a propositionally parallel
reconstruction. -/
theorem roseFlatCandidateIdentityAnalysis09
    (readiness : RoseFlatCandidateReadiness09) :
    (roseFlatCandidateIdentitySemantic09 readiness).normalization.checkBlock? =
      some roseNestedC.generation.block := by
  rw [roseFlatCandidateIdentityNormalization09]
  apply BlockGenerationChecked.identity_checkBlock?
  apply NestedBlockChecked.generation_eq_of_check
  exact (Option.some_get (x := roseNestedC?) (by native_decide)).symm

def roseFlatProducedCandidateIdentitySemantic09
    (readiness : RoseFlatCandidateReadiness09) :
    ProducedNormalizationCandidateBlockSemanticRun
      { roseFlatCandidateContext09 with lctx := {} }
      { roseFlatCandidateContext09 with
        env := roseFlatNormalizationExecution09.familyEnv, lctx := {} }
      listFinalEnv07 roseFlatBlockEnv09 [`u]
      roseFlatNormalizationExecution09.candidate roseNestedC.elim.flat where
  semantic := roseFlatCandidateIdentitySemantic09 readiness
  familyTypesProduced := by
    change AddInductive.CandidateFamilyTypeListProduced _
      roseFlatNormalizationExecution09.families.candidates.familyTypes
    rw [roseFlatNormalizationExecution09.families.produced.familyTypes_eq]
    exact roseFlatNormalizationExecution09.familyTypes.produced
  familiesProduced :=
    roseFlatNormalizationExecution09.families.produced.reindex

/-- Exact flattened semantic generation from the real retained producer,
conditional only on the isolated completed-`List` readiness package. -/
def roseFlatExactProducedBlockGeneration09
    (readiness : RoseFlatCandidateReadiness09) :
    ExactProducedBlockGenerationRun listFinalEnv07 roseFlatBlockEnv09 [`u]
      roseFlatProducedGeneration09 roseNestedC.generation where
  producedSemantic :=
    roseFlatProducedCandidateIdentitySemantic09 readiness
  analysis := roseFlatCandidateIdentityAnalysis09 readiness
  checked := roseFlatCheckedBlockWF09
  resultLevelWF := roseFlatResultLevelWF

/-- The existing outer execution and the newly closed flattened semantics
jointly produce the exact recursor run, with no manually rebuilt candidate. -/
def roseFlatExactProducedBlockRecursor09
    (readiness : RoseFlatCandidateReadiness09) :
    ExactProducedBlockRecursorRun listFinalEnv07 roseFlatBlockEnv09 [`u]
      roseFlatRecursorShapeCandidate roseNestedC.generation :=
  roseFlatExactRecursorOfGeneration
    (roseFlatExactProducedBlockGeneration09 readiness)

/-! ## Exact flattened metadata prefix -/

private theorem roseListEqGetTwo [Inhabited α]
    (values : List α) (length_eq : values.length = 2) :
    values = [values[0]!, values[1]!] := by
  cases values with
  | nil => simp at length_eq
  | cons first tail =>
      cases tail with
      | nil => simp at length_eq
      | cons second tail =>
          cases tail with
          | nil => rfl
          | cons third tail => simp at length_eq

def roseFlatNodeEnv09 : VEnv :=
  (roseFlatBlockEnv09.addConst roseFlatNode09.name
    roseFlatNode09.toVConstant).get!

def roseFlatNilEnv09 : VEnv :=
  (roseFlatNodeEnv09.addConst roseFlatNil09.name
    roseFlatNil09.toVConstant).get!

def roseFlatCtorEnv09 : VEnv :=
  (roseFlatNilEnv09.addConst roseFlatCons09.name
    roseFlatCons09.toVConstant).get!

theorem roseFlatAddNode09 :
    roseFlatBlockEnv09.addConst roseFlatNode09.name
      roseFlatNode09.toVConstant = some roseFlatNodeEnv09 := rfl

theorem roseFlatAddNil09 :
    roseFlatNodeEnv09.addConst roseFlatNil09.name
      roseFlatNil09.toVConstant = some roseFlatNilEnv09 := rfl

theorem roseFlatAddCons09 :
    roseFlatNilEnv09.addConst roseFlatCons09.name
      roseFlatCons09.toVConstant = some roseFlatCtorEnv09 := rfl

theorem roseFlatNodeEnvOrdered09 : roseFlatNodeEnv09.Ordered :=
  .const roseFlatBlockEnvOrdered09 roseFlatNodeWF09 roseFlatAddNode09

theorem roseFlatNilEnvOrdered09 : roseFlatNilEnv09.Ordered := by
  refine .const roseFlatNodeEnvOrdered09 ?_ roseFlatAddNil09
  exact roseFlatNilWF09.mono (VEnv.addConst_le roseFlatAddNode09)

theorem roseFlatCtorEnvOrdered09 : roseFlatCtorEnv09.Ordered := by
  refine .const roseFlatNilEnvOrdered09 ?_ roseFlatAddCons09
  exact roseFlatConsWF09.mono
    ((VEnv.addConst_le roseFlatAddNode09).trans
      (VEnv.addConst_le roseFlatAddNil09))

theorem roseFlatConstructorFold09 :
    roseNestedC.elim.flat.blockConstructorConstants.foldlM
      (fun env constructor =>
        env.addConst constructor.name constructor.toVConstant)
      roseFlatBlockEnv09 = some roseFlatCtorEnv09 := by
  rw [roseFlatDecl09_eq]
  rfl

noncomputable def roseFlatDeclaration09
    (readiness : RoseFlatCandidateReadiness09) :
    ExactProducedBlockDeclarationRun
      (roseFlatExactProducedBlockRecursor09 readiness).elimination :=
  (roseFlatExactProducedBlockRecursor09 readiness).elimination.declarationRun
    (roseFlatCandidateStaging09 readiness)

theorem roseFlatDeclarationCtorEnv09
    (readiness : RoseFlatCandidateReadiness09) :
    (roseFlatDeclaration09 readiness).constructors.ctorEnv =
      roseFlatCtorEnv09 := by
  have exactFold :=
    (roseFlatDeclaration09 readiness).constructors.addCtors.to_foldlM
  rw [roseFlatConstructorFold09] at exactFold
  exact Option.some.inj exactFold.symm

theorem roseFlatInputLeCtor09 :
    listFinalEnv07 ≤ roseFlatCtorEnv09 := by
  exact (VEnv.addConst_le roseFlatFirstTypeEnv09_eq).trans
    ((VEnv.addConst_le roseFlatBlockEnv09_eq).trans
      ((VEnv.addConst_le roseFlatAddNode09).trans
        ((VEnv.addConst_le roseFlatAddNil09).trans
          (VEnv.addConst_le roseFlatAddCons09))))

theorem roseFlatBlockLeCtor09 :
    roseFlatBlockEnv09 ≤ roseFlatCtorEnv09 :=
  (VEnv.addConst_le roseFlatAddNode09).trans
    ((VEnv.addConst_le roseFlatAddNil09).trans
      (VEnv.addConst_le roseFlatAddCons09))

theorem roseFlatGenerationEnv09
    (readiness : RoseFlatCandidateReadiness09) :
    BlockGenerationEnv roseNestedC.generation roseFlatCtorEnv09 := by
  let flatWF :=
    (roseFlatExactProducedBlockGeneration09 readiness).blockGenerationRun.wf
  apply flatWF.toBlockGenerationEnv roseFlatInputLeCtor09
      roseFlatBlockLeCtor09 roseFlatCtorEnvOrdered09
  · intro family member
    have rawMember : family.raw ∈ roseNestedC.elim.flat.types := by
      rw [← roseNestedC.generation.families_map_raw]
      exact List.mem_map_of_mem member
    rw [roseFlatDecl09_eq] at rawMember
    simp [roseFlatDecl09] at rawMember
    rcases rawMember with rawEq | rawEq <;> rw [rawEq] <;> rfl
  · intro constructor member
    have rawMember : constructor.ctor.raw ∈
        roseNestedC.elim.flat.blockConstructorConstants := by
      rw [← roseNestedC.generation.flatCtors_map_raw]
      exact List.mem_map_of_mem member
    rw [roseFlatDecl09_eq] at rawMember
    simp [VInductDecl.blockConstructorConstants, roseFlatDecl09,
      roseFlatFamily09, roseFlatAuxFamily09] at rawMember
    rcases rawMember with rawEq | rawEq | rawEq <;> rw [rawEq] <;> rfl

abbrev roseFlatProducedRecInfo09 : RecursorVal :=
  roseFlatRecursorShapeCandidate.execution.recursors.infos[0]!

abbrev roseFlatProducedAuxRecInfo09 : RecursorVal :=
  roseFlatRecursorShapeCandidate.execution.recursors.infos[1]!

def roseFlatNestedHead09 (name : Name) : Option Name :=
  if name == ``List then some roseFlatAuxName09
  else if name == ``List.nil then some (roseFlatAuxName09 ++ `nil)
  else if name == ``List.cons then some (roseFlatAuxName09 ++ `cons)
  else none

def roseReflattenKernelExpr09 : Expr → Expr
  | .const name levels =>
      if name == `Lean4Lean.NestedRepresentation.RoseTree.rec_1 then
        .const (.str roseFlatAuxName09 "rec") levels
      else
        .const name levels
  | .app (.const name levels) nested@(.app (.const family _) alpha) =>
      if family == ``RoseTree then
        match roseFlatNestedHead09 name with
        | some flatName =>
            .app (.const flatName levels)
              (roseReflattenKernelExpr09 alpha)
        | none =>
            .app (roseReflattenKernelExpr09 (.const name levels))
              (roseReflattenKernelExpr09 nested)
      else
        .app (roseReflattenKernelExpr09 (.const name levels))
          (roseReflattenKernelExpr09 nested)
  | .app fn arg =>
      .app (roseReflattenKernelExpr09 fn)
        (roseReflattenKernelExpr09 arg)
  | .lam name type body binderInfo =>
      .lam name (roseReflattenKernelExpr09 type)
        (roseReflattenKernelExpr09 body) binderInfo
  | .forallE name type body binderInfo =>
      .forallE name (roseReflattenKernelExpr09 type)
        (roseReflattenKernelExpr09 body) binderInfo
  | expr => expr

def roseReflattenVExpr09 : VExpr → VExpr
  | .const name levels =>
      if name == `Lean4Lean.NestedRepresentation.RoseTree.rec_1 then
        .const (.str roseFlatAuxName09 "rec") levels
      else
        .const name levels
  | .app (.const name levels) nested@(.app (.const family _) alpha) =>
      if family == ``RoseTree then
        match roseFlatNestedHead09 name with
        | some flatName =>
            .app (.const flatName levels) (roseReflattenVExpr09 alpha)
        | none =>
            .app (roseReflattenVExpr09 (.const name levels))
              (roseReflattenVExpr09 nested)
      else
        .app (roseReflattenVExpr09 (.const name levels))
          (roseReflattenVExpr09 nested)
  | .app fn arg =>
      .app (roseReflattenVExpr09 fn) (roseReflattenVExpr09 arg)
  | .lam type body =>
      .lam (roseReflattenVExpr09 type)
        (roseReflattenVExpr09 body)
  | .forallE type body =>
      .forallE (roseReflattenVExpr09 type)
        (roseReflattenVExpr09 body)
  | expr => expr

def roseFlatExpectedRecInfo09 : RecursorVal :=
  { roseFlatProducedRecInfo09 with
    name := ``RoseTree.rec
    levelParams := [`u_1, `u]
    type := roseReflattenKernelExpr09 roseRecInfo09.type }

def roseFlatRecType09 : VExpr :=
  roseReflattenVExpr09 roseRecTypeL

theorem roseFlatRecType09_eq :
    roseNestedC.generation.recursors[0]!.type =
      roseFlatRecType09 := by
  native_decide

set_option maxRecDepth 8000 in
theorem roseFlatProducedRecTr09
    (readiness : RoseFlatCandidateReadiness09) :
    TrConstVal .safe roseFlatCtorEnv09
      (.recInfo roseFlatProducedRecInfo09)
      roseNestedC.generation.recursors[0]! := by
  have hRose : roseFlatCtorEnv09.constants ``RoseTree =
      some roseFlatFamily09.toVConstant := rfl
  have hAux : roseFlatCtorEnv09.constants roseFlatAuxName09 =
      some roseFlatAuxFamily09.toVConstant := rfl
  have hNode : roseFlatCtorEnv09.constants roseFlatNode09.name =
      some roseFlatNode09.toVConstant := rfl
  have hNil : roseFlatCtorEnv09.constants roseFlatNil09.name =
      some roseFlatNil09.toVConstant := rfl
  have hCons : roseFlatCtorEnv09.constants roseFlatCons09.name =
      some roseFlatCons09.toVConstant := rfl
  apply trConstVal_of_translation_header
    (expected := .recInfo roseFlatExpectedRecInfo09)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  refine ⟨⟨by native_decide, by native_decide, ?_⟩, by native_decide⟩
  have shape : TrTypeExpr roseFlatCtorEnv09
      roseFlatExpectedRecInfo09.levelParams []
      roseFlatExpectedRecInfo09.type
      roseFlatRecType09 := by
    change TrTypeExpr roseFlatCtorEnv09 [`u_1, `u] []
      (roseReflattenKernelExpr09 roseRecInfo09.type)
      (roseReflattenVExpr09 roseRecTypeL)
    simp [roseReflattenKernelExpr09, roseReflattenVExpr09,
      roseFlatNestedHead09, roseFlatAuxName09, roseRecTypeL,
      roseRecInfo09, ConstantInfo.type, ConstantInfo.toConstantVal]
    tr_type_expr_tac
  have recursorMember : roseNestedC.generation.recursors[0]! ∈
      roseNestedC.generation.recursors := by native_decide
  simp only [BlockGenerationChecked.recursors, List.mem_map] at recursorMember
  obtain ⟨family, familyMember, recursorEq⟩ := recursorMember
  obtain ⟨u, recWF⟩ :=
    (roseFlatGenerationEnv09 readiness).recursor_wf familyMember
  have rawHasType : roseFlatCtorEnv09.HasType
      roseNestedC.generation.recursors[0]!.uvars []
      roseNestedC.generation.recursors[0]!.type (.sort u) := by
    simp only [BlockGenerationChecked.recursors]
    rw [← recursorEq]
    exact recWF
  have rawUvars : roseNestedC.generation.recursors[0]!.uvars = 2 := by
    native_decide
  have flatHasType : roseFlatCtorEnv09.HasType 2 []
      roseFlatRecType09 (.sort u) := by
    rw [← rawUvars, ← roseFlatRecType09_eq]
    exact rawHasType
  change TrExprS roseFlatCtorEnv09
    roseFlatExpectedRecInfo09.levelParams []
      roseFlatExpectedRecInfo09.type
      roseNestedC.generation.recursors[0]!.type
  rw [roseFlatRecType09_eq]
  apply shape.to_trExprS roseFlatCtorEnvOrdered09 trivial
  refine ⟨.sort u, ?_⟩
  change roseFlatCtorEnv09.IsDefEq
    roseFlatExpectedRecInfo09.levelParams.length []
      roseFlatRecType09 roseFlatRecType09 (.sort u)
  rw [show roseFlatExpectedRecInfo09.levelParams.length = 2 by
    native_decide]
  exact flatHasType

def roseFlatExpectedAuxRecInfo09 : RecursorVal :=
  { roseFlatProducedAuxRecInfo09 with
    name := .str roseFlatAuxName09 "rec"
    levelParams := [`u_1, `u]
    type := roseReflattenKernelExpr09 roseRec1Info09.type }

def roseFlatAuxRecType09 : VExpr :=
  roseReflattenVExpr09 roseRec1TypeL

theorem roseFlatAuxRecType09_eq :
    roseNestedC.generation.recursors[1]!.type =
      roseFlatAuxRecType09 := by
  native_decide

set_option maxRecDepth 8000 in
theorem roseFlatProducedAuxRecTr09
    (readiness : RoseFlatCandidateReadiness09) :
    TrConstVal .safe roseFlatCtorEnv09
      (.recInfo roseFlatProducedAuxRecInfo09)
      roseNestedC.generation.recursors[1]! := by
  have hRose : roseFlatCtorEnv09.constants ``RoseTree =
      some roseFlatFamily09.toVConstant := rfl
  have hAux : roseFlatCtorEnv09.constants roseFlatAuxName09 =
      some roseFlatAuxFamily09.toVConstant := rfl
  have hNode : roseFlatCtorEnv09.constants roseFlatNode09.name =
      some roseFlatNode09.toVConstant := rfl
  have hNil : roseFlatCtorEnv09.constants roseFlatNil09.name =
      some roseFlatNil09.toVConstant := rfl
  have hCons : roseFlatCtorEnv09.constants roseFlatCons09.name =
      some roseFlatCons09.toVConstant := rfl
  apply trConstVal_of_translation_header
    (expected := .recInfo roseFlatExpectedAuxRecInfo09)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
  refine ⟨⟨by native_decide, by native_decide, ?_⟩, by native_decide⟩
  have shape : TrTypeExpr roseFlatCtorEnv09
      roseFlatExpectedAuxRecInfo09.levelParams []
      roseFlatExpectedAuxRecInfo09.type
      roseFlatAuxRecType09 := by
    change TrTypeExpr roseFlatCtorEnv09 [`u_1, `u] []
      (roseReflattenKernelExpr09 roseRec1Info09.type)
      (roseReflattenVExpr09 roseRec1TypeL)
    simp [roseReflattenKernelExpr09, roseReflattenVExpr09,
      roseFlatNestedHead09, roseFlatAuxName09, roseRec1TypeL,
      roseRec1Info09, ConstantInfo.type, ConstantInfo.toConstantVal]
    tr_type_expr_tac
  have recursorMember : roseNestedC.generation.recursors[1]! ∈
      roseNestedC.generation.recursors := by native_decide
  simp only [BlockGenerationChecked.recursors, List.mem_map] at recursorMember
  obtain ⟨family, familyMember, recursorEq⟩ := recursorMember
  obtain ⟨u, recWF⟩ :=
    (roseFlatGenerationEnv09 readiness).recursor_wf familyMember
  have rawHasType : roseFlatCtorEnv09.HasType
      roseNestedC.generation.recursors[1]!.uvars []
      roseNestedC.generation.recursors[1]!.type (.sort u) := by
    simp only [BlockGenerationChecked.recursors]
    rw [← recursorEq]
    exact recWF
  have rawUvars : roseNestedC.generation.recursors[1]!.uvars = 2 := by
    native_decide
  have flatHasType : roseFlatCtorEnv09.HasType 2 []
      roseFlatAuxRecType09 (.sort u) := by
    rw [← rawUvars, ← roseFlatAuxRecType09_eq]
    exact rawHasType
  change TrExprS roseFlatCtorEnv09
    roseFlatExpectedAuxRecInfo09.levelParams []
      roseFlatExpectedAuxRecInfo09.type
      roseNestedC.generation.recursors[1]!.type
  rw [roseFlatAuxRecType09_eq]
  apply shape.to_trExprS roseFlatCtorEnvOrdered09 trivial
  refine ⟨.sort u, ?_⟩
  change roseFlatCtorEnv09.IsDefEq
    roseFlatExpectedAuxRecInfo09.levelParams.length []
      roseFlatAuxRecType09 roseFlatAuxRecType09 (.sort u)
  rw [show roseFlatExpectedAuxRecInfo09.levelParams.length = 2 by
    native_decide]
  exact flatHasType

theorem roseFlatGeneratedRecursorEvidence09
    (readiness : RoseFlatCandidateReadiness09) :
    List.Forall₂
      (fun info raw => TrConstVal .safe
        (roseFlatDeclaration09 readiness).constructors.ctorEnv
        (.recInfo info) raw)
      roseFlatRecursorShapeCandidate.execution.recursors.infos
      roseNestedC.generation.recursors := by
  rw [roseFlatDeclarationCtorEnv09]
  have infos :
      roseFlatRecursorShapeCandidate.execution.recursors.infos =
        [roseFlatProducedRecInfo09,
          roseFlatProducedAuxRecInfo09] :=
    roseListEqGetTwo _ (by native_decide)
  have raws : roseNestedC.generation.recursors =
      [roseNestedC.generation.recursors[0]!,
        roseNestedC.generation.recursors[1]!] :=
    roseListEqGetTwo _ (by native_decide)
  rw [infos, raws]
  exact .cons (roseFlatProducedRecTr09 readiness)
    (.cons (roseFlatProducedAuxRecTr09 readiness) .nil)

theorem roseFlatGeneratedRecursorsWF09
    (readiness : RoseFlatCandidateReadiness09) :
    ∀ raw ∈ roseNestedC.generation.recursors,
      raw.toVConstant.WF
        (roseFlatDeclaration09 readiness).constructors.ctorEnv := by
  intro raw member
  rw [roseFlatDeclarationCtorEnv09]
  simp only [BlockGenerationChecked.recursors, List.mem_map] at member
  obtain ⟨family, familyMember, rfl⟩ := member
  exact (roseFlatGenerationEnv09 readiness).recursor_wf familyMember

noncomputable def roseFlatMetadataPrefix09
    (readiness : RoseFlatCandidateReadiness09) :
    ExactProducedBlockMetadataPrefixRun
      (roseFlatExactProducedBlockRecursor09 readiness) :=
  (roseFlatExactProducedBlockRecursor09 readiness).metadataPrefix
    (roseFlatCandidateStaging09 readiness)
    (roseFlatGeneratedRecursorEvidence09 readiness)
    (roseFlatGeneratedRecursorsWF09 readiness)

def roseFlatFirstRecEnv09 : VEnv :=
  (roseFlatCtorEnv09.addConst
    roseNestedC.generation.recursors[0]!.name
    roseNestedC.generation.recursors[0]!.toVConstant).get
      (by native_decide)

def roseFlatRecEnv09 : VEnv :=
  (roseFlatFirstRecEnv09.addConst
    roseNestedC.generation.recursors[1]!.name
    roseNestedC.generation.recursors[1]!.toVConstant).get
      (by native_decide)

theorem roseFlatAddFirstRec09 :
    roseFlatCtorEnv09.addConst
      roseNestedC.generation.recursors[0]!.name
      roseNestedC.generation.recursors[0]!.toVConstant =
        some roseFlatFirstRecEnv09 :=
  (Option.some_get (x := roseFlatCtorEnv09.addConst
    roseNestedC.generation.recursors[0]!.name
    roseNestedC.generation.recursors[0]!.toVConstant)
    (by native_decide)).symm

theorem roseFlatAddSecondRec09 :
    roseFlatFirstRecEnv09.addConst
      roseNestedC.generation.recursors[1]!.name
      roseNestedC.generation.recursors[1]!.toVConstant =
        some roseFlatRecEnv09 :=
  (Option.some_get (x := roseFlatFirstRecEnv09.addConst
    roseNestedC.generation.recursors[1]!.name
    roseNestedC.generation.recursors[1]!.toVConstant)
    (by native_decide)).symm

theorem roseFlatRecursorFold09 :
    roseNestedC.generation.recursors.foldlM
      (fun env recursor => env.addConst recursor.name recursor.toVConstant)
      roseFlatCtorEnv09 = some roseFlatRecEnv09 := by
  rw [roseListEqGetTwo roseNestedC.generation.recursors (by native_decide)]
  simp only [List.foldlM_cons, List.foldlM_nil]
  apply Option.bind_eq_some_iff.mpr
  refine ⟨roseFlatFirstRecEnv09, roseFlatAddFirstRec09, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  exact ⟨roseFlatRecEnv09, roseFlatAddSecondRec09, rfl⟩

theorem roseFlatMetadataRecEnv09
    (readiness : RoseFlatCandidateReadiness09) :
    (roseFlatMetadataPrefix09 readiness).recursors.recEnv =
      roseFlatRecEnv09 := by
  have ctorEnvEq :
      (roseFlatMetadataPrefix09 readiness).declarations.constructors.ctorEnv =
        roseFlatCtorEnv09 := by
    change (roseFlatDeclaration09 readiness).constructors.ctorEnv =
      roseFlatCtorEnv09
    exact roseFlatDeclarationCtorEnv09 readiness
  have exactFold :=
    (roseFlatMetadataPrefix09 readiness).recursors.addRecs.to_foldlM
  have folds := congrArg
    (fun start => roseNestedC.generation.recursors.foldlM
      (fun env recursor => env.addConst recursor.name recursor.toVConstant)
      start) ctorEnvEq
  rw [exactFold, roseFlatRecursorFold09] at folds
  exact Option.some.inj folds

def roseFlatFinalEnv09 : VEnv :=
  roseNestedC.generation.generatedRules.foldl VEnv.addDefEq
    roseFlatRecEnv09

theorem roseFlatAddRules09
    (readiness : RoseFlatCandidateReadiness09) :
    AddDefEqs (roseFlatMetadataPrefix09 readiness).recursors.recEnv
      roseNestedC.generation.generatedRules roseFlatFinalEnv09 where
  fold_eq := by
    rw [roseFlatMetadataRecEnv09]
    rfl


/-! ## Stored-metadata translations -/

theorem roseInfoTr09 :
    TrConstVal .safe listFinalEnv07 roseInfo09 roseFamilyV := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr listFinalEnv07 roseInfo09.levelParams []
      roseInfo09.type roseFamilyV.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS listFinalOrdered07 trivial ⟨_, by type_tac⟩

theorem roseNodeTr09 :
    TrConstVal .safe roseTypeEnv09 roseNodeInfo09 roseNodeV := by
  have hList : roseTypeEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseTypeEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr roseTypeEnv09 roseNodeInfo09.levelParams []
      roseNodeInfo09.type roseNodeV.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS roseTypeOrdered09 trivial ⟨_, by type_tac⟩

theorem roseRecTr09 :
    TrConstVal .safe roseCtorEnv09 roseRecInfo09 roseRecVL := by
  have hList : roseCtorEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseCtorEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseCtorEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseCtorEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseCtorEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr roseCtorEnv09 roseRecInfo09.levelParams []
      roseRecInfo09.type roseRecVL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := roseRecWF09
  exact shape.to_trExprS roseCtorOrdered09 trivial ⟨_, hty⟩

theorem roseRec1Tr09 :
    TrConstVal .safe roseRecEnv09 roseRec1Info09 roseRec1VL := by
  have hList : roseRecEnv09.constants ``List =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hRose : roseRecEnv09.constants ``RoseTree =
      some ⟨1, .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩ := rfl
  have hNode : roseRecEnv09.constants ``RoseTree.node =
      some roseNodeV.toVConstant := rfl
  have hNil : roseRecEnv09.constants ``List.nil =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
  have hCons : roseRecEnv09.constants ``List.cons =
      some ⟨1, .forallE (.sort (.succ (.param 0)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const `List [.param 0]) (.bvar 1))
            (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr roseRecEnv09 roseRec1Info09.levelParams []
      roseRec1Info09.type roseRec1VL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := roseRec1WF09
  exact shape.to_trExprS roseRecOrdered09 trivial ⟨_, hty⟩

def roseStoredCtorInfoVal09 : ConstructorVal :=
  match roseNodeInfo09 with
  | .ctorInfo info => info
  | _ => default

def roseStoredRecInfoVal09 : RecursorVal :=
  match roseRecInfo09 with
  | .recInfo info => info
  | _ => default

def roseStoredAuxRecInfoVal09 : RecursorVal :=
  match roseRec1Info09 with
  | .recInfo info => info
  | _ => default

/-- Full role-specific restoration parity.  The family pins cover every
non-expression metadata field; constructor and recursor `BEq` additionally
cover their complete payloads, including all restored recursor rules. -/
theorem roseProducedFamilyPins09 :
    (let info := roseProducedRestoredFamilyInfo09;
      NestedRepresentation.InductPins.mk info.name info.levelParams
        info.numParams info.numIndices info.all info.ctors info.numNested
        info.isRec info.isReflexive info.isUnsafe) ==
      nestedInductPins09A% RoseTree := by
  native_decide

theorem roseProducedCtorInfo_match09 :
    roseProducedRestoredCtorInfo09 == roseStoredCtorInfoVal09 := by
  native_decide

theorem roseProducedRecInfo_match09 :
    roseProducedRestoredRecInfo09 == roseStoredRecInfoVal09 := by
  native_decide

theorem roseProducedAuxRecInfo_match09 :
    roseProducedRestoredAuxRecInfo09 == roseStoredAuxRecInfoVal09 := by
  native_decide

theorem roseProducedFamilyTranslationHeader09 :
    let actual : ConstantInfo :=
      .inductInfo roseProducedRestoredFamilyInfo09
    actual.safety = roseInfo09.safety ∧
      actual.levelParams = roseInfo09.levelParams ∧
      actual.type.eqv roseInfo09.type ∧
      actual.name = roseInfo09.name := by
  native_decide

theorem roseProducedCtorTranslationHeader09 :
    let actual : ConstantInfo := .ctorInfo roseProducedRestoredCtorInfo09
    actual.safety = roseNodeInfo09.safety ∧
      actual.levelParams = roseNodeInfo09.levelParams ∧
      actual.type.eqv roseNodeInfo09.type ∧
      actual.name = roseNodeInfo09.name := by
  native_decide

theorem roseProducedFamilyTr09 :
    TrConstVal .safe listFinalEnv07
      (.inductInfo roseProducedRestoredFamilyInfo09) roseFamilyV := by
  rcases roseProducedFamilyTranslationHeader09 with ⟨hs, hl, ht, hn⟩
  exact trConstVal_of_translation_header hs hl ht hn roseInfoTr09

theorem roseProducedCtorTr09 :
    TrConstVal .safe roseTypeEnv09
      (.ctorInfo roseProducedRestoredCtorInfo09) roseNodeV := by
  rcases roseProducedCtorTranslationHeader09 with ⟨hs, hl, ht, hn⟩
  exact trConstVal_of_translation_header hs hl ht hn roseNodeTr09

theorem roseProducedRecTr09 :
    TrConstVal .safe roseCtorEnv09
      (.recInfo roseProducedRestoredRecInfo09) roseRecVL := by
  apply recursorInfoTranslation_of_beq roseProducedRecInfo_match09
  simpa [roseStoredRecInfoVal09, roseRecInfo09] using roseRecTr09

theorem roseProducedAuxRecTr09 :
    TrConstVal .safe roseRecEnv09
      (.recInfo roseProducedRestoredAuxRecInfo09) roseRec1VL := by
  apply recursorInfoTranslation_of_beq roseProducedAuxRecInfo_match09
  simpa [roseStoredAuxRecInfoVal09, roseRec1Info09] using roseRec1Tr09


/-! ## Recursor K metadata and stored lookups -/

theorem roseKTarget09 : roseNestedC.generation.kTarget = false := by
  native_decide

theorem roseProducedRecK09 :
    roseProducedRestoredRecInfo09.k = roseNestedC.generation.kTarget ∧
      roseProducedRestoredAuxRecInfo09.k =
        roseNestedC.generation.kTarget := by
  native_decide

theorem roseRecLookup09 :
    roseMap09.find? ``RoseTree.rec = some roseRecInfo09 := by
  rw [roseMap09, roseRecMapWF09.find?_insert]
  simp [roseRecMap09, roseCtorMapWF09.find?_insert]

theorem roseRec1Lookup09 :
    roseMap09.find? `Lean4Lean.NestedRepresentation.RoseTree.rec_1 =
      some roseRec1Info09 := by
  rw [roseMap09, roseRecMapWF09.find?_insert]
  simp

theorem roseRecK09 :
    RecursorMapKMatches roseMap09 roseNestedC.recursors
      roseNestedC.generation.kTarget := by
  rw [roseRecursors_eq, roseKTarget09]
  intro recursor hmem
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨roseRecInfo09, roseRecLookup09, by decide⟩
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨roseRec1Info09, roseRec1Lookup09, by decide⟩
  · cases hmem

/-! ## The nested alignment trace and its `TrEnv'` drive -/

def roseTrace09 :
    AddInductNestedTrace listMap07 listFinalEnv07 roseSourceV
      roseMap09 roseFinalEnv09 where
  nested := roseNestedC
  nested_wf := roseNestedWF09
  typeMap := roseTypeMap09
  typeEnv := roseTypeEnv09
  ctorMap := roseCtorMap09
  ctorEnv := roseCtorEnv09
  recEnv := roseRec1Env09
  addTypes := .cons
    { info := roseInfo09
      kind_eq := trivial
      tr := roseInfoTr09
      map_fresh := roseTypeFresh09
      env_add := roseTypeEnv09_eq
      map_add := rfl } .nil
  addCtors := .cons
    { info := roseNodeInfo09
      kind_eq := trivial
      tr := roseNodeTr09
      map_fresh := roseNodeFresh09
      env_add := roseCtorEnv09_eq
      map_add := rfl } .nil
  addRecs := roseRecursors_eq ▸ .cons
    { info := roseRecInfo09
      kind_eq := trivial
      tr := roseRecTr09
      map_fresh := roseRecFresh09
      env_add := roseRecEnv09_eq
      map_add := rfl } (.cons
    { info := roseRec1Info09
      kind_eq := trivial
      tr := roseRec1Tr09
      map_fresh := roseRec1Fresh09
      env_add := roseRec1Env09_eq
      map_add := rfl } .nil)
  recK := roseRecK09
  addRules := ⟨by rw [roseRules_eq]; rfl⟩

theorem roseAddInductNested09 :
    AddInductNested listMap07 listFinalEnv07 roseSourceV
      roseMap09 roseFinalEnv09 :=
  ⟨roseTrace09⟩

/-! ## Paired flattened/restored certificate -/

def roseNestedCertificate09 :
    roseSourceV.NestedBlockCertificate listFinalEnv07 roseFinalEnv09 where
  nested := roseNestedC
  semantic := roseNestedWF09
  success := roseTrace09.to_addInductNested
  beforeWF := listTrEnv07.wf

noncomputable def roseNestedStagedCertificate09
    (readiness : RoseFlatCandidateReadiness09) :
    roseSourceV.NestedStagedCertificate listFinalEnv07
      roseFlatFinalEnv09 roseFinalEnv09 :=
  (roseFlatMetadataPrefix09 readiness).nestedStagedCertificate
    roseNestedCertificate09 (roseFlatAddRules09 readiness)

theorem roseNestedStagedRuleFacts09
    (readiness : RoseFlatCandidateReadiness09)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (entry : roseNestedC.generation.ruleEntry i constructor) :
    (roseNestedStagedCertificate09 readiness).RecursorRuleFacts
      i constructor :=
  (roseNestedStagedCertificate09 readiness).recursorRuleFacts entry

theorem roseFlatRuleCount09 :
    roseNestedC.generation.flatCtors.length = 3 := by
  native_decide

/-- Every one of the three concrete flattened constructor positions yields
the ordinary pattern facts and the restored registration/WF facts from the
same paired certificate. -/
theorem roseNestedStagedRuleFactsAt09
    (readiness : RoseFlatCandidateReadiness09)
    (i : Nat) (inBounds : i < roseNestedC.generation.flatCtors.length) :
    (roseNestedStagedCertificate09 readiness).RecursorRuleFacts i
      ((roseNestedC.generation.flatCtors)[i]'inBounds) := by
  apply roseNestedStagedRuleFacts09 readiness
  exact getElem?_eq_some_iff.mpr ⟨inBounds, rfl⟩

/-! ## Selected host-rule bridges -/

/-- The concrete host rule selected for the restored main recursor. -/
def roseProducedMainSelectedRule09 : RecursorRule :=
  (getRecRuleFor roseProducedRestoredRecInfo09
    (.const `Lean4Lean.NestedRepresentation.RoseTree.node [])).get
      (by native_decide)

/-- The concrete host rule selected for the restored auxiliary recursor at
`List.nil`. -/
def roseProducedNilSelectedRule09 : RecursorRule :=
  (getRecRuleFor roseProducedRestoredAuxRecInfo09
    (.const ``List.nil [])).get (by native_decide)

/-- The concrete host rule selected for the restored auxiliary recursor at
`List.cons`. -/
def roseProducedConsSelectedRule09 : RecursorRule :=
  (getRecRuleFor roseProducedRestoredAuxRecInfo09
    (.const ``List.cons [])).get (by native_decide)

theorem roseProducedMainSelectedRuleShape09 :
    roseProducedMainSelectedRule09.ctor =
        `Lean4Lean.NestedRepresentation.RoseTree.node ∧
      roseProducedMainSelectedRule09.nfields = 2 := by
  native_decide

theorem roseProducedNilSelectedRuleShape09 :
    roseProducedNilSelectedRule09.ctor = ``List.nil ∧
      roseProducedNilSelectedRule09.nfields = 0 := by
  native_decide

theorem roseProducedConsSelectedRuleShape09 :
    roseProducedConsSelectedRule09.ctor = ``List.cons ∧
      roseProducedConsSelectedRule09.nfields = 2 := by
  native_decide

private theorem roseGetAppFnMkAppList09 (head : Expr) (args : List Expr) :
    (Expr.mkAppList head args).getAppFn = head.getAppFn := by
  induction args generalizing head with
  | nil => rfl
  | cons arg args ih =>
    rw [Expr.mkAppList, ih]
    rfl

private theorem roseGetRecRuleForMkAppList09 (info : RecursorVal)
    (head : Expr) (args : List Expr) :
    getRecRuleFor info (Expr.mkAppList head args) =
      getRecRuleFor info head := by
  unfold getRecRuleFor
  rw [roseGetAppFnMkAppList09]

/-- Runtime rule selection is invariant under the completed `node`
constructor spine and picks the exact retained main rule. -/
theorem roseProducedMainSelectedRuleLookup09
    (levels : List Level) (args : List Expr) :
    getRecRuleFor roseProducedRestoredRecInfo09
      (Expr.mkAppList
        (.const `Lean4Lean.NestedRepresentation.RoseTree.node levels) args) =
        some roseProducedMainSelectedRule09 := by
  unfold getRecRuleFor
  rw [roseGetAppFnMkAppList09]
  exact (Option.some_get
    (x := List.find? (fun rule => rule.ctor ==
      `Lean4Lean.NestedRepresentation.RoseTree.node)
      roseProducedRestoredRecInfo09.rules) (by native_decide)).symm

/-- Runtime rule selection is invariant under the completed `List.nil`
constructor spine and picks the exact retained auxiliary rule. -/
theorem roseProducedNilSelectedRuleLookup09
    (levels : List Level) (args : List Expr) :
    getRecRuleFor roseProducedRestoredAuxRecInfo09
      (Expr.mkAppList (.const ``List.nil levels) args) =
        some roseProducedNilSelectedRule09 := by
  rw [roseGetRecRuleForMkAppList09]
  exact (Option.some_get
    (x := getRecRuleFor roseProducedRestoredAuxRecInfo09
      (.const ``List.nil [])) (by native_decide)).symm

/-- Runtime rule selection is invariant under the completed `List.cons`
constructor spine and picks the exact retained auxiliary rule. -/
theorem roseProducedConsSelectedRuleLookup09
    (levels : List Level) (args : List Expr) :
    getRecRuleFor roseProducedRestoredAuxRecInfo09
      (Expr.mkAppList (.const ``List.cons levels) args) =
        some roseProducedConsSelectedRule09 := by
  rw [roseGetRecRuleForMkAppList09]
  exact (Option.some_get
    (x := getRecRuleFor roseProducedRestoredAuxRecInfo09
      (.const ``List.cons [])) (by native_decide)).symm

/-- The one finite executable observation needed to classify every retained
Rose rule position.  Only constructor names are decided here; the actual
`RecursorRule` equalities below are recovered propositionally from `find?`. -/
theorem roseProducedRuleCtorInventories09 :
    roseProducedRestoredRecInfo09.rules.map RecursorRule.ctor =
        [`Lean4Lean.NestedRepresentation.RoseTree.node] ∧
      roseProducedRestoredAuxRecInfo09.rules.map RecursorRule.ctor =
        [``List.nil, ``List.cons] := by
  native_decide

/-- The restored main recursor contains exactly its node rule; the auxiliary
recursor contains exactly the inherited nil and cons rules. -/
theorem roseProducedRuleInventoryLengths09 :
    roseProducedRestoredRecInfo09.rules.length = 1 ∧
      roseProducedRestoredAuxRecInfo09.rules.length = 2 := by
  constructor
  · have := congrArg List.length roseProducedRuleCtorInventories09.1
    simpa using this
  · have := congrArg List.length roseProducedRuleCtorInventories09.2
    simpa using this

/-- The unique main-rule position is propositionally the retained selected
rule.  This is derived through `find?` so it does not require decidable
equality on `RecursorRule`. -/
theorem roseProducedMainRuleZero09 :
    roseProducedRestoredRecInfo09.rules[0]? =
      some roseProducedMainSelectedRule09 := by
  rcases List.find?_eq_some_iff_getElem.mp
      (roseProducedMainSelectedRuleLookup09 [] []) with
    ⟨_, i, hi, hget, _⟩
  have : i = 0 := by
    rw [roseProducedRuleInventoryLengths09.1] at hi
    omega
  subst i
  exact getElem?_eq_some_iff.mpr ⟨hi, hget⟩

/-- The two auxiliary positions are propositionally the retained nil and
cons rules, again recovered through their executable selectors. -/
theorem roseProducedAuxRuleZero09 :
    roseProducedRestoredAuxRecInfo09.rules[0]? =
      some roseProducedNilSelectedRule09 := by
  rcases List.find?_eq_some_iff_getElem.mp
      (roseProducedNilSelectedRuleLookup09 [] []) with
    ⟨_, i, hi, hget, _⟩
  have hiCases : i = 0 ∨ i = 1 := by
    rw [roseProducedRuleInventoryLengths09.2] at hi
    omega
  rcases hiCases with rfl | rfl
  · exact getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  · have hctorAt := congrArg (fun xs => xs[1]?)
        roseProducedRuleCtorInventories09.2
    simp only [List.getElem?_map] at hctorAt
    have hgetOpt : roseProducedRestoredAuxRecInfo09.rules[1]? =
        some roseProducedNilSelectedRule09 :=
      getElem?_eq_some_iff.mpr ⟨hi, hget⟩
    rw [hgetOpt] at hctorAt
    simp [roseProducedNilSelectedRuleShape09.1] at hctorAt

theorem roseProducedAuxRuleOne09 :
    roseProducedRestoredAuxRecInfo09.rules[1]? =
      some roseProducedConsSelectedRule09 := by
  rcases List.find?_eq_some_iff_getElem.mp
      (roseProducedConsSelectedRuleLookup09 [] []) with
    ⟨_, i, hi, hget, _⟩
  have hiCases : i = 0 ∨ i = 1 := by
    rw [roseProducedRuleInventoryLengths09.2] at hi
    omega
  rcases hiCases with rfl | rfl
  · have hctorAt := congrArg (fun xs => xs[0]?)
        roseProducedRuleCtorInventories09.2
    simp only [List.getElem?_map] at hctorAt
    have hgetOpt : roseProducedRestoredAuxRecInfo09.rules[0]? =
        some roseProducedConsSelectedRule09 :=
      getElem?_eq_some_iff.mpr ⟨hi, hget⟩
    rw [hgetOpt] at hctorAt
    simp [roseProducedConsSelectedRuleShape09.1] at hctorAt
  · exact getElem?_eq_some_iff.mpr ⟨hi, hget⟩

/-- Invert any successful main-recursion selector into the exact node spine
and retained main rule.  The spine arguments and universe levels remain
arbitrary runtime data. -/
theorem roseProducedMainSelectedRuleInv09
    {major : Expr} {rule : RecursorRule}
    (h : getRecRuleFor roseProducedRestoredRecInfo09 major = some rule) :
    ∃ levels args,
      major = Expr.mkAppList
        (.const `Lean4Lean.NestedRepresentation.RoseTree.node levels) args ∧
      rule = roseProducedMainSelectedRule09 := by
  unfold getRecRuleFor at h
  cases hhead : major.getAppFn <;> simp [hhead] at h
  rename_i name levels
  rcases List.find?_eq_some_iff_getElem.mp h with
    ⟨hpred, i, hi, hget, _⟩
  have hi0 : i = 0 := by
    rw [roseProducedRuleInventoryLengths09.1] at hi
    omega
  subst i
  have hgetOpt : roseProducedRestoredRecInfo09.rules[0]? = some rule :=
    getElem?_eq_some_iff.mpr ⟨hi, hget⟩
  have hrule : rule = roseProducedMainSelectedRule09 :=
    Option.some.inj (hgetOpt.symm.trans roseProducedMainRuleZero09)
  have hnameEq := beq_iff_eq.mp hpred
  rw [hrule, roseProducedMainSelectedRuleShape09.1] at hnameEq
  have hname : name =
      `Lean4Lean.NestedRepresentation.RoseTree.node := hnameEq.symm
  refine ⟨levels, major.getAppArgsList, ?_, hrule⟩
  calc
    major = Expr.mkAppList major.getAppFn major.getAppArgsList :=
      major.mkAppList_getAppArgsList.symm
    _ = Expr.mkAppList
        (.const `Lean4Lean.NestedRepresentation.RoseTree.node levels)
        major.getAppArgsList := by rw [hhead, hname]

/-- Invert any successful auxiliary selector into exactly one of its two
runtime constructor spines and the corresponding retained rule. -/
theorem roseProducedAuxSelectedRuleInv09
    {major : Expr} {rule : RecursorRule}
    (h : getRecRuleFor roseProducedRestoredAuxRecInfo09 major = some rule) :
    (∃ levels args,
      major = Expr.mkAppList (.const ``List.nil levels) args ∧
      rule = roseProducedNilSelectedRule09) ∨
    (∃ levels args,
      major = Expr.mkAppList (.const ``List.cons levels) args ∧
      rule = roseProducedConsSelectedRule09) := by
  unfold getRecRuleFor at h
  cases hhead : major.getAppFn <;> simp [hhead] at h
  rename_i name levels
  rcases List.find?_eq_some_iff_getElem.mp h with
    ⟨hpred, i, hi, hget, _⟩
  have hiCases : i = 0 ∨ i = 1 := by
    rw [roseProducedRuleInventoryLengths09.2] at hi
    omega
  rcases hiCases with rfl | rfl
  · have hgetOpt : roseProducedRestoredAuxRecInfo09.rules[0]? = some rule :=
      getElem?_eq_some_iff.mpr ⟨hi, hget⟩
    have hrule : rule = roseProducedNilSelectedRule09 :=
      Option.some.inj (hgetOpt.symm.trans roseProducedAuxRuleZero09)
    have hnameEq := beq_iff_eq.mp hpred
    rw [hrule, roseProducedNilSelectedRuleShape09.1] at hnameEq
    have hname : name = ``List.nil := hnameEq.symm
    left
    refine ⟨levels, major.getAppArgsList, ?_, hrule⟩
    calc
      major = Expr.mkAppList major.getAppFn major.getAppArgsList :=
        major.mkAppList_getAppArgsList.symm
      _ = Expr.mkAppList (.const ``List.nil levels)
          major.getAppArgsList := by rw [hhead, hname]
  · have hgetOpt : roseProducedRestoredAuxRecInfo09.rules[1]? = some rule :=
      getElem?_eq_some_iff.mpr ⟨hi, hget⟩
    have hrule : rule = roseProducedConsSelectedRule09 :=
      Option.some.inj (hgetOpt.symm.trans roseProducedAuxRuleOne09)
    have hnameEq := beq_iff_eq.mp hpred
    rw [hrule, roseProducedConsSelectedRuleShape09.1] at hnameEq
    have hname : name = ``List.cons := hnameEq.symm
    right
    refine ⟨levels, major.getAppArgsList, ?_, hrule⟩
    calc
      major = Expr.mkAppList major.getAppFn major.getAppArgsList :=
        major.mkAppList_getAppArgsList.symm
      _ = Expr.mkAppList (.const ``List.cons levels)
          major.getAppArgsList := by rw [hhead, hname]

theorem roseFlatRuleBound0_09 :
    0 < roseNestedC.generation.flatCtors.length := by
  native_decide

theorem roseFlatRuleBound1_09 :
    1 < roseNestedC.generation.flatCtors.length := by
  native_decide

theorem roseFlatRuleBound2_09 :
    2 < roseNestedC.generation.flatCtors.length := by
  native_decide

abbrev roseFlatRuleConstructor0_09 :=
  (roseNestedC.generation.flatCtors)[0]'roseFlatRuleBound0_09

abbrev roseFlatRuleConstructor1_09 :=
  (roseNestedC.generation.flatCtors)[1]'roseFlatRuleBound1_09

abbrev roseFlatRuleConstructor2_09 :=
  (roseNestedC.generation.flatCtors)[2]'roseFlatRuleBound2_09

theorem roseFlatRuleEntry0_09 :
    roseNestedC.generation.ruleEntry 0 roseFlatRuleConstructor0_09 := by
  exact getElem?_eq_some_iff.mpr ⟨roseFlatRuleBound0_09, rfl⟩

theorem roseFlatRuleEntry1_09 :
    roseNestedC.generation.ruleEntry 1 roseFlatRuleConstructor1_09 := by
  exact getElem?_eq_some_iff.mpr ⟨roseFlatRuleBound1_09, rfl⟩

theorem roseFlatRuleEntry2_09 :
    roseNestedC.generation.ruleEntry 2 roseFlatRuleConstructor2_09 := by
  exact getElem?_eq_some_iff.mpr ⟨roseFlatRuleBound2_09, rfl⟩

/-! ### Runtime extraction and restoration alignment -/

/-- The host reducer's universe arity, capture-prefix boundary, major
position, and field count agree exactly with flattened rule zero. -/
theorem roseProducedMainReducerAlignment09 :
    roseProducedRestoredRecInfo09.levelParams.length =
        roseNestedC.generation.recUvars ∧
      roseProducedRestoredRecInfo09.getFirstIndexIdx =
        roseNestedC.elim.flat.nparams +
          roseNestedC.generation.familyCount +
          roseNestedC.generation.minorCount ∧
      roseProducedRestoredRecInfo09.getMajorIdx =
        roseNestedC.generation.ruleMajorArity
          roseFlatRuleConstructor0_09 ∧
      roseProducedMainSelectedRule09.nfields =
        roseNestedC.generation.ruleFieldCount
          roseFlatRuleConstructor0_09 ∧
      roseNestedC.generation.ruleIdx roseFlatRuleConstructor0_09 = [] ∧
      roseNestedC.generation.ruleArgArity roseFlatRuleConstructor0_09 =
        roseNestedC.elim.flat.nparams +
          roseProducedMainSelectedRule09.nfields := by
  native_decide

/-- The same exact reducer/generator alignment for the restored auxiliary
`List.nil` rule. -/
theorem roseProducedNilReducerAlignment09 :
    roseProducedRestoredAuxRecInfo09.levelParams.length =
        roseNestedC.generation.recUvars ∧
      roseProducedRestoredAuxRecInfo09.getFirstIndexIdx =
        roseNestedC.elim.flat.nparams +
          roseNestedC.generation.familyCount +
          roseNestedC.generation.minorCount ∧
      roseProducedRestoredAuxRecInfo09.getMajorIdx =
        roseNestedC.generation.ruleMajorArity
          roseFlatRuleConstructor1_09 ∧
      roseProducedNilSelectedRule09.nfields =
        roseNestedC.generation.ruleFieldCount
          roseFlatRuleConstructor1_09 ∧
      roseNestedC.generation.ruleIdx roseFlatRuleConstructor1_09 = [] ∧
      roseNestedC.generation.ruleArgArity roseFlatRuleConstructor1_09 =
        roseNestedC.elim.flat.nparams +
          roseProducedNilSelectedRule09.nfields := by
  native_decide

/-- The same exact reducer/generator alignment for the restored auxiliary
`List.cons` rule. -/
theorem roseProducedConsReducerAlignment09 :
    roseProducedRestoredAuxRecInfo09.levelParams.length =
        roseNestedC.generation.recUvars ∧
      roseProducedRestoredAuxRecInfo09.getFirstIndexIdx =
        roseNestedC.elim.flat.nparams +
          roseNestedC.generation.familyCount +
          roseNestedC.generation.minorCount ∧
      roseProducedRestoredAuxRecInfo09.getMajorIdx =
        roseNestedC.generation.ruleMajorArity
          roseFlatRuleConstructor2_09 ∧
      roseProducedConsSelectedRule09.nfields =
        roseNestedC.generation.ruleFieldCount
          roseFlatRuleConstructor2_09 ∧
      roseNestedC.generation.ruleIdx roseFlatRuleConstructor2_09 = [] ∧
      roseNestedC.generation.ruleArgArity roseFlatRuleConstructor2_09 =
        roseNestedC.elim.flat.nparams +
          roseProducedConsSelectedRule09.nfields := by
  native_decide

/-- The selected main RoseTree rule is unindexed, so its generated check has
no computed-index component. -/
theorem roseFlatMainRuleUnindexed09 :
    roseNestedC.generation.ruleIdx roseFlatRuleConstructor0_09 = [] :=
  roseProducedMainReducerAlignment09.2.2.2.2.1

/-- The selected flattened `List.nil` rule is likewise unindexed. -/
theorem roseFlatNilRuleUnindexed09 :
    roseNestedC.generation.ruleIdx roseFlatRuleConstructor1_09 = [] :=
  roseProducedNilReducerAlignment09.2.2.2.2.1

/-- The selected flattened `List.nil` rule has no constructor-field
continuation. -/
theorem roseFlatNilRuleNoFields09 :
    roseNestedC.generation.ruleFieldCount roseFlatRuleConstructor1_09 = 0 :=
  roseProducedNilReducerAlignment09.2.2.2.1.symm.trans
    roseProducedNilSelectedRuleShape09.2

/-- The selected flattened `List.cons` rule is likewise unindexed. -/
theorem roseFlatConsRuleUnindexed09 :
    roseNestedC.generation.ruleIdx roseFlatRuleConstructor2_09 = [] :=
  roseProducedConsReducerAlignment09.2.2.2.2.1

/-- The selected main Rose rule recovers its owner family directly from the
completed flattened transaction. -/
theorem roseFlatMainRuleOwnerFacts09
    (readiness : RoseFlatCandidateReadiness09) :
    ∃ family,
      (roseNestedStagedCertificate09 readiness).flatCertificate.RuleOwnerFacts
        roseFlatRuleConstructor0_09 family :=
  (roseNestedStagedCertificate09 readiness).flatCertificate.ruleOwnerFacts
    (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry0_09).flat

/-- The selected auxiliary nil rule recovers the certified family owning its
flattened constructor. -/
theorem roseFlatNilRuleOwnerFacts09
    (readiness : RoseFlatCandidateReadiness09) :
    ∃ family,
      (roseNestedStagedCertificate09 readiness).flatCertificate.RuleOwnerFacts
        roseFlatRuleConstructor1_09 family :=
  (roseNestedStagedCertificate09 readiness).flatCertificate.ruleOwnerFacts
    (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry1_09).flat

/-- The selected auxiliary cons rule recovers the certified family owning
its flattened constructor. -/
theorem roseFlatConsRuleOwnerFacts09
    (readiness : RoseFlatCandidateReadiness09) :
    ∃ family,
      (roseNestedStagedCertificate09 readiness).flatCertificate.RuleOwnerFacts
        roseFlatRuleConstructor2_09 family :=
  (roseNestedStagedCertificate09 readiness).flatCertificate.ruleOwnerFacts
    (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry2_09).flat

/-- Complete static package for the selected main Rose rule at the generic
one-parameter reduction consumer: the owner and unindexed shape come from the
same staged certificate, while the flattened declaration supplies the single
shared parameter needed for dependent field transport. -/
theorem roseFlatMainRuleOneParamReductionBoundary09
    (readiness : RoseFlatCandidateReadiness09) :
    ∃ family,
      (roseNestedStagedCertificate09 readiness).flatCertificate.RuleOwnerFacts
          roseFlatRuleConstructor0_09 family ∧
        roseNestedC.generation.ruleIdx roseFlatRuleConstructor0_09 = [] ∧
        roseNestedC.elim.flat.nparams = 1 := by
  obtain ⟨family, owner⟩ := roseFlatMainRuleOwnerFacts09 readiness
  exact ⟨family, owner, roseFlatMainRuleUnindexed09, roseFlatNparams⟩

/-- The selected flattened `List.cons` rule has the same complete
one-parameter reduction boundary, including both dependent constructor
fields. -/
theorem roseFlatConsRuleOneParamReductionBoundary09
    (readiness : RoseFlatCandidateReadiness09) :
    ∃ family,
      (roseNestedStagedCertificate09 readiness).flatCertificate.RuleOwnerFacts
          roseFlatRuleConstructor2_09 family ∧
        roseNestedC.generation.ruleIdx roseFlatRuleConstructor2_09 = [] ∧
        roseNestedC.elim.flat.nparams = 1 := by
  obtain ⟨family, owner⟩ := roseFlatConsRuleOwnerFacts09 readiness
  exact ⟨family, owner, roseFlatConsRuleUnindexed09, roseFlatNparams⟩

/-- Complete static package for the selected flattened nil reduction: its
owner is certificate-derived, it is unindexed, and it has no field
continuation.  Consequently the generated-head reduction consumer leaves
only inductive-head injectivity and the two exact runtime spines. -/
theorem roseFlatNilRuleReductionBoundary09
    (readiness : RoseFlatCandidateReadiness09) :
    ∃ family,
      (roseNestedStagedCertificate09 readiness).flatCertificate.RuleOwnerFacts
          roseFlatRuleConstructor1_09 family ∧
        roseNestedC.generation.ruleIdx roseFlatRuleConstructor1_09 = [] ∧
        roseNestedC.generation.ruleFieldCount
          roseFlatRuleConstructor1_09 = 0 := by
  obtain ⟨family, owner⟩ := roseFlatNilRuleOwnerFacts09 readiness
  exact ⟨family, owner, roseFlatNilRuleUnindexed09,
    roseFlatNilRuleNoFields09⟩

/-- The main rule's canonical Theory captures are exactly the two host slices
used by `inductiveReduceRec`. -/
theorem roseMainCaptureSlices09 (recArgs ctorArgs : List VExpr)
    (hctorLength : ctorArgs.length =
      roseNestedC.generation.ruleArgArity roseFlatRuleConstructor0_09) :
    roseNestedC.generation.ruleCaptureValues roseFlatRuleConstructor0_09
        recArgs ctorArgs =
      recArgs.take roseProducedRestoredRecInfo09.getFirstIndexIdx ++
        ctorArgs.drop
          (ctorArgs.length - roseProducedMainSelectedRule09.nfields) := by
  apply roseNestedC.generation.ruleCaptureValues_eq_reducerSlices
  · exact roseProducedMainReducerAlignment09.2.1
  · exact roseProducedMainReducerAlignment09.2.2.2.1
  · exact hctorLength

/-- The same exact capture-slice alignment for the flattened `List.nil`
rule. -/
theorem roseNilCaptureSlices09 (recArgs ctorArgs : List VExpr)
    (hctorLength : ctorArgs.length =
      roseNestedC.generation.ruleArgArity roseFlatRuleConstructor1_09) :
    roseNestedC.generation.ruleCaptureValues roseFlatRuleConstructor1_09
        recArgs ctorArgs =
      recArgs.take roseProducedRestoredAuxRecInfo09.getFirstIndexIdx ++
        ctorArgs.drop
          (ctorArgs.length - roseProducedNilSelectedRule09.nfields) := by
  apply roseNestedC.generation.ruleCaptureValues_eq_reducerSlices
  · exact roseProducedNilReducerAlignment09.2.1
  · exact roseProducedNilReducerAlignment09.2.2.2.1
  · exact hctorLength

/-- The same exact capture-slice alignment for the flattened `List.cons`
rule. -/
theorem roseConsCaptureSlices09 (recArgs ctorArgs : List VExpr)
    (hctorLength : ctorArgs.length =
      roseNestedC.generation.ruleArgArity roseFlatRuleConstructor2_09) :
    roseNestedC.generation.ruleCaptureValues roseFlatRuleConstructor2_09
        recArgs ctorArgs =
      recArgs.take roseProducedRestoredAuxRecInfo09.getFirstIndexIdx ++
        ctorArgs.drop
          (ctorArgs.length - roseProducedConsSelectedRule09.nfields) := by
  apply roseNestedC.generation.ruleCaptureValues_eq_reducerSlices
  · exact roseProducedConsReducerAlignment09.2.1
  · exact roseProducedConsReducerAlignment09.2.2.2.1
  · exact hctorLength

/-- The one concrete recursor-world restoration entry represents
`List (RoseTree α)`. -/
def roseRecRestoreEntry09 : RestoreEntry where
  aux := roseFlatAuxName09
  np := 1
  value :=
    .app (.const ``List [.param 1])
      (.app
        (.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1])
        (.bvar 0))

theorem roseRecEntries09_eq :
    roseNestedC.recEntries = [roseRecRestoreEntry09] := by
  native_decide

theorem roseNestedRecMap09_eq :
    roseNestedC.recMap =
      [(.str roseFlatAuxName09 "rec",
        `Lean4Lean.NestedRepresentation.RoseTree.rec_1)] := by
  native_decide

/-! ### Concrete constant interpretation for flattened Rose artifacts -/

/-- Declaration-level interpretation of the generated auxiliary family:
`_nested.List_1 α` is represented by `List (RoseTree α)`. -/
def roseAuxFamilyInterpValue09 : VExpr :=
  .lam (.sort (.succ (.param 0)))
    (.app (.const ``List [.param 0])
      (.app
        (.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0])
        (.bvar 0)))

/-- Declaration-level interpretation of the generated auxiliary nil
constructor. -/
def roseAuxNilInterpValue09 : VExpr :=
  .lam (.sort (.succ (.param 0)))
    (.app (.const ``List.nil [.param 0])
      (.app
        (.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0])
        (.bvar 0)))

/-- Declaration-level interpretation of the generated auxiliary cons
constructor.  After its parameter is supplied, the ordinary `List.cons`
field spine remains. -/
def roseAuxConsInterpValue09 : VExpr :=
  .lam (.sort (.succ (.param 0)))
    (.app (.const ``List.cons [.param 0])
      (.app
        (.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0])
        (.bvar 0)))

/-- Canonical σ̂ for the concrete Rose staging transaction.  Constants whose
types change under restoration are interpreted even when their runtime name
is unchanged; the auxiliary recursor is additionally renamed. -/
def roseRestoreInterp09 (name : Name) : Option VExpr :=
  if name = roseFlatAuxName09 then
    some roseAuxFamilyInterpValue09
  else if name = `Lean4Lean.NestedRepresentation.RoseTree.node then
    some (.const `Lean4Lean.NestedRepresentation.RoseTree.node
      (VLevel.params 1))
  else if name = roseFlatAuxName09 ++ `nil then
    some roseAuxNilInterpValue09
  else if name = roseFlatAuxName09 ++ `cons then
    some roseAuxConsInterpValue09
  else if name = `Lean4Lean.NestedRepresentation.RoseTree.rec then
    some (.const `Lean4Lean.NestedRepresentation.RoseTree.rec
      (VLevel.params 2))
  else if name = .str roseFlatAuxName09 "rec" then
    some (.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
      (VLevel.params 2))
  else none

theorem roseRestoreInterp_auxFamily09 :
    roseRestoreInterp09 roseFlatAuxName09 =
      some roseAuxFamilyInterpValue09 := by
  native_decide

theorem roseRestoreInterp_mainCtor09 :
    roseRestoreInterp09
        `Lean4Lean.NestedRepresentation.RoseTree.node =
      some (.const `Lean4Lean.NestedRepresentation.RoseTree.node
        (VLevel.params 1)) := by
  native_decide

theorem roseRestoreInterp_auxNil09 :
    roseRestoreInterp09 (roseFlatAuxName09 ++ `nil) =
      some roseAuxNilInterpValue09 := by
  native_decide

theorem roseRestoreInterp_auxCons09 :
    roseRestoreInterp09 (roseFlatAuxName09 ++ `cons) =
      some roseAuxConsInterpValue09 := by
  native_decide

theorem roseRestoreInterp_mainRec09 :
    roseRestoreInterp09
        `Lean4Lean.NestedRepresentation.RoseTree.rec =
      some (.const `Lean4Lean.NestedRepresentation.RoseTree.rec
        (VLevel.params 2)) := by
  native_decide

theorem roseRestoreInterp_auxRec09 :
    roseRestoreInterp09 (.str roseFlatAuxName09 "rec") =
      some (.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
        (VLevel.params 2)) := by
  native_decide

/-- Literal-name form of the auxiliary recursor lookup used after concrete
reflattening has normalized the generated namespace. -/
theorem roseRestoreInterp_auxRecLiteral09 :
    roseRestoreInterp09 `_nested.List_1.rec =
      some (.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
        (VLevel.params 2)) := by
  simpa only [roseFlatAuxName09] using roseRestoreInterp_auxRec09

theorem roseRestoreInterp_listFamily09 :
    roseRestoreInterp09 ``List = none := by
  native_decide

theorem roseRestoreInterp_listNil09 :
    roseRestoreInterp09 ``List.nil = none := by
  native_decide

theorem roseRestoreInterp_listCons09 :
    roseRestoreInterp09 ``List.cons = none := by
  native_decide

theorem roseRestoreInterp_listRec09 :
    roseRestoreInterp09 ``List.rec = none := by
  native_decide

theorem roseRestoreInterp_mainFamily09 :
    roseRestoreInterp09
      `Lean4Lean.NestedRepresentation.RoseTree = none := by
  native_decide

/-- Literal-name lookup forms used after the concrete reflattening function
has reduced `roseFlatAuxName09`. -/
theorem roseRestoreInterp_auxFamilyLiteral09 :
    roseRestoreInterp09 `_nested.List_1 =
      some roseAuxFamilyInterpValue09 := by
  simpa only [roseFlatAuxName09] using roseRestoreInterp_auxFamily09

theorem roseRestoreInterp_auxNilLiteral09 :
    roseRestoreInterp09 (`_nested.List_1 ++ `nil) =
      some roseAuxNilInterpValue09 := by
  simpa only [roseFlatAuxName09] using roseRestoreInterp_auxNil09

theorem roseRestoreInterp_auxConsLiteral09 :
    roseRestoreInterp09 (`_nested.List_1 ++ `cons) =
      some roseAuxConsInterpValue09 := by
  simpa only [roseFlatAuxName09] using roseRestoreInterp_auxCons09

/-- Every value selected by the concrete Rose interpretation is closed, the
first proof field required by the flat-to-final environment morphism. -/
theorem roseRestoreInterpClosed09 :
    InterpClosed roseRestoreInterp09 := by
  intro c v h
  unfold roseRestoreInterp09 at h
  split at h
  · cases h
    simp [roseAuxFamilyInterpValue09, VExpr.ClosedN]
  · split at h
    · cases h
      simp [VExpr.ClosedN]
    · split at h
      · cases h
        simp [roseAuxNilInterpValue09, VExpr.ClosedN]
      · split at h
        · cases h
          simp [roseAuxConsInterpValue09, VExpr.ClosedN]
        · split at h
          · cases h
            simp [VExpr.ClosedN]
          · split at h
            · cases h
              simp [VExpr.ClosedN]
            · cases h

/-- The generated auxiliary-family closure itself has the σ̂-image of the
flattened family type. -/
theorem roseAuxFamilyInterpValueTyping09 :
    roseFinalEnv09.HasType 1 [] roseAuxFamilyInterpValue09
      (roseFlatAuxFamily09.type.substConst roseRestoreInterp09) := by
  rose_rule_hyps roseFinalEnv09
  simp [roseFlatAuxFamily09, roseAuxFamilyInterpValue09,
    roseFlatAuxName09, VExpr.substConst]
  type_tac

/-- Declaration-level β-collapse of the interpreted auxiliary family.  This
is the reusable type-alignment atom for the flattened main and auxiliary
constructor values. -/
theorem roseSubstAuxFamilyBeta09
    {Γ : List VExpr} {param : VExpr}
    (hparamType : roseFinalEnv09.HasType 1 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 0)))) :
    roseFinalEnv09.IsDefEq 1 Γ
      (((VExpr.const roseFlatAuxName09 [.param 0]).appN [param]).substConst
        roseRestoreInterp09)
      ((VExpr.const ``List [.param 0]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
          (param.substConst roseRestoreInterp09)))
      (.sort (.succ (.param 0))) := by
  let binder : VExpr := .sort (.succ (.param 0))
  let body : VExpr :=
    (VExpr.const ``List [.param 0]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
        (.bvar 0))
  have hTel : roseFinalEnv09.OnTel 1 Γ [binder] := by
    refine ⟨?_, trivial⟩
    exact ⟨_, VEnv.HasType.sort (by decide)⟩
  have hbody : roseFinalEnv09.HasType 1
      ([binder].reverse ++ Γ) body (.sort (.succ (.param 0))) := by
    rose_rule_hyps roseFinalEnv09
    simp only [binder, body, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
    type_tac
  have hspine : roseFinalEnv09.SpineWF 1 Γ
      (VExpr.forallN [binder] (.sort (.succ (.param 0))))
      [param.substConst roseRestoreInterp09]
      (.sort (.succ (.param 0))) := by
    exact .cons hparamType .nil
  have hbeta := VEnv.IsDefEq.substConst_aux_beta_instL
    roseNestedCertificate09.afterWF.ordered
    (interp := roseRestoreInterp09) (aux := roseFlatAuxName09)
    (levels := [.param 0]) (args := [param])
    (As := [.sort (.succ (.param 0))])
    (body :=
      (VExpr.const ``List [.param 0]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
          (.bvar 0)))
    roseRestoreInterp_auxFamily09
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hTel)
    (by simpa [body, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hbody)
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hspine) rfl
  simpa [binder, body, roseAuxFamilyInterpValue09, VExpr.lamN,
    VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD,
    VExpr.instRev, VExpr.inst, VExpr.instVar, VExpr.liftN] using hbeta

/-- The same declaration-level auxiliary-family collapse instantiated in the
two-universe recursor world.  Keeping this certificate separate from the
one-universe constructor case avoids relying on raw kernel reduction when a
restored family occurs inside a recursor telescope. -/
theorem roseSubstAuxFamilyBetaRec09
    {Γ : List VExpr} {param : VExpr}
    (hparamType : roseFinalEnv09.HasType 2 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 1)))) :
    roseFinalEnv09.IsDefEq 2 Γ
      (((VExpr.const roseFlatAuxName09 [.param 1]).appN [param]).substConst
        roseRestoreInterp09)
      ((VExpr.const ``List [.param 1]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
          (param.substConst roseRestoreInterp09)))
      (.sort (.succ (.param 1))) := by
  let binder : VExpr := .sort (.succ (.param 1))
  let body : VExpr :=
    (VExpr.const ``List [.param 1]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (.bvar 0))
  have hTel : roseFinalEnv09.OnTel 2 Γ [binder] := by
    refine ⟨?_, trivial⟩
    exact ⟨_, VEnv.HasType.sort (by decide)⟩
  have hbody : roseFinalEnv09.HasType 2
      ([binder].reverse ++ Γ) body (.sort (.succ (.param 1))) := by
    rose_rule_hyps roseFinalEnv09
    simp only [binder, body, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
    type_tac
  have hspine : roseFinalEnv09.SpineWF 2 Γ
      (VExpr.forallN [binder] (.sort (.succ (.param 1))))
      [param.substConst roseRestoreInterp09]
      (.sort (.succ (.param 1))) :=
    .cons hparamType .nil
  have hbeta := VEnv.IsDefEq.substConst_aux_beta_instL
    roseNestedCertificate09.afterWF.ordered
    (interp := roseRestoreInterp09) (aux := roseFlatAuxName09)
    (levels := [.param 1]) (args := [param])
    (As := [.sort (.succ (.param 0))])
    (body :=
      (VExpr.const ``List [.param 0]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
          (.bvar 0)))
    roseRestoreInterp_auxFamily09
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hTel)
    (by simpa [body, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hbody)
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hspine) rfl
  simpa [binder, body, roseAuxFamilyInterpValue09, VExpr.lamN,
    VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD,
    VExpr.instRev, VExpr.inst, VExpr.instVar, VExpr.liftN] using hbeta

/-- The unchanged main constructor is typed at its σ̂-imaged flattened type;
the only nonreflexive domain is discharged by auxiliary-family beta. -/
theorem roseMainCtorInterpValueTyping09 :
    roseFinalEnv09.HasType 1 []
      (.const `Lean4Lean.NestedRepresentation.RoseTree.node
        (VLevel.params 1))
      (roseFlatNode09.type.substConst roseRestoreInterp09) := by
  let A : VExpr := .sort (.succ (.param 0))
  let roseAt (i : Nat) : VExpr :=
    (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
      (.bvar i)
  let listRoseAt (i : Nat) : VExpr :=
    (VExpr.const ``List [.param 0]).app (roseAt i)
  let auxAt (i : Nat) : VExpr :=
    ((VExpr.const roseFlatAuxName09 [.param 0]).appN [.bvar i]).substConst
      roseRestoreInterp09
  have hv : roseFinalEnv09.HasType 1 []
      (.const `Lean4Lean.NestedRepresentation.RoseTree.node
        (VLevel.params 1))
      (.forallE A (.forallE (.bvar 0)
        (.forallE (listRoseAt 1) (roseAt 2)))) := by
    rose_rule_hyps roseFinalEnv09
    simp only [A, roseAt, listRoseAt]
    type_tac
  have hA : roseFinalEnv09.IsDefEq 1 [] A A
      (.sort (.succ (.succ (.param 0)))) :=
    VEnv.HasType.sort (by decide)
  have hAlpha : roseFinalEnv09.IsDefEq 1 [A]
      (.bvar 0) (.bvar 0) A := by
    simp only [A]
    type_tac
  have hparam : roseFinalEnv09.HasType 1 [.bvar 0, A]
      (.bvar 1) A := by
    simp only [A]
    type_tac
  have hList : roseFinalEnv09.IsDefEq 1 [.bvar 0, A]
      (listRoseAt 1) (auxAt 1) (.sort (.succ (.param 0))) := by
    simpa [A, roseAt, listRoseAt, auxAt, VExpr.substConst] using
      (roseSubstAuxFamilyBeta09
        (Γ := [.bvar 0, A]) (param := .bvar 1)
        (by simpa [VExpr.substConst] using hparam)).symm
  have hResult : roseFinalEnv09.IsDefEq 1
      [listRoseAt 1, .bvar 0, A]
      (roseAt 2) (roseAt 2) (.sort (.succ (.param 0))) := by
    rose_rule_hyps roseFinalEnv09
    simp only [A, roseAt, listRoseAt]
    type_tac
  have htype := VEnv.IsDefEq.forallEDF hA
    (VEnv.IsDefEq.forallEDF hAlpha
      (VEnv.IsDefEq.forallEDF hList hResult))
  have hout := htype.defeq hv
  simpa [A, roseAt, listRoseAt, auxAt, roseFlatNode09,
    VExpr.substConst, VExpr.substConst_appN, VExpr.appN,
    roseRestoreInterp_auxFamily09, roseRestoreInterp_mainFamily09] using hout

/-- The auxiliary nil closure is typed at the σ̂-imaged flattened nil type. -/
theorem roseAuxNilInterpValueTyping09 :
    roseFinalEnv09.HasType 1 [] roseAuxNilInterpValue09
      (roseFlatNil09.type.substConst roseRestoreInterp09) := by
  let A : VExpr := .sort (.succ (.param 0))
  let listRose : VExpr :=
    (VExpr.const ``List [.param 0]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
        (.bvar 0))
  let auxApp : VExpr :=
    ((VExpr.const roseFlatAuxName09 [.param 0]).appN [.bvar 0]).substConst
      roseRestoreInterp09
  have hv : roseFinalEnv09.HasType 1 [] roseAuxNilInterpValue09
      (.forallE A listRose) := by
    rose_rule_hyps roseFinalEnv09
    simp only [A, listRose, roseAuxNilInterpValue09]
    type_tac
  have hparam : roseFinalEnv09.HasType 1 [A] (.bvar 0) A := by
    have hz : Lookup [A] 0 A := by
      simpa [A, VExpr.lift, VExpr.liftN] using
        (Lookup.zero (ty := A) (Γ := []))
    exact VEnv.HasType.bvar hz
  have hcod : roseFinalEnv09.IsDefEq 1 [A] listRose auxApp
      (.sort (.succ (.param 0))) := by
    simpa [A, listRose, auxApp, VExpr.substConst] using
      (roseSubstAuxFamilyBeta09 (Γ := [A]) (param := .bvar 0)
        (by simpa [VExpr.substConst] using hparam)).symm
  have hdom : roseFinalEnv09.IsDefEq 1 [] A A
      (.sort (.succ (.succ (.param 0)))) := by
    exact VEnv.HasType.sort (by decide)
  have htype := VEnv.IsDefEq.forallEDF hdom hcod
  have hout := htype.defeq hv
  simpa [A, listRose, auxApp, roseFlatNil09, VExpr.substConst,
    VExpr.substConst_appN, VExpr.appN, roseRestoreInterp_auxFamily09] using hout

/-- The auxiliary cons closure is typed at the σ̂-imaged flattened cons type,
including both occurrences of the represented-family field/result type. -/
theorem roseAuxConsInterpValueTyping09 :
    roseFinalEnv09.HasType 1 [] roseAuxConsInterpValue09
      (roseFlatCons09.type.substConst roseRestoreInterp09) := by
  let A : VExpr := .sort (.succ (.param 0))
  let roseAt (i : Nat) : VExpr :=
    (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
      (.bvar i)
  let listRoseAt (i : Nat) : VExpr :=
    (VExpr.const ``List [.param 0]).app (roseAt i)
  let auxAt (i : Nat) : VExpr :=
    ((VExpr.const roseFlatAuxName09 [.param 0]).appN [.bvar i]).substConst
      roseRestoreInterp09
  have hv : roseFinalEnv09.HasType 1 [] roseAuxConsInterpValue09
      (.forallE A (.forallE (roseAt 0)
        (.forallE (listRoseAt 1) (listRoseAt 2)))) := by
    rose_rule_hyps roseFinalEnv09
    simp only [A, roseAt, listRoseAt, roseAuxConsInterpValue09]
    type_tac
  have hA : roseFinalEnv09.IsDefEq 1 [] A A
      (.sort (.succ (.succ (.param 0)))) :=
    VEnv.HasType.sort (by decide)
  have hRose : roseFinalEnv09.IsDefEq 1 [A]
      (roseAt 0) (roseAt 0) (.sort (.succ (.param 0))) := by
    rose_rule_hyps roseFinalEnv09
    simp only [A, roseAt]
    type_tac
  have hparam1 : roseFinalEnv09.HasType 1 [roseAt 0, A]
      (.bvar 1) A := by
    rose_rule_hyps roseFinalEnv09
    simp only [A, roseAt]
    type_tac
  have hList : roseFinalEnv09.IsDefEq 1 [roseAt 0, A]
      (listRoseAt 1) (auxAt 1) (.sort (.succ (.param 0))) := by
    simpa [A, roseAt, listRoseAt, auxAt, VExpr.substConst] using
      (roseSubstAuxFamilyBeta09
        (Γ := [roseAt 0, A]) (param := .bvar 1)
        (by simpa [VExpr.substConst] using hparam1)).symm
  have hparam2 : roseFinalEnv09.HasType 1
      [listRoseAt 1, roseAt 0, A] (.bvar 2) A := by
    rose_rule_hyps roseFinalEnv09
    simp only [A, roseAt, listRoseAt]
    type_tac
  have hResult : roseFinalEnv09.IsDefEq 1
      [listRoseAt 1, roseAt 0, A]
      (listRoseAt 2) (auxAt 2) (.sort (.succ (.param 0))) := by
    simpa [A, roseAt, listRoseAt, auxAt, VExpr.substConst] using
      (roseSubstAuxFamilyBeta09
        (Γ := [listRoseAt 1, roseAt 0, A]) (param := .bvar 2)
        (by simpa [VExpr.substConst] using hparam2)).symm
  have htype := VEnv.IsDefEq.forallEDF hA
    (VEnv.IsDefEq.forallEDF hRose
      (VEnv.IsDefEq.forallEDF hList hResult))
  have hout := htype.defeq hv
  simpa [A, roseAt, listRoseAt, auxAt, roseFlatCons09,
    VExpr.substConst, VExpr.substConst_appN, VExpr.appN,
    roseRestoreInterp_auxFamily09, roseRestoreInterp_mainFamily09] using hout

/-- Finite classification of the concrete interpretation's value field.
Family and constructor cases are closed above; only the two whole recursor
type alignments remain explicit. -/
theorem roseRestoreInterpValueOfRecursors09
    (hmainRec : roseFinalEnv09.HasType 2 []
      (.const `Lean4Lean.NestedRepresentation.RoseTree.rec
        (VLevel.params 2))
      ((roseNestedC.generation.recursors[0]!).type.substConst
        roseRestoreInterp09))
    (hauxRec : roseFinalEnv09.HasType 2 []
      (.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
        (VLevel.params 2))
      ((roseNestedC.generation.recursors[1]!).type.substConst
        roseRestoreInterp09))
    {c : Name} {ci : VConstant} {v : VExpr}
    (hflat : roseFlatFinalEnv09.constants c = some ci)
    (hinterp : roseRestoreInterp09 c = some v) :
    roseFinalEnv09.HasType ci.uvars [] v
      (ci.type.substConst roseRestoreInterp09) := by
  unfold roseRestoreInterp09 at hinterp
  split at hinterp <;> rename_i hc
  · have hc' : c = roseFlatAuxName09 := by simpa using hc
    subst c
    cases hinterp
    have hci : roseFlatFinalEnv09.constants roseFlatAuxName09 =
        some roseFlatAuxFamily09.toVConstant := by native_decide
    rw [hci] at hflat
    cases hflat
    exact roseAuxFamilyInterpValueTyping09
  · split at hinterp <;> rename_i hcNode
    · have hcNode' : c =
          `Lean4Lean.NestedRepresentation.RoseTree.node := by
        simpa using hcNode
      subst c
      cases hinterp
      have hci : roseFlatFinalEnv09.constants
          `Lean4Lean.NestedRepresentation.RoseTree.node =
            some roseFlatNode09.toVConstant := by native_decide
      rw [hci] at hflat
      cases hflat
      exact roseMainCtorInterpValueTyping09
    · split at hinterp <;> rename_i hcNil
      · have hcNil' : c = roseFlatAuxName09 ++ `nil := by
          simpa using hcNil
        subst c
        cases hinterp
        have hci : roseFlatFinalEnv09.constants
            (roseFlatAuxName09 ++ `nil) =
              some roseFlatNil09.toVConstant := by native_decide
        rw [hci] at hflat
        cases hflat
        exact roseAuxNilInterpValueTyping09
      · split at hinterp <;> rename_i hcCons
        · have hcCons' : c = roseFlatAuxName09 ++ `cons := by
            simpa using hcCons
          subst c
          cases hinterp
          have hci : roseFlatFinalEnv09.constants
              (roseFlatAuxName09 ++ `cons) =
                some roseFlatCons09.toVConstant := by native_decide
          rw [hci] at hflat
          cases hflat
          exact roseAuxConsInterpValueTyping09
        · split at hinterp <;> rename_i hcRec
          · have hcRec' : c =
                `Lean4Lean.NestedRepresentation.RoseTree.rec := by
              simpa using hcRec
            subst c
            cases hinterp
            have hci : roseFlatFinalEnv09.constants
                `Lean4Lean.NestedRepresentation.RoseTree.rec =
                  some (roseNestedC.generation.recursors[0]!).toVConstant := by
              native_decide
            rw [hci] at hflat
            cases hflat
            rw [show (roseNestedC.generation.recursors[0]!).uvars = 2 by
              native_decide]
            exact hmainRec
          · split at hinterp <;> rename_i hcRec1
            · have hcRec1' : c = .str roseFlatAuxName09 "rec" := by
                simpa using hcRec1
              subst c
              cases hinterp
              have hci : roseFlatFinalEnv09.constants
                  (.str roseFlatAuxName09 "rec") =
                    some (roseNestedC.generation.recursors[1]!).toVConstant := by
                native_decide
              rw [hci] at hflat
              cases hflat
              rw [show (roseNestedC.generation.recursors[1]!).uvars = 2 by
                native_decide]
              exact hauxRec
            · cases hinterp

/-- The flattened Rose staging transaction contains no structure-eta rules:
it is built from the eta-free completed List fixture using only constant and
definitional-equation insertions. -/
theorem roseFlatNoStructEta09 (rule : VStructEta) :
    ¬ roseFlatFinalEnv09.structEtas rule := by
  intro h
  rw [roseFlatFinalEnv09,
    VEnv.foldl_addDefEq_structEtas_iff] at h
  have h := (VEnv.addConst_structEtas_iff
    roseFlatAddSecondRec09 rule).mp h
  have h := (VEnv.addConst_structEtas_iff
    roseFlatAddFirstRec09 rule).mp h
  have h := (VEnv.addConst_structEtas_iff
    roseFlatAddCons09 rule).mp h
  have h := (VEnv.addConst_structEtas_iff
    roseFlatAddNil09 rule).mp h
  have h := (VEnv.addConst_structEtas_iff
    roseFlatAddNode09 rule).mp h
  have h := (VEnv.addConst_structEtas_iff
    roseFlatBlockEnv09_eq rule).mp h
  have h := (VEnv.addConst_structEtas_iff
    roseFlatFirstTypeEnv09_eq rule).mp h
  exact h

/-- Restoration renames the complete flattened auxiliary recursor spine and
recursively restores every argument. -/
theorem roseRestoreAuxRecSpine09 (levels : List VLevel)
    (args : List VExpr) :
    roseNestedC.restoreRec
      ((VExpr.const (.str roseFlatAuxName09 "rec") levels).appN args) =
    (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 levels).appN
      (args.map roseNestedC.restoreRec) := by
  apply VInductDecl.restoreExpr_rec_appN
  all_goals
    simp only [roseRecEntries09_eq, roseNestedRecMap09_eq]
    decide

/-- The main recursor head is inert under restoration, while its complete
argument spine is restored recursively. -/
theorem roseRestoreMainRecSpine09 (levels : List VLevel)
    (args : List VExpr) :
    roseNestedC.restoreRec
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
        levels).appN args) =
    (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
      levels).appN (args.map roseNestedC.restoreRec) := by
  apply VInductDecl.restoreExpr_appN_of_head_inert
    (name := `Lean4Lean.NestedRepresentation.RoseTree.rec)
    (ls := levels)
  · change VInductDecl.restoreExpr roseNestedC.recEntries
      roseNestedC.recMap
      (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec levels) = _
    rw [roseRecEntries09_eq, roseNestedRecMap09_eq]
    rfl
  · rfl
  all_goals
    simp only [roseRecEntries09_eq, roseNestedRecMap09_eq]
    decide

/-- The source `RoseTree.node` constructor is likewise inert at its head. -/
theorem roseRestoreMainCtorSpine09 (levels : List VLevel)
    (args : List VExpr) :
    roseNestedC.restoreRec
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
        levels).appN args) =
    (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
      levels).appN (args.map roseNestedC.restoreRec) := by
  apply VInductDecl.restoreExpr_appN_of_head_inert
    (name := `Lean4Lean.NestedRepresentation.RoseTree.node)
    (ls := levels)
  · change VInductDecl.restoreExpr roseNestedC.recEntries
      roseNestedC.recMap
      (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node levels) = _
    rw [roseRecEntries09_eq, roseNestedRecMap09_eq]
    rfl
  · rfl
  all_goals
    simp only [roseRecEntries09_eq, roseNestedRecMap09_eq]
    decide

/-- At every complete two-level auxiliary-recursor instantiation, σ̂ is
exactly recursive restoration once the argument images agree pointwise. -/
theorem roseSubstRestoreAuxRecSpineLevels09
    (levels : List VLevel) (args : List VExpr)
    (hlen : levels.length = 2)
    (hargs : args.map roseNestedC.restoreRec =
      args.map (VExpr.substConst roseRestoreInterp09)) :
    (((VExpr.const (.str roseFlatAuxName09 "rec") levels).appN args).substConst
        roseRestoreInterp09) =
      roseNestedC.restoreRec
        ((VExpr.const (.str roseFlatAuxName09 "rec") levels).appN args) := by
  rw [VExpr.substConst_appN, roseRestoreAuxRecSpine09]
  simp only [VExpr.substConst, roseRestoreInterp_auxRec09]
  change (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
      ((VLevel.params 2).map (VLevel.inst levels))).appN
        (args.map (VExpr.substConst roseRestoreInterp09)) = _
  rw [VLevel.inst_map_id hlen, ← hargs]

/-- Direct runtime normal form of σ̂ on an auxiliary recursor spine. -/
theorem roseSubstAuxRecSpineLevels09
    (levels : List VLevel) (args : List VExpr)
    (hlen : levels.length = 2) :
    (((VExpr.const (.str roseFlatAuxName09 "rec") levels).appN args).substConst
        roseRestoreInterp09) =
      (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
        levels).appN (args.map (VExpr.substConst roseRestoreInterp09)) := by
  rw [VExpr.substConst_appN]
  simp only [VExpr.substConst, roseRestoreInterp_auxRec09]
  change (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
      ((VLevel.params 2).map (VLevel.inst levels))).appN _ = _
  rw [VLevel.inst_map_id hlen]

/-- Canonical-parameter specialization of the level-polymorphic auxiliary
recursor alignment. -/
theorem roseSubstRestoreAuxRecSpine09
    (args : List VExpr)
    (hargs : args.map roseNestedC.restoreRec =
      args.map (VExpr.substConst roseRestoreInterp09)) :
    (((VExpr.const (.str roseFlatAuxName09 "rec")
        (VLevel.params 2)).appN args).substConst roseRestoreInterp09) =
      roseNestedC.restoreRec
        ((VExpr.const (.str roseFlatAuxName09 "rec")
          (VLevel.params 2)).appN args) := by
  exact roseSubstRestoreAuxRecSpineLevels09 (VLevel.params 2) args
    (by simp) hargs

/-- The unchanged main recursor head has the same exact agreement for every
complete two-level instantiation. -/
theorem roseSubstRestoreMainRecSpineLevels09
    (levels : List VLevel) (args : List VExpr)
    (hlen : levels.length = 2)
    (hargs : args.map roseNestedC.restoreRec =
      args.map (VExpr.substConst roseRestoreInterp09)) :
    (((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec levels).appN
        args).substConst roseRestoreInterp09) =
      roseNestedC.restoreRec
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec levels).appN
          args) := by
  rw [VExpr.substConst_appN, roseRestoreMainRecSpine09]
  simp only [VExpr.substConst, roseRestoreInterp_mainRec09]
  change (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
      ((VLevel.params 2).map (VLevel.inst levels))).appN
        (args.map (VExpr.substConst roseRestoreInterp09)) = _
  rw [VLevel.inst_map_id hlen, ← hargs]

/-- Direct runtime normal form of σ̂ on the main recursor spine. -/
theorem roseSubstMainRecSpineLevels09
    (levels : List VLevel) (args : List VExpr)
    (hlen : levels.length = 2) :
    (((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec levels).appN
        args).substConst roseRestoreInterp09) =
      (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
        levels).appN (args.map (VExpr.substConst roseRestoreInterp09)) := by
  rw [VExpr.substConst_appN]
  simp only [VExpr.substConst, roseRestoreInterp_mainRec09]
  change (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
      ((VLevel.params 2).map (VLevel.inst levels))).appN _ = _
  rw [VLevel.inst_map_id hlen]

/-- Canonical-parameter specialization of the main recursor alignment. -/
theorem roseSubstRestoreMainRecSpine09
    (args : List VExpr)
    (hargs : args.map roseNestedC.restoreRec =
      args.map (VExpr.substConst roseRestoreInterp09)) :
    (((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
        (VLevel.params 2)).appN args).substConst roseRestoreInterp09) =
      roseNestedC.restoreRec
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
          (VLevel.params 2)).appN args) := by
  exact roseSubstRestoreMainRecSpineLevels09 (VLevel.params 2) args
    (by simp) hargs

/-- The unchanged source constructor head agrees exactly at every complete
one-level instantiation. -/
theorem roseSubstRestoreMainCtorSpineLevels09
    (levels : List VLevel) (args : List VExpr)
    (hlen : levels.length = 1)
    (hargs : args.map roseNestedC.restoreRec =
      args.map (VExpr.substConst roseRestoreInterp09)) :
    (((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node levels).appN
        args).substConst roseRestoreInterp09) =
      roseNestedC.restoreRec
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node levels).appN
          args) := by
  rw [VExpr.substConst_appN, roseRestoreMainCtorSpine09]
  simp only [VExpr.substConst, roseRestoreInterp_mainCtor09]
  change (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
      ((VLevel.params 1).map (VLevel.inst levels))).appN
        (args.map (VExpr.substConst roseRestoreInterp09)) = _
  rw [VLevel.inst_map_id hlen, ← hargs]

/-- Direct runtime normal form of σ̂ on the main constructor spine. -/
theorem roseSubstMainCtorSpineLevels09
    (levels : List VLevel) (args : List VExpr)
    (hlen : levels.length = 1) :
    (((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node levels).appN
        args).substConst roseRestoreInterp09) =
      (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
        levels).appN (args.map (VExpr.substConst roseRestoreInterp09)) := by
  rw [VExpr.substConst_appN]
  simp only [VExpr.substConst, roseRestoreInterp_mainCtor09]
  change (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
      ((VLevel.params 1).map (VLevel.inst levels))).appN _ = _
  rw [VLevel.inst_map_id hlen]

/-- Canonical-parameter specialization of the main constructor alignment. -/
theorem roseSubstRestoreMainCtorSpine09
    (args : List VExpr)
    (hargs : args.map roseNestedC.restoreRec =
      args.map (VExpr.substConst roseRestoreInterp09)) :
    (((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
        (VLevel.params 1)).appN args).substConst roseRestoreInterp09) =
      roseNestedC.restoreRec
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
          (VLevel.params 1)).appN args) := by
  exact roseSubstRestoreMainCtorSpineLevels09 (VLevel.params 1) args
    (by simp) hargs

/-- Saturating the flattened `nil` constructor at its sole parameter
restores the host `List.nil (RoseTree α)` prefix. -/
theorem roseRestoreNilPrefix09 (levels : List VLevel) (param : VExpr) :
    roseNestedC.restoreRec
      ((VExpr.const (roseFlatAuxName09 ++ `nil) levels).appN [param]) =
    (VExpr.const ``List.nil [.param 1]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (roseNestedC.restoreRec param)) := by
  have h := VInductDecl.restoreExpr_ctor_appN
    (entries := roseNestedC.recEntries)
    (recMap := roseNestedC.recMap)
    (entry := roseRecRestoreEntry09)
    (ctor := roseFlatAuxName09 ++ `nil)
    (suffix := `nil) (target := ``List)
    (ls := levels) (targetLevels := [.param 1])
    (valueArgs :=
      [.app
        (.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1])
        (.bvar 0)])
    (args := [param])
    (by simp only [roseNestedRecMap09_eq]; decide)
    (by simp only [roseRecEntries09_eq]; decide)
    (by simp only [roseRecEntries09_eq]; decide) rfl rfl
  have hsuffix : ``List ++ `nil = ``List.nil := by decide
  rw [← hsuffix]
  simpa [NestedBlockChecked.restoreRec, roseRecRestoreEntry09,
    VInductDecl.instRevParams, VExpr.instRev, VExpr.inst,
    VExpr.instN_appN, VExpr.instVar, VExpr.liftN, VExpr.appN] using h

/-- At the generated rule's recursor-world level, the canonical σ̂-image of
the saturated auxiliary nil prefix β-reduces to its exact nested restoration.
The sole dynamic premise types the interpreted family parameter. -/
theorem roseSubstRestoreNilPrefixDefEq09
    {Γ : List VExpr} {param : VExpr}
    (hparam : roseNestedC.restoreRec param =
      param.substConst roseRestoreInterp09)
    (hparamType : roseFinalEnv09.HasType 2 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 1)))) :
    roseFinalEnv09.IsDefEq 2 Γ
      (((VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
        [param]).substConst roseRestoreInterp09)
      (roseNestedC.restoreRec
        ((VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
          [param]))
      ((VExpr.const ``List [.param 1]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
          (param.substConst roseRestoreInterp09))) := by
  let binder : VExpr := .sort (.succ (.param 1))
  let body : VExpr :=
    (VExpr.const ``List.nil [.param 1]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (.bvar 0))
  let bodyType : VExpr :=
    (VExpr.const ``List [.param 1]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (.bvar 0))
  have hTel : roseFinalEnv09.OnTel 2 Γ [binder] := by
    refine ⟨?_, trivial⟩
    have hb : roseFinalEnv09.HasType 2 Γ
        (.sort (.succ (.param 1))) (.sort (.succ (.succ (.param 1)))) :=
      VEnv.HasType.sort (by decide)
    exact ⟨_, by simpa only [binder] using hb⟩
  have hbody : roseFinalEnv09.HasType 2
      ([binder].reverse ++ Γ) body bodyType := by
    rose_rule_hyps roseFinalEnv09
    simp only [binder, body, bodyType, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
    type_tac
  have hspine : roseFinalEnv09.SpineWF 2 Γ
      (VExpr.forallN [binder] bodyType)
      [param.substConst roseRestoreInterp09]
      ((VExpr.const ``List [.param 1]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
          (param.substConst roseRestoreInterp09))) := by
    refine .cons hparamType ?_
    simpa [binder, bodyType, VExpr.forallN, VExpr.inst, VExpr.instVar,
      VExpr.liftN] using
      (VEnv.SpineWF.nil (env := roseFinalEnv09) (uvars := 2) (Γ := Γ)
        (A := (VExpr.const ``List [.param 1]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (param.substConst roseRestoreInterp09))))
  have hbeta := VEnv.IsDefEq.substConst_aux_beta_instL
    roseNestedCertificate09.afterWF.ordered
    (interp := roseRestoreInterp09)
    (aux := roseFlatAuxName09 ++ `nil)
    (levels := [.param 1])
    (args := [param])
    (As := [.sort (.succ (.param 0))])
    (body :=
      (VExpr.const ``List.nil [.param 0]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
          (.bvar 0)))
    (by simpa [roseAuxNilInterpValue09, VExpr.lamN] using
      roseRestoreInterp_auxNil09)
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hTel)
    (by simpa [body, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hbody)
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hspine) rfl
  rw [roseRestoreNilPrefix09, hparam]
  simpa [binder, body, bodyType, roseAuxNilInterpValue09,
    VExpr.lamN, VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD,
    VExpr.instRev, VExpr.inst, VExpr.instVar, VExpr.liftN] using hbeta

/-- Saturating the flattened `cons` constructor at its sole parameter
restores the host `List.cons (RoseTree α)` prefix. -/
theorem roseRestoreConsPrefix09 (levels : List VLevel) (param : VExpr) :
    roseNestedC.restoreRec
      ((VExpr.const (roseFlatAuxName09 ++ `cons) levels).appN [param]) =
    (VExpr.const ``List.cons [.param 1]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (roseNestedC.restoreRec param)) := by
  have h := VInductDecl.restoreExpr_ctor_appN
    (entries := roseNestedC.recEntries)
    (recMap := roseNestedC.recMap)
    (entry := roseRecRestoreEntry09)
    (ctor := roseFlatAuxName09 ++ `cons)
    (suffix := `cons) (target := ``List)
    (ls := levels) (targetLevels := [.param 1])
    (valueArgs :=
      [.app
        (.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1])
        (.bvar 0)])
    (args := [param])
    (by simp only [roseNestedRecMap09_eq]; decide)
    (by simp only [roseRecEntries09_eq]; decide)
    (by simp only [roseRecEntries09_eq]; decide) rfl rfl
  have hsuffix : ``List ++ `cons = ``List.cons := by decide
  rw [← hsuffix]
  simpa [NestedBlockChecked.restoreRec, roseRecRestoreEntry09,
    VInductDecl.instRevParams, VExpr.instRev, VExpr.inst,
    VExpr.instN_appN, VExpr.instVar, VExpr.liftN, VExpr.appN] using h

/-- Exact residual two-field telescope after σ̂ supplies the auxiliary cons
constructor's represented-family parameter. -/
def roseConsPrefixType09 (param : VExpr) : VExpr :=
  (VExpr.forallE
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (.bvar 0))
      (.forallE
        ((VExpr.const ``List [.param 1]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (.bvar 1)))
        ((VExpr.const ``List [.param 1]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (.bvar 2))))).inst (param.substConst roseRestoreInterp09)

/-- At the generated rule's recursor-world level, the canonical σ̂-image of
the saturated auxiliary cons prefix β-reduces to its exact nested restoration.
The exact residual constructor telescope is retained for typed trailing-field
congruence. -/
theorem roseSubstRestoreConsPrefixDefEq09
    {Γ : List VExpr} {param : VExpr}
    (hparam : roseNestedC.restoreRec param =
      param.substConst roseRestoreInterp09)
    (hparamType : roseFinalEnv09.HasType 2 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 1)))) :
    roseFinalEnv09.IsDefEq 2 Γ
      (((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
        [param]).substConst roseRestoreInterp09)
      (roseNestedC.restoreRec
        ((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
          [param]))
      (roseConsPrefixType09 param) := by
  let binder : VExpr := .sort (.succ (.param 1))
  let body : VExpr :=
    (VExpr.const ``List.cons [.param 1]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (.bvar 0))
  let bodyType : VExpr :=
    .forallE
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (.bvar 0))
      (.forallE
        ((VExpr.const ``List [.param 1]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (.bvar 1)))
        ((VExpr.const ``List [.param 1]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (.bvar 2))))
  have hTel : roseFinalEnv09.OnTel 2 Γ [binder] := by
    refine ⟨?_, trivial⟩
    have hb : roseFinalEnv09.HasType 2 Γ
        (.sort (.succ (.param 1))) (.sort (.succ (.succ (.param 1)))) :=
      VEnv.HasType.sort (by decide)
    exact ⟨_, by simpa only [binder] using hb⟩
  have hbody : roseFinalEnv09.HasType 2
      ([binder].reverse ++ Γ) body bodyType := by
    rose_rule_hyps roseFinalEnv09
    simp only [binder, body, bodyType, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
    type_tac
  have hspine : roseFinalEnv09.SpineWF 2 Γ
      (VExpr.forallN [binder] bodyType)
      [param.substConst roseRestoreInterp09]
      (bodyType.inst (param.substConst roseRestoreInterp09)) := by
    exact .cons hparamType .nil
  have hbeta := VEnv.IsDefEq.substConst_aux_beta_instL
    roseNestedCertificate09.afterWF.ordered
    (interp := roseRestoreInterp09)
    (aux := roseFlatAuxName09 ++ `cons)
    (levels := [.param 1])
    (args := [param])
    (As := [.sort (.succ (.param 0))])
    (body :=
      (VExpr.const ``List.cons [.param 0]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
          (.bvar 0)))
    (by simpa [roseAuxConsInterpValue09, VExpr.lamN] using
      roseRestoreInterp_auxCons09)
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hTel)
    (by simpa [body, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hbody)
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hspine) rfl
  rw [roseRestoreConsPrefix09, hparam]
  simpa [binder, body, bodyType, roseConsPrefixType09,
    roseAuxConsInterpValue09,
    VExpr.lamN, VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD,
    VExpr.instRev, VExpr.inst, VExpr.instVar, VExpr.liftN] using hbeta

/-- Universe-polymorphic wrapper around the exact cons-prefix alignment. -/
theorem roseSubstRestoreConsPrefixDefEqU09
    {Γ : List VExpr} {param : VExpr}
    (hparam : roseNestedC.restoreRec param =
      param.substConst roseRestoreInterp09)
    (hparamType : roseFinalEnv09.HasType 2 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 1)))) :
    roseFinalEnv09.IsDefEqU 2 Γ
      (((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
        [param]).substConst roseRestoreInterp09)
      (roseNestedC.restoreRec
        ((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
          [param])) :=
  (roseSubstRestoreConsPrefixDefEq09 hparam hparamType).toU

/-- Residual final-runtime `List.cons` telescope after σ̂ supplies the
represented-family parameter at an arbitrary universe level. -/
def roseConsRuntimePrefixType09 (level : VLevel) (param : VExpr) : VExpr :=
  (VExpr.forallE
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
        (.bvar 0))
      (.forallE
        ((VExpr.const ``List [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (.bvar 1)))
        ((VExpr.const ``List [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (.bvar 2))))).inst (param.substConst roseRestoreInterp09)

/-- Direct runtime β-normalization of the interpreted auxiliary nil prefix
at an arbitrary well-formed universe level. -/
theorem roseSubstNilRuntimePrefixDefEq09
    {univs : Nat} {Γ : List VExpr} {level : VLevel} {param : VExpr}
    (hlevel : level.WF univs)
    (hparamType : roseFinalEnv09.HasType univs Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ level))) :
    roseFinalEnv09.IsDefEq univs Γ
      (((VExpr.const (roseFlatAuxName09 ++ `nil) [level]).appN
        [param]).substConst roseRestoreInterp09)
      ((VExpr.const ``List.nil [level]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
          (param.substConst roseRestoreInterp09)))
      ((VExpr.const ``List [level]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
          (param.substConst roseRestoreInterp09))) := by
  let binder : VExpr := .sort (.succ level)
  let body : VExpr :=
    (VExpr.const ``List.nil [level]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
        (.bvar 0))
  let bodyType : VExpr :=
    (VExpr.const ``List [level]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
        (.bvar 0))
  have hTel : roseFinalEnv09.OnTel univs Γ [binder] := by
    refine ⟨?_, trivial⟩
    have hb : roseFinalEnv09.HasType univs Γ
        (.sort (.succ level)) (.sort (.succ (.succ level))) :=
      VEnv.HasType.sort (by simpa [VLevel.WF] using hlevel)
    exact ⟨_, by simpa only [binder] using hb⟩
  have hbody : roseFinalEnv09.HasType univs
      ([binder].reverse ++ Γ) body bodyType := by
    have hNil' : roseFinalEnv09.constants ``List.nil =
        some ⟨1, .forallE (.sort (.succ (.param 0)))
          (.app (.const `List [.param 0]) (.bvar 0))⟩ := rfl
    have hRose' : roseFinalEnv09.constants
        `Lean4Lean.NestedRepresentation.RoseTree =
        some ⟨1, .forallE (.sort (.succ (.param 0)))
          (.sort (.succ (.param 0)))⟩ := rfl
    have hlevels : ∀ l ∈ [level], l.WF univs := by
      simpa using hlevel
    simp only [binder, body, bodyType, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
    have hNilT : roseFinalEnv09.HasType univs
        (.sort (.succ level) :: Γ)
        (.const ``List.nil [level])
        (.forallE (.sort (.succ level))
          ((VExpr.const ``List [level]).app (.bvar 0))) := by
      exact VEnv.HasType.const' hNil' hlevels rfl (by
        simp [VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD])
    have hRoseT : roseFinalEnv09.HasType univs
        (.sort (.succ level) :: Γ)
        (.const `Lean4Lean.NestedRepresentation.RoseTree [level])
        (.forallE (.sort (.succ level)) (.sort (.succ level))) := by
      exact VEnv.HasType.const' hRose' hlevels rfl (by
        simp [VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD])
    have hvar : roseFinalEnv09.HasType univs
        (.sort (.succ level) :: Γ) (.bvar 0) (.sort (.succ level)) := by
      type_tac
    exact VEnv.HasType.app hNilT (VEnv.HasType.app hRoseT hvar)
  have hspine : roseFinalEnv09.SpineWF univs Γ
      (VExpr.forallN [binder] bodyType)
      [param.substConst roseRestoreInterp09]
      ((VExpr.const ``List [level]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
          (param.substConst roseRestoreInterp09))) := by
    refine .cons hparamType ?_
    simpa [binder, bodyType, VExpr.forallN, VExpr.inst, VExpr.instVar,
      VExpr.liftN] using
      (VEnv.SpineWF.nil (env := roseFinalEnv09) (uvars := univs) (Γ := Γ)
        (A := (VExpr.const ``List [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (param.substConst roseRestoreInterp09))))
  have hbeta := VEnv.IsDefEq.substConst_aux_beta_instL
    roseNestedCertificate09.afterWF.ordered
    (interp := roseRestoreInterp09)
    (aux := roseFlatAuxName09 ++ `nil)
    (levels := [level]) (args := [param])
    (As := [.sort (.succ (.param 0))])
    (body :=
      (VExpr.const ``List.nil [.param 0]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
          (.bvar 0)))
    (by simpa [roseAuxNilInterpValue09, VExpr.lamN] using
      roseRestoreInterp_auxNil09)
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hTel)
    (by simpa [body, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hbody)
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hspine) rfl
  simpa [binder, body, bodyType, roseAuxNilInterpValue09,
    VExpr.lamN, VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD,
    VExpr.instRev, VExpr.inst, VExpr.instVar, VExpr.liftN] using hbeta

/-- Direct runtime β-normalization of the interpreted auxiliary cons prefix
at an arbitrary well-formed universe level. -/
theorem roseSubstConsRuntimePrefixDefEq09
    {univs : Nat} {Γ : List VExpr} {level : VLevel} {param : VExpr}
    (hlevel : level.WF univs)
    (hparamType : roseFinalEnv09.HasType univs Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ level))) :
    roseFinalEnv09.IsDefEq univs Γ
      (((VExpr.const (roseFlatAuxName09 ++ `cons) [level]).appN
        [param]).substConst roseRestoreInterp09)
      ((VExpr.const ``List.cons [level]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
          (param.substConst roseRestoreInterp09)))
      (roseConsRuntimePrefixType09 level param) := by
  let binder : VExpr := .sort (.succ level)
  let body : VExpr :=
    (VExpr.const ``List.cons [level]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
        (.bvar 0))
  let bodyType : VExpr :=
    .forallE
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
        (.bvar 0))
      (.forallE
        ((VExpr.const ``List [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (.bvar 1)))
        ((VExpr.const ``List [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (.bvar 2))))
  have hTel : roseFinalEnv09.OnTel univs Γ [binder] := by
    refine ⟨?_, trivial⟩
    have hb : roseFinalEnv09.HasType univs Γ
        (.sort (.succ level)) (.sort (.succ (.succ level))) :=
      VEnv.HasType.sort (by simpa [VLevel.WF] using hlevel)
    exact ⟨_, by simpa only [binder] using hb⟩
  have hbody : roseFinalEnv09.HasType univs
      ([binder].reverse ++ Γ) body bodyType := by
    have hCons' : roseFinalEnv09.constants ``List.cons =
        some ⟨1, .forallE (.sort (.succ (.param 0)))
          (.forallE (.bvar 0)
            (.forallE (.app (.const `List [.param 0]) (.bvar 1))
              (.app (.const `List [.param 0]) (.bvar 2))))⟩ := rfl
    have hRose' : roseFinalEnv09.constants
        `Lean4Lean.NestedRepresentation.RoseTree =
        some ⟨1, .forallE (.sort (.succ (.param 0)))
          (.sort (.succ (.param 0)))⟩ := rfl
    have hlevels : ∀ l ∈ [level], l.WF univs := by
      simpa using hlevel
    simp only [binder, body, bodyType, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append]
    have hConsT : roseFinalEnv09.HasType univs
        (.sort (.succ level) :: Γ)
        (.const ``List.cons [level])
        (.forallE (.sort (.succ level))
          (.forallE (.bvar 0)
            (.forallE (.app (.const `List [level]) (.bvar 1))
              (.app (.const `List [level]) (.bvar 2))))) := by
      exact VEnv.HasType.const' hCons' hlevels rfl (by
        simp [VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD])
    have hRoseT : roseFinalEnv09.HasType univs
        (.sort (.succ level) :: Γ)
        (.const `Lean4Lean.NestedRepresentation.RoseTree [level])
        (.forallE (.sort (.succ level)) (.sort (.succ level))) := by
      exact VEnv.HasType.const' hRose' hlevels rfl (by
        simp [VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD])
    have hvar : roseFinalEnv09.HasType univs
        (.sort (.succ level) :: Γ) (.bvar 0) (.sort (.succ level)) := by
      type_tac
    exact VEnv.HasType.app hConsT (VEnv.HasType.app hRoseT hvar)
  have hspine : roseFinalEnv09.SpineWF univs Γ
      (VExpr.forallN [binder] bodyType)
      [param.substConst roseRestoreInterp09]
      (bodyType.inst (param.substConst roseRestoreInterp09)) := by
    exact .cons hparamType .nil
  have hbeta := VEnv.IsDefEq.substConst_aux_beta_instL
    roseNestedCertificate09.afterWF.ordered
    (interp := roseRestoreInterp09)
    (aux := roseFlatAuxName09 ++ `cons)
    (levels := [level]) (args := [param])
    (As := [.sort (.succ (.param 0))])
    (body :=
      (VExpr.const ``List.cons [.param 0]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 0]).app
          (.bvar 0)))
    (by simpa [roseAuxConsInterpValue09, VExpr.lamN] using
      roseRestoreInterp_auxCons09)
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hTel)
    (by simpa [body, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hbody)
    (by simpa [binder, VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hspine) rfl
  simpa [binder, body, bodyType, roseConsRuntimePrefixType09,
    roseAuxConsInterpValue09,
    VExpr.lamN, VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD,
    VExpr.instRev, VExpr.inst, VExpr.instVar, VExpr.liftN] using hbeta

/-- Extend the arbitrary-level runtime nil β-normalization through its
complete interpreted field spine. -/
theorem roseSubstNilRuntimeCtorSpineDefEq09
    {univs : Nat} {Γ : List VExpr} {level : VLevel}
    {param : VExpr} {fields : List VExpr} {C : VExpr}
    (hlevel : level.WF univs)
    (hparamType : roseFinalEnv09.HasType univs Γ
      (param.substConst roseRestoreInterp09) (.sort (.succ level)))
    (hfieldsSpine : roseFinalEnv09.SpineWF univs Γ
      ((VExpr.const ``List [level]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
          (param.substConst roseRestoreInterp09)))
      (fields.map (VExpr.substConst roseRestoreInterp09)) C) :
    roseFinalEnv09.IsDefEq univs Γ
      (((VExpr.const (roseFlatAuxName09 ++ `nil) [level]).appN
        ([param] ++ fields)).substConst roseRestoreInterp09)
      (((VExpr.const ``List.nil [level]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
          (param.substConst roseRestoreInterp09))).appN
        (fields.map (VExpr.substConst roseRestoreInterp09))) C := by
  let base : VExpr :=
    (VExpr.const (roseFlatAuxName09 ++ `nil) [level]).appN [param]
  have happ :
      (VExpr.const (roseFlatAuxName09 ++ `nil) [level]).appN
          ([param] ++ fields) = base.appN fields :=
    VExpr.appN_append _ [param] fields
  have hout := VEnv.IsDefEq.appN_congr
    (roseSubstNilRuntimePrefixDefEq09 hlevel hparamType) hfieldsSpine
  rw [happ]
  simpa [base, VExpr.substConst_appN] using hout

/-- Extend the arbitrary-level runtime cons β-normalization through its
complete interpreted two-field spine. -/
theorem roseSubstConsRuntimeCtorSpineDefEq09
    {univs : Nat} {Γ : List VExpr} {level : VLevel}
    {param : VExpr} {fields : List VExpr} {C : VExpr}
    (hlevel : level.WF univs)
    (hparamType : roseFinalEnv09.HasType univs Γ
      (param.substConst roseRestoreInterp09) (.sort (.succ level)))
    (hfieldsSpine : roseFinalEnv09.SpineWF univs Γ
      (roseConsRuntimePrefixType09 level param)
      (fields.map (VExpr.substConst roseRestoreInterp09)) C) :
    roseFinalEnv09.IsDefEq univs Γ
      (((VExpr.const (roseFlatAuxName09 ++ `cons) [level]).appN
        ([param] ++ fields)).substConst roseRestoreInterp09)
      (((VExpr.const ``List.cons [level]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
          (param.substConst roseRestoreInterp09))).appN
        (fields.map (VExpr.substConst roseRestoreInterp09))) C := by
  let base : VExpr :=
    (VExpr.const (roseFlatAuxName09 ++ `cons) [level]).appN [param]
  have happ :
      (VExpr.const (roseFlatAuxName09 ++ `cons) [level]).appN
          ([param] ++ fields) = base.appN fields :=
    VExpr.appN_append _ [param] fields
  have hout := VEnv.IsDefEq.appN_congr
    (roseSubstConsRuntimePrefixDefEq09 hlevel hparamType) hfieldsSpine
  rw [happ]
  simpa [base, VExpr.substConst_appN] using hout

/-- Nil restoration remains aligned under an arbitrary trailing field
spine; the actual nil rule specializes this theorem to the empty spine. -/
theorem roseRestoreNilCtorSpine09 (levels : List VLevel)
    (param : VExpr) (fields : List VExpr) :
    roseNestedC.restoreRec
      ((VExpr.const (roseFlatAuxName09 ++ `nil) levels).appN
        ([param] ++ fields)) =
    ((VExpr.const ``List.nil [.param 1]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (roseNestedC.restoreRec param))).appN
      (fields.map roseNestedC.restoreRec) := by
  rw [VExpr.appN_append]
  apply VInductDecl.restoreExpr_appN_of_head_inert
    (name := ``List.nil) (ls := [.param 1])
  · exact roseRestoreNilPrefix09 levels param
  · rfl
  all_goals
    simp only [roseRecEntries09_eq, roseNestedRecMap09_eq]
    decide

/-- Cons restoration remains aligned under its complete two-field spine (or
any longer inert trailing spine). -/
theorem roseRestoreConsCtorSpine09 (levels : List VLevel)
    (param : VExpr) (fields : List VExpr) :
    roseNestedC.restoreRec
      ((VExpr.const (roseFlatAuxName09 ++ `cons) levels).appN
        ([param] ++ fields)) =
    ((VExpr.const ``List.cons [.param 1]).app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (roseNestedC.restoreRec param))).appN
      (fields.map roseNestedC.restoreRec) := by
  rw [VExpr.appN_append]
  apply VInductDecl.restoreExpr_appN_of_head_inert
    (name := ``List.cons) (ls := [.param 1])
  · exact roseRestoreConsPrefix09 levels param
  · rfl
  all_goals
    simp only [roseRecEntries09_eq, roseNestedRecMap09_eq]
    decide

/-- The σ̂/restoration nil-prefix alignment extends through any typed trailing
field spine whose restored fields agree pointwise with their σ̂-images. -/
theorem roseSubstRestoreNilCtorSpineDefEq09
    {Γ : List VExpr} {param : VExpr} {fields : List VExpr} {C : VExpr}
    (hparam : roseNestedC.restoreRec param =
      param.substConst roseRestoreInterp09)
    (hparamType : roseFinalEnv09.HasType 2 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 1))))
    (hfieldsSpine : roseFinalEnv09.SpineWF 2 Γ
      ((VExpr.const ``List [.param 1]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
          (param.substConst roseRestoreInterp09)))
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hfields : fields.map roseNestedC.restoreRec =
      fields.map (VExpr.substConst roseRestoreInterp09)) :
    roseFinalEnv09.IsDefEq 2 Γ
      (((VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
        ([param] ++ fields)).substConst roseRestoreInterp09)
      (roseNestedC.restoreRec
        ((VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
          ([param] ++ fields))) C := by
  let base : VExpr :=
    (VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN [param]
  have happ :
      (VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
          ([param] ++ fields) =
        base.appN fields := by
    exact VExpr.appN_append _ [param] fields
  have hrestore : roseNestedC.restoreRec (base.appN fields) =
      (roseNestedC.restoreRec base).appN
        (fields.map roseNestedC.restoreRec) := by
    rw [← happ, roseRestoreNilPrefix09]
    exact roseRestoreNilCtorSpine09 [.param 1] param fields
  have hout := VEnv.IsDefEq.substConst_restoreExpr_appN_of_prefix
    (interp := roseRestoreInterp09)
    (entries := roseNestedC.recEntries) (recMap := roseNestedC.recMap)
    (base := base)
    (roseSubstRestoreNilPrefixDefEq09 hparam hparamType)
    hfieldsSpine hfields hrestore
  rw [happ]
  simpa [base, NestedBlockChecked.restoreRec] using hout

/-- The exact cons-prefix telescope similarly carries σ̂/restoration
alignment across the complete two-field runtime constructor spine. -/
theorem roseSubstRestoreConsCtorSpineDefEq09
    {Γ : List VExpr} {param : VExpr} {fields : List VExpr} {C : VExpr}
    (hparam : roseNestedC.restoreRec param =
      param.substConst roseRestoreInterp09)
    (hparamType : roseFinalEnv09.HasType 2 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 1))))
    (hfieldsSpine : roseFinalEnv09.SpineWF 2 Γ
      (roseConsPrefixType09 param)
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hfields : fields.map roseNestedC.restoreRec =
      fields.map (VExpr.substConst roseRestoreInterp09)) :
    roseFinalEnv09.IsDefEq 2 Γ
      (((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
        ([param] ++ fields)).substConst roseRestoreInterp09)
      (roseNestedC.restoreRec
        ((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
          ([param] ++ fields))) C := by
  let base : VExpr :=
    (VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN [param]
  have happ :
      (VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
          ([param] ++ fields) =
        base.appN fields := by
    exact VExpr.appN_append _ [param] fields
  have hrestore : roseNestedC.restoreRec (base.appN fields) =
      (roseNestedC.restoreRec base).appN
        (fields.map roseNestedC.restoreRec) := by
    rw [← happ, roseRestoreConsPrefix09]
    exact roseRestoreConsCtorSpine09 [.param 1] param fields
  have hout := VEnv.IsDefEq.substConst_restoreExpr_appN_of_prefix
    (interp := roseRestoreInterp09)
    (entries := roseNestedC.recEntries) (recMap := roseNestedC.recMap)
    (base := base)
    (roseSubstRestoreConsPrefixDefEq09 hparam hparamType)
    hfieldsSpine hfields hrestore
  rw [happ]
  simpa [base, NestedBlockChecked.restoreRec] using hout

/-! ### Whole recursor-type alignment -/

/-- Close one represented-family domain in the concrete recursor telescope
using the typed declaration-level σ̂ certificate. -/
macro "rose_rec_family_beta" param:term : tactic => `(tactic| (
  simpa [roseAuxFamilyInterpValue09, VExpr.appN, VExpr.substConst,
    VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamily09] using
    (roseSubstAuxFamilyBetaRec09
      (param := $param) (by type_tac)).symm))

/-- Close the nil-case domain of either generated recursor type. -/
macro "rose_rec_nil_domain" : tactic => `(tactic| (
  apply VEnv.IsDefEq.appDF
    (A := (VExpr.const ``List [.param 1]).app
      ((VExpr.const
        `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (.bvar 3)))
    (B := .sort (.param 0))
  · type_tac
  · have hrestore :
        roseNestedC.restoreRec
          ((VExpr.const (`_nested.List_1 ++ `nil) [.param 1]).app
            (.bvar 3)) =
        (VExpr.const ``List.nil [.param 1]).app
          ((VExpr.const
            `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (.bvar 3)) := by
      simpa [roseFlatAuxName09, VExpr.appN,
        NestedBlockChecked.restoreRec, VInductDecl.restoreExpr] using
        (roseRestoreNilPrefix09 [.param 1] (.bvar 3))
    have hsigma :
        (((VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
          [.bvar 3]).substConst roseRestoreInterp09) =
        ((VExpr.sort (VLevel.param 1).succ).lam
          ((VExpr.const ``List.nil [.param 1]).app
            ((VExpr.const
              `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
              (.bvar 0)))).app (.bvar 3) := by
      simp [roseAuxNilInterpValue09, VExpr.appN, VExpr.substConst,
        VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD,
        roseRestoreInterp_auxNil09]
    apply VEnv.IsDefEq.symm
    rw [← hsigma, ← hrestore]
    apply roseSubstRestoreNilPrefixDefEq09
    · rfl
    · type_tac))

/-- Close the complete two-field cons-case domain of either generated
recursor type. -/
macro "rose_rec_cons_domain" : tactic => `(tactic| (
  apply VEnv.IsDefEq.appDF
    (A := (VExpr.const ``List [.param 1]).app
      ((VExpr.const
        `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
        (.bvar 8)))
    (B := .sort (.param 0))
  · type_tac
  · have hrestore :
        roseNestedC.restoreRec
          ((((VExpr.const (`_nested.List_1 ++ `cons) [.param 1]).app
            (.bvar 8)).app (.bvar 3)).app (.bvar 2)) =
        (((VExpr.const ``List.cons [.param 1]).app
            ((VExpr.const
              `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
              (.bvar 8))).app (.bvar 3)).app (.bvar 2) := by
      simpa [roseFlatAuxName09, VExpr.appN,
        NestedBlockChecked.restoreRec, VInductDecl.restoreExpr] using
        (roseRestoreConsCtorSpine09 [.param 1] (.bvar 8)
          [.bvar 3, .bvar 2])
    have hsigma :
        (((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
          ([.bvar 8] ++ [.bvar 3, .bvar 2])).substConst
            roseRestoreInterp09) =
        (((((VExpr.sort (VLevel.param 1).succ).lam
          ((VExpr.const ``List.cons [.param 1]).app
            ((VExpr.const
              `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
              (.bvar 0)))).app (.bvar 8)).app (.bvar 3)).app
            (.bvar 2)) := by
      simp [roseAuxConsInterpValue09, VExpr.appN,
        VExpr.substConst, VExpr.instL, VLevel.inst,
        List.getD_eq_getElem?_getD, roseRestoreInterp_auxCons09]
    apply VEnv.IsDefEq.symm
    rw [← hsigma, ← hrestore]
    apply roseSubstRestoreConsCtorSpineDefEq09
    · rfl
    · type_tac
    · exact .cons (by type_tac) (.cons (by type_tac) .nil)
    · rfl))

/- The restored main recursor type and the σ̂-image of its flattened type
are definitionally equal in the completed nested environment. -/
set_option maxRecDepth 16000 in
theorem roseMainRecTypeAlignment09 :
    roseFinalEnv09.IsDefEqU 2 [] roseRecTypeL
      (roseFlatRecType09.substConst roseRestoreInterp09) := by
  rose_rule_hyps roseFinalEnv09
  simp [roseFlatRecType09, roseReflattenVExpr09, roseRecTypeL,
    roseFlatNestedHead09, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    roseFlatAuxName09, VExpr.substConst, VExpr.instL,
    VLevel.params, VLevel.inst, List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09]
  apply VEnv.IsDefEq.toU
  exact .forallEDF (by type_tac) <|
    .forallEDF (by type_tac) <|
    .forallEDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .forallEDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .forallEDF (by rose_rec_nil_domain) <|
    .forallEDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) <|
    .forallEDF (by type_tac) (by type_tac)

/- The auxiliary recursor has the same restored motive/case telescope; its
final major domain is the represented family and is closed by one last typed
family β-certificate. -/
set_option maxRecDepth 16000 in
theorem roseAuxRecTypeAlignment09 :
    roseFinalEnv09.IsDefEqU 2 [] roseRec1TypeL
      (roseFlatAuxRecType09.substConst roseRestoreInterp09) := by
  rose_rule_hyps roseFinalEnv09
  simp [roseFlatAuxRecType09, roseReflattenVExpr09, roseRec1TypeL,
    roseFlatNestedHead09, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    roseFlatAuxName09, VExpr.substConst, VExpr.instL,
    VLevel.params, VLevel.inst, List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09]
  apply VEnv.IsDefEq.toU
  exact .forallEDF (by type_tac) <|
    .forallEDF (by type_tac) <|
    .forallEDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .forallEDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .forallEDF (by rose_rec_nil_domain) <|
    .forallEDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) <|
    .forallEDF (by rose_rec_family_beta (.bvar 5)) (by type_tac)

/-- The unchanged main recursor constant is typed at the interpreted
flattened recursor type. -/
theorem roseMainRecInterpValueTyping09 :
    roseFinalEnv09.HasType 2 []
      (.const `Lean4Lean.NestedRepresentation.RoseTree.rec
        (VLevel.params 2))
      ((roseNestedC.generation.recursors[0]!).type.substConst
        roseRestoreInterp09) := by
  have hv : roseFinalEnv09.HasType 2 []
      (.const `Lean4Lean.NestedRepresentation.RoseTree.rec
        (VLevel.params 2)) roseRecTypeL := by
    rose_rule_hyps roseFinalEnv09
    type_tac
  have hout := hv.defeqU_r roseNestedCertificate09.afterWF
    (by trivial) roseMainRecTypeAlignment09
  rw [roseFlatRecType09_eq]
  exact hout

/-- The renamed auxiliary recursor constant is typed at the interpreted
flattened auxiliary-recursor type. -/
theorem roseAuxRecInterpValueTyping09 :
    roseFinalEnv09.HasType 2 []
      (.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
        (VLevel.params 2))
      ((roseNestedC.generation.recursors[1]!).type.substConst
        roseRestoreInterp09) := by
  have hv : roseFinalEnv09.HasType 2 []
      (.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
        (VLevel.params 2)) roseRec1TypeL := by
    rose_rule_hyps roseFinalEnv09
    type_tac
  have hout := hv.defeqU_r roseNestedCertificate09.afterWF
    (by trivial) roseAuxRecTypeAlignment09
  rw [roseFlatAuxRecType09_eq]
  exact hout

/-- All six concrete σ̂ values are typed at the interpreted source
declaration type. -/
theorem roseRestoreInterpValue09
    {c : Name} {ci : VConstant} {v : VExpr}
    (hflat : roseFlatFinalEnv09.constants c = some ci)
    (hinterp : roseRestoreInterp09 c = some v) :
    roseFinalEnv09.HasType ci.uvars [] v
      (ci.type.substConst roseRestoreInterp09) :=
  roseRestoreInterpValueOfRecursors09
    roseMainRecInterpValueTyping09 roseAuxRecInterpValueTyping09
    hflat hinterp

/-- Every source declaration outside the six-point restoration map is kept
verbatim in the completed nested environment.  The finite lookup split is
deliberate: it checks the one unchanged Rose family and the inherited List
boundary independently of the interpreted declarations. -/
theorem roseRestoreInterpKeep09
    {c : Name} {ci : VConstant}
    (hflat : roseFlatFinalEnv09.constants c = some ci)
    (hinterp : roseRestoreInterp09 c = none) :
    roseFinalEnv09.constants c =
      some ⟨ci.uvars, ci.type.substConst roseRestoreInterp09⟩ := by
  have hmainRecName :
      (roseNestedC.generation.recursors[0]!).name =
        `Lean4Lean.NestedRepresentation.RoseTree.rec := by
    native_decide
  have hauxRecName :
      (roseNestedC.generation.recursors[1]!).name =
        .str roseFlatAuxName09 "rec" := by
    native_decide
  rw [roseFlatFinalEnv09,
    VEnv.foldl_addDefEq_constants_eq,
    VEnv.addConst_constants_eq roseFlatAddSecondRec09,
    VEnv.addConst_constants_eq roseFlatAddFirstRec09,
    VEnv.addConst_constants_eq roseFlatAddCons09,
    VEnv.addConst_constants_eq roseFlatAddNil09,
    VEnv.addConst_constants_eq roseFlatAddNode09,
    VEnv.addConst_constants_eq roseFlatBlockEnv09_eq,
    VEnv.addConst_constants_eq roseFlatFirstTypeEnv09_eq,
    hmainRecName, hauxRecName] at hflat
  simp only at hflat
  split at hflat <;> rename_i hrec1
  · subst c
    rw [roseRestoreInterp_auxRec09] at hinterp
    contradiction
  · split at hflat <;> rename_i hrec
    · subst c
      rw [roseRestoreInterp_mainRec09] at hinterp
      contradiction
    · split at hflat <;> rename_i hcons
      · subst c
        change roseRestoreInterp09 (roseFlatAuxName09 ++ `cons) = none at hinterp
        rw [roseRestoreInterp_auxCons09] at hinterp
        contradiction
      · split at hflat <;> rename_i hnil
        · subst c
          change roseRestoreInterp09 (roseFlatAuxName09 ++ `nil) = none at hinterp
          rw [roseRestoreInterp_auxNil09] at hinterp
          contradiction
        · split at hflat <;> rename_i hnode
          · subst c
            change roseRestoreInterp09
              `Lean4Lean.NestedRepresentation.RoseTree.node = none at hinterp
            rw [roseRestoreInterp_mainCtor09] at hinterp
            contradiction
          · split at hflat <;> rename_i haux
            · subst c
              change roseRestoreInterp09 roseFlatAuxName09 = none at hinterp
              rw [roseRestoreInterp_auxFamily09] at hinterp
              contradiction
            · split at hflat <;> rename_i hrose
              · subst c
                cases hflat
                native_decide
              ·
                have listRecAdd :
                    listCtorEnv07.addConst ``List.rec
                      (inductGenerationRecVal
                        Lean4Lean.InductiveFixtures.listGenerationChecked).toVConstant =
                        some listRecEnv07 := rfl
                have listConsAdd :
                    listNilEnv07.addConst
                      Lean4Lean.InductiveFixtures.listType.ctors[1].name
                      Lean4Lean.InductiveFixtures.listType.ctors[1].toVConstant =
                        some listCtorEnv07 := rfl
                have listNilAdd :
                    listTypeEnv07.addConst
                      Lean4Lean.InductiveFixtures.listType.ctors[0].name
                      Lean4Lean.InductiveFixtures.listType.ctors[0].toVConstant =
                        some listNilEnv07 := rfl
                have listTypeAdd :
                    VEnv.empty.addConst
                      Lean4Lean.InductiveFixtures.listType.name
                      Lean4Lean.InductiveFixtures.listType.toVConstant =
                        some listTypeEnv07 := rfl
                rw [listFinalEnv07,
                  VEnv.foldl_addDefEq_constants_eq,
                  VEnv.addConst_constants_eq listRecAdd,
                  VEnv.addConst_constants_eq listConsAdd,
                  VEnv.addConst_constants_eq listNilAdd,
                  VEnv.addConst_constants_eq listTypeAdd] at hflat
                simp only at hflat
                split at hflat
                · subst c
                  cases hflat
                  native_decide
                · split at hflat
                  · subst c
                    cases hflat
                    native_decide
                  · split at hflat
                    · subst c
                      cases hflat
                      native_decide
                    · split at hflat
                      · subst c
                        cases hflat
                        native_decide
                      · cases hflat

/-- Complete flattened main-rule redexes restore to the exact main runtime
head pair, with every captured argument restored pointwise. -/
theorem roseRestoreMainRuleRedex09
    (recLevels ctorLevels : List VLevel)
    (recArgs ctorArgs : List VExpr) :
    roseNestedC.restoreRec
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
          recLevels).appN recArgs)
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
          ctorLevels).appN ctorArgs)) =
    .app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
        recLevels).appN (recArgs.map roseNestedC.restoreRec))
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
        ctorLevels).appN (ctorArgs.map roseNestedC.restoreRec)) := by
  have h := roseRestoreMainRecSpine09 recLevels
    (recArgs ++
      [(VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
        ctorLevels).appN ctorArgs])
  simp only [List.map_append, List.map_cons, List.map_nil] at h
  rw [roseRestoreMainCtorSpine09] at h
  simpa [VExpr.appN_append, VExpr.appN] using h

/-- At arbitrary complete recursor/constructor universe instantiations, the
constant interpretation and nested restoration of the complete main flat
redex are syntactically identical.  Only pointwise agreement on runtime
arguments remains. -/
theorem roseSubstRestoreMainRuleRedexLevels09
    (recLevels ctorLevels : List VLevel)
    (recArgs ctorArgs : List VExpr)
    (hrecLevels : recLevels.length = 2)
    (hctorLevels : ctorLevels.length = 1)
    (hrecArgs : recArgs.map roseNestedC.restoreRec =
      recArgs.map (VExpr.substConst roseRestoreInterp09))
    (hctorArgs : ctorArgs.map roseNestedC.restoreRec =
      ctorArgs.map (VExpr.substConst roseRestoreInterp09)) :
    ((.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
          recLevels).appN recArgs)
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
          ctorLevels).appN ctorArgs) : VExpr).substConst
          roseRestoreInterp09) =
      roseNestedC.restoreRec
        (.app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
            recLevels).appN recArgs)
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
            ctorLevels).appN ctorArgs)) := by
  simp only [VExpr.substConst]
  rw [roseSubstRestoreMainRecSpineLevels09 recLevels recArgs
      hrecLevels hrecArgs,
    roseSubstRestoreMainCtorSpineLevels09 ctorLevels ctorArgs
      hctorLevels hctorArgs,
    roseRestoreMainRuleRedex09,
    roseRestoreMainRecSpine09, roseRestoreMainCtorSpine09]

/-- Direct final-runtime normal form of the complete interpreted main
recursor redex.  This is the exact endpoint needed by the selected reducer
site and is independent of recursive-restoration syntax. -/
theorem roseSubstMainRuleRuntimeRedex09
    (recLevels ctorLevels : List VLevel)
    (recArgs ctorArgs : List VExpr)
    (hrecLevels : recLevels.length = 2)
    (hctorLevels : ctorLevels.length = 1) :
    ((.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
          recLevels).appN recArgs)
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
          ctorLevels).appN ctorArgs) : VExpr).substConst
          roseRestoreInterp09) =
      .app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
          recLevels).appN
            (recArgs.map (VExpr.substConst roseRestoreInterp09)))
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
          ctorLevels).appN
            (ctorArgs.map (VExpr.substConst roseRestoreInterp09))) := by
  simp only [VExpr.substConst]
  rw [roseSubstMainRecSpineLevels09 recLevels recArgs hrecLevels,
    roseSubstMainCtorSpineLevels09 ctorLevels ctorArgs hctorLevels]

/-- Canonical-parameter compatibility specialization of the complete main
redex alignment. -/
theorem roseSubstRestoreMainRuleRedex09
    (recArgs ctorArgs : List VExpr)
    (hrecArgs : recArgs.map roseNestedC.restoreRec =
      recArgs.map (VExpr.substConst roseRestoreInterp09))
    (hctorArgs : ctorArgs.map roseNestedC.restoreRec =
      ctorArgs.map (VExpr.substConst roseRestoreInterp09)) :
    ((.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
          (VLevel.params 2)).appN recArgs)
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
          (VLevel.params 1)).appN ctorArgs) : VExpr).substConst
          roseRestoreInterp09) =
      roseNestedC.restoreRec
        (.app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
            (VLevel.params 2)).appN recArgs)
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
            (VLevel.params 1)).appN ctorArgs)) := by
  exact roseSubstRestoreMainRuleRedexLevels09
    (VLevel.params 2) (VLevel.params 1) recArgs ctorArgs
    (by simp) (by simp) hrecArgs hctorArgs

/-- Complete flattened nil-rule redexes restore to the exact auxiliary
runtime recursor and `List.nil` major. -/
theorem roseRestoreNilRuleRedex09
    (recLevels ctorLevels : List VLevel)
    (recArgs : List VExpr) (param : VExpr) (fields : List VExpr) :
    roseNestedC.restoreRec
      (.app
        ((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN
          recArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `nil) ctorLevels).appN
          ([param] ++ fields))) =
    .app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
        recLevels).appN (recArgs.map roseNestedC.restoreRec))
      (((VExpr.const ``List.nil [.param 1]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
          (roseNestedC.restoreRec param))).appN
        (fields.map roseNestedC.restoreRec)) := by
  have h := roseRestoreAuxRecSpine09 recLevels
    (recArgs ++
      [(VExpr.const (roseFlatAuxName09 ++ `nil) ctorLevels).appN
        ([param] ++ fields)])
  simp only [List.map_append, List.map_cons, List.map_nil] at h
  rw [roseRestoreNilCtorSpine09] at h
  simpa [VExpr.appN_append, VExpr.appN] using h

/-- Complete flattened cons-rule redexes restore to the exact auxiliary
runtime recursor and `List.cons` major. -/
theorem roseRestoreConsRuleRedex09
    (recLevels ctorLevels : List VLevel)
    (recArgs : List VExpr) (param : VExpr) (fields : List VExpr) :
    roseNestedC.restoreRec
      (.app
        ((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN
          recArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `cons) ctorLevels).appN
          ([param] ++ fields))) =
    .app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
        recLevels).appN (recArgs.map roseNestedC.restoreRec))
      (((VExpr.const ``List.cons [.param 1]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
          (roseNestedC.restoreRec param))).appN
        (fields.map roseNestedC.restoreRec)) := by
  have h := roseRestoreAuxRecSpine09 recLevels
    (recArgs ++
      [(VExpr.const (roseFlatAuxName09 ++ `cons) ctorLevels).appN
        ([param] ++ fields)])
  simp only [List.map_append, List.map_cons, List.map_nil] at h
  rw [roseRestoreConsCtorSpine09] at h
  simpa [VExpr.appN_append, VExpr.appN] using h

/-- A typed auxiliary-major σ̂/restoration alignment composes with exact
auxiliary-recursor renaming at arbitrary complete universe instantiations,
retaining the result type induced by the interpreted major. -/
theorem roseSubstRestoreAuxRuleRedexLevelsDefEq09
    {Γ : List VExpr} {recLevels : List VLevel}
    {recArgs : List VExpr} {major A B : VExpr}
    (hrecLevels : recLevels.length = 2)
    (hrecArgs : recArgs.map roseNestedC.restoreRec =
      recArgs.map (VExpr.substConst roseRestoreInterp09))
    (hmajor : roseFinalEnv09.IsDefEq 2 Γ
      (major.substConst roseRestoreInterp09)
      (roseNestedC.restoreRec major) A)
    (hrecType : roseFinalEnv09.HasType 2 Γ
      (((VExpr.const (.str roseFlatAuxName09 "rec")
        recLevels).appN recArgs).substConst roseRestoreInterp09)
      (.forallE A B)) :
    roseFinalEnv09.IsDefEq 2 Γ
      ((.app
        ((VExpr.const (.str roseFlatAuxName09 "rec")
          recLevels).appN recArgs) major : VExpr).substConst
            roseRestoreInterp09)
      (roseNestedC.restoreRec
        (.app
          ((VExpr.const (.str roseFlatAuxName09 "rec")
            recLevels).appN recArgs) major))
      (B.inst (major.substConst roseRestoreInterp09)) := by
  let fn : VExpr :=
    (VExpr.const (.str roseFlatAuxName09 "rec")
      recLevels).appN recArgs
  have hrestore : roseNestedC.restoreRec (fn.app major) =
      (roseNestedC.restoreRec fn).app (roseNestedC.restoreRec major) := by
    have h := roseRestoreAuxRecSpine09 recLevels (recArgs ++ [major])
    rw [roseRestoreAuxRecSpine09 recLevels recArgs]
    simpa [fn, VExpr.appN_append, VExpr.appN, List.map_append] using h
  exact VEnv.IsDefEq.substConst_restoreExpr_app_of_head_eq
    (interp := roseRestoreInterp09)
    (entries := roseNestedC.recEntries) (recMap := roseNestedC.recMap)
    (fn := fn) (arg := major)
    (by
      simpa [fn, NestedBlockChecked.restoreRec] using
        (roseSubstRestoreAuxRecSpineLevels09 recLevels recArgs
          hrecLevels hrecArgs))
    (by simpa [fn] using hrecType) hmajor hrestore

/-- Direct final-runtime auxiliary-redex alignment.  The interpreted flat
major may be definitionally equal to any typed final major; recursor renaming
and argument substitution are then exact at every complete level
instantiation. -/
theorem roseSubstAuxRuleRuntimeRedexDefEq09
    {univs : Nat} {Γ : List VExpr} {recLevels : List VLevel}
    {recArgs : List VExpr} {major targetMajor A B : VExpr}
    (hrecLevels : recLevels.length = 2)
    (hmajor : roseFinalEnv09.IsDefEq univs Γ
      (major.substConst roseRestoreInterp09) targetMajor A)
    (hrecType : roseFinalEnv09.HasType univs Γ
      (((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN
        recArgs).substConst roseRestoreInterp09)
      (.forallE A B)) :
    roseFinalEnv09.IsDefEq univs Γ
      ((.app
        ((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN recArgs)
        major : VExpr).substConst roseRestoreInterp09)
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
          recLevels).appN
            (recArgs.map (VExpr.substConst roseRestoreInterp09)))
        targetMajor)
      (B.inst (major.substConst roseRestoreInterp09)) := by
  let fn : VExpr :=
    (VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN recArgs
  have hhead : fn.substConst roseRestoreInterp09 =
      (VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
        recLevels).appN
          (recArgs.map (VExpr.substConst roseRestoreInterp09)) := by
    simpa only [fn] using
      roseSubstAuxRecSpineLevels09 recLevels recArgs hrecLevels
  have happ := VEnv.IsDefEq.appDF hrecType hmajor
  simpa only [fn, VExpr.substConst, hhead] using happ

/-- Canonical-parameter specialization of the exact auxiliary-redex
alignment. -/
theorem roseSubstRestoreAuxRuleRedexDefEq09
    {Γ : List VExpr} {recArgs : List VExpr} {major A B : VExpr}
    (hrecArgs : recArgs.map roseNestedC.restoreRec =
      recArgs.map (VExpr.substConst roseRestoreInterp09))
    (hmajor : roseFinalEnv09.IsDefEq 2 Γ
      (major.substConst roseRestoreInterp09)
      (roseNestedC.restoreRec major) A)
    (hrecType : roseFinalEnv09.HasType 2 Γ
      (((VExpr.const (.str roseFlatAuxName09 "rec")
        (VLevel.params 2)).appN recArgs).substConst roseRestoreInterp09)
      (.forallE A B)) :
    roseFinalEnv09.IsDefEq 2 Γ
      ((.app
        ((VExpr.const (.str roseFlatAuxName09 "rec")
          (VLevel.params 2)).appN recArgs) major : VExpr).substConst
            roseRestoreInterp09)
      (roseNestedC.restoreRec
        (.app
          ((VExpr.const (.str roseFlatAuxName09 "rec")
            (VLevel.params 2)).appN recArgs) major))
      (B.inst (major.substConst roseRestoreInterp09)) := by
  exact roseSubstRestoreAuxRuleRedexLevelsDefEq09 (by simp)
    hrecArgs hmajor hrecType

/-- Existentially typed compatibility wrapper for callers that do not need
the exact auxiliary-redex result type. -/
theorem roseSubstRestoreAuxRuleRedexDefEqU09
    {Γ : List VExpr} {recArgs : List VExpr} {major A B : VExpr}
    (hrecArgs : recArgs.map roseNestedC.restoreRec =
      recArgs.map (VExpr.substConst roseRestoreInterp09))
    (hmajor : roseFinalEnv09.IsDefEq 2 Γ
      (major.substConst roseRestoreInterp09)
      (roseNestedC.restoreRec major) A)
    (hrecType : roseFinalEnv09.HasType 2 Γ
      (((VExpr.const (.str roseFlatAuxName09 "rec")
        (VLevel.params 2)).appN recArgs).substConst roseRestoreInterp09)
      (.forallE A B)) :
    roseFinalEnv09.IsDefEqU 2 Γ
      ((.app
        ((VExpr.const (.str roseFlatAuxName09 "rec")
          (VLevel.params 2)).appN recArgs) major : VExpr).substConst
            roseRestoreInterp09)
      (roseNestedC.restoreRec
        (.app
          ((VExpr.const (.str roseFlatAuxName09 "rec")
            (VLevel.params 2)).appN recArgs) major)) :=
  (roseSubstRestoreAuxRuleRedexDefEq09 hrecArgs hmajor hrecType).toU

/-- Complete final-runtime nil redex alignment at arbitrary well-formed
recursor and constructor universe levels. -/
theorem roseSubstNilRuleRuntimeRedexDefEq09
    {univs : Nat} {Γ : List VExpr}
    {recLevels : List VLevel} {level : VLevel}
    {recArgs : List VExpr} {param : VExpr}
    {fields : List VExpr} {C D : VExpr}
    (hrecLevels : recLevels.length = 2)
    (hlevel : level.WF univs)
    (hparamType : roseFinalEnv09.HasType univs Γ
      (param.substConst roseRestoreInterp09) (.sort (.succ level)))
    (hfieldsSpine : roseFinalEnv09.SpineWF univs Γ
      ((VExpr.const ``List [level]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
          (param.substConst roseRestoreInterp09)))
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hrecType : roseFinalEnv09.HasType univs Γ
      (((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN
        recArgs).substConst roseRestoreInterp09)
      (.forallE C D)) :
    roseFinalEnv09.IsDefEq univs Γ
      ((.app
        ((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN recArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `nil) [level]).appN
          ([param] ++ fields)) : VExpr).substConst roseRestoreInterp09)
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
          recLevels).appN
            (recArgs.map (VExpr.substConst roseRestoreInterp09)))
        (((VExpr.const ``List.nil [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (param.substConst roseRestoreInterp09))).appN
          (fields.map (VExpr.substConst roseRestoreInterp09))))
      (D.inst
        (((VExpr.const (roseFlatAuxName09 ++ `nil) [level]).appN
          ([param] ++ fields)).substConst roseRestoreInterp09)) := by
  exact roseSubstAuxRuleRuntimeRedexDefEq09 hrecLevels
    (roseSubstNilRuntimeCtorSpineDefEq09 hlevel hparamType hfieldsSpine)
    hrecType

/-- Complete final-runtime cons redex alignment at arbitrary well-formed
recursor and constructor universe levels. -/
theorem roseSubstConsRuleRuntimeRedexDefEq09
    {univs : Nat} {Γ : List VExpr}
    {recLevels : List VLevel} {level : VLevel}
    {recArgs : List VExpr} {param : VExpr}
    {fields : List VExpr} {C D : VExpr}
    (hrecLevels : recLevels.length = 2)
    (hlevel : level.WF univs)
    (hparamType : roseFinalEnv09.HasType univs Γ
      (param.substConst roseRestoreInterp09) (.sort (.succ level)))
    (hfieldsSpine : roseFinalEnv09.SpineWF univs Γ
      (roseConsRuntimePrefixType09 level param)
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hrecType : roseFinalEnv09.HasType univs Γ
      (((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN
        recArgs).substConst roseRestoreInterp09)
      (.forallE C D)) :
    roseFinalEnv09.IsDefEq univs Γ
      ((.app
        ((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN recArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `cons) [level]).appN
          ([param] ++ fields)) : VExpr).substConst roseRestoreInterp09)
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
          recLevels).appN
            (recArgs.map (VExpr.substConst roseRestoreInterp09)))
        (((VExpr.const ``List.cons [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (param.substConst roseRestoreInterp09))).appN
          (fields.map (VExpr.substConst roseRestoreInterp09))))
      (D.inst
        (((VExpr.const (roseFlatAuxName09 ++ `cons) [level]).appN
          ([param] ++ fields)).substConst roseRestoreInterp09)) := by
  exact roseSubstAuxRuleRuntimeRedexDefEq09 hrecLevels
    (roseSubstConsRuntimeCtorSpineDefEq09 hlevel hparamType hfieldsSpine)
    hrecType

/-- Complete concrete nil redex alignment at the exact result type induced
by the interpreted auxiliary major. -/
theorem roseSubstRestoreNilRuleRedexDefEq09
    {Γ : List VExpr} {recArgs : List VExpr} {param : VExpr}
    {fields : List VExpr} {C D : VExpr}
    (hrecArgs : recArgs.map roseNestedC.restoreRec =
      recArgs.map (VExpr.substConst roseRestoreInterp09))
    (hparam : roseNestedC.restoreRec param =
      param.substConst roseRestoreInterp09)
    (hparamType : roseFinalEnv09.HasType 2 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 1))))
    (hfieldsSpine : roseFinalEnv09.SpineWF 2 Γ
      ((VExpr.const ``List [.param 1]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
          (param.substConst roseRestoreInterp09)))
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hfields : fields.map roseNestedC.restoreRec =
      fields.map (VExpr.substConst roseRestoreInterp09))
    (hrecType : roseFinalEnv09.HasType 2 Γ
      (((VExpr.const (.str roseFlatAuxName09 "rec")
        (VLevel.params 2)).appN recArgs).substConst roseRestoreInterp09)
      (.forallE C D)) :
    roseFinalEnv09.IsDefEq 2 Γ
      ((.app
        ((VExpr.const (.str roseFlatAuxName09 "rec")
          (VLevel.params 2)).appN recArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
          ([param] ++ fields)) : VExpr).substConst roseRestoreInterp09)
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
          (VLevel.params 2)).appN (recArgs.map roseNestedC.restoreRec))
        (((VExpr.const ``List.nil [.param 1]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (roseNestedC.restoreRec param))).appN
          (fields.map roseNestedC.restoreRec)))
      (D.inst
        (((VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
          ([param] ++ fields)).substConst roseRestoreInterp09)) := by
  let major : VExpr :=
    (VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
      ([param] ++ fields)
  have hmajor := roseSubstRestoreNilCtorSpineDefEq09 hparam hparamType
    hfieldsSpine hfields
  have hout := roseSubstRestoreAuxRuleRedexDefEq09 hrecArgs
    (major := major) hmajor (by simpa [major] using hrecType)
  rw [roseRestoreNilRuleRedex09] at hout
  simpa [major] using hout

/-- Existentially typed compatibility wrapper for the complete nil redex. -/
theorem roseSubstRestoreNilRuleRedexDefEqU09
    {Γ : List VExpr} {recArgs : List VExpr} {param : VExpr}
    {fields : List VExpr} {C D : VExpr}
    (hrecArgs : recArgs.map roseNestedC.restoreRec =
      recArgs.map (VExpr.substConst roseRestoreInterp09))
    (hparam : roseNestedC.restoreRec param =
      param.substConst roseRestoreInterp09)
    (hparamType : roseFinalEnv09.HasType 2 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 1))))
    (hfieldsSpine : roseFinalEnv09.SpineWF 2 Γ
      ((VExpr.const ``List [.param 1]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
          (param.substConst roseRestoreInterp09)))
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hfields : fields.map roseNestedC.restoreRec =
      fields.map (VExpr.substConst roseRestoreInterp09))
    (hrecType : roseFinalEnv09.HasType 2 Γ
      (((VExpr.const (.str roseFlatAuxName09 "rec")
        (VLevel.params 2)).appN recArgs).substConst roseRestoreInterp09)
      (.forallE C D)) :
    roseFinalEnv09.IsDefEqU 2 Γ
      ((.app
        ((VExpr.const (.str roseFlatAuxName09 "rec")
          (VLevel.params 2)).appN recArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
          ([param] ++ fields)) : VExpr).substConst roseRestoreInterp09)
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
          (VLevel.params 2)).appN (recArgs.map roseNestedC.restoreRec))
        (((VExpr.const ``List.nil [.param 1]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (roseNestedC.restoreRec param))).appN
          (fields.map roseNestedC.restoreRec))) :=
  (roseSubstRestoreNilRuleRedexDefEq09 hrecArgs hparam hparamType
    hfieldsSpine hfields hrecType).toU

/-- Complete concrete cons redex alignment at the same final-environment
boundary, retaining the exact result type and two-field residual constructor
telescope. -/
theorem roseSubstRestoreConsRuleRedexDefEq09
    {Γ : List VExpr} {recArgs : List VExpr} {param : VExpr}
    {fields : List VExpr} {C D : VExpr}
    (hrecArgs : recArgs.map roseNestedC.restoreRec =
      recArgs.map (VExpr.substConst roseRestoreInterp09))
    (hparam : roseNestedC.restoreRec param =
      param.substConst roseRestoreInterp09)
    (hparamType : roseFinalEnv09.HasType 2 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 1))))
    (hfieldsSpine : roseFinalEnv09.SpineWF 2 Γ
      (roseConsPrefixType09 param)
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hfields : fields.map roseNestedC.restoreRec =
      fields.map (VExpr.substConst roseRestoreInterp09))
    (hrecType : roseFinalEnv09.HasType 2 Γ
      (((VExpr.const (.str roseFlatAuxName09 "rec")
        (VLevel.params 2)).appN recArgs).substConst roseRestoreInterp09)
      (.forallE C D)) :
    roseFinalEnv09.IsDefEq 2 Γ
      ((.app
        ((VExpr.const (.str roseFlatAuxName09 "rec")
          (VLevel.params 2)).appN recArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
          ([param] ++ fields)) : VExpr).substConst roseRestoreInterp09)
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
          (VLevel.params 2)).appN (recArgs.map roseNestedC.restoreRec))
        (((VExpr.const ``List.cons [.param 1]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (roseNestedC.restoreRec param))).appN
          (fields.map roseNestedC.restoreRec)))
      (D.inst
        (((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
          ([param] ++ fields)).substConst roseRestoreInterp09)) := by
  let major : VExpr :=
    (VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
      ([param] ++ fields)
  have hmajor := roseSubstRestoreConsCtorSpineDefEq09 hparam hparamType
    hfieldsSpine hfields
  have hout := roseSubstRestoreAuxRuleRedexDefEq09 hrecArgs
    (major := major) hmajor (by simpa [major] using hrecType)
  rw [roseRestoreConsRuleRedex09] at hout
  simpa [major] using hout

/-- Existentially typed compatibility wrapper for the complete cons redex. -/
theorem roseSubstRestoreConsRuleRedexDefEqU09
    {Γ : List VExpr} {recArgs : List VExpr} {param : VExpr}
    {fields : List VExpr} {C D : VExpr}
    (hrecArgs : recArgs.map roseNestedC.restoreRec =
      recArgs.map (VExpr.substConst roseRestoreInterp09))
    (hparam : roseNestedC.restoreRec param =
      param.substConst roseRestoreInterp09)
    (hparamType : roseFinalEnv09.HasType 2 Γ
      (param.substConst roseRestoreInterp09)
      (.sort (.succ (.param 1))))
    (hfieldsSpine : roseFinalEnv09.SpineWF 2 Γ
      (roseConsPrefixType09 param)
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hfields : fields.map roseNestedC.restoreRec =
      fields.map (VExpr.substConst roseRestoreInterp09))
    (hrecType : roseFinalEnv09.HasType 2 Γ
      (((VExpr.const (.str roseFlatAuxName09 "rec")
        (VLevel.params 2)).appN recArgs).substConst roseRestoreInterp09)
      (.forallE C D)) :
    roseFinalEnv09.IsDefEqU 2 Γ
      ((.app
        ((VExpr.const (.str roseFlatAuxName09 "rec")
          (VLevel.params 2)).appN recArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
          ([param] ++ fields)) : VExpr).substConst roseRestoreInterp09)
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
          (VLevel.params 2)).appN (recArgs.map roseNestedC.restoreRec))
        (((VExpr.const ``List.cons [.param 1]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (roseNestedC.restoreRec param))).appN
          (fields.map roseNestedC.restoreRec))) :=
  (roseSubstRestoreConsRuleRedexDefEq09 hrecArgs hparam hparamType
    hfieldsSpine hfields hrecType).toU

/-! ### Concrete generated-rule interpretation -/

/-- The flattened rule components are the literal restored components after
the concrete Rose reflattening pass. -/
theorem roseFlatRule0LhsReflatten09 :
    (roseNestedC.generation.rule 0 roseFlatRuleConstructor0_09).lhs =
      roseReflattenVExpr09 roseRule0LhsL := by
  native_decide

theorem roseFlatRule0RhsReflatten09 :
    (roseNestedC.generation.rule 0 roseFlatRuleConstructor0_09).rhs =
      roseReflattenVExpr09 roseRule0RhsL := by
  native_decide

theorem roseFlatRule0TypeReflatten09 :
    (roseNestedC.generation.rule 0 roseFlatRuleConstructor0_09).type =
      roseReflattenVExpr09 roseRule0TypeL := by
  native_decide

theorem roseFlatRule1LhsReflatten09 :
    (roseNestedC.generation.rule 1 roseFlatRuleConstructor1_09).lhs =
      roseReflattenVExpr09 roseRule1LhsL := by
  native_decide

theorem roseFlatRule1RhsReflatten09 :
    (roseNestedC.generation.rule 1 roseFlatRuleConstructor1_09).rhs =
      roseReflattenVExpr09 roseRule1RhsL := by
  native_decide

theorem roseFlatRule1TypeReflatten09 :
    (roseNestedC.generation.rule 1 roseFlatRuleConstructor1_09).type =
      roseReflattenVExpr09 roseRule1TypeL := by
  native_decide

theorem roseFlatRule2LhsReflatten09 :
    (roseNestedC.generation.rule 2 roseFlatRuleConstructor2_09).lhs =
      roseReflattenVExpr09 roseRule2LhsL := by
  native_decide

theorem roseFlatRule2RhsReflatten09 :
    (roseNestedC.generation.rule 2 roseFlatRuleConstructor2_09).rhs =
      roseReflattenVExpr09 roseRule2RhsL := by
  native_decide

theorem roseFlatRule2TypeReflatten09 :
    (roseNestedC.generation.rule 2 roseFlatRuleConstructor2_09).type =
      roseReflattenVExpr09 roseRule2TypeL := by
  native_decide

/-- Literal forms of the three restored certificate-owned rules. -/
theorem roseRestoredRule0Literal09 :
    roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09 =
      ⟨2, roseRule0LhsL, roseRule0RhsL, roseRule0TypeL⟩ := by
  native_decide

theorem roseRestoredRule1Literal09 :
    roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09 =
      ⟨2, roseRule1LhsL, roseRule1RhsL, roseRule1TypeL⟩ := by
  native_decide

theorem roseRestoredRule2Literal09 :
    roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09 =
      ⟨2, roseRule2LhsL, roseRule2RhsL, roseRule2TypeL⟩ := by
  native_decide

/-- Close a saturated auxiliary-nil value against its σ̂ β-redex in the
current concrete rule context. -/
macro "rose_rule_nil_beta" param:term : tactic => `(tactic| (
  have hrestore :
      roseNestedC.restoreRec
        ((VExpr.const (`_nested.List_1 ++ `nil) [.param 1]).app $param) =
      (VExpr.const ``List.nil [.param 1]).app
        ((VExpr.const
          `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
          $param) := by
    simpa [roseFlatAuxName09, VExpr.appN,
      VInductDecl.NestedBlockChecked.restoreRec,
      VInductDecl.restoreExpr] using
      (roseRestoreNilPrefix09 [.param 1] $param)
  have hsigma :
      (((VExpr.const (roseFlatAuxName09 ++ `nil) [.param 1]).appN
        [$param]).substConst roseRestoreInterp09) =
      ((VExpr.sort (VLevel.param 1).succ).lam
        ((VExpr.const ``List.nil [.param 1]).app
          ((VExpr.const
            `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (.bvar 0)))).app $param := by
    simp [roseAuxNilInterpValue09, VExpr.appN, VExpr.substConst,
      VExpr.instL, VLevel.inst, List.getD_eq_getElem?_getD,
      roseRestoreInterp_auxNil09]
  rw [← hrestore, ← hsigma]
  exact (roseSubstRestoreNilPrefixDefEq09 (by rfl)
    (by type_tac)).symm))

/-- The corresponding two-field auxiliary-cons β bridge. -/
macro "rose_rule_cons_beta" "(" param:term "," head:term "," tail:term ")" : tactic =>
  `(tactic| (
    have hrestore :
        roseNestedC.restoreRec
          ((((VExpr.const (`_nested.List_1 ++ `cons) [.param 1]).app
            $param).app $head).app $tail) =
        (((VExpr.const ``List.cons [.param 1]).app
          ((VExpr.const
            `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            $param)).app $head).app $tail := by
      simpa [roseFlatAuxName09, VExpr.appN,
        VInductDecl.NestedBlockChecked.restoreRec,
        VInductDecl.restoreExpr] using
        (roseRestoreConsCtorSpine09 [.param 1] $param [$head, $tail])
    have hsigma :
        (((VExpr.const (roseFlatAuxName09 ++ `cons) [.param 1]).appN
          ([$param] ++ [$head, $tail])).substConst roseRestoreInterp09) =
        (((((VExpr.sort (VLevel.param 1).succ).lam
          ((VExpr.const ``List.cons [.param 1]).app
            ((VExpr.const
              `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
              (.bvar 0)))).app $param).app $head).app $tail) := by
      simp [roseAuxConsInterpValue09, VExpr.appN,
        VExpr.substConst, VExpr.instL, VLevel.inst,
        List.getD_eq_getElem?_getD, roseRestoreInterp_auxCons09]
    rw [← hrestore, ← hsigma]
    exact (roseSubstRestoreConsCtorSpineDefEq09
      (param := $param) (fields := [$head, $tail])
      (by rfl) (by type_tac)
      (by exact .cons (by type_tac) (.cons (by type_tac) .nil))
      (by rfl)).symm))

/-- The restored main-rule lhs is definitionally equal to the σ̂-image of
the flattened lhs at its literal rule type. -/
theorem roseFlatRule0LhsAlignment09 :
    roseFinalEnv09.IsDefEq 2 [] roseRule0LhsL
      ((roseNestedC.generation.rule 0
        roseFlatRuleConstructor0_09).lhs.substConst roseRestoreInterp09)
      roseRule0TypeL := by
  rose_rule_hyps roseFinalEnv09
  have hparams1 :
      (VLevel.params 1).map (VLevel.inst [.param 1]) = [.param 1] :=
    VLevel.inst_map_id rfl
  have hparams2 :
      (VLevel.params 2).map
          (VLevel.inst [.param 0, .param 1]) = [.param 0, .param 1] :=
    VLevel.inst_map_id rfl
  rw [roseFlatRule0LhsReflatten09]
  simp [roseReflattenVExpr09, roseFlatNestedHead09, roseFlatAuxName09,
    roseRule0LhsL, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    VExpr.substConst, VExpr.instL, VLevel.inst, hparams1, hparams2,
    List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09,
    roseRestoreInterp_mainRec09]
  exact .lamDF (by type_tac) <|
    .lamDF (by type_tac) <|
    .lamDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .lamDF (by rose_rec_nil_domain) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) <|
    .lamDF (by type_tac) <|
    .lamDF (by rose_rec_family_beta (.bvar 6)) (by type_tac)

/-- Main-rule rhs alignment under σ̂. -/
theorem roseFlatRule0RhsAlignment09 :
    roseFinalEnv09.IsDefEq 2 [] roseRule0RhsL
      ((roseNestedC.generation.rule 0
        roseFlatRuleConstructor0_09).rhs.substConst roseRestoreInterp09)
      roseRule0TypeL := by
  rose_rule_hyps roseFinalEnv09
  have hparams1 :
      (VLevel.params 1).map (VLevel.inst [.param 1]) = [.param 1] :=
    VLevel.inst_map_id rfl
  have hparams2 :
      (VLevel.params 2).map
          (VLevel.inst [.param 0, .param 1]) = [.param 0, .param 1] :=
    VLevel.inst_map_id rfl
  rw [roseFlatRule0RhsReflatten09]
  simp [roseReflattenVExpr09, roseFlatNestedHead09, roseFlatAuxName09,
    roseRule0RhsL, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    VExpr.substConst, VExpr.instL, VLevel.inst, hparams1, hparams2,
    List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09,
    roseRestoreInterp_auxRecLiteral09]
  exact .lamDF (by type_tac) <|
    .lamDF (by type_tac) <|
    .lamDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .lamDF (by rose_rec_nil_domain) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) <|
    .lamDF (by type_tac) <|
    .lamDF (by rose_rec_family_beta (.bvar 6)) (by type_tac)

/-- Main-rule type alignment under σ̂. -/
theorem roseFlatRule0TypeAlignment09 :
    roseFinalEnv09.IsDefEqU 2 [] roseRule0TypeL
      ((roseNestedC.generation.rule 0
        roseFlatRuleConstructor0_09).type.substConst roseRestoreInterp09) := by
  rose_rule_hyps roseFinalEnv09
  have hparams1 :
      (VLevel.params 1).map (VLevel.inst [.param 1]) = [.param 1] :=
    VLevel.inst_map_id rfl
  rw [roseFlatRule0TypeReflatten09]
  simp [roseReflattenVExpr09, roseFlatNestedHead09, roseFlatAuxName09,
    roseRule0TypeL, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    VExpr.substConst, VExpr.instL, VLevel.inst, hparams1,
    List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09]
  apply VEnv.IsDefEq.toU
  exact .forallEDF (by type_tac) <|
    .forallEDF (by type_tac) <|
    .forallEDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .forallEDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .forallEDF (by rose_rec_nil_domain) <|
    .forallEDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) <|
    .forallEDF (by type_tac) <|
    .forallEDF (by rose_rec_family_beta (.bvar 6)) (by type_tac)

/-- The certificate-owned restored main equation transports to the σ̂-image
of the flattened main equation. -/
theorem roseRestoreInterpRule0DefEq09 :
    roseFinalEnv09.IsDefEq 2 []
      ((roseNestedC.generation.rule 0
        roseFlatRuleConstructor0_09).lhs.substConst roseRestoreInterp09)
      ((roseNestedC.generation.rule 0
        roseFlatRuleConstructor0_09).rhs.substConst roseRestoreInterp09)
      ((roseNestedC.generation.rule 0
        roseFlatRuleConstructor0_09).type.substConst roseRestoreInterp09) := by
  have hrest := VEnv.IsDefEq.extra0
    (roseNestedCertificate09.restoredRuleRegistered roseFlatRuleEntry0_09)
    (roseNestedCertificate09.restoredRuleWF roseFlatRuleEntry0_09)
  change roseFinalEnv09.IsDefEq
    (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).uvars []
    (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).lhs
    (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).rhs
    (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).type at hrest
  rw [roseRestoredRule0Literal09] at hrest
  have hmid := roseFlatRule0LhsAlignment09.symm.trans
    (hrest.trans roseFlatRule0RhsAlignment09)
  exact roseFlatRule0TypeAlignment09.defeqDF
    roseNestedCertificate09.afterWF (by trivial) hmid

/-- Nil-rule lhs alignment, with the final auxiliary major discharged by the
typed nil β bridge. -/
theorem roseFlatRule1LhsAlignment09 :
    roseFinalEnv09.IsDefEq 2 [] roseRule1LhsL
      ((roseNestedC.generation.rule 1
        roseFlatRuleConstructor1_09).lhs.substConst roseRestoreInterp09)
      roseRule1TypeL := by
  rose_rule_hyps roseFinalEnv09
  have hparams1 :
      (VLevel.params 1).map (VLevel.inst [.param 1]) = [.param 1] :=
    VLevel.inst_map_id rfl
  have hparams2 :
      (VLevel.params 2).map
          (VLevel.inst [.param 0, .param 1]) = [.param 0, .param 1] :=
    VLevel.inst_map_id rfl
  rw [roseFlatRule1LhsReflatten09]
  simp [roseReflattenVExpr09, roseFlatNestedHead09, roseFlatAuxName09,
    roseRule1LhsL, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    VExpr.substConst, VExpr.instL, VLevel.inst, hparams1, hparams2,
    List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09,
    roseRestoreInterp_auxRecLiteral09]
  exact .lamDF (by type_tac) <|
    .lamDF (by type_tac) <|
    .lamDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .lamDF (by rose_rec_nil_domain) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) <|
    (by
      apply VEnv.IsDefEq.appDF
        (A := (VExpr.const ``List [.param 1]).app
          ((VExpr.const
            `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (.bvar 5)))
        (B := (VExpr.bvar 4).app (.bvar 0))
      · type_tac
      · rose_rule_nil_beta (.bvar 5))

/-- Nil-rule rhs alignment under σ̂. -/
theorem roseFlatRule1RhsAlignment09 :
    roseFinalEnv09.IsDefEq 2 [] roseRule1RhsL
      ((roseNestedC.generation.rule 1
        roseFlatRuleConstructor1_09).rhs.substConst roseRestoreInterp09)
      roseRule1TypeL := by
  rose_rule_hyps roseFinalEnv09
  have hparams1 :
      (VLevel.params 1).map (VLevel.inst [.param 1]) = [.param 1] :=
    VLevel.inst_map_id rfl
  rw [roseFlatRule1RhsReflatten09]
  simp [roseReflattenVExpr09, roseFlatNestedHead09, roseFlatAuxName09,
    roseRule1RhsL, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    VExpr.substConst, VExpr.instL, VLevel.inst, hparams1,
    List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09]
  exact .lamDF (by type_tac) <|
    .lamDF (by type_tac) <|
    .lamDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .lamDF (by rose_rec_nil_domain) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) (by type_tac)

/-- Nil-rule type alignment under σ̂. -/
theorem roseFlatRule1TypeAlignment09 :
    roseFinalEnv09.IsDefEqU 2 [] roseRule1TypeL
      ((roseNestedC.generation.rule 1
        roseFlatRuleConstructor1_09).type.substConst roseRestoreInterp09) := by
  rose_rule_hyps roseFinalEnv09
  have hparams1 :
      (VLevel.params 1).map (VLevel.inst [.param 1]) = [.param 1] :=
    VLevel.inst_map_id rfl
  rw [roseFlatRule1TypeReflatten09]
  simp [roseReflattenVExpr09, roseFlatNestedHead09, roseFlatAuxName09,
    roseRule1TypeL, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    VExpr.substConst, VExpr.instL, VLevel.inst, hparams1,
    List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09]
  apply VEnv.IsDefEq.toU
  exact .forallEDF (by type_tac) <|
    .forallEDF (by type_tac) <|
    .forallEDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .forallEDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .forallEDF (by rose_rec_nil_domain) <|
    .forallEDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) <|
    (by
      apply VEnv.IsDefEq.appDF
        (A := (VExpr.const ``List [.param 1]).app
          ((VExpr.const
            `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (.bvar 5)))
        (B := .sort (.param 0))
      · type_tac
      · rose_rule_nil_beta (.bvar 5))

/-- The certificate-owned restored nil equation transports to the σ̂-image
of the flattened nil equation. -/
theorem roseRestoreInterpRule1DefEq09 :
    roseFinalEnv09.IsDefEq 2 []
      ((roseNestedC.generation.rule 1
        roseFlatRuleConstructor1_09).lhs.substConst roseRestoreInterp09)
      ((roseNestedC.generation.rule 1
        roseFlatRuleConstructor1_09).rhs.substConst roseRestoreInterp09)
      ((roseNestedC.generation.rule 1
        roseFlatRuleConstructor1_09).type.substConst roseRestoreInterp09) := by
  have hrest := VEnv.IsDefEq.extra0
    (roseNestedCertificate09.restoredRuleRegistered roseFlatRuleEntry1_09)
    (roseNestedCertificate09.restoredRuleWF roseFlatRuleEntry1_09)
  change roseFinalEnv09.IsDefEq
    (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).uvars []
    (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).lhs
    (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).rhs
    (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).type at hrest
  rw [roseRestoredRule1Literal09] at hrest
  have hmid := roseFlatRule1LhsAlignment09.symm.trans
    (hrest.trans roseFlatRule1RhsAlignment09)
  exact roseFlatRule1TypeAlignment09.defeqDF
    roseNestedCertificate09.afterWF (by trivial) hmid

/-- Cons-rule lhs alignment, including its two-field auxiliary major. -/
theorem roseFlatRule2LhsAlignment09 :
    roseFinalEnv09.IsDefEq 2 [] roseRule2LhsL
      ((roseNestedC.generation.rule 2
        roseFlatRuleConstructor2_09).lhs.substConst roseRestoreInterp09)
      roseRule2TypeL := by
  rose_rule_hyps roseFinalEnv09
  have hparams1 :
      (VLevel.params 1).map (VLevel.inst [.param 1]) = [.param 1] :=
    VLevel.inst_map_id rfl
  have hparams2 :
      (VLevel.params 2).map
          (VLevel.inst [.param 0, .param 1]) = [.param 0, .param 1] :=
    VLevel.inst_map_id rfl
  rw [roseFlatRule2LhsReflatten09]
  simp [roseReflattenVExpr09, roseFlatNestedHead09, roseFlatAuxName09,
    roseRule2LhsL, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    VExpr.substConst, VExpr.instL, VLevel.inst, hparams1, hparams2,
    List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09,
    roseRestoreInterp_auxRecLiteral09]
  exact .lamDF (by type_tac) <|
    .lamDF (by type_tac) <|
    .lamDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .lamDF (by rose_rec_nil_domain) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) <|
    .lamDF (by type_tac) <|
    .lamDF (by rose_rec_family_beta (.bvar 6)) <|
    (by
      apply VEnv.IsDefEq.appDF
        (A := (VExpr.const ``List [.param 1]).app
          ((VExpr.const
            `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (.bvar 7)))
        (B := (VExpr.bvar 6).app (.bvar 0))
      · type_tac
      · rose_rule_cons_beta (.bvar 7, .bvar 1, .bvar 0))

/-- Cons-rule rhs alignment under σ̂. -/
theorem roseFlatRule2RhsAlignment09 :
    roseFinalEnv09.IsDefEq 2 [] roseRule2RhsL
      ((roseNestedC.generation.rule 2
        roseFlatRuleConstructor2_09).rhs.substConst roseRestoreInterp09)
      roseRule2TypeL := by
  rose_rule_hyps roseFinalEnv09
  have hparams1 :
      (VLevel.params 1).map (VLevel.inst [.param 1]) = [.param 1] :=
    VLevel.inst_map_id rfl
  have hparams2 :
      (VLevel.params 2).map
          (VLevel.inst [.param 0, .param 1]) = [.param 0, .param 1] :=
    VLevel.inst_map_id rfl
  rw [roseFlatRule2RhsReflatten09]
  simp [roseReflattenVExpr09, roseFlatNestedHead09, roseFlatAuxName09,
    roseRule2RhsL, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    VExpr.substConst, VExpr.instL, VLevel.inst, hparams1, hparams2,
    List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09,
    roseRestoreInterp_mainRec09, roseRestoreInterp_auxRecLiteral09]
  exact .lamDF (by type_tac) <|
    .lamDF (by type_tac) <|
    .lamDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .lamDF (by rose_rec_nil_domain) <|
    .lamDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) <|
    .lamDF (by type_tac) <|
    .lamDF (by rose_rec_family_beta (.bvar 6)) (by type_tac)

/-- Cons-rule type alignment under σ̂. -/
theorem roseFlatRule2TypeAlignment09 :
    roseFinalEnv09.IsDefEqU 2 [] roseRule2TypeL
      ((roseNestedC.generation.rule 2
        roseFlatRuleConstructor2_09).type.substConst roseRestoreInterp09) := by
  rose_rule_hyps roseFinalEnv09
  have hparams1 :
      (VLevel.params 1).map (VLevel.inst [.param 1]) = [.param 1] :=
    VLevel.inst_map_id rfl
  rw [roseFlatRule2TypeReflatten09]
  simp [roseReflattenVExpr09, roseFlatNestedHead09, roseFlatAuxName09,
    roseRule2TypeL, roseAuxFamilyInterpValue09,
    roseAuxNilInterpValue09, roseAuxConsInterpValue09,
    VExpr.substConst, VExpr.instL, VLevel.inst, hparams1,
    List.getD_eq_getElem?_getD,
    roseRestoreInterp_auxFamilyLiteral09,
    roseRestoreInterp_auxNilLiteral09,
    roseRestoreInterp_auxConsLiteral09,
    roseRestoreInterp_mainCtor09, roseRestoreInterp_mainFamily09]
  apply VEnv.IsDefEq.toU
  exact .forallEDF (by type_tac) <|
    .forallEDF (by type_tac) <|
    .forallEDF
      (.forallEDF (by rose_rec_family_beta (.bvar 1)) (by type_tac)) <|
    .forallEDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 3)) <|
        .forallEDF (by type_tac) (by type_tac)) <|
    .forallEDF (by rose_rec_nil_domain) <|
    .forallEDF
      (.forallEDF (by type_tac) <|
        .forallEDF (by rose_rec_family_beta (.bvar 5)) <|
        .forallEDF (by type_tac) <|
        .forallEDF (by type_tac) <|
        (by rose_rec_cons_domain)) <|
    .forallEDF (by type_tac) <|
    .forallEDF (by rose_rec_family_beta (.bvar 6)) <|
    (by
      apply VEnv.IsDefEq.appDF
        (A := (VExpr.const ``List [.param 1]).app
          ((VExpr.const
            `Lean4Lean.NestedRepresentation.RoseTree [.param 1]).app
            (.bvar 7)))
        (B := .sort (.param 0))
      · type_tac
      · rose_rule_cons_beta (.bvar 7, .bvar 1, .bvar 0))

/-- The certificate-owned restored cons equation transports to the σ̂-image
of the flattened cons equation. -/
theorem roseRestoreInterpRule2DefEq09 :
    roseFinalEnv09.IsDefEq 2 []
      ((roseNestedC.generation.rule 2
        roseFlatRuleConstructor2_09).lhs.substConst roseRestoreInterp09)
      ((roseNestedC.generation.rule 2
        roseFlatRuleConstructor2_09).rhs.substConst roseRestoreInterp09)
      ((roseNestedC.generation.rule 2
        roseFlatRuleConstructor2_09).type.substConst roseRestoreInterp09) := by
  have hrest := VEnv.IsDefEq.extra0
    (roseNestedCertificate09.restoredRuleRegistered roseFlatRuleEntry2_09)
    (roseNestedCertificate09.restoredRuleWF roseFlatRuleEntry2_09)
  change roseFinalEnv09.IsDefEq
    (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).uvars []
    (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).lhs
    (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).rhs
    (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).type at hrest
  rw [roseRestoredRule2Literal09] at hrest
  have hmid := roseFlatRule2LhsAlignment09.symm.trans
    (hrest.trans roseFlatRule2RhsAlignment09)
  exact roseFlatRule2TypeAlignment09.defeqDF
    roseNestedCertificate09.afterWF (by trivial) hmid

/-- Exact finite inventories used to discharge the remaining `ConstInterp`
equation field. -/
theorem roseFlatGeneratedRulesLiteral09 :
    roseNestedC.generation.generatedRules =
      [roseNestedC.generation.rule 0 roseFlatRuleConstructor0_09,
       roseNestedC.generation.rule 1 roseFlatRuleConstructor1_09,
       roseNestedC.generation.rule 2 roseFlatRuleConstructor2_09] := by
  native_decide

theorem roseListRuleBound0_09 :
    0 < Lean4Lean.InductiveFixtures.listGenerationChecked.generatedRules.length := by
  native_decide

theorem roseListRuleBound1_09 :
    1 < Lean4Lean.InductiveFixtures.listGenerationChecked.generatedRules.length := by
  native_decide

abbrev roseListRule0_09 :=
  Lean4Lean.InductiveFixtures.listGenerationChecked.generatedRules[0]'
    roseListRuleBound0_09

abbrev roseListRule1_09 :=
  Lean4Lean.InductiveFixtures.listGenerationChecked.generatedRules[1]'
    roseListRuleBound1_09

theorem roseListGeneratedRulesLiteral09 :
    Lean4Lean.InductiveFixtures.listGenerationChecked.generatedRules =
      [roseListRule0_09, roseListRule1_09] := by
  native_decide

/-- σ̂ is literally the identity on both inherited List equations. -/
theorem roseRestoreInterpListRule0Fixed09 :
    roseListRule0_09.lhs.substConst roseRestoreInterp09 =
        roseListRule0_09.lhs ∧
    roseListRule0_09.rhs.substConst roseRestoreInterp09 =
        roseListRule0_09.rhs ∧
    roseListRule0_09.type.substConst roseRestoreInterp09 =
        roseListRule0_09.type := by
  native_decide

theorem roseRestoreInterpListRule1Fixed09 :
    roseListRule1_09.lhs.substConst roseRestoreInterp09 =
        roseListRule1_09.lhs ∧
    roseListRule1_09.rhs.substConst roseRestoreInterp09 =
        roseListRule1_09.rhs ∧
    roseListRule1_09.type.substConst roseRestoreInterp09 =
        roseListRule1_09.type := by
  native_decide

/-- The first inherited List equation remains semantic in the completed
nested environment. -/
theorem roseRestoreInterpListRule0DefEq09 :
    roseFinalEnv09.IsDefEq roseListRule0_09.uvars []
      (roseListRule0_09.lhs.substConst roseRestoreInterp09)
      (roseListRule0_09.rhs.substConst roseRestoreInterp09)
      (roseListRule0_09.type.substConst roseRestoreInterp09) := by
  have hmem : roseListRule0_09 ∈
      Lean4Lean.InductiveFixtures.listGenerationChecked.generatedRules := by
    native_decide
  have hsource : listFinalEnv07.defeqs roseListRule0_09 := by
    exact (VInductDecl.rulesFold_spec
      Lean4Lean.InductiveFixtures.listGenerationChecked.generatedRules
      listRecEnv07).2 roseListRule0_09 hmem
  have hreg := roseNestedCertificate09.envLE.defeqs hsource
  have hsem := VEnv.IsDefEq.extra0 hreg
    (roseNestedCertificate09.afterWF.ordered.defEqWF hreg)
  rw [roseRestoreInterpListRule0Fixed09.1,
    roseRestoreInterpListRule0Fixed09.2.1,
    roseRestoreInterpListRule0Fixed09.2.2]
  exact hsem

/-- The second inherited List equation remains semantic in the completed
nested environment. -/
theorem roseRestoreInterpListRule1DefEq09 :
    roseFinalEnv09.IsDefEq roseListRule1_09.uvars []
      (roseListRule1_09.lhs.substConst roseRestoreInterp09)
      (roseListRule1_09.rhs.substConst roseRestoreInterp09)
      (roseListRule1_09.type.substConst roseRestoreInterp09) := by
  have hmem : roseListRule1_09 ∈
      Lean4Lean.InductiveFixtures.listGenerationChecked.generatedRules := by
    native_decide
  have hsource : listFinalEnv07.defeqs roseListRule1_09 := by
    exact (VInductDecl.rulesFold_spec
      Lean4Lean.InductiveFixtures.listGenerationChecked.generatedRules
      listRecEnv07).2 roseListRule1_09 hmem
  have hreg := roseNestedCertificate09.envLE.defeqs hsource
  have hsem := VEnv.IsDefEq.extra0 hreg
    (roseNestedCertificate09.afterWF.ordered.defEqWF hreg)
  rw [roseRestoreInterpListRule1Fixed09.1,
    roseRestoreInterpListRule1Fixed09.2.1,
    roseRestoreInterpListRule1Fixed09.2.2]
  exact hsem

/-- Every definitional equation in the completed flattened environment has
its σ̂-image semantically valid in the completed nested environment.  The
source inventory consists exactly of the three flattened Rose equations and
the two inherited List equations. -/
theorem roseRestoreInterpDefEq09
    {df : VDefEq} (hdf : roseFlatFinalEnv09.defeqs df) :
    roseFinalEnv09.IsDefEq df.uvars []
      (df.lhs.substConst roseRestoreInterp09)
      (df.rhs.substConst roseRestoreInterp09)
      (df.type.substConst roseRestoreInterp09) := by
  rw [roseFlatFinalEnv09,
    VEnv.foldl_addDefEq_defeqs_iff] at hdf
  rcases hdf with hrose | hbase
  · rw [roseFlatGeneratedRulesLiteral09] at hrose
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrose
    rcases hrose with rfl | rfl | rfl
    · rw [show (roseNestedC.generation.rule 0
          roseFlatRuleConstructor0_09).uvars = 2 by native_decide]
      exact roseRestoreInterpRule0DefEq09
    · rw [show (roseNestedC.generation.rule 1
          roseFlatRuleConstructor1_09).uvars = 2 by native_decide]
      exact roseRestoreInterpRule1DefEq09
    · rw [show (roseNestedC.generation.rule 2
          roseFlatRuleConstructor2_09).uvars = 2 by native_decide]
      exact roseRestoreInterpRule2DefEq09
  · have hfirstRec :=
      (VEnv.addConst_defeqs_iff roseFlatAddSecondRec09 df).1 hbase
    have hctor :=
      (VEnv.addConst_defeqs_iff roseFlatAddFirstRec09 df).1 hfirstRec
    have hnil :=
      (VEnv.addConst_defeqs_iff roseFlatAddCons09 df).1 hctor
    have hnode :=
      (VEnv.addConst_defeqs_iff roseFlatAddNil09 df).1 hnil
    have hblock :=
      (VEnv.addConst_defeqs_iff roseFlatAddNode09 df).1 hnode
    have hfirstType :=
      (VEnv.addConst_defeqs_iff roseFlatBlockEnv09_eq df).1 hblock
    have hlist :=
      (VEnv.addConst_defeqs_iff roseFlatFirstTypeEnv09_eq df).1 hfirstType
    rw [listFinalEnv07,
      VEnv.foldl_addDefEq_defeqs_iff] at hlist
    rcases hlist with hlistRule | hrec
    · rw [roseListGeneratedRulesLiteral09] at hlistRule
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlistRule
      rcases hlistRule with rfl | rfl
      · exact roseRestoreInterpListRule0DefEq09
      · exact roseRestoreInterpListRule1DefEq09
    · have listRecAdd :
          listCtorEnv07.addConst ``List.rec
            (inductGenerationRecVal
              Lean4Lean.InductiveFixtures.listGenerationChecked).toVConstant =
              some listRecEnv07 := rfl
      have listConsAdd :
          listNilEnv07.addConst
            Lean4Lean.InductiveFixtures.listType.ctors[1].name
            Lean4Lean.InductiveFixtures.listType.ctors[1].toVConstant =
              some listCtorEnv07 := rfl
      have listNilAdd :
          listTypeEnv07.addConst
            Lean4Lean.InductiveFixtures.listType.ctors[0].name
            Lean4Lean.InductiveFixtures.listType.ctors[0].toVConstant =
              some listNilEnv07 := rfl
      have listTypeAdd :
          VEnv.empty.addConst
            Lean4Lean.InductiveFixtures.listType.name
            Lean4Lean.InductiveFixtures.listType.toVConstant =
              some listTypeEnv07 := rfl
      have hctor := (VEnv.addConst_defeqs_iff listRecAdd df).1 hrec
      have hnil := (VEnv.addConst_defeqs_iff listConsAdd df).1 hctor
      have htype := (VEnv.addConst_defeqs_iff listNilAdd df).1 hnil
      have hempty := (VEnv.addConst_defeqs_iff listTypeAdd df).1 htype
      exact hempty.elim

/-- The completed flattened Rose environment interprets into the completed
nested environment under the six-point restoration substitution σ̂. -/
theorem roseFlatFinalToFinalConstInterp09 :
    VEnv.ConstInterp roseFlatFinalEnv09 roseFinalEnv09
      roseRestoreInterp09 where
  ordered' := roseNestedCertificate09.afterWF.ordered
  closed := roseRestoreInterpClosed09
  value := roseRestoreInterpValue09
  keep := roseRestoreInterpKeep09
  defeq := roseRestoreInterpDefEq09
  structEta := by
    intro rule h
    exact (roseFlatNoStructEta09 rule h).elim
  structEta_familyType := by
    intro rule h
    exact (roseFlatNoStructEta09 rule h).elim
  structEta_structureType := by
    intro rule h
    exact (roseFlatNoStructEta09 rule h).elim
  structEta_rebuild := by
    intro rule h
    exact (roseFlatNoStructEta09 rule h).elim

/-- Whole restored-rule type alignment at arbitrary well-formed universe
instantiations and local contexts.  These are the exact `htype` inputs used
by the generic staged capture-spine consumer. -/
theorem roseRestoreInterpRule0TypeAlignment09
    {univs : Nat} {Γ : List VExpr} {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs) :
    roseFinalEnv09.IsDefEqU univs Γ
      ((roseNestedC.restoredRule 0
        roseFlatRuleConstructor0_09).type.instL m1)
      (((roseNestedC.generation.rule 0
        roseFlatRuleConstructor0_09).type.instL m1).substConst
          roseRestoreInterp09) := by
  rw [roseRestoredRule0Literal09]
  have h := VEnv.IsDefEqU.instL hm1 roseFlatRule0TypeAlignment09
  have h := h.weak0 (Γ := Γ) roseNestedCertificate09.afterWF.ordered
  rw [VExpr.substConst_instL]
  exact h

theorem roseRestoreInterpRule1TypeAlignment09
    {univs : Nat} {Γ : List VExpr} {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs) :
    roseFinalEnv09.IsDefEqU univs Γ
      ((roseNestedC.restoredRule 1
        roseFlatRuleConstructor1_09).type.instL m1)
      (((roseNestedC.generation.rule 1
        roseFlatRuleConstructor1_09).type.instL m1).substConst
          roseRestoreInterp09) := by
  rw [roseRestoredRule1Literal09]
  have h := VEnv.IsDefEqU.instL hm1 roseFlatRule1TypeAlignment09
  have h := h.weak0 (Γ := Γ) roseNestedCertificate09.afterWF.ordered
  rw [VExpr.substConst_instL]
  exact h

theorem roseRestoreInterpRule2TypeAlignment09
    {univs : Nat} {Γ : List VExpr} {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs) :
    roseFinalEnv09.IsDefEqU univs Γ
      ((roseNestedC.restoredRule 2
        roseFlatRuleConstructor2_09).type.instL m1)
      (((roseNestedC.generation.rule 2
        roseFlatRuleConstructor2_09).type.instL m1).substConst
          roseRestoreInterp09) := by
  rw [roseRestoredRule2Literal09]
  have h := VEnv.IsDefEqU.instL hm1 roseFlatRule2TypeAlignment09
  have h := h.weak0 (Γ := Γ) roseNestedCertificate09.afterWF.ordered
  rw [VExpr.substConst_instL]
  exact h

/-- Whole restored-rule LHS alignments at arbitrary universe
instantiations and local contexts.  Together with the corresponding type
alignments, these make the saturated restored-body alignment a generic
consequence of the staged certificate. -/
theorem roseRestoreInterpRule0LhsAlignment09
    {univs : Nat} {Γ : List VExpr} {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs) :
    roseFinalEnv09.IsDefEqU univs Γ
      ((roseNestedC.restoredRule 0
        roseFlatRuleConstructor0_09).lhs.instL m1)
      (((roseNestedC.generation.rule 0
        roseFlatRuleConstructor0_09).lhs.instL m1).substConst
          roseRestoreInterp09) := by
  rw [roseRestoredRule0Literal09]
  have h := VEnv.IsDefEqU.instL hm1 roseFlatRule0LhsAlignment09.toU
  have h := h.weak0 (Γ := Γ) roseNestedCertificate09.afterWF.ordered
  rw [VExpr.substConst_instL]
  exact h

theorem roseRestoreInterpRule1LhsAlignment09
    {univs : Nat} {Γ : List VExpr} {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs) :
    roseFinalEnv09.IsDefEqU univs Γ
      ((roseNestedC.restoredRule 1
        roseFlatRuleConstructor1_09).lhs.instL m1)
      (((roseNestedC.generation.rule 1
        roseFlatRuleConstructor1_09).lhs.instL m1).substConst
          roseRestoreInterp09) := by
  rw [roseRestoredRule1Literal09]
  have h := VEnv.IsDefEqU.instL hm1 roseFlatRule1LhsAlignment09.toU
  have h := h.weak0 (Γ := Γ) roseNestedCertificate09.afterWF.ordered
  rw [VExpr.substConst_instL]
  exact h

theorem roseRestoreInterpRule2LhsAlignment09
    {univs : Nat} {Γ : List VExpr} {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs) :
    roseFinalEnv09.IsDefEqU univs Γ
      ((roseNestedC.restoredRule 2
        roseFlatRuleConstructor2_09).lhs.instL m1)
      (((roseNestedC.generation.rule 2
        roseFlatRuleConstructor2_09).lhs.instL m1).substConst
          roseRestoreInterp09) := by
  rw [roseRestoredRule2Literal09]
  have h := VEnv.IsDefEqU.instL hm1 roseFlatRule2LhsAlignment09.toU
  have h := h.weak0 (Γ := Γ) roseNestedCertificate09.afterWF.ordered
  rw [VExpr.substConst_instL]
  exact h

/-- The main Rose rule's local `restoreRec`/σ̂ body obligation follows
from its whole-LHS alignment for every certified flattened capture spine. -/
theorem roseRestoreInterpRule0BodyAlignment09
    (readiness : RoseFlatCandidateReadiness09)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (roseFlatFinalEnv09.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseFinalEnv09.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {B : VExpr}
    (hcaps : roseFlatFinalEnv09.SpineWF univs Γ
      ((roseNestedC.generation.rule 0
        roseFlatRuleConstructor0_09).type.instL m1) captures B)
    (hcapsLen : captures.length =
      (roseNestedC.generation.ruleBinders
        roseFlatRuleConstructor0_09).length) :
    roseFinalEnv09.IsDefEqU univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (VExpr.instRev
        ((roseNestedC.restoreRec
          (roseNestedC.generation.ruleLhsBody
            roseFlatRuleConstructor0_09)).instL m1)
        (captures.map (VExpr.substConst roseRestoreInterp09)))
      (VExpr.instRev
        (((roseNestedC.generation.ruleLhsBody
          roseFlatRuleConstructor0_09).substConst
            roseRestoreInterp09).instL m1)
        (captures.map (VExpr.substConst roseRestoreInterp09))) := by
  exact (roseNestedStagedCertificate09 readiness)
    |>.restoredRuleBodyAlignmentOfLhs
      (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry0_09)
      roseFlatFinalToFinalConstInterp09 hΓflat hΓrestored hm1 hcaps
      hcapsLen (roseRestoreInterpRule0TypeAlignment09 hm1)
      (roseRestoreInterpRule0LhsAlignment09 hm1)

/-- The selected auxiliary nil rule has the same certificate-derived body
alignment; no constructor-specific restoration reduction remains. -/
theorem roseRestoreInterpRule1BodyAlignment09
    (readiness : RoseFlatCandidateReadiness09)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (roseFlatFinalEnv09.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseFinalEnv09.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {B : VExpr}
    (hcaps : roseFlatFinalEnv09.SpineWF univs Γ
      ((roseNestedC.generation.rule 1
        roseFlatRuleConstructor1_09).type.instL m1) captures B)
    (hcapsLen : captures.length =
      (roseNestedC.generation.ruleBinders
        roseFlatRuleConstructor1_09).length) :
    roseFinalEnv09.IsDefEqU univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (VExpr.instRev
        ((roseNestedC.restoreRec
          (roseNestedC.generation.ruleLhsBody
            roseFlatRuleConstructor1_09)).instL m1)
        (captures.map (VExpr.substConst roseRestoreInterp09)))
      (VExpr.instRev
        (((roseNestedC.generation.ruleLhsBody
          roseFlatRuleConstructor1_09).substConst
            roseRestoreInterp09).instL m1)
        (captures.map (VExpr.substConst roseRestoreInterp09))) := by
  exact (roseNestedStagedCertificate09 readiness)
    |>.restoredRuleBodyAlignmentOfLhs
      (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry1_09)
      roseFlatFinalToFinalConstInterp09 hΓflat hΓrestored hm1 hcaps
      hcapsLen (roseRestoreInterpRule1TypeAlignment09 hm1)
      (roseRestoreInterpRule1LhsAlignment09 hm1)

/-- The selected auxiliary cons rule's restored body is likewise aligned
with its σ̂-image for every certified flattened capture spine. -/
theorem roseRestoreInterpRule2BodyAlignment09
    (readiness : RoseFlatCandidateReadiness09)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (roseFlatFinalEnv09.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseFinalEnv09.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {B : VExpr}
    (hcaps : roseFlatFinalEnv09.SpineWF univs Γ
      ((roseNestedC.generation.rule 2
        roseFlatRuleConstructor2_09).type.instL m1) captures B)
    (hcapsLen : captures.length =
      (roseNestedC.generation.ruleBinders
        roseFlatRuleConstructor2_09).length) :
    roseFinalEnv09.IsDefEqU univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (VExpr.instRev
        ((roseNestedC.restoreRec
          (roseNestedC.generation.ruleLhsBody
            roseFlatRuleConstructor2_09)).instL m1)
        (captures.map (VExpr.substConst roseRestoreInterp09)))
      (VExpr.instRev
        (((roseNestedC.generation.ruleLhsBody
          roseFlatRuleConstructor2_09).substConst
            roseRestoreInterp09).instL m1)
        (captures.map (VExpr.substConst roseRestoreInterp09))) := by
  exact (roseNestedStagedCertificate09 readiness)
    |>.restoredRuleBodyAlignmentOfLhs
      (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry2_09)
      roseFlatFinalToFinalConstInterp09 hΓflat hΓrestored hm1 hcaps
      hcapsLen (roseRestoreInterpRule2TypeAlignment09 hm1)
      (roseRestoreInterpRule2LhsAlignment09 hm1)

/-- End-to-end restoration transport for the selected main rule after the
flattened certificate has matched its generated body.  All σ̂, whole-rule,
and final-runtime redex obligations are discharged concretely. -/
theorem roseRestoreInterpRule0BodyMatchedRuntime09
    (readiness : RoseFlatCandidateReadiness09)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (roseFlatFinalEnv09.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseFinalEnv09.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {B : VExpr}
    (hcaps : roseFlatFinalEnv09.SpineWF univs Γ
      ((roseNestedC.generation.rule 0
        roseFlatRuleConstructor0_09).type.instL m1) captures B)
    (hcapsLen : captures.length =
      (roseNestedC.generation.ruleBinders
        roseFlatRuleConstructor0_09).length)
    {recLevels ctorLevels : List VLevel}
    {recArgs ctorArgs : List VExpr}
    (hrecLevels : recLevels.length = 2)
    (hctorLevels : ctorLevels.length = 1)
    (hflat : roseFlatFinalEnv09.IsDefEq univs Γ
      (VExpr.instRev
        ((roseNestedC.generation.ruleLhsBody
          roseFlatRuleConstructor0_09).instL m1) captures)
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
          recLevels).appN recArgs)
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
          ctorLevels).appN ctorArgs)) B) :
    roseFinalEnv09.IsDefEqU univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (VExpr.instRev
        ((roseNestedC.restoreRec
          (roseNestedC.generation.ruleLhsBody
            roseFlatRuleConstructor0_09)).instL m1)
        (captures.map (VExpr.substConst roseRestoreInterp09)))
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
          recLevels).appN
            (recArgs.map (VExpr.substConst roseRestoreInterp09)))
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
          ctorLevels).appN
            (ctorArgs.map (VExpr.substConst roseRestoreInterp09)))) := by
  let redex : VExpr :=
    .app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
        recLevels).appN recArgs)
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
        ctorLevels).appN ctorArgs)
  let target : VExpr :=
    .app
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec
        recLevels).appN
          (recArgs.map (VExpr.substConst roseRestoreInterp09)))
      ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
        ctorLevels).appN
          (ctorArgs.map (VExpr.substConst roseRestoreInterp09)))
  have hredexEq : redex.substConst roseRestoreInterp09 = target := by
    simpa only [redex, target] using
      roseSubstMainRuleRuntimeRedex09 recLevels ctorLevels recArgs ctorArgs
        hrecLevels hctorLevels
  have hσ := VEnv.IsDefEq.substConst roseFlatFinalToFinalConstInterp09 hflat
  have hredex : roseFinalEnv09.IsDefEqU univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (redex.substConst roseRestoreInterp09) target := by
    rw [hredexEq]
    refine ⟨B.substConst roseRestoreInterp09, ?_⟩
    rw [← hredexEq]
    exact hσ.hasType.2
  exact (roseNestedStagedCertificate09 readiness)
    |>.restoredRuleBodyMatchedOfFlatOfLhs
      (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry0_09)
      roseFlatFinalToFinalConstInterp09 hΓflat hΓrestored hm1 hcaps
      hcapsLen (roseRestoreInterpRule0TypeAlignment09 hm1)
      (roseRestoreInterpRule0LhsAlignment09 hm1)
      hflat hredex

/-- End-to-end restoration transport for the selected auxiliary nil rule.
The local redex endpoint is supplied by the arbitrary-level runtime β bridge. -/
theorem roseRestoreInterpRule1BodyMatchedRuntime09
    (readiness : RoseFlatCandidateReadiness09)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (roseFlatFinalEnv09.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseFinalEnv09.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {B : VExpr}
    (hcaps : roseFlatFinalEnv09.SpineWF univs Γ
      ((roseNestedC.generation.rule 1
        roseFlatRuleConstructor1_09).type.instL m1) captures B)
    (hcapsLen : captures.length =
      (roseNestedC.generation.ruleBinders
        roseFlatRuleConstructor1_09).length)
    {recLevels : List VLevel} {level : VLevel}
    {recArgs : List VExpr} {param : VExpr}
    {fields : List VExpr} {C D : VExpr}
    (hrecLevels : recLevels.length = 2)
    (hlevel : level.WF univs)
    (hparamType : roseFinalEnv09.HasType univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (param.substConst roseRestoreInterp09) (.sort (.succ level)))
    (hfieldsSpine : roseFinalEnv09.SpineWF univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      ((VExpr.const ``List [level]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
          (param.substConst roseRestoreInterp09)))
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hrecType : roseFinalEnv09.HasType univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN
        recArgs).substConst roseRestoreInterp09)
      (.forallE C D))
    (hflat : roseFlatFinalEnv09.IsDefEq univs Γ
      (VExpr.instRev
        ((roseNestedC.generation.ruleLhsBody
          roseFlatRuleConstructor1_09).instL m1) captures)
      (.app
        ((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN recArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `nil) [level]).appN
          ([param] ++ fields))) B) :
    roseFinalEnv09.IsDefEqU univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (VExpr.instRev
        ((roseNestedC.restoreRec
          (roseNestedC.generation.ruleLhsBody
            roseFlatRuleConstructor1_09)).instL m1)
        (captures.map (VExpr.substConst roseRestoreInterp09)))
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
          recLevels).appN
            (recArgs.map (VExpr.substConst roseRestoreInterp09)))
        (((VExpr.const ``List.nil [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (param.substConst roseRestoreInterp09))).appN
          (fields.map (VExpr.substConst roseRestoreInterp09)))) := by
  have hredex := roseSubstNilRuleRuntimeRedexDefEq09 hrecLevels hlevel
    hparamType hfieldsSpine hrecType
  exact (roseNestedStagedCertificate09 readiness)
    |>.restoredRuleBodyMatchedOfFlatOfLhs
      (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry1_09)
      roseFlatFinalToFinalConstInterp09 hΓflat hΓrestored hm1 hcaps
      hcapsLen (roseRestoreInterpRule1TypeAlignment09 hm1)
      (roseRestoreInterpRule1LhsAlignment09 hm1) hflat hredex.toU

/-- End-to-end restoration transport for the selected auxiliary cons rule.
As for nil, the only semantic input left is the flattened generated-body
match produced by the ordinary rule certificate. -/
theorem roseRestoreInterpRule2BodyMatchedRuntime09
    (readiness : RoseFlatCandidateReadiness09)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (roseFlatFinalEnv09.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseFinalEnv09.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {B : VExpr}
    (hcaps : roseFlatFinalEnv09.SpineWF univs Γ
      ((roseNestedC.generation.rule 2
        roseFlatRuleConstructor2_09).type.instL m1) captures B)
    (hcapsLen : captures.length =
      (roseNestedC.generation.ruleBinders
        roseFlatRuleConstructor2_09).length)
    {recLevels : List VLevel} {level : VLevel}
    {recArgs : List VExpr} {param : VExpr}
    {fields : List VExpr} {C D : VExpr}
    (hrecLevels : recLevels.length = 2)
    (hlevel : level.WF univs)
    (hparamType : roseFinalEnv09.HasType univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (param.substConst roseRestoreInterp09) (.sort (.succ level)))
    (hfieldsSpine : roseFinalEnv09.SpineWF univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseConsRuntimePrefixType09 level param)
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hrecType : roseFinalEnv09.HasType univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN
        recArgs).substConst roseRestoreInterp09)
      (.forallE C D))
    (hflat : roseFlatFinalEnv09.IsDefEq univs Γ
      (VExpr.instRev
        ((roseNestedC.generation.ruleLhsBody
          roseFlatRuleConstructor2_09).instL m1) captures)
      (.app
        ((VExpr.const (.str roseFlatAuxName09 "rec") recLevels).appN recArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `cons) [level]).appN
          ([param] ++ fields))) B) :
    roseFinalEnv09.IsDefEqU univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (VExpr.instRev
        ((roseNestedC.restoreRec
          (roseNestedC.generation.ruleLhsBody
            roseFlatRuleConstructor2_09)).instL m1)
        (captures.map (VExpr.substConst roseRestoreInterp09)))
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1
          recLevels).appN
            (recArgs.map (VExpr.substConst roseRestoreInterp09)))
        (((VExpr.const ``List.cons [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (param.substConst roseRestoreInterp09))).appN
          (fields.map (VExpr.substConst roseRestoreInterp09)))) := by
  have hredex := roseSubstConsRuleRuntimeRedexDefEq09 hrecLevels hlevel
    hparamType hfieldsSpine hrecType
  exact (roseNestedStagedCertificate09 readiness)
    |>.restoredRuleBodyMatchedOfFlatOfLhs
      (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry2_09)
      roseFlatFinalToFinalConstInterp09 hΓflat hΓrestored hm1 hcaps
      hcapsLen (roseRestoreInterpRule2TypeAlignment09 hm1)
      (roseRestoreInterpRule2LhsAlignment09 hm1) hflat hredex.toU

/-- The selected main rule now runs from the exact local inductive-head
injectivity consequence to the final restored runtime redex.  The flattened
capture spine and generated-body match are both constructed by the staged
certificate and retained together for σ̂ transport. -/
theorem roseRestoreInterpRule0BodyMatchedRuntimeOfMajorInjectivity09
    (readiness : RoseFlatCandidateReadiness09)
    {family : VInductDecl.NormalizedFamily}
    (owner : (roseNestedStagedCertificate09 readiness).flatCertificate.RuleOwnerFacts
      roseFlatRuleConstructor0_09 family)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (roseFlatFinalEnv09.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseFinalEnv09.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = roseNestedC.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      roseNestedC.generation.ruleMajorArity roseFlatRuleConstructor0_09)
    (hNlen : aArgs.length =
      roseNestedC.generation.ruleArgArity roseFlatRuleConstructor0_09)
    (hmajorInjective :
      roseFlatFinalEnv09.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (roseNestedC.generation.sourceLevels.map (VLevel.inst m1)))
          (aArgs.take roseNestedC.elim.flat.nparams))
        (VExpr.appN (.const family.raw.name
          (roseNestedC.generation.sourceLevels.map (VLevel.inst m1)))
          (fArgs.take roseNestedC.elim.flat.nparams)) →
      List.Forall₂ (roseFlatFinalEnv09.IsDefEqU univs Γ)
        (aArgs.take roseNestedC.elim.flat.nparams)
        (fArgs.take roseNestedC.elim.flat.nparams))
    {Ae Actor : VExpr}
    (hrecspine : roseFlatFinalEnv09.SpineWF univs Γ
      ((roseNestedC.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const roseFlatRuleConstructor0_09.ctor.raw.name
        (roseNestedC.generation.sourceLevels.map (VLevel.inst m1))) aArgs]) Ae)
    (hctorspine : roseFlatFinalEnv09.SpineWF univs Γ
      (VExpr.forallN
        ((roseNestedC.generation.paramsTel ++
          roseFlatRuleConstructor0_09.ctor.fieldsR
            roseNestedC.elim.flat.uvars roseNestedC.elim.flat.nparams
            roseNestedC.generation.elimination).map (VExpr.instL m1))
        ((roseNestedC.generation.ruleCtorType
          roseFlatRuleConstructor0_09).instL m1))
      aArgs Actor) :
    roseFinalEnv09.IsDefEqU univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (VExpr.instRev
        ((roseNestedC.restoreRec
          (roseNestedC.generation.ruleLhsBody
            roseFlatRuleConstructor0_09)).instL m1)
        ((roseNestedC.generation.ruleCaptureValues
          roseFlatRuleConstructor0_09 fArgs aArgs).map
            (VExpr.substConst roseRestoreInterp09)))
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec m1).appN
          (fArgs.map (VExpr.substConst roseRestoreInterp09)))
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
          (roseNestedC.generation.sourceLevels.map (VLevel.inst m1))).appN
          (aArgs.map (VExpr.substConst roseRestoreInterp09)))) := by
  obtain ⟨B, hcaps, hflat⟩ :=
    (roseNestedStagedCertificate09 readiness)
      |>.flatRuleCaptureAndLhsBodyMatchedUnindexedOfMajorInjectivityOneParam
        (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry0_09)
        owner roseFlatMainRuleUnindexed09 roseFlatNparams hΓflat hm1 hlen1
        hMlen hNlen hmajorInjective hrecspine hctorspine
  have hcapsLen := roseNestedC.generation.ruleCaptureValues_length
    roseFlatRuleConstructor0_09 hMlen hNlen
  have hrecLevels : m1.length = 2 :=
    hlen1.trans (by native_decide)
  have hctorLevels :
      (roseNestedC.generation.sourceLevels.map (VLevel.inst m1)).length = 1 := by
    rw [List.length_map]
    native_decide
  have hrecName : roseNestedC.generation.ruleRecName
      roseFlatRuleConstructor0_09 =
      `Lean4Lean.NestedRepresentation.RoseTree.rec := by
    native_decide
  have hctorName : roseFlatRuleConstructor0_09.ctor.raw.name =
      `Lean4Lean.NestedRepresentation.RoseTree.node := by
    native_decide
  have hflat' : roseFlatFinalEnv09.IsDefEq univs Γ
      (VExpr.instRev
        ((roseNestedC.generation.ruleLhsBody
          roseFlatRuleConstructor0_09).instL m1)
        (roseNestedC.generation.ruleCaptureValues
          roseFlatRuleConstructor0_09 fArgs aArgs))
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec m1).appN
          fArgs)
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.node
          (roseNestedC.generation.sourceLevels.map (VLevel.inst m1))).appN
          aArgs)) B := by
    simpa only [roseNestedStagedCertificate09,
      ExactProducedBlockMetadataPrefixRun.nestedStagedCertificate,
      roseNestedCertificate09, hrecName, hctorName] using hflat
  exact roseRestoreInterpRule0BodyMatchedRuntime09 readiness hΓflat
    hΓrestored hm1 hcaps hcapsLen hrecLevels hctorLevels hflat'

/-- The inherited `List.nil` rule has the same direct NORM-to-runtime
boundary.  Its explicit source-level and constructor-argument decompositions
identify the unary parameter prefix needed by the final `List.nil` β step. -/
theorem roseRestoreInterpRule1BodyMatchedRuntimeOfMajorInjectivity09
    (readiness : RoseFlatCandidateReadiness09)
    {family : VInductDecl.NormalizedFamily}
    (owner : (roseNestedStagedCertificate09 readiness).flatCertificate.RuleOwnerFacts
      roseFlatRuleConstructor1_09 family)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (roseFlatFinalEnv09.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseFinalEnv09.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = roseNestedC.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      roseNestedC.generation.ruleMajorArity roseFlatRuleConstructor1_09)
    (hNlen : aArgs.length =
      roseNestedC.generation.ruleArgArity roseFlatRuleConstructor1_09)
    (hmajorInjective :
      roseFlatFinalEnv09.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (roseNestedC.generation.sourceLevels.map (VLevel.inst m1)))
          (aArgs.take roseNestedC.elim.flat.nparams))
        (VExpr.appN (.const family.raw.name
          (roseNestedC.generation.sourceLevels.map (VLevel.inst m1)))
          (fArgs.take roseNestedC.elim.flat.nparams)) →
      List.Forall₂ (roseFlatFinalEnv09.IsDefEqU univs Γ)
        (aArgs.take roseNestedC.elim.flat.nparams)
        (fArgs.take roseNestedC.elim.flat.nparams))
    {Ae Actor : VExpr}
    (hrecspine : roseFlatFinalEnv09.SpineWF univs Γ
      ((roseNestedC.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const roseFlatRuleConstructor1_09.ctor.raw.name
        (roseNestedC.generation.sourceLevels.map (VLevel.inst m1))) aArgs]) Ae)
    (hctorspine : roseFlatFinalEnv09.SpineWF univs Γ
      (VExpr.forallN
        ((roseNestedC.generation.paramsTel ++
          roseFlatRuleConstructor1_09.ctor.fieldsR
            roseNestedC.elim.flat.uvars roseNestedC.elim.flat.nparams
            roseNestedC.generation.elimination).map (VExpr.instL m1))
        ((roseNestedC.generation.ruleCtorType
          roseFlatRuleConstructor1_09).instL m1))
      aArgs Actor)
    {level : VLevel} {param : VExpr} {fields : List VExpr}
    (hsourceLevels :
      roseNestedC.generation.sourceLevels.map (VLevel.inst m1) = [level])
    (haArgs : aArgs = [param] ++ fields)
    (hlevel : level.WF univs)
    {C D : VExpr}
    (hparamType : roseFinalEnv09.HasType univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (param.substConst roseRestoreInterp09) (.sort (.succ level)))
    (hfieldsSpine : roseFinalEnv09.SpineWF univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      ((VExpr.const ``List [level]).app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
          (param.substConst roseRestoreInterp09)))
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hrecType : roseFinalEnv09.HasType univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (((VExpr.const (.str roseFlatAuxName09 "rec") m1).appN
        fArgs).substConst roseRestoreInterp09)
      (.forallE C D)) :
    roseFinalEnv09.IsDefEqU univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (VExpr.instRev
        ((roseNestedC.restoreRec
          (roseNestedC.generation.ruleLhsBody
            roseFlatRuleConstructor1_09)).instL m1)
        ((roseNestedC.generation.ruleCaptureValues
          roseFlatRuleConstructor1_09 fArgs aArgs).map
            (VExpr.substConst roseRestoreInterp09)))
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 m1).appN
          (fArgs.map (VExpr.substConst roseRestoreInterp09)))
        (((VExpr.const ``List.nil [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (param.substConst roseRestoreInterp09))).appN
          (fields.map (VExpr.substConst roseRestoreInterp09)))) := by
  obtain ⟨B, hcaps, hflat⟩ :=
    (roseNestedStagedCertificate09 readiness)
      |>.flatRuleCaptureAndLhsBodyMatchedUnindexedOfMajorInjectivityOneParam
        (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry1_09)
        owner roseFlatNilRuleUnindexed09 roseFlatNparams hΓflat hm1 hlen1
        hMlen hNlen hmajorInjective hrecspine hctorspine
  have hcapsLen := roseNestedC.generation.ruleCaptureValues_length
    roseFlatRuleConstructor1_09 hMlen hNlen
  have hrecLevels : m1.length = 2 :=
    hlen1.trans (by native_decide)
  have hrecName : roseNestedC.generation.ruleRecName
      roseFlatRuleConstructor1_09 = .str roseFlatAuxName09 "rec" := by
    native_decide
  have hctorName : roseFlatRuleConstructor1_09.ctor.raw.name =
      roseFlatAuxName09 ++ `nil := by
    native_decide
  have hflat' : roseFlatFinalEnv09.IsDefEq univs Γ
      (VExpr.instRev
        ((roseNestedC.generation.ruleLhsBody
          roseFlatRuleConstructor1_09).instL m1)
        (roseNestedC.generation.ruleCaptureValues
          roseFlatRuleConstructor1_09 fArgs aArgs))
      (.app
        ((VExpr.const (.str roseFlatAuxName09 "rec") m1).appN fArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `nil) [level]).appN
          ([param] ++ fields))) B := by
    simpa only [roseNestedStagedCertificate09,
      ExactProducedBlockMetadataPrefixRun.nestedStagedCertificate,
      roseNestedCertificate09, hrecName, hctorName, hsourceLevels, haArgs]
      using hflat
  exact roseRestoreInterpRule1BodyMatchedRuntime09 readiness hΓflat
    hΓrestored hm1 hcaps hcapsLen hrecLevels hlevel hparamType
    hfieldsSpine hrecType hflat'

/-- The inherited `List.cons` rule completes the same chain while retaining
its dependent two-field suffix.  No flattened match premise remains: only
the local inductive-head injectivity consequence and the two typed runtime
spines cross the NORM/replay boundary. -/
theorem roseRestoreInterpRule2BodyMatchedRuntimeOfMajorInjectivity09
    (readiness : RoseFlatCandidateReadiness09)
    {family : VInductDecl.NormalizedFamily}
    (owner : (roseNestedStagedCertificate09 readiness).flatCertificate.RuleOwnerFacts
      roseFlatRuleConstructor2_09 family)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (roseFlatFinalEnv09.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseFinalEnv09.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = roseNestedC.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      roseNestedC.generation.ruleMajorArity roseFlatRuleConstructor2_09)
    (hNlen : aArgs.length =
      roseNestedC.generation.ruleArgArity roseFlatRuleConstructor2_09)
    (hmajorInjective :
      roseFlatFinalEnv09.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (roseNestedC.generation.sourceLevels.map (VLevel.inst m1)))
          (aArgs.take roseNestedC.elim.flat.nparams))
        (VExpr.appN (.const family.raw.name
          (roseNestedC.generation.sourceLevels.map (VLevel.inst m1)))
          (fArgs.take roseNestedC.elim.flat.nparams)) →
      List.Forall₂ (roseFlatFinalEnv09.IsDefEqU univs Γ)
        (aArgs.take roseNestedC.elim.flat.nparams)
        (fArgs.take roseNestedC.elim.flat.nparams))
    {Ae Actor : VExpr}
    (hrecspine : roseFlatFinalEnv09.SpineWF univs Γ
      ((roseNestedC.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const roseFlatRuleConstructor2_09.ctor.raw.name
        (roseNestedC.generation.sourceLevels.map (VLevel.inst m1))) aArgs]) Ae)
    (hctorspine : roseFlatFinalEnv09.SpineWF univs Γ
      (VExpr.forallN
        ((roseNestedC.generation.paramsTel ++
          roseFlatRuleConstructor2_09.ctor.fieldsR
            roseNestedC.elim.flat.uvars roseNestedC.elim.flat.nparams
            roseNestedC.generation.elimination).map (VExpr.instL m1))
        ((roseNestedC.generation.ruleCtorType
          roseFlatRuleConstructor2_09).instL m1))
      aArgs Actor)
    {level : VLevel} {param : VExpr} {fields : List VExpr}
    (hsourceLevels :
      roseNestedC.generation.sourceLevels.map (VLevel.inst m1) = [level])
    (haArgs : aArgs = [param] ++ fields)
    (hlevel : level.WF univs)
    {C D : VExpr}
    (hparamType : roseFinalEnv09.HasType univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (param.substConst roseRestoreInterp09) (.sort (.succ level)))
    (hfieldsSpine : roseFinalEnv09.SpineWF univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (roseConsRuntimePrefixType09 level param)
      (fields.map (VExpr.substConst roseRestoreInterp09)) C)
    (hrecType : roseFinalEnv09.HasType univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (((VExpr.const (.str roseFlatAuxName09 "rec") m1).appN
        fArgs).substConst roseRestoreInterp09)
      (.forallE C D)) :
    roseFinalEnv09.IsDefEqU univs
      (Γ.map (VExpr.substConst roseRestoreInterp09))
      (VExpr.instRev
        ((roseNestedC.restoreRec
          (roseNestedC.generation.ruleLhsBody
            roseFlatRuleConstructor2_09)).instL m1)
        ((roseNestedC.generation.ruleCaptureValues
          roseFlatRuleConstructor2_09 fArgs aArgs).map
            (VExpr.substConst roseRestoreInterp09)))
      (.app
        ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 m1).appN
          (fArgs.map (VExpr.substConst roseRestoreInterp09)))
        (((VExpr.const ``List.cons [level]).app
          ((VExpr.const `Lean4Lean.NestedRepresentation.RoseTree [level]).app
            (param.substConst roseRestoreInterp09))).appN
          (fields.map (VExpr.substConst roseRestoreInterp09)))) := by
  obtain ⟨B, hcaps, hflat⟩ :=
    (roseNestedStagedCertificate09 readiness)
      |>.flatRuleCaptureAndLhsBodyMatchedUnindexedOfMajorInjectivityOneParam
        (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry2_09)
        owner roseFlatConsRuleUnindexed09 roseFlatNparams hΓflat hm1 hlen1
        hMlen hNlen hmajorInjective hrecspine hctorspine
  have hcapsLen := roseNestedC.generation.ruleCaptureValues_length
    roseFlatRuleConstructor2_09 hMlen hNlen
  have hrecLevels : m1.length = 2 :=
    hlen1.trans (by native_decide)
  have hrecName : roseNestedC.generation.ruleRecName
      roseFlatRuleConstructor2_09 = .str roseFlatAuxName09 "rec" := by
    native_decide
  have hctorName : roseFlatRuleConstructor2_09.ctor.raw.name =
      roseFlatAuxName09 ++ `cons := by
    native_decide
  have hflat' : roseFlatFinalEnv09.IsDefEq univs Γ
      (VExpr.instRev
        ((roseNestedC.generation.ruleLhsBody
          roseFlatRuleConstructor2_09).instL m1)
        (roseNestedC.generation.ruleCaptureValues
          roseFlatRuleConstructor2_09 fArgs aArgs))
      (.app
        ((VExpr.const (.str roseFlatAuxName09 "rec") m1).appN fArgs)
        ((VExpr.const (roseFlatAuxName09 ++ `cons) [level]).appN
          ([param] ++ fields))) B := by
    simpa only [roseNestedStagedCertificate09,
      ExactProducedBlockMetadataPrefixRun.nestedStagedCertificate,
      roseNestedCertificate09, hrecName, hctorName, hsourceLevels, haArgs]
      using hflat
  exact roseRestoreInterpRule2BodyMatchedRuntime09 readiness hΓflat
    hΓrestored hm1 hcaps hcapsLen hrecLevels hlevel hparamType
    hfieldsSpine hrecType hflat'

/-- The deterministic strict translation of the selected host `node` rule
RHS is the exact restored Theory RHS at flattened position zero. -/
theorem roseProducedMainSelectedRuleRhs09 :
    trExprS? roseProducedRestoredRecInfo09.levelParams []
      roseProducedMainSelectedRule09.rhs =
        some (roseNestedC.restoredRule 0
          roseFlatRuleConstructor0_09).rhs := by
  native_decide

/-- The deterministic strict translation of the selected host `nil` rule
RHS is the exact restored Theory RHS at flattened position one. -/
theorem roseProducedNilSelectedRuleRhs09 :
    trExprS? roseProducedRestoredAuxRecInfo09.levelParams []
      roseProducedNilSelectedRule09.rhs =
        some (roseNestedC.restoredRule 1
          roseFlatRuleConstructor1_09).rhs := by
  native_decide

/-- The deterministic strict translation of the selected host `cons` rule
RHS is the exact restored Theory RHS at flattened position two. -/
theorem roseProducedConsSelectedRuleRhs09 :
    trExprS? roseProducedRestoredAuxRecInfo09.levelParams []
      roseProducedConsSelectedRule09.rhs =
        some (roseNestedC.restoredRule 2
          roseFlatRuleConstructor2_09).rhs := by
  native_decide

private def roseStoredMainSelectedRule09 : RecursorRule :=
  (getRecRuleFor roseStoredRecInfoVal09
    (.const `Lean4Lean.NestedRepresentation.RoseTree.node [])).get
      (by native_decide)

private def roseStoredNilSelectedRule09 : RecursorRule :=
  (getRecRuleFor roseStoredAuxRecInfoVal09
    (.const ``List.nil [])).get (by native_decide)

private def roseStoredConsSelectedRule09 : RecursorRule :=
  (getRecRuleFor roseStoredAuxRecInfoVal09
    (.const ``List.cons [])).get (by native_decide)

private theorem roseStoredMainSelectedRuleEqv09 :
    roseStoredMainSelectedRule09.rhs ==
      roseProducedMainSelectedRule09.rhs := by
  native_decide

private theorem roseStoredNilSelectedRuleEqv09 :
    roseStoredNilSelectedRule09.rhs ==
      roseProducedNilSelectedRule09.rhs := by
  native_decide

private theorem roseStoredConsSelectedRuleEqv09 :
    roseStoredConsSelectedRule09.rhs ==
      roseProducedConsSelectedRule09.rhs := by
  native_decide

private theorem roseRestoredRule0Rhs09 :
    (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).rhs =
      roseRule0RhsL := by
  native_decide

private theorem roseRestoredRule1Rhs09 :
    (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).rhs =
      roseRule1RhsL := by
  native_decide

private theorem roseRestoredRule2Rhs09 :
    (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).rhs =
      roseRule2RhsL := by
  native_decide

/-- The selected host `node` rule carries a semantic strict translation to
the exact restored Theory RHS.  Structural replay is upgraded with the
restored rule's certificate-owned WF proof. -/
theorem roseProducedMainSelectedRuleTr09
    (readiness : RoseFlatCandidateReadiness09) :
    TrExprS roseFinalEnv09 roseProducedRestoredRecInfo09.levelParams []
      roseProducedMainSelectedRule09.rhs
      (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).rhs := by
  rw [roseRestoredRule0Rhs09]
  have shape : TrTypeExpr roseFinalEnv09
      roseStoredRecInfoVal09.levelParams []
      roseStoredMainSelectedRule09.rhs roseRule0RhsL := by
    rose_rule_hyps roseFinalEnv09
    tr_type_expr_tac
  have stored : TrExprS roseFinalEnv09
      roseStoredRecInfoVal09.levelParams []
      roseStoredMainSelectedRule09.rhs roseRule0RhsL := by
    apply shape.to_trExprS
      (roseNestedStagedCertificate09 readiness).restored.afterWF.ordered
      trivial
    have wf :=
      (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry0_09).restoredWF.2
    change roseFinalEnv09.HasType
      (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).uvars []
      (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).rhs
      (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).type at wf
    rw [roseRestoredRule0Rhs09] at wf
    have uvars :
        (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).uvars =
          roseStoredRecInfoVal09.levelParams.length := by
      native_decide
    rw [uvars] at wf
    exact ⟨_, wf⟩
  have levels : roseStoredRecInfoVal09.levelParams =
      roseProducedRestoredRecInfo09.levelParams := by
    native_decide
  rw [← levels]
  exact stored.eqv roseStoredMainSelectedRuleEqv09

/-- The selected host `List.nil` rule carries a semantic strict translation
to the exact restored Theory RHS. -/
theorem roseProducedNilSelectedRuleTr09
    (readiness : RoseFlatCandidateReadiness09) :
    TrExprS roseFinalEnv09
      roseProducedRestoredAuxRecInfo09.levelParams []
      roseProducedNilSelectedRule09.rhs
      (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).rhs := by
  rw [roseRestoredRule1Rhs09]
  have shape : TrTypeExpr roseFinalEnv09
      roseStoredAuxRecInfoVal09.levelParams []
      roseStoredNilSelectedRule09.rhs roseRule1RhsL := by
    rose_rule_hyps roseFinalEnv09
    tr_type_expr_tac
  have stored : TrExprS roseFinalEnv09
      roseStoredAuxRecInfoVal09.levelParams []
      roseStoredNilSelectedRule09.rhs roseRule1RhsL := by
    apply shape.to_trExprS
      (roseNestedStagedCertificate09 readiness).restored.afterWF.ordered
      trivial
    have wf :=
      (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry1_09).restoredWF.2
    change roseFinalEnv09.HasType
      (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).uvars []
      (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).rhs
      (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).type at wf
    rw [roseRestoredRule1Rhs09] at wf
    have uvars :
        (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).uvars =
          roseStoredAuxRecInfoVal09.levelParams.length := by
      native_decide
    rw [uvars] at wf
    exact ⟨_, wf⟩
  have levels : roseStoredAuxRecInfoVal09.levelParams =
      roseProducedRestoredAuxRecInfo09.levelParams := by
    native_decide
  rw [← levels]
  exact stored.eqv roseStoredNilSelectedRuleEqv09

/-- The selected host `List.cons` rule carries a semantic strict translation
to the exact restored Theory RHS. -/
theorem roseProducedConsSelectedRuleTr09
    (readiness : RoseFlatCandidateReadiness09) :
    TrExprS roseFinalEnv09
      roseProducedRestoredAuxRecInfo09.levelParams []
      roseProducedConsSelectedRule09.rhs
      (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).rhs := by
  rw [roseRestoredRule2Rhs09]
  have shape : TrTypeExpr roseFinalEnv09
      roseStoredAuxRecInfoVal09.levelParams []
      roseStoredConsSelectedRule09.rhs roseRule2RhsL := by
    rose_rule_hyps roseFinalEnv09
    tr_type_expr_tac
  have stored : TrExprS roseFinalEnv09
      roseStoredAuxRecInfoVal09.levelParams []
      roseStoredConsSelectedRule09.rhs roseRule2RhsL := by
    apply shape.to_trExprS
      (roseNestedStagedCertificate09 readiness).restored.afterWF.ordered
      trivial
    have wf :=
      (roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry2_09).restoredWF.2
    change roseFinalEnv09.HasType
      (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).uvars []
      (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).rhs
      (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).type at wf
    rw [roseRestoredRule2Rhs09] at wf
    have uvars :
        (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).uvars =
          roseStoredAuxRecInfoVal09.levelParams.length := by
      native_decide
    rw [uvars] at wf
    exact ⟨_, wf⟩
  have levels : roseStoredAuxRecInfoVal09.levelParams =
      roseProducedRestoredAuxRecInfo09.levelParams := by
    native_decide
  rw [← levels]
  exact stored.eqv roseStoredConsSelectedRuleEqv09

/-- One named package connects the main runtime selector to the exact
registered and well-formed restored Theory rule. -/
theorem roseProducedMainSelectedRuleBridge09
    (readiness : RoseFlatCandidateReadiness09) :
    (∀ levels args,
      getRecRuleFor roseProducedRestoredRecInfo09
        (Expr.mkAppList
          (.const `Lean4Lean.NestedRepresentation.RoseTree.node levels)
          args) = some roseProducedMainSelectedRule09) ∧
      roseProducedMainSelectedRule09.ctor =
        `Lean4Lean.NestedRepresentation.RoseTree.node ∧
      roseProducedMainSelectedRule09.nfields = 2 ∧
      trExprS? roseProducedRestoredRecInfo09.levelParams []
        roseProducedMainSelectedRule09.rhs =
          some (roseNestedC.restoredRule 0
            roseFlatRuleConstructor0_09).rhs ∧
      TrExprS roseFinalEnv09 roseProducedRestoredRecInfo09.levelParams []
        roseProducedMainSelectedRule09.rhs
        (roseNestedC.restoredRule 0 roseFlatRuleConstructor0_09).rhs ∧
      (roseNestedStagedCertificate09 readiness).RecursorRuleFacts 0
        roseFlatRuleConstructor0_09 := by
  exact ⟨roseProducedMainSelectedRuleLookup09,
    roseProducedMainSelectedRuleShape09.1,
    roseProducedMainSelectedRuleShape09.2,
    roseProducedMainSelectedRuleRhs09,
    roseProducedMainSelectedRuleTr09 readiness,
    roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry0_09⟩

/-- One named package connects the `List.nil` runtime selector to the exact
registered and well-formed restored Theory rule. -/
theorem roseProducedNilSelectedRuleBridge09
    (readiness : RoseFlatCandidateReadiness09) :
    (∀ levels args,
      getRecRuleFor roseProducedRestoredAuxRecInfo09
        (Expr.mkAppList (.const ``List.nil levels) args) =
          some roseProducedNilSelectedRule09) ∧
      roseProducedNilSelectedRule09.ctor = ``List.nil ∧
      roseProducedNilSelectedRule09.nfields = 0 ∧
      trExprS? roseProducedRestoredAuxRecInfo09.levelParams []
        roseProducedNilSelectedRule09.rhs =
          some (roseNestedC.restoredRule 1
            roseFlatRuleConstructor1_09).rhs ∧
      TrExprS roseFinalEnv09
        roseProducedRestoredAuxRecInfo09.levelParams []
        roseProducedNilSelectedRule09.rhs
        (roseNestedC.restoredRule 1 roseFlatRuleConstructor1_09).rhs ∧
      (roseNestedStagedCertificate09 readiness).RecursorRuleFacts 1
        roseFlatRuleConstructor1_09 := by
  exact ⟨roseProducedNilSelectedRuleLookup09,
    roseProducedNilSelectedRuleShape09.1,
    roseProducedNilSelectedRuleShape09.2,
    roseProducedNilSelectedRuleRhs09,
    roseProducedNilSelectedRuleTr09 readiness,
    roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry1_09⟩

/-- One named package connects the `List.cons` runtime selector to the exact
registered and well-formed restored Theory rule. -/
theorem roseProducedConsSelectedRuleBridge09
    (readiness : RoseFlatCandidateReadiness09) :
    (∀ levels args,
      getRecRuleFor roseProducedRestoredAuxRecInfo09
        (Expr.mkAppList (.const ``List.cons levels) args) =
          some roseProducedConsSelectedRule09) ∧
      roseProducedConsSelectedRule09.ctor = ``List.cons ∧
      roseProducedConsSelectedRule09.nfields = 2 ∧
      trExprS? roseProducedRestoredAuxRecInfo09.levelParams []
        roseProducedConsSelectedRule09.rhs =
          some (roseNestedC.restoredRule 2
            roseFlatRuleConstructor2_09).rhs ∧
      TrExprS roseFinalEnv09
        roseProducedRestoredAuxRecInfo09.levelParams []
        roseProducedConsSelectedRule09.rhs
        (roseNestedC.restoredRule 2 roseFlatRuleConstructor2_09).rhs ∧
      (roseNestedStagedCertificate09 readiness).RecursorRuleFacts 2
        roseFlatRuleConstructor2_09 := by
  exact ⟨roseProducedConsSelectedRuleLookup09,
    roseProducedConsSelectedRuleShape09.1,
    roseProducedConsSelectedRuleShape09.2,
    roseProducedConsSelectedRuleRhs09,
    roseProducedConsSelectedRuleTr09 readiness,
    roseNestedStagedRuleFacts09 readiness roseFlatRuleEntry2_09⟩

private theorem roseProducedMainSelectedRuleFVars09 :
    FVarsIn (fun _ => False) roseProducedMainSelectedRule09.rhs := by
  rw [fvarsIn_iff]
  constructor
  · rw [show roseProducedMainSelectedRule09.rhs.fvarsList = [] by
      native_decide]
    simp
  · apply fvarsIn_iff_hasMVar
    native_decide

private theorem roseProducedNilSelectedRuleFVars09 :
    FVarsIn (fun _ => False) roseProducedNilSelectedRule09.rhs := by
  rw [fvarsIn_iff]
  constructor
  · rw [show roseProducedNilSelectedRule09.rhs.fvarsList = [] by
      native_decide]
    simp
  · apply fvarsIn_iff_hasMVar
    native_decide

private theorem roseProducedConsSelectedRuleFVars09 :
    FVarsIn (fun _ => False) roseProducedConsSelectedRule09.rhs := by
  rw [fvarsIn_iff]
  constructor
  · rw [show roseProducedConsSelectedRule09.rhs.fvarsList = [] by
      native_decide]
    simp
  · apply fvarsIn_iff_hasMVar
    native_decide

/-- The selected main Rose rule is syntactically free-variable closed after
a checked universe instantiation.  Together with the runtime major lookup,
this supplies the free-variable half of the live reducer contract. -/
theorem roseProducedMainApplyRecursorRuleFVarsBelow09
    {Us : List Name} {levels : List Level} {levelVals : List VLevel}
    {Δ : VLCtx} {e major whnfMajor : Expr}
    (Hlevels : levels.mapM (VLevel.ofLevel Us) = some levelVals)
    (hmajorArg :
      e.getAppArgs[roseProducedRestoredRecInfo09.getMajorIdx]? = some major)
    (hmajor : FVarsBelow Δ e whnfMajor) :
    FVarsBelow Δ e
      (applyRecursorRule roseProducedRestoredRecInfo09
        roseProducedMainSelectedRule09 levels e.getAppArgs
        whnfMajor.getAppArgs) := by
  apply applyRecursorRule_fvarsBelow
  · have hbound := Array.getElem?_eq_some_iff.mp hmajorArg |>.1
    have hmeta : roseProducedRestoredRecInfo09.getFirstIndexIdx ≤
        roseProducedRestoredRecInfo09.getMajorIdx := by
      native_decide
    exact Nat.le_trans hmeta (Nat.le_of_lt hbound)
  · exact roseProducedMainSelectedRuleFVars09.instantiateLevelParamsCpp Hlevels
  · exact hmajor

/-- The inherited `List.nil` rule instantiates the same free-variable
boundary at its exact auxiliary recursor metadata. -/
theorem roseProducedNilApplyRecursorRuleFVarsBelow09
    {Us : List Name} {levels : List Level} {levelVals : List VLevel}
    {Δ : VLCtx} {e major whnfMajor : Expr}
    (Hlevels : levels.mapM (VLevel.ofLevel Us) = some levelVals)
    (hmajorArg : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (hmajor : FVarsBelow Δ e whnfMajor) :
    FVarsBelow Δ e
      (applyRecursorRule roseProducedRestoredAuxRecInfo09
        roseProducedNilSelectedRule09 levels e.getAppArgs
        whnfMajor.getAppArgs) := by
  apply applyRecursorRule_fvarsBelow
  · have hbound := Array.getElem?_eq_some_iff.mp hmajorArg |>.1
    have hmeta : roseProducedRestoredAuxRecInfo09.getFirstIndexIdx ≤
        roseProducedRestoredAuxRecInfo09.getMajorIdx := by
      native_decide
    exact Nat.le_trans hmeta (Nat.le_of_lt hbound)
  · exact roseProducedNilSelectedRuleFVars09.instantiateLevelParamsCpp Hlevels
  · exact hmajor

/-- The inherited `List.cons` rule instantiates the same free-variable
boundary at its exact auxiliary recursor metadata. -/
theorem roseProducedConsApplyRecursorRuleFVarsBelow09
    {Us : List Name} {levels : List Level} {levelVals : List VLevel}
    {Δ : VLCtx} {e major whnfMajor : Expr}
    (Hlevels : levels.mapM (VLevel.ofLevel Us) = some levelVals)
    (hmajorArg : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (hmajor : FVarsBelow Δ e whnfMajor) :
    FVarsBelow Δ e
      (applyRecursorRule roseProducedRestoredAuxRecInfo09
        roseProducedConsSelectedRule09 levels e.getAppArgs
        whnfMajor.getAppArgs) := by
  apply applyRecursorRule_fvarsBelow
  · have hbound := Array.getElem?_eq_some_iff.mp hmajorArg |>.1
    have hmeta : roseProducedRestoredAuxRecInfo09.getFirstIndexIdx ≤
        roseProducedRestoredAuxRecInfo09.getMajorIdx := by
      native_decide
    exact Nat.le_trans hmeta (Nat.le_of_lt hbound)
  · exact roseProducedConsSelectedRuleFVars09.instantiateLevelParamsCpp Hlevels
  · exact hmajor

/-- Build the live selected-branch certificate for the main recursor from
only its possible `RoseTree.node` semantic output.  Rule inversion identifies
the runtime spine, while strict input translation and RHS closure discharge
the universe-instantiation and free-variable halves automatically. -/
theorem roseProducedMainSelectedBranchWF09
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {e : Expr} {e' : VExpr} {major : Expr} {levels : List Level}
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec levels)
    (hmajor :
      e.getAppArgs[roseProducedRestoredRecInfo09.getMajorIdx]? = some major)
    (he : c.TrExprS e e')
    (hnode : ∀ {ctorLevels : List Level} {ctorArgs : List Expr}
        {majorV : VExpr},
      c.TrExprS major majorV →
      c.TrExpr
        (Expr.mkAppList
          (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
          ctorArgs) majorV →
      2 ≤ ctorArgs.length →
      levels.length = roseProducedRestoredRecInfo09.levelParams.length →
      c.TrExpr
        (applyRecursorRule roseProducedRestoredRecInfo09
          roseProducedMainSelectedRule09 levels e.getAppArgs
          (Expr.mkAppList
            (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
            ctorArgs).getAppArgs) e') :
    inductiveReduceRec.SelectedBranchWF c s e e' major levels
      roseProducedRestoredRecInfo09 := by
  obtain ⟨_, Hlevels⟩ := he.getAppFn_const_levels hfn
  constructor
  intro state major' majorV rule _hle hmajorTr hbelow hmajor'Tr
    hrule hfields hlevels
  rcases roseProducedMainSelectedRuleInv09 hrule with
    ⟨ctorLevels, ctorArgs, rfl, rfl⟩
  constructor
  · exact roseProducedMainApplyRecursorRuleFVarsBelow09
      Hlevels hmajor hbelow
  · apply hnode hmajorTr hmajor'Tr
    · rw [roseProducedMainSelectedRuleShape09.2,
        ← Array.length_toList, getAppArgs_mkAppList_const] at hfields
      exact hfields
    · exact hlevels

/-- Build the auxiliary live selected-branch certificate from exactly its
two possible inherited constructor outputs.  A successful selector is
inverted to either `List.nil` or `List.cons`; no catch-all rule premise and no
exact WHNF equation remain. -/
theorem roseProducedAuxSelectedBranchWF09
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {e : Expr} {e' : VExpr} {major : Expr} {levels : List Level}
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 levels)
    (hmajor : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (he : c.TrExprS e e')
    (hnil : ∀ {ctorLevels : List Level} {ctorArgs : List Expr}
        {majorV : VExpr},
      c.TrExprS major majorV →
      c.TrExpr (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs)
        majorV →
      levels.length =
        roseProducedRestoredAuxRecInfo09.levelParams.length →
      c.TrExpr
        (applyRecursorRule roseProducedRestoredAuxRecInfo09
          roseProducedNilSelectedRule09 levels e.getAppArgs
          (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs).getAppArgs)
        e')
    (hcons : ∀ {ctorLevels : List Level} {ctorArgs : List Expr}
        {majorV : VExpr},
      c.TrExprS major majorV →
      c.TrExpr (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs)
        majorV →
      2 ≤ ctorArgs.length →
      levels.length =
        roseProducedRestoredAuxRecInfo09.levelParams.length →
      c.TrExpr
        (applyRecursorRule roseProducedRestoredAuxRecInfo09
          roseProducedConsSelectedRule09 levels e.getAppArgs
          (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs).getAppArgs)
        e') :
    inductiveReduceRec.SelectedBranchWF c s e e' major levels
      roseProducedRestoredAuxRecInfo09 := by
  obtain ⟨_, Hlevels⟩ := he.getAppFn_const_levels hfn
  constructor
  intro state major' majorV rule _hle hmajorTr hbelow hmajor'Tr
    hrule hfields hlevels
  rcases roseProducedAuxSelectedRuleInv09 hrule with
    (⟨ctorLevels, ctorArgs, rfl, rfl⟩ | ⟨ctorLevels, ctorArgs, rfl, rfl⟩)
  · constructor
    · exact roseProducedNilApplyRecursorRuleFVarsBelow09
        Hlevels hmajor hbelow
    · exact hnil hmajorTr hmajor'Tr hlevels
  · constructor
    · exact roseProducedConsApplyRecursorRuleFVarsBelow09
        Hlevels hmajor hbelow
    · apply hcons hmajorTr hmajor'Tr
      · rw [roseProducedConsSelectedRuleShape09.2,
          ← Array.length_toList, getAppArgs_mkAppList_const] at hfields
        exact hfields
      · exact hlevels


/-- The existing Theory nested transaction, rebuilt over the records and
kernel map emitted by the actual full restoration execution. -/
theorem roseProducedAddInductNested09 :
    AddInductNested listMap07 listFinalEnv07 roseSourceV
      roseEnvironmentInductiveRestoration.env.constants roseFinalEnv09 := by
  have infosEq : roseEnvironmentInductiveRestoration.infos =
      [.inductInfo roseProducedRestoredFamilyInfo09,
       .ctorInfo roseProducedRestoredCtorInfo09,
       .recInfo roseProducedRestoredRecInfo09,
       .recInfo roseProducedRestoredAuxRecInfo09] := by
    exact roseEnvironmentInductiveRestoration.infos_eq.trans
      roseProducedRestoredInfoRun.infos_eq
  have kernelTrace := roseEnvironmentInductiveRestoration.trace
  rw [infosEq] at kernelTrace
  cases kernelTrace with
  | cons familyCheck familyTail =>
    cases familyTail with
    | cons ctorCheck ctorTail =>
      cases ctorTail with
      | cons recCheck recTail =>
        cases recTail with
        | cons auxRecCheck finalTail =>
          have finalEnvEq := finalTail.environment
          simp only [List.foldl_nil] at finalEnvEq
          rw [finalEnvEq]
          let familyStage := restoredConstantDeclarationStaging
            (kind := .induct) familyCheck trivial roseProducedFamilyTr09
              roseFamilyWF09 roseTypeEnv09_eq listTrEnv07
          let ctorStage := restoredConstantDeclarationStaging
            (kind := .ctor) ctorCheck trivial roseProducedCtorTr09
              roseNodeWF09 roseCtorEnv09_eq familyStage.trenv
          let recStage := restoredConstantDeclarationStaging
            (kind := .recursor) recCheck trivial roseProducedRecTr09
              roseRecWF09 roseRecEnv09_eq ctorStage.trenv
          let auxRecStage := restoredConstantDeclarationStaging
            (kind := .recursor) auxRecCheck trivial
              roseProducedAuxRecTr09 roseRec1WF09 roseRec1Env09_eq
              recStage.trenv
          have familyMapWF := familyStage.add.map_wf listMapWF07
          have ctorMapWF := ctorStage.add.map_wf familyMapWF
          have recMapWF := recStage.add.map_wf ctorMapWF
          exact ⟨{
            nested := roseNestedC
            nested_wf := roseNestedWF09
            typeMap :=
              (roseInputKernelEnv09.add
                (.inductInfo roseProducedRestoredFamilyInfo09)).constants
            typeEnv := roseTypeEnv09
            ctorMap :=
              ((roseInputKernelEnv09.add
                (.inductInfo roseProducedRestoredFamilyInfo09)).add
                  (.ctorInfo roseProducedRestoredCtorInfo09)).constants
            ctorEnv := roseCtorEnv09
            recEnv := roseRec1Env09
            addTypes := .cons familyStage.add .nil
            addCtors := .cons ctorStage.add .nil
            addRecs := roseRecursors_eq ▸ .cons recStage.add
              (.cons auxRecStage.add .nil)
            recK := by
              rw [roseRecursors_eq]
              intro recursor member
              rcases List.mem_cons.mp member with rfl | member
              · refine ⟨.recInfo roseProducedRestoredRecInfo09, ?_, ?_⟩
                · exact auxRecStage.add.preserve_map_lookup recMapWF
                    (recStage.add.map_lookup ctorMapWF)
                · simpa [RecursorKMatches] using roseProducedRecK09.1
              · rcases List.mem_cons.mp member with rfl | member
                · refine ⟨.recInfo roseProducedRestoredAuxRecInfo09,
                    auxRecStage.add.map_lookup recMapWF, ?_⟩
                  simpa [RecursorKMatches] using roseProducedRecK09.2
                · contradiction
            addRules := ⟨by rw [roseRules_eq]; rfl⟩ }⟩

/-- The restored host environment retains the quotient-initialization flag of
the public call's input environment. -/
theorem roseEnvironmentInductiveExecution_quotInit_eq :
    roseEnvironmentInductiveExecution.1.quotInit =
      roseInputKernelEnv09.quotInit := by
  rw [roseEnvironmentInductiveExecution_finalEnv_eq]
  exact roseEnvironmentInductiveRestoration.trace.quotInit

/-- The real outer execution and the restored Theory replay inhabit the
generic nested semantic-transaction interface. -/
theorem roseEnvironmentInductiveExecution_exactSemanticTransaction :
    roseEnvironmentInductiveExecution.2.ExactSemanticTransaction roseSourceV
      listFinalEnv07 roseFinalEnv09 := by
  apply AddInductive.EnvironmentInductiveExecution.ExactSemanticTransaction.nested
    (by rw [roseEnvironmentInductiveExecution_numNested]; decide)
  rw [roseEnvironmentInductiveExecution_finalEnv_eq]
  simpa [roseInputKernelEnv09, Kernel.Environment.ofConstants] using
    roseProducedAddInductNested09

/-- Data-bearing trace recovered from the proposition-valued operational
alignment after its mixed restoration trace has been interpreted. -/
noncomputable def roseProducedTrace09 :
    AddInductNestedTrace listMap07 listFinalEnv07 roseSourceV
      roseEnvironmentInductiveRestoration.env.constants roseFinalEnv09 :=
  Classical.choice roseProducedAddInductNested09

theorem roseProducedTrEnv09 : TrEnv' .safe
    roseEnvironmentInductiveRestoration.env.constants false roseFinalEnv09 :=
  .inductNested roseProducedAddInductNested09 listTrEnv07

/-- The concrete restoration fold leaves both synthesized recursors at their
exact host names and metadata values.  This is the environment-lookup input
needed by the real `inductiveReduceRec` control-flow theorem. -/
theorem roseProducedRecursorHostLookups09 :
    roseEnvironmentInductiveRestoration.env.find? ``RoseTree.rec =
        some (.recInfo roseProducedRestoredRecInfo09) ∧
      roseEnvironmentInductiveRestoration.env.find?
          `Lean4Lean.NestedRepresentation.RoseTree.rec_1 =
        some (.recInfo roseProducedRestoredAuxRecInfo09) := by
  have hconstants := roseEnvironmentInductiveRestoration.trace.constants
  rw [show roseEnvironmentInductiveRestoration.infos =
      [.inductInfo roseProducedRestoredFamilyInfo09,
       .ctorInfo roseProducedRestoredCtorInfo09,
       .recInfo roseProducedRestoredRecInfo09,
       .recInfo roseProducedRestoredAuxRecInfo09] from
    roseEnvironmentInductiveRestoration.infos_eq.trans
      roseProducedRestoredInfoRun.infos_eq] at hconstants
  simp only [List.foldl_cons, List.foldl_nil] at hconstants
  have hfamilyName :
      (ConstantInfo.inductInfo roseProducedRestoredFamilyInfo09).name =
        ``RoseTree := by
    simpa [roseFamilyV, roseSourceV] using roseProducedFamilyTr09.2
  have hctorName :
      (ConstantInfo.ctorInfo roseProducedRestoredCtorInfo09).name =
        ``RoseTree.node := by
    simpa [roseNodeV, roseSourceV] using roseProducedCtorTr09.2
  have hrecName :
      (ConstantInfo.recInfo roseProducedRestoredRecInfo09).name =
        ``RoseTree.rec := by
    simpa [roseRecVL] using roseProducedRecTr09.2
  have hauxName :
      (ConstantInfo.recInfo roseProducedRestoredAuxRecInfo09).name =
        `Lean4Lean.NestedRepresentation.RoseTree.rec_1 := by
    simpa [roseRec1VL] using roseProducedAuxRecTr09.2
  rw [hfamilyName, hctorName, hrecName, hauxName] at hconstants
  have hinputWF : roseInputKernelEnv09.constants.WF := by
    simpa [roseInputKernelEnv09, Kernel.Environment.ofConstants] using
      listMapWF07
  have hfamilyFresh :
      roseInputKernelEnv09.constants.find? ``RoseTree = none := by
    simpa [roseInputKernelEnv09, Kernel.Environment.ofConstants] using
      roseTypeFresh09
  have hnodeFresh :
      roseInputKernelEnv09.constants.find? ``RoseTree.node = none := by
    change listMap07.find? ``RoseTree.node = none
    rw [listMap07, listCtorMapWF07.find?_insert, listCtorMap07,
      listNilMapWF07.find?_insert, listNilMap07,
      listTypeMapWF07.find?_insert, listTypeMap07,
      SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
    simp [SMap.find?]
  have hrecFresh :
      roseInputKernelEnv09.constants.find? ``RoseTree.rec = none := by
    change listMap07.find? ``RoseTree.rec = none
    rw [listMap07, listCtorMapWF07.find?_insert, listCtorMap07,
      listNilMapWF07.find?_insert, listNilMap07,
      listTypeMapWF07.find?_insert, listTypeMap07,
      SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
    simp [SMap.find?]
  have h1WF := hinputWF.insert ``RoseTree
    (.inductInfo roseProducedRestoredFamilyInfo09) hfamilyFresh
  have hnodeFresh' :
      (roseInputKernelEnv09.constants.insert ``RoseTree
        (.inductInfo roseProducedRestoredFamilyInfo09)).find?
          ``RoseTree.node = none := by
    rw [hinputWF.find?_insert, if_neg (by decide)]
    exact hnodeFresh
  have h2WF := h1WF.insert ``RoseTree.node
    (.ctorInfo roseProducedRestoredCtorInfo09) hnodeFresh'
  have hrecFresh' :
      ((roseInputKernelEnv09.constants.insert ``RoseTree
          (.inductInfo roseProducedRestoredFamilyInfo09)).insert
        ``RoseTree.node (.ctorInfo roseProducedRestoredCtorInfo09)).find?
          ``RoseTree.rec = none := by
    rw [h1WF.find?_insert, if_neg (by decide),
      hinputWF.find?_insert, if_neg (by decide)]
    exact hrecFresh
  have h3WF := h2WF.insert ``RoseTree.rec
    (.recInfo roseProducedRestoredRecInfo09) hrecFresh'
  constructor
  · change roseEnvironmentInductiveRestoration.env.constants.find?'
      ``RoseTree.rec = _
    rw [roseProducedTrEnv09.map_wf.find?'_eq_find?, hconstants,
      h3WF.find?_insert, if_neg (by decide), h2WF.find?_insert]
    simp
  · change roseEnvironmentInductiveRestoration.env.constants.find?'
      `Lean4Lean.NestedRepresentation.RoseTree.rec_1 = _
    rw [roseProducedTrEnv09.map_wf.find?'_eq_find?, hconstants,
      h3WF.find?_insert]
    simp

/-- The same restored host environment recognizes the completed main and
inherited constructor heads used by the three selected runtime rules.  The
`List` entries are preserved exactly from the input environment. -/
theorem roseProducedConstructorHostLookups09 :
    roseEnvironmentInductiveRestoration.env.find? ``RoseTree.node =
        some (.ctorInfo roseProducedRestoredCtorInfo09) ∧
      roseEnvironmentInductiveRestoration.env.find? ``List.nil =
        some listNilInfo07 ∧
      roseEnvironmentInductiveRestoration.env.find? ``List.cons =
        some listConsInfo07 := by
  have hconstants := roseEnvironmentInductiveRestoration.trace.constants
  rw [show roseEnvironmentInductiveRestoration.infos =
      [.inductInfo roseProducedRestoredFamilyInfo09,
       .ctorInfo roseProducedRestoredCtorInfo09,
       .recInfo roseProducedRestoredRecInfo09,
       .recInfo roseProducedRestoredAuxRecInfo09] from
    roseEnvironmentInductiveRestoration.infos_eq.trans
      roseProducedRestoredInfoRun.infos_eq] at hconstants
  simp only [List.foldl_cons, List.foldl_nil] at hconstants
  have hfamilyName :
      (ConstantInfo.inductInfo roseProducedRestoredFamilyInfo09).name =
        ``RoseTree := by
    simpa [roseFamilyV, roseSourceV] using roseProducedFamilyTr09.2
  have hctorName :
      (ConstantInfo.ctorInfo roseProducedRestoredCtorInfo09).name =
        ``RoseTree.node := by
    simpa [roseNodeV, roseSourceV] using roseProducedCtorTr09.2
  have hrecName :
      (ConstantInfo.recInfo roseProducedRestoredRecInfo09).name =
        ``RoseTree.rec := by
    simpa [roseRecVL] using roseProducedRecTr09.2
  have hauxName :
      (ConstantInfo.recInfo roseProducedRestoredAuxRecInfo09).name =
        `Lean4Lean.NestedRepresentation.RoseTree.rec_1 := by
    simpa [roseRec1VL] using roseProducedAuxRecTr09.2
  rw [hfamilyName, hctorName, hrecName, hauxName] at hconstants
  have hinputWF : roseInputKernelEnv09.constants.WF := by
    simpa [roseInputKernelEnv09, Kernel.Environment.ofConstants] using
      listMapWF07
  have hfamilyFresh :
      roseInputKernelEnv09.constants.find? ``RoseTree = none := by
    simpa [roseInputKernelEnv09, Kernel.Environment.ofConstants] using
      roseTypeFresh09
  have hnodeFresh :
      roseInputKernelEnv09.constants.find? ``RoseTree.node = none := by
    change listMap07.find? ``RoseTree.node = none
    rw [listMap07, listCtorMapWF07.find?_insert, listCtorMap07,
      listNilMapWF07.find?_insert, listNilMap07,
      listTypeMapWF07.find?_insert, listTypeMap07,
      SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
    simp [SMap.find?]
  have hrecFresh :
      roseInputKernelEnv09.constants.find? ``RoseTree.rec = none := by
    change listMap07.find? ``RoseTree.rec = none
    rw [listMap07, listCtorMapWF07.find?_insert, listCtorMap07,
      listNilMapWF07.find?_insert, listNilMap07,
      listTypeMapWF07.find?_insert, listTypeMap07,
      SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
    simp [SMap.find?]
  have h1WF := hinputWF.insert ``RoseTree
    (.inductInfo roseProducedRestoredFamilyInfo09) hfamilyFresh
  have hnodeFresh' :
      (roseInputKernelEnv09.constants.insert ``RoseTree
        (.inductInfo roseProducedRestoredFamilyInfo09)).find?
          ``RoseTree.node = none := by
    rw [hinputWF.find?_insert, if_neg (by decide)]
    exact hnodeFresh
  have h2WF := h1WF.insert ``RoseTree.node
    (.ctorInfo roseProducedRestoredCtorInfo09) hnodeFresh'
  have hrecFresh' :
      ((roseInputKernelEnv09.constants.insert ``RoseTree
          (.inductInfo roseProducedRestoredFamilyInfo09)).insert
        ``RoseTree.node (.ctorInfo roseProducedRestoredCtorInfo09)).find?
          ``RoseTree.rec = none := by
    rw [h1WF.find?_insert, if_neg (by decide),
      hinputWF.find?_insert, if_neg (by decide)]
    exact hrecFresh
  have h3WF := h2WF.insert ``RoseTree.rec
    (.recInfo roseProducedRestoredRecInfo09) hrecFresh'
  constructor
  · change roseEnvironmentInductiveRestoration.env.constants.find?'
      ``RoseTree.node = _
    rw [roseProducedTrEnv09.map_wf.find?'_eq_find?, hconstants,
      h3WF.find?_insert, if_neg (by decide), h2WF.find?_insert,
      if_neg (by decide), h1WF.find?_insert]
    simp
  constructor
  · change roseEnvironmentInductiveRestoration.env.constants.find?'
      ``List.nil = _
    rw [roseProducedTrEnv09.map_wf.find?'_eq_find?, hconstants,
      h3WF.find?_insert, if_neg (by decide), h2WF.find?_insert,
      if_neg (by decide), h1WF.find?_insert, if_neg (by decide),
      hinputWF.find?_insert, if_neg (by decide)]
    change listMap07.find? ``List.nil = some listNilInfo07
    rw [listMap07, listCtorMapWF07.find?_insert, if_neg (by decide),
      listCtorMap07, listNilMapWF07.find?_insert, if_neg (by decide),
      listNilMap07, listTypeMapWF07.find?_insert]
    simp
  · change roseEnvironmentInductiveRestoration.env.constants.find?'
      ``List.cons = _
    rw [roseProducedTrEnv09.map_wf.find?'_eq_find?, hconstants,
      h3WF.find?_insert, if_neg (by decide), h2WF.find?_insert,
      if_neg (by decide), h1WF.find?_insert, if_neg (by decide),
      hinputWF.find?_insert, if_neg (by decide)]
    change listMap07.find? ``List.cons = some listConsInfo07
    rw [listMap07, listCtorMapWF07.find?_insert, if_neg (by decide),
      listCtorMap07, listNilMapWF07.find?_insert]
    simp

/-- The environment returned by the public outer execution has the same exact
recursor lookups as its restoration object. -/
theorem roseEnvironmentInductiveExecution_recursorLookups09 :
    roseEnvironmentInductiveExecution.1.find? ``RoseTree.rec =
        some (.recInfo roseProducedRestoredRecInfo09) ∧
      roseEnvironmentInductiveExecution.1.find?
          `Lean4Lean.NestedRepresentation.RoseTree.rec_1 =
        some (.recInfo roseProducedRestoredAuxRecInfo09) := by
  rw [roseEnvironmentInductiveExecution_finalEnv_eq]
  exact roseProducedRecursorHostLookups09

/-- Constructor recognition inputs transported to the environment returned
by the public outer execution. -/
theorem roseEnvironmentInductiveExecution_constructorLookups09 :
    roseEnvironmentInductiveExecution.1.find? ``RoseTree.node =
        some (.ctorInfo roseProducedRestoredCtorInfo09) ∧
      roseEnvironmentInductiveExecution.1.find? ``List.nil =
        some listNilInfo07 ∧
      roseEnvironmentInductiveExecution.1.find? ``List.cons =
        some listConsInfo07 := by
  rw [roseEnvironmentInductiveExecution_finalEnv_eq]
  exact roseProducedConstructorHostLookups09

/-- Neither generated Rose recursor targets a nonrecursive structure, so the
live reducer's structure-expansion callback is statically inactive on both
ordinary paths. -/
theorem roseEnvironmentInductiveExecution_notNonRecStructure09 :
    roseEnvironmentInductiveExecution.1.isNonRecStructure
        roseProducedRestoredRecInfo09.getMajorInduct = false ∧
      roseEnvironmentInductiveExecution.1.isNonRecStructure
        roseProducedRestoredAuxRecInfo09.getMajorInduct = false := by
  native_decide

/-- Execute the actual public-environment recursor reducer on a completed
`RoseTree.node` WHNF.  Exact restored lookups, K metadata, constructor
recognition, rule selection, and universe arity are all discharged here;
the caller supplies only the recursor/major shape, the WHNF callback result,
and the field bound visible at that live call site. -/
theorem roseEnvironmentInductiveExecution_mainReduceRec09
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (whnf inferType : Expr → m Expr) (isDefEq : Expr → Expr → m Bool)
    {e major : Expr} {levels ctorLevels : List Level}
    {ctorArgs : List Expr}
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec levels)
    (hmajor :
      e.getAppArgs[roseProducedRestoredRecInfo09.getMajorIdx]? = some major)
    (hwhnf : whnf major = pure (Expr.mkAppList
      (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
      ctorArgs))
    (hfields : 2 ≤ ctorArgs.length)
    (hlevels : levels.length = 2) :
    inductiveReduceRec roseEnvironmentInductiveExecution.1 e whnf inferType
        isDefEq =
      pure (some (applyRecursorRule roseProducedRestoredRecInfo09
        roseProducedMainSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList
          (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
          ctorArgs).getAppArgs)) := by
  apply inductiveReduceRec_eq_some_applyRecursorRule_of_constructor
  · exact hfn
  · exact roseEnvironmentInductiveExecution_recursorLookups09.1
  · exact hmajor
  · exact roseProducedRecK09.1.trans roseKTarget09
  · exact hwhnf
  · exact roseEnvironmentInductiveExecution_constructorLookups09.1
  · exact roseProducedMainSelectedRuleLookup09 ctorLevels ctorArgs
  · simpa [roseProducedMainSelectedRuleShape09.2] using hfields
  · exact hlevels.trans (by native_decide)

/-- The corresponding actual reducer execution for the inherited nullary
`List.nil` rule.  Its zero-field bound is automatic. -/
theorem roseEnvironmentInductiveExecution_nilReduceRec09
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (whnf inferType : Expr → m Expr) (isDefEq : Expr → Expr → m Bool)
    {e major : Expr} {levels ctorLevels : List Level}
    {ctorArgs : List Expr}
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 levels)
    (hmajor : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (hwhnf : whnf major = pure
      (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs))
    (hlevels : levels.length = 2) :
    inductiveReduceRec roseEnvironmentInductiveExecution.1 e whnf inferType
        isDefEq =
      pure (some (applyRecursorRule roseProducedRestoredAuxRecInfo09
        roseProducedNilSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs).getAppArgs)) := by
  apply inductiveReduceRec_eq_some_applyRecursorRule_of_constructor
  · exact hfn
  · exact roseEnvironmentInductiveExecution_recursorLookups09.2
  · exact hmajor
  · exact roseProducedRecK09.2.trans roseKTarget09
  · exact hwhnf
  · simpa [listNilInfo07] using
      roseEnvironmentInductiveExecution_constructorLookups09.2.1
  · exact roseProducedNilSelectedRuleLookup09 ctorLevels ctorArgs
  · rw [roseProducedNilSelectedRuleShape09.2]
    omega
  · exact hlevels.trans (by native_decide)

/-- The corresponding actual reducer execution for the inherited
two-field `List.cons` rule. -/
theorem roseEnvironmentInductiveExecution_consReduceRec09
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (whnf inferType : Expr → m Expr) (isDefEq : Expr → Expr → m Bool)
    {e major : Expr} {levels ctorLevels : List Level}
    {ctorArgs : List Expr}
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 levels)
    (hmajor : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (hwhnf : whnf major = pure
      (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs))
    (hfields : 2 ≤ ctorArgs.length)
    (hlevels : levels.length = 2) :
    inductiveReduceRec roseEnvironmentInductiveExecution.1 e whnf inferType
        isDefEq =
      pure (some (applyRecursorRule roseProducedRestoredAuxRecInfo09
        roseProducedConsSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs).getAppArgs)) := by
  apply inductiveReduceRec_eq_some_applyRecursorRule_of_constructor
  · exact hfn
  · exact roseEnvironmentInductiveExecution_recursorLookups09.2
  · exact hmajor
  · exact roseProducedRecK09.2.trans roseKTarget09
  · exact hwhnf
  · simpa [listConsInfo07] using
      roseEnvironmentInductiveExecution_constructorLookups09.2.2
  · exact roseProducedConsSelectedRuleLookup09 ctorLevels ctorArgs
  · simpa [roseProducedConsSelectedRuleShape09.2] using hfields
  · exact hlevels.trans (by native_decide)

/-- Lift an exact inductive-reducer equation to the actual pointwise
`reduceRecursor` run over the public Rose environment.  Quotient reduction is
disabled by the preserved input flag, and an equation to `pure` also proves
that the type-checker state is unchanged. -/
theorem roseEnvironmentInductiveExecution_reduceRecursorRun09
    (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) {e : Expr} {result : Option Expr}
    (henv : context.env = roseEnvironmentInductiveExecution.1)
    (hind : inductiveReduceRec roseEnvironmentInductiveExecution.1 e
      whnf inferType isDefEq = pure result) :
    reduceRecursor e methods context state = .ok (result, state) := by
  have hquot : context.env.quotInit = false := by
    rw [henv, roseEnvironmentInductiveExecution_quotInit_eq]
    rfl
  apply reduceRecursor_run_eq_of_quotInit_false methods context state hquot
  rw [henv]
  have run := congrArg
    (fun action => action methods context state) hind
  simpa [ReaderT.pure, StateT.pure, Except.pure, Pure.pure] using run

/-- The selected main Rose rule now executes through the actual pointwise
`reduceRecursor` wrapper.  The remaining WHNF equation is exactly the live
callback premise to be obtained from the verifier proof. -/
theorem roseEnvironmentInductiveExecution_mainReduceRecursorRun09
    (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State)
    {e major : Expr} {levels ctorLevels : List Level}
    {ctorArgs : List Expr}
    (henv : context.env = roseEnvironmentInductiveExecution.1)
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec levels)
    (hmajor :
      e.getAppArgs[roseProducedRestoredRecInfo09.getMajorIdx]? = some major)
    (hwhnf : whnf major = pure (Expr.mkAppList
      (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
      ctorArgs))
    (hfields : 2 ≤ ctorArgs.length)
    (hlevels : levels.length = 2) :
    reduceRecursor e methods context state =
      .ok (some (applyRecursorRule roseProducedRestoredRecInfo09
        roseProducedMainSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList
          (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
          ctorArgs).getAppArgs), state) := by
  apply roseEnvironmentInductiveExecution_reduceRecursorRun09
    methods context state henv
  exact roseEnvironmentInductiveExecution_mainReduceRec09
    whnf inferType isDefEq hfn hmajor hwhnf hfields hlevels

/-- The selected auxiliary nil rule through the same actual wrapper. -/
theorem roseEnvironmentInductiveExecution_nilReduceRecursorRun09
    (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State)
    {e major : Expr} {levels ctorLevels : List Level}
    {ctorArgs : List Expr}
    (henv : context.env = roseEnvironmentInductiveExecution.1)
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 levels)
    (hmajor : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (hwhnf : whnf major = pure
      (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs))
    (hlevels : levels.length = 2) :
    reduceRecursor e methods context state =
      .ok (some (applyRecursorRule roseProducedRestoredAuxRecInfo09
        roseProducedNilSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs).getAppArgs),
        state) := by
  apply roseEnvironmentInductiveExecution_reduceRecursorRun09
    methods context state henv
  exact roseEnvironmentInductiveExecution_nilReduceRec09
    whnf inferType isDefEq hfn hmajor hwhnf hlevels

/-- The selected auxiliary cons rule through the same actual wrapper. -/
theorem roseEnvironmentInductiveExecution_consReduceRecursorRun09
    (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State)
    {e major : Expr} {levels ctorLevels : List Level}
    {ctorArgs : List Expr}
    (henv : context.env = roseEnvironmentInductiveExecution.1)
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 levels)
    (hmajor : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (hwhnf : whnf major = pure
      (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs))
    (hfields : 2 ≤ ctorArgs.length)
    (hlevels : levels.length = 2) :
    reduceRecursor e methods context state =
      .ok (some (applyRecursorRule roseProducedRestoredAuxRecInfo09
        roseProducedConsSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs).getAppArgs),
        state) := by
  apply roseEnvironmentInductiveExecution_reduceRecursorRun09
    methods context state henv
  exact roseEnvironmentInductiveExecution_consReduceRec09
    whnf inferType isDefEq hfn hmajor hwhnf hfields hlevels

/-- Exhaustive live verifier contract for the main Rose recursor.  No exact
WHNF callback equation is assumed: the supported generic reducer theorem runs
the callback and closes every non-selected path.  The remaining branch
certificate is required only if the runtime major actually selects the
generated `node` rule. -/
theorem roseEnvironmentInductiveExecution_mainReduceRecursorWFExhaustive09
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {e : Expr} {e' : VExpr} {major : Expr} {levels : List Level}
    (henv : c.env = roseEnvironmentInductiveExecution.1)
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec levels)
    (hmajor :
      e.getAppArgs[roseProducedRestoredRecInfo09.getMajorIdx]? = some major)
    (he : c.TrExprS e e')
    (hbranch : inductiveReduceRec.SelectedBranchWF c s e e' major levels
      roseProducedRestoredRecInfo09) :
    TypeChecker.RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ result, oe = some result →
        c.FVarsBelow e result ∧ c.TrExpr result e' := by
  have hquot : c.env.quotInit = false := by
    rw [henv, roseEnvironmentInductiveExecution_quotInit_eq]
    rfl
  have hfind : c.env.find?
      `Lean4Lean.NestedRepresentation.RoseTree.rec =
        some (.recInfo roseProducedRestoredRecInfo09) := by
    rw [henv]
    exact roseEnvironmentInductiveExecution_recursorLookups09.1
  apply
    reduceRecursor.WF_of_quotInit_false_of_k_false_of_not_structure
      hquot he hfn hfind hmajor
  · exact roseProducedRecK09.1.trans roseKTarget09
  · rw [henv]
    exact roseEnvironmentInductiveExecution_notNonRecStructure09.1
  · exact hbranch

/-- Exhaustive live verifier contract for the auxiliary Rose recursor.  One
branch contract covers both inherited `List.nil` and `List.cons`; arbitrary
other WHNF shapes, missing rules, and arity failures are closed internally. -/
theorem roseEnvironmentInductiveExecution_auxReduceRecursorWFExhaustive09
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {e : Expr} {e' : VExpr} {major : Expr} {levels : List Level}
    (henv : c.env = roseEnvironmentInductiveExecution.1)
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 levels)
    (hmajor : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (he : c.TrExprS e e')
    (hbranch : inductiveReduceRec.SelectedBranchWF c s e e' major levels
      roseProducedRestoredAuxRecInfo09) :
    TypeChecker.RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ result, oe = some result →
        c.FVarsBelow e result ∧ c.TrExpr result e' := by
  have hquot : c.env.quotInit = false := by
    rw [henv, roseEnvironmentInductiveExecution_quotInit_eq]
    rfl
  have hfind : c.env.find?
      `Lean4Lean.NestedRepresentation.RoseTree.rec_1 =
        some (.recInfo roseProducedRestoredAuxRecInfo09) := by
    rw [henv]
    exact roseEnvironmentInductiveExecution_recursorLookups09.2
  apply
    reduceRecursor.WF_of_quotInit_false_of_k_false_of_not_structure
      hquot he hfn hfind hmajor
  · exact roseProducedRecK09.2.trans roseKTarget09
  · rw [henv]
    exact roseEnvironmentInductiveExecution_notNonRecStructure09.2
  · exact hbranch

/-- End-to-end exhaustive main-recursion contract with the generic success
certificate hidden.  Every live control-flow branch is complete except the
single `RoseTree.node` semantic output supplied here with both translations
of its major premise. -/
theorem roseEnvironmentInductiveExecution_mainReduceRecursorWFBranches09
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {e : Expr} {e' : VExpr} {major : Expr} {levels : List Level}
    (henv : c.env = roseEnvironmentInductiveExecution.1)
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec levels)
    (hmajor :
      e.getAppArgs[roseProducedRestoredRecInfo09.getMajorIdx]? = some major)
    (he : c.TrExprS e e')
    (hnode : ∀ {ctorLevels : List Level} {ctorArgs : List Expr}
        {majorV : VExpr},
      c.TrExprS major majorV →
      c.TrExpr
        (Expr.mkAppList
          (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
          ctorArgs) majorV →
      2 ≤ ctorArgs.length →
      levels.length = roseProducedRestoredRecInfo09.levelParams.length →
      c.TrExpr
        (applyRecursorRule roseProducedRestoredRecInfo09
          roseProducedMainSelectedRule09 levels e.getAppArgs
          (Expr.mkAppList
            (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
            ctorArgs).getAppArgs) e') :
    TypeChecker.RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ result, oe = some result →
        c.FVarsBelow e result ∧ c.TrExpr result e' := by
  apply roseEnvironmentInductiveExecution_mainReduceRecursorWFExhaustive09
    henv hfn hmajor he
  exact roseProducedMainSelectedBranchWF09 hfn hmajor he hnode

/-- End-to-end auxiliary counterpart: exhaustive live reduction is reduced
to exactly the inherited nil and cons semantic outputs. -/
theorem roseEnvironmentInductiveExecution_auxReduceRecursorWFBranches09
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {e : Expr} {e' : VExpr} {major : Expr} {levels : List Level}
    (henv : c.env = roseEnvironmentInductiveExecution.1)
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 levels)
    (hmajor : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (he : c.TrExprS e e')
    (hnil : ∀ {ctorLevels : List Level} {ctorArgs : List Expr}
        {majorV : VExpr},
      c.TrExprS major majorV →
      c.TrExpr (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs)
        majorV →
      levels.length =
        roseProducedRestoredAuxRecInfo09.levelParams.length →
      c.TrExpr
        (applyRecursorRule roseProducedRestoredAuxRecInfo09
          roseProducedNilSelectedRule09 levels e.getAppArgs
          (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs).getAppArgs)
        e')
    (hcons : ∀ {ctorLevels : List Level} {ctorArgs : List Expr}
        {majorV : VExpr},
      c.TrExprS major majorV →
      c.TrExpr (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs)
        majorV →
      2 ≤ ctorArgs.length →
      levels.length =
        roseProducedRestoredAuxRecInfo09.levelParams.length →
      c.TrExpr
        (applyRecursorRule roseProducedRestoredAuxRecInfo09
          roseProducedConsSelectedRule09 levels e.getAppArgs
          (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs).getAppArgs)
        e') :
    TypeChecker.RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ result, oe = some result →
        c.FVarsBelow e result ∧ c.TrExpr result e' := by
  apply roseEnvironmentInductiveExecution_auxReduceRecursorWFExhaustive09
    henv hfn hmajor he
  exact roseProducedAuxSelectedBranchWF09 hfn hmajor he hnil hcons

/-- The concrete main Rose execution now inhabits the live
`reduceRecursor.WF` contract.  Strict input translation and the exact WHNF
callback equation derive the selected major's free-variable bound; only the
semantic translation of the already-factored rule output remains explicit. -/
theorem roseEnvironmentInductiveExecution_mainReduceRecursorWF09
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {e : Expr} {e' : VExpr} {major : Expr}
    {levels ctorLevels : List Level} {ctorArgs : List Expr}
    (henv : c.env = roseEnvironmentInductiveExecution.1)
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec levels)
    (hmajor :
      e.getAppArgs[roseProducedRestoredRecInfo09.getMajorIdx]? = some major)
    (hwhnf : whnf major = pure (Expr.mkAppList
      (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
      ctorArgs))
    (hfields : 2 ≤ ctorArgs.length)
    (he : c.TrExprS e e')
    (hout : c.TrExpr
      (applyRecursorRule roseProducedRestoredRecInfo09
        roseProducedMainSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList
          (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
          ctorArgs).getAppArgs) e') :
    TypeChecker.RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  have hquot : c.env.quotInit = false := by
    rw [henv, roseEnvironmentInductiveExecution_quotInit_eq]
    rfl
  have hfind : c.env.find?
      `Lean4Lean.NestedRepresentation.RoseTree.rec =
        some (.recInfo roseProducedRestoredRecInfo09) := by
    rw [henv]
    exact roseEnvironmentInductiveExecution_recursorLookups09.1
  have hlevels : levels.length = 2 :=
    (getAppFn_const_levels_length_of_trExprS he hfn hfind).trans (by
      native_decide)
  have hind : inductiveReduceRec c.env e whnf inferType isDefEq =
      pure (some (applyRecursorRule roseProducedRestoredRecInfo09
        roseProducedMainSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList
          (.const `Lean4Lean.NestedRepresentation.RoseTree.node ctorLevels)
          ctorArgs).getAppArgs)) := by
    rw [henv]
    exact roseEnvironmentInductiveExecution_mainReduceRec09
      whnf inferType isDefEq hfn hmajor hwhnf hfields hlevels
  apply
    reduceRecursor.WF_of_quotInit_false_of_applyRecursorRule_of_whnf
      hquot hind hmajor hwhnf he
  · have hbound := Array.getElem?_eq_some_iff.mp hmajor |>.1
    have hmeta : roseProducedRestoredRecInfo09.getFirstIndexIdx ≤
        roseProducedRestoredRecInfo09.getMajorIdx := by
      native_decide
    exact Nat.le_trans hmeta (Nat.le_of_lt hbound)
  · obtain ⟨_, Hlevels⟩ := he.getAppFn_const_levels hfn
    exact roseProducedMainSelectedRuleFVars09.instantiateLevelParamsCpp Hlevels
  · exact hout

/-- The inherited `List.nil` execution inhabits the same live verifier
contract at the auxiliary Rose recursor. -/
theorem roseEnvironmentInductiveExecution_nilReduceRecursorWF09
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {e : Expr} {e' : VExpr} {major : Expr}
    {levels ctorLevels : List Level} {ctorArgs : List Expr}
    (henv : c.env = roseEnvironmentInductiveExecution.1)
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 levels)
    (hmajor : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (hwhnf : whnf major = pure
      (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs))
    (he : c.TrExprS e e')
    (hout : c.TrExpr
      (applyRecursorRule roseProducedRestoredAuxRecInfo09
        roseProducedNilSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs).getAppArgs)
      e') :
    TypeChecker.RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  have hquot : c.env.quotInit = false := by
    rw [henv, roseEnvironmentInductiveExecution_quotInit_eq]
    rfl
  have hfind : c.env.find?
      `Lean4Lean.NestedRepresentation.RoseTree.rec_1 =
        some (.recInfo roseProducedRestoredAuxRecInfo09) := by
    rw [henv]
    exact roseEnvironmentInductiveExecution_recursorLookups09.2
  have hlevels : levels.length = 2 :=
    (getAppFn_const_levels_length_of_trExprS he hfn hfind).trans (by
      native_decide)
  have hind : inductiveReduceRec c.env e whnf inferType isDefEq =
      pure (some (applyRecursorRule roseProducedRestoredAuxRecInfo09
        roseProducedNilSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList (.const ``List.nil ctorLevels) ctorArgs).getAppArgs)) := by
    rw [henv]
    exact roseEnvironmentInductiveExecution_nilReduceRec09
      whnf inferType isDefEq hfn hmajor hwhnf hlevels
  apply
    reduceRecursor.WF_of_quotInit_false_of_applyRecursorRule_of_whnf
      hquot hind hmajor hwhnf he
  · have hbound := Array.getElem?_eq_some_iff.mp hmajor |>.1
    have hmeta : roseProducedRestoredAuxRecInfo09.getFirstIndexIdx ≤
        roseProducedRestoredAuxRecInfo09.getMajorIdx := by
      native_decide
    exact Nat.le_trans hmeta (Nat.le_of_lt hbound)
  · obtain ⟨_, Hlevels⟩ := he.getAppFn_const_levels hfn
    exact roseProducedNilSelectedRuleFVars09.instantiateLevelParamsCpp Hlevels
  · exact hout

/-- The inherited `List.cons` execution inhabits the same live verifier
contract at the auxiliary Rose recursor. -/
theorem roseEnvironmentInductiveExecution_consReduceRecursorWF09
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {e : Expr} {e' : VExpr} {major : Expr}
    {levels ctorLevels : List Level} {ctorArgs : List Expr}
    (henv : c.env = roseEnvironmentInductiveExecution.1)
    (hfn : e.getAppFn =
      .const `Lean4Lean.NestedRepresentation.RoseTree.rec_1 levels)
    (hmajor : e.getAppArgs[
      roseProducedRestoredAuxRecInfo09.getMajorIdx]? = some major)
    (hwhnf : whnf major = pure
      (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs))
    (hfields : 2 ≤ ctorArgs.length)
    (he : c.TrExprS e e')
    (hout : c.TrExpr
      (applyRecursorRule roseProducedRestoredAuxRecInfo09
        roseProducedConsSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs).getAppArgs)
      e') :
    TypeChecker.RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  have hquot : c.env.quotInit = false := by
    rw [henv, roseEnvironmentInductiveExecution_quotInit_eq]
    rfl
  have hfind : c.env.find?
      `Lean4Lean.NestedRepresentation.RoseTree.rec_1 =
        some (.recInfo roseProducedRestoredAuxRecInfo09) := by
    rw [henv]
    exact roseEnvironmentInductiveExecution_recursorLookups09.2
  have hlevels : levels.length = 2 :=
    (getAppFn_const_levels_length_of_trExprS he hfn hfind).trans (by
      native_decide)
  have hind : inductiveReduceRec c.env e whnf inferType isDefEq =
      pure (some (applyRecursorRule roseProducedRestoredAuxRecInfo09
        roseProducedConsSelectedRule09 levels e.getAppArgs
        (Expr.mkAppList (.const ``List.cons ctorLevels) ctorArgs).getAppArgs)) := by
    rw [henv]
    exact roseEnvironmentInductiveExecution_consReduceRec09
      whnf inferType isDefEq hfn hmajor hwhnf hfields hlevels
  apply
    reduceRecursor.WF_of_quotInit_false_of_applyRecursorRule_of_whnf
      hquot hind hmajor hwhnf he
  · have hbound := Array.getElem?_eq_some_iff.mp hmajor |>.1
    have hmeta : roseProducedRestoredAuxRecInfo09.getFirstIndexIdx ≤
        roseProducedRestoredAuxRecInfo09.getMajorIdx := by
      native_decide
    exact Nat.le_trans hmeta (Nat.le_of_lt hbound)
  · obtain ⟨_, Hlevels⟩ := he.getAppFn_const_levels hfn
    exact roseProducedConsSelectedRuleFVars09.instantiateLevelParamsCpp Hlevels
  · exact hout

/-- End-to-end concrete vertical slice: the exact environment returned by the
public executable nested-inductive call translates to the certified Theory
nested transaction. -/
theorem roseEnvironmentInductiveExecution_trEnv : TrEnv' .safe
    roseEnvironmentInductiveExecution.1.constants false roseFinalEnv09 := by
  have pre : TrEnv' .safe roseInputKernelEnv09.constants
      roseInputKernelEnv09.quotInit listFinalEnv07 := by
    simpa [roseInputKernelEnv09, Kernel.Environment.ofConstants] using
      listTrEnv07
  have translated :=
    roseEnvironmentInductiveExecution_exactSemanticTransaction.trEnv pre
  simpa [roseEnvironmentInductiveExecution_quotInit_eq,
    roseInputKernelEnv09, Kernel.Environment.ofConstants] using translated

/-- Concrete `addDecl` vertical slice through the actual nested output and
the certified Theory transaction. -/
theorem roseAddDeclExactNestedTransaction :
    addDecl roseInputKernelEnv09 roseKernelDeclaration09 =
        .ok roseEnvironmentInductiveExecution.1 ∧
      TrEnv' .safe roseEnvironmentInductiveExecution.1.constants false
        roseFinalEnv09 :=
  ⟨roseEnvironmentInductiveExecution_addDecl,
    roseEnvironmentInductiveExecution_trEnv⟩

/-- The rose-tree nested declaration, replayed from real stored metadata
over the completed `List` environment through the nested alignment
constructor. -/
theorem roseTrEnv09 : TrEnv' .safe roseMap09 false roseFinalEnv09 :=
  .inductNested roseAddInductNested09 listTrEnv07

theorem roseFinalOrdered09 : roseFinalEnv09.Ordered :=
  roseTrEnv09.wf.ordered


/-! ## Round-trip guards

The stored-metadata surface inserted by the trace is tied to the Theory
artifact inventory, and the final map/environment pair carries the
documented closure (persistent-map contracts plus the compiler-trust axioms
introduced by the `native_decide` observations). -/

#guard roseNestedC.elim.numNested == 1
#guard roseRecV == roseRecVL && roseRec1V == roseRec1VL

/--
info: 'Lean4Lean.NestedReplayFixtures.roseMainCaptureSlices09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseEnvironmentInductiveExecutionResult_isOk._native.native_decide.ax_1_1,
 roseFlatRuleBound0_09._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1,
 roseProducedMainReducerAlignment09._native.native_decide.ax_1_1,
 roseProducedMainSelectedRule09._native.native_decide.ax_1,
 roseProducedRestoredInfoRun_isSome._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseMainCaptureSlices09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseNilCaptureSlices09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseEnvironmentInductiveExecutionResult_isOk._native.native_decide.ax_1_1,
 roseFlatRuleBound1_09._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1,
 roseProducedNilReducerAlignment09._native.native_decide.ax_1_1,
 roseProducedNilSelectedRule09._native.native_decide.ax_1,
 roseProducedRestoredInfoRun_isSome._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseNilCaptureSlices09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseConsCaptureSlices09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseEnvironmentInductiveExecutionResult_isOk._native.native_decide.ax_1_1,
 roseFlatRuleBound2_09._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1,
 roseProducedConsReducerAlignment09._native.native_decide.ax_1_1,
 roseProducedConsSelectedRule09._native.native_decide.ax_1,
 roseProducedRestoredInfoRun_isSome._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseConsCaptureSlices09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseRestoreMainRuleRedex09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseNestedC._native.native_decide.ax_1,
 roseNestedRecMap09_eq._native.native_decide.ax_1_1,
 roseRecEntries09_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseRestoreMainRuleRedex09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseRestoreNilRuleRedex09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseNestedC._native.native_decide.ax_1,
 roseNestedRecMap09_eq._native.native_decide.ax_1_1,
 roseRecEntries09_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseRestoreNilRuleRedex09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseRestoreConsRuleRedex09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseNestedC._native.native_decide.ax_1,
 roseNestedRecMap09_eq._native.native_decide.ax_1_1,
 roseRecEntries09_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseRestoreConsRuleRedex09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseSubstMainRuleRuntimeRedex09' depends on axioms: [propext,
 Quot.sound,
 roseRestoreInterp_mainCtor09._native.native_decide.ax_1_1,
 roseRestoreInterp_mainRec09._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseSubstMainRuleRuntimeRedex09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseSubstAuxRuleRuntimeRedexDefEq09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseRestoreInterp_auxRec09._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseSubstAuxRuleRuntimeRedexDefEq09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseSubstNilRuleRuntimeRedexDefEq09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert,
 roseKTarget09._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1,
 roseRecursors_eq._native.native_decide.ax_1_1,
 roseRestoreInterp_auxNil09._native.native_decide.ax_1_1,
 roseRestoreInterp_auxRec09._native.native_decide.ax_1_1,
 roseRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseSubstNilRuleRuntimeRedexDefEq09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseSubstConsRuleRuntimeRedexDefEq09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert,
 roseKTarget09._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1,
 roseRecursors_eq._native.native_decide.ax_1_1,
 roseRestoreInterp_auxCons09._native.native_decide.ax_1_1,
 roseRestoreInterp_auxRec09._native.native_decide.ax_1_1,
 roseRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseSubstConsRuleRuntimeRedexDefEq09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseFlatFinalToFinalConstInterp09' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert,
 roseFlatAddFirstRec09._native.native_decide.ax_1_1,
 roseFlatAddSecondRec09._native.native_decide.ax_1_1,
 roseFlatAuxRecType09_eq._native.native_decide.ax_1_1,
 roseFlatFirstRecEnv09._native.native_decide.ax_1,
 roseFlatGeneratedRulesLiteral09._native.native_decide.ax_1_1,
 roseFlatRecEnv09._native.native_decide.ax_1,
 roseFlatRecType09_eq._native.native_decide.ax_1_1,
 roseFlatRule0LhsReflatten09._native.native_decide.ax_1_1,
 roseFlatRule0RhsReflatten09._native.native_decide.ax_1_1,
 roseFlatRule0TypeReflatten09._native.native_decide.ax_1_1,
 roseFlatRule1LhsReflatten09._native.native_decide.ax_1_1,
 roseFlatRule1RhsReflatten09._native.native_decide.ax_1_1,
 roseFlatRule1TypeReflatten09._native.native_decide.ax_1_1,
 roseFlatRule2LhsReflatten09._native.native_decide.ax_1_1,
 roseFlatRule2RhsReflatten09._native.native_decide.ax_1_1,
 roseFlatRule2TypeReflatten09._native.native_decide.ax_1_1,
 roseFlatRuleBound0_09._native.native_decide.ax_1_1,
 roseFlatRuleBound1_09._native.native_decide.ax_1_1,
 roseFlatRuleBound2_09._native.native_decide.ax_1_1,
 roseKTarget09._native.native_decide.ax_1_1,
 roseListGeneratedRulesLiteral09._native.native_decide.ax_1_1,
 roseListRuleBound0_09._native.native_decide.ax_1_1,
 roseListRuleBound1_09._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1,
 roseNestedRecMap09_eq._native.native_decide.ax_1_1,
 roseRecEntries09_eq._native.native_decide.ax_1_1,
 roseRecursors_eq._native.native_decide.ax_1_1,
 roseRestoreInterpDefEq09._native.native_decide.ax_1_4,
 roseRestoreInterpDefEq09._native.native_decide.ax_1_5,
 roseRestoreInterpDefEq09._native.native_decide.ax_1_6,
 roseRestoreInterpKeep09._native.native_decide.ax_1_1,
 roseRestoreInterpKeep09._native.native_decide.ax_1_2,
 roseRestoreInterpKeep09._native.native_decide.ax_1_4,
 roseRestoreInterpKeep09._native.native_decide.ax_1_6,
 roseRestoreInterpKeep09._native.native_decide.ax_1_7,
 roseRestoreInterpKeep09._native.native_decide.ax_1_8,
 roseRestoreInterpKeep09._native.native_decide.ax_1_9,
 roseRestoreInterpListRule0DefEq09._native.native_decide.ax_1_1,
 roseRestoreInterpListRule0Fixed09._native.native_decide.ax_1_1,
 roseRestoreInterpListRule1DefEq09._native.native_decide.ax_1_1,
 roseRestoreInterpListRule1Fixed09._native.native_decide.ax_1_1,
 roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_1,
 roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_2,
 roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_3,
 roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_4,
 roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_5,
 roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_6,
 roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_7,
 roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_8,
 roseRestoreInterp_auxCons09._native.native_decide.ax_1_1,
 roseRestoreInterp_auxFamily09._native.native_decide.ax_1_1,
 roseRestoreInterp_auxNil09._native.native_decide.ax_1_1,
 roseRestoreInterp_auxRec09._native.native_decide.ax_1_1,
 roseRestoreInterp_mainCtor09._native.native_decide.ax_1_1,
 roseRestoreInterp_mainFamily09._native.native_decide.ax_1_1,
 roseRestoreInterp_mainRec09._native.native_decide.ax_1_1,
 roseRestoredRule0Literal09._native.native_decide.ax_1_1,
 roseRestoredRule1Literal09._native.native_decide.ax_1_1,
 roseRestoredRule2Literal09._native.native_decide.ax_1_1,
 roseRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseFlatFinalToFinalConstInterp09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseFlatRecursorShapeCandidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseEnvironmentInductiveExecutionResult_isOk._native.native_decide.ax_1_1,
 roseFlatGenerationShape._native.native_decide.ax_1_1,
 roseFlatNparams._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1]
-/
#guard_msgs in
#print axioms roseFlatRecursorShapeCandidate

/--
info: 'Lean4Lean.NestedReplayFixtures.roseFlatEliminationAlignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseEnvironmentInductiveExecutionResult_isOk._native.native_decide.ax_1_1,
 roseFlatEliminationAlignment._native.native_decide.ax_1,
 roseFlatGenerationShape._native.native_decide.ax_1_1,
 roseFlatNparams._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1]
-/
#guard_msgs in
#print axioms roseFlatEliminationAlignment

/--
info: 'Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_addInductive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseEnvironmentInductiveExecutionResult_isOk._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseEnvironmentInductiveExecution_addInductive

/--
info: 'Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_addDecl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseEnvironmentInductiveExecutionResult_isOk._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseEnvironmentInductiveExecution_addDecl

/--
info: 'Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_trEnv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert,
 roseEnvironmentInductiveExecutionResult_isOk._native.native_decide.ax_1_1,
 roseEnvironmentInductiveExecution_numNested._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1,
 roseProducedAuxRecInfo_match09._native.native_decide.ax_1_1,
 roseProducedCtorTranslationHeader09._native.native_decide.ax_1_1,
 roseProducedFamilyTranslationHeader09._native.native_decide.ax_1_1,
 roseProducedRecInfo_match09._native.native_decide.ax_1_1,
 roseProducedRecK09._native.native_decide.ax_1_1,
 roseProducedRestoredInfoRun_isSome._native.native_decide.ax_1_1,
 roseRecursors_eq._native.native_decide.ax_1_1,
 roseRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseEnvironmentInductiveExecution_trEnv

/--
info: 'Lean4Lean.NestedReplayFixtures.roseAddDeclExactNestedTransaction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert,
 roseEnvironmentInductiveExecutionResult_isOk._native.native_decide.ax_1_1,
 roseEnvironmentInductiveExecution_numNested._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1,
 roseProducedAuxRecInfo_match09._native.native_decide.ax_1_1,
 roseProducedCtorTranslationHeader09._native.native_decide.ax_1_1,
 roseProducedFamilyTranslationHeader09._native.native_decide.ax_1_1,
 roseProducedRecInfo_match09._native.native_decide.ax_1_1,
 roseProducedRecK09._native.native_decide.ax_1_1,
 roseProducedRestoredInfoRun_isSome._native.native_decide.ax_1_1,
 roseRecursors_eq._native.native_decide.ax_1_1,
 roseRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseAddDeclExactNestedTransaction

/--
info: 'Lean4Lean.NestedReplayFixtures.roseTrEnv09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert,
 roseKTarget09._native.native_decide.ax_1_1,
 roseNestedC._native.native_decide.ax_1,
 roseRecursors_eq._native.native_decide.ax_1_1,
 roseRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseTrEnv09

/--
info: 'Lean4Lean.NestedReplayFixtures.roseNestedWF09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 roseNestedC._native.native_decide.ax_1,
 roseRecursors_eq._native.native_decide.ax_1_1,
 roseRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms roseNestedWF09


/-! # The nested-indexed fixture

`NVTree` nests through the locally declared indexed `PVec`.  The base
environment stages the `PVec` family and constructors over the completed
`Nat` replay through `TrEnv'.inductStaging`; the nested trace then inserts
the stored `NVTree` metadata and drives `TrEnv'.inductNested`. -/

/-! ## Staged `PVec` base -/

def pvecInfo09 : ConstantInfo := kernelInductInfo% PVec
def pvecNilInfo09 : ConstantInfo := kernelCtorInfo% PVec.nil
def pvecConsInfo09 : ConstantInfo := kernelCtorInfo% PVec.cons

def pvecFamilyVL : VConstVal :=
  ⟨⟨0, .forallE (.sort (.succ .zero))
    (.forallE (.const `Nat []) (.sort (.succ .zero)))⟩, ``PVec⟩
def pvecNilVL : VConstVal := ⟨⟨0, nestedConstVType09A% PVec.nil⟩, ``PVec.nil⟩
def pvecConsVL : VConstVal := ⟨⟨0, nestedConstVType09A% PVec.cons⟩, ``PVec.cons⟩

def pvecTypeMap09 : ConstMap := natMap.insert ``PVec pvecInfo09
def pvecNilMap09 : ConstMap := pvecTypeMap09.insert ``PVec.nil pvecNilInfo09
def pvecCtorMap09 : ConstMap := pvecNilMap09.insert ``PVec.cons pvecConsInfo09

def pvecTypeEnv09 : VEnv :=
  (natFinalEnv.addConst pvecFamilyVL.name pvecFamilyVL.toVConstant).get!
def pvecNilEnv09 : VEnv :=
  (pvecTypeEnv09.addConst pvecNilVL.name pvecNilVL.toVConstant).get!
def pvecCtorEnv09 : VEnv :=
  (pvecNilEnv09.addConst pvecConsVL.name pvecConsVL.toVConstant).get!

theorem pvecTypeFresh09 : natMap.find? ``PVec = none := by
  rw [natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem pvecTypeMapWF09 : pvecTypeMap09.WF :=
  natMap_wf.insert _ _ pvecTypeFresh09

theorem pvecNilFresh09 : pvecTypeMap09.find? ``PVec.nil = none := by
  rw [pvecTypeMap09, natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem pvecNilMapWF09 : pvecNilMap09.WF :=
  pvecTypeMapWF09.insert _ _ pvecNilFresh09

theorem pvecConsFresh09 : pvecNilMap09.find? ``PVec.cons = none := by
  rw [pvecNilMap09, pvecTypeMapWF09.find?_insert, pvecTypeMap09,
    natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem pvecCtorMapWF09 : pvecCtorMap09.WF :=
  pvecNilMapWF09.insert _ _ pvecConsFresh09

theorem natFinalOrdered09 : natFinalEnv.Ordered :=
  (nat_trEnv' (safety := .safe)).wf.ordered

theorem pvecFamilyWF09 : pvecFamilyVL.toVConstant.WF natFinalEnv := by
  have hNat : natFinalEnv.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  exact ⟨_, by type_tac⟩

theorem pvecTypeEnv09_eq :
    natFinalEnv.addConst pvecFamilyVL.name pvecFamilyVL.toVConstant =
      some pvecTypeEnv09 := rfl

theorem pvecTypeOrdered09 : pvecTypeEnv09.Ordered :=
  .const natFinalOrdered09 pvecFamilyWF09 pvecTypeEnv09_eq

theorem pvecNilWF09 : pvecNilVL.toVConstant.WF pvecTypeEnv09 := by
  have hNat : pvecTypeEnv09.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hZero : pvecTypeEnv09.constants ``Nat.zero = some ⟨0, .const `Nat []⟩ := rfl
  have hPVec : pvecTypeEnv09.constants ``PVec = some pvecFamilyVL.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem pvecNilEnv09_eq :
    pvecTypeEnv09.addConst pvecNilVL.name pvecNilVL.toVConstant =
      some pvecNilEnv09 := rfl

theorem pvecNilOrdered09 : pvecNilEnv09.Ordered :=
  .const pvecTypeOrdered09 pvecNilWF09 pvecNilEnv09_eq

theorem pvecConsWF09 : pvecConsVL.toVConstant.WF pvecNilEnv09 := by
  have hNat : pvecNilEnv09.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hSucc : pvecNilEnv09.constants ``Nat.succ =
      some ⟨0, .forallE (.const `Nat []) (.const `Nat [])⟩ := rfl
  have hPVec : pvecNilEnv09.constants ``PVec = some pvecFamilyVL.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem pvecConsEnv09_eq :
    pvecNilEnv09.addConst pvecConsVL.name pvecConsVL.toVConstant =
      some pvecCtorEnv09 := rfl

theorem pvecCtorOrdered09 : pvecCtorEnv09.Ordered :=
  .const pvecNilOrdered09 pvecConsWF09 pvecConsEnv09_eq

theorem pvecInfoTr09 : TrConstVal .safe natFinalEnv pvecInfo09 pvecFamilyVL := by
  have hNat : natFinalEnv.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr natFinalEnv pvecInfo09.levelParams []
      pvecInfo09.type pvecFamilyVL.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS natFinalOrdered09 trivial ⟨_, by type_tac⟩

theorem pvecNilTr09 : TrConstVal .safe pvecTypeEnv09 pvecNilInfo09 pvecNilVL := by
  have hNat : pvecTypeEnv09.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hZero : pvecTypeEnv09.constants ``Nat.zero = some ⟨0, .const `Nat []⟩ := rfl
  have hPVec : pvecTypeEnv09.constants ``PVec = some pvecFamilyVL.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr pvecTypeEnv09 pvecNilInfo09.levelParams []
      pvecNilInfo09.type pvecNilVL.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS pvecTypeOrdered09 trivial ⟨_, by type_tac⟩

theorem pvecConsTr09 : TrConstVal .safe pvecNilEnv09 pvecConsInfo09 pvecConsVL := by
  have hNat : pvecNilEnv09.constants ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hSucc : pvecNilEnv09.constants ``Nat.succ =
      some ⟨0, .forallE (.const `Nat []) (.const `Nat [])⟩ := rfl
  have hPVec : pvecNilEnv09.constants ``PVec = some pvecFamilyVL.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr pvecNilEnv09 pvecConsInfo09.levelParams []
      pvecConsInfo09.type pvecConsVL.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS pvecNilOrdered09 trivial ⟨_, by type_tac⟩

/-- The staged `PVec` boundary: family and constructors present, no
recursor or rules — exactly the constants the nested `NVTree` artifacts
reference. -/
theorem pvecTrEnv09 : TrEnv' .safe pvecCtorMap09 false pvecCtorEnv09 :=
  .inductStaging (kind := .ctor)
    { info := pvecConsInfo09
      kind_eq := trivial
      tr := pvecConsTr09
      map_fresh := pvecConsFresh09
      env_add := pvecConsEnv09_eq
      map_add := rfl } pvecConsWF09 <|
  .inductStaging (kind := .ctor)
    { info := pvecNilInfo09
      kind_eq := trivial
      tr := pvecNilTr09
      map_fresh := pvecNilFresh09
      env_add := pvecNilEnv09_eq
      map_add := rfl } pvecNilWF09 <|
  .inductStaging (kind := .induct)
    { info := pvecInfo09
      kind_eq := trivial
      tr := pvecInfoTr09
      map_fresh := pvecTypeFresh09
      env_add := pvecTypeEnv09_eq
      map_add := rfl } pvecFamilyWF09 nat_trEnv'


/-! ## The translated NV source and its nested artifact -/

def nvSourceV : VInductDecl where
  uvars := 0
  nparams := 0
  types :=
    [{ name := ``NVTree
       uvars := 0
       type := nestedConstVType09A% NVTree
       ctors := [⟨⟨0, nestedConstVType09A% NVTree.node⟩, ``NVTree.node⟩] }]

def nvNestedC? : Option (NestedBlockChecked nvSourceV) :=
  nestedBlockChecked? [NestedTransformation.pvecStoredTarget] nvSourceV

#guard nvNestedC?.isSome

def nvNestedC : NestedBlockChecked nvSourceV :=
  nvNestedC?.get (by native_decide)

def nvInfo09 : ConstantInfo := kernelInductInfo% NVTree
def nvNodeInfo09 : ConstantInfo := kernelCtorInfo% NVTree.node
def nvRecInfo09 : ConstantInfo := kernelRecInfo% NVTree.rec
def nvRec1Info09 : ConstantInfo := kernelRecInfo% NVTree.rec_1

def nvFamilyV : VConstVal := nvSourceV.types[0].toVConstVal
def nvNodeV : VConstVal := nvSourceV.types[0].ctors[0]

def nvTypeMap09 : ConstMap := pvecCtorMap09.insert ``NVTree nvInfo09
def nvCtorMap09 : ConstMap := nvTypeMap09.insert ``NVTree.node nvNodeInfo09
def nvRecMap09 : ConstMap := nvCtorMap09.insert ``NVTree.rec nvRecInfo09
def nvMap09 : ConstMap :=
  nvRecMap09.insert `Lean4Lean.NestedRepresentation.NVTree.rec_1 nvRec1Info09

def nvTypeEnv09 : VEnv :=
  (pvecCtorEnv09.addConst nvFamilyV.name nvFamilyV.toVConstant).get!
def nvCtorEnv09 : VEnv :=
  (nvTypeEnv09.addConst nvNodeV.name nvNodeV.toVConstant).get!

def nvFamilyTypeL : VExpr :=
  .sort (.succ (.zero))

def nvNodeTypeL : VExpr :=
  .forallE
    (.const `Nat [])
    (.forallE
      (.app
        (.app
          (.const `Lean4Lean.NestedRepresentation.PVec [])
          (.const `Lean4Lean.NestedRepresentation.NVTree []))
        (.bvar 0))
      (.const `Lean4Lean.NestedRepresentation.NVTree []))

def nvRecTypeL : VExpr :=
  .forallE
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.forallE
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.forallE
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.forallE
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.forallE
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.app (.bvar 5) (.bvar 0)))))))

def nvRec1TypeL : VExpr :=
  .forallE
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.forallE
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.forallE
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.forallE
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.forallE
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.forallE
              (.const `Nat [])
              (.forallE
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.PVec [])
                    (.const `Lean4Lean.NestedRepresentation.NVTree []))
                  (.bvar 0))
                (.app
                  (.app (.bvar 5) (.bvar 1))
                  (.bvar 0))))))))

def nvRule0LhsL : VExpr :=
  .lam
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.lam
              (.const `Nat [])
              (.lam
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.PVec [])
                    (.const `Lean4Lean.NestedRepresentation.NVTree []))
                  (.bvar 0))
                (.app
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.const
                              `Lean4Lean.NestedRepresentation.NVTree.rec
                              [.param 0])
                            (.bvar 6))
                          (.bvar 5))
                        (.bvar 4))
                      (.bvar 3))
                    (.bvar 2))
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                      (.bvar 1))
                    (.bvar 0)))))))))

def nvRule0RhsL : VExpr :=
  .lam
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.lam
              (.const `Nat [])
              (.lam
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.PVec [])
                    (.const `Lean4Lean.NestedRepresentation.NVTree []))
                  (.bvar 0))
                (.app
                  (.app
                    (.app (.bvar 4) (.bvar 1))
                    (.bvar 0))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree.rec_1
                                  [.param 0])
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 2))
                      (.bvar 1))
                    (.bvar 0)))))))))

def nvRule0TypeL : VExpr :=
  .forallE
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.forallE
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.forallE
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.forallE
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.forallE
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.forallE
              (.const `Nat [])
              (.forallE
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.PVec [])
                    (.const `Lean4Lean.NestedRepresentation.NVTree []))
                  (.bvar 0))
                (.app
                  (.bvar 6)
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                      (.bvar 1))
                    (.bvar 0)))))))))

def nvRule1LhsL : VExpr :=
  .lam
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.app
              (.app
                (.app
                  (.app
                    (.app
                      (.app
                        (.app
                          (.const
                            `Lean4Lean.NestedRepresentation.NVTree.rec_1
                            [.param 0])
                          (.bvar 4))
                        (.bvar 3))
                      (.bvar 2))
                    (.bvar 1))
                  (.bvar 0))
                (.const `Nat.zero []))
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
                (.const `Lean4Lean.NestedRepresentation.NVTree [])))))))

def nvRule1RhsL : VExpr :=
  .lam
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.bvar 1)))))

def nvRule1TypeL : VExpr :=
  .forallE
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.forallE
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.forallE
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.forallE
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.forallE
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.app
              (.app (.bvar 3) (.const `Nat.zero []))
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
                (.const `Lean4Lean.NestedRepresentation.NVTree [])))))))

def nvRule2LhsL : VExpr :=
  .lam
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.lam
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.lam
                (.const `Nat [])
                (.lam
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree.rec_1
                                  [.param 0])
                                (.bvar 7))
                              (.bvar 6))
                            (.bvar 5))
                          (.bvar 4))
                        (.bvar 3))
                      (.app
                        (.const `Nat.succ [])
                        (.bvar 1)))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.const `Lean4Lean.NestedRepresentation.PVec.cons [])
                            (.const `Lean4Lean.NestedRepresentation.NVTree []))
                          (.bvar 2))
                        (.bvar 1))
                      (.bvar 0))))))))))

def nvRule2RhsL : VExpr :=
  .lam
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.lam
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.lam
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.lam
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.lam
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.lam
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.lam
                (.const `Nat [])
                (.lam
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.app
                    (.app
                      (.app
                        (.app
                          (.app (.bvar 3) (.bvar 2))
                          (.bvar 1))
                        (.bvar 0))
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.const
                                    `Lean4Lean.NestedRepresentation.NVTree.rec
                                    [.param 0])
                                  (.bvar 7))
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 2)))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.app
                              (.app
                                (.app
                                  (.const
                                    `Lean4Lean.NestedRepresentation.NVTree.rec_1
                                    [.param 0])
                                  (.bvar 7))
                                (.bvar 6))
                              (.bvar 5))
                            (.bvar 4))
                          (.bvar 3))
                        (.bvar 1))
                      (.bvar 0))))))))))

def nvRule2TypeL : VExpr :=
  .forallE
    (.forallE
      (.const `Lean4Lean.NestedRepresentation.NVTree [])
      (.sort (.param 0)))
    (.forallE
      (.forallE
        (.const `Nat [])
        (.forallE
          (.app
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec [])
              (.const `Lean4Lean.NestedRepresentation.NVTree []))
            (.bvar 0))
          (.sort (.param 0))))
      (.forallE
        (.forallE
          (.const `Nat [])
          (.forallE
            (.app
              (.app
                (.const `Lean4Lean.NestedRepresentation.PVec [])
                (.const `Lean4Lean.NestedRepresentation.NVTree []))
              (.bvar 0))
            (.forallE
              (.app
                (.app (.bvar 2) (.bvar 1))
                (.bvar 0))
              (.app
                (.bvar 4)
                (.app
                  (.app
                    (.const `Lean4Lean.NestedRepresentation.NVTree.node [])
                    (.bvar 2))
                  (.bvar 1))))))
        (.forallE
          (.app
            (.app (.bvar 1) (.const `Nat.zero []))
            (.app
              (.const `Lean4Lean.NestedRepresentation.PVec.nil [])
              (.const `Lean4Lean.NestedRepresentation.NVTree [])))
          (.forallE
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.forallE
                    (.app (.bvar 6) (.bvar 2))
                    (.forallE
                      (.app
                        (.app (.bvar 6) (.bvar 2))
                        (.bvar 1))
                      (.app
                        (.app
                          (.bvar 7)
                          (.app
                            (.const `Nat.succ [])
                            (.bvar 3)))
                        (.app
                          (.app
                            (.app
                              (.app
                                (.const
                                  `Lean4Lean.NestedRepresentation.PVec.cons
                                  [])
                                (.const
                                  `Lean4Lean.NestedRepresentation.NVTree
                                  []))
                              (.bvar 4))
                            (.bvar 3))
                          (.bvar 2))))))))
            (.forallE
              (.const `Lean4Lean.NestedRepresentation.NVTree [])
              (.forallE
                (.const `Nat [])
                (.forallE
                  (.app
                    (.app
                      (.const `Lean4Lean.NestedRepresentation.PVec [])
                      (.const `Lean4Lean.NestedRepresentation.NVTree []))
                    (.bvar 0))
                  (.app
                    (.app
                      (.bvar 6)
                      (.app
                        (.const `Nat.succ [])
                        (.bvar 1)))
                    (.app
                      (.app
                        (.app
                          (.app
                            (.const `Lean4Lean.NestedRepresentation.PVec.cons [])
                            (.const `Lean4Lean.NestedRepresentation.NVTree []))
                          (.bvar 2))
                        (.bvar 1))
                      (.bvar 0))))))))))

def nvRecVL : VConstVal := ⟨⟨1, nvRecTypeL⟩, ``NVTree.rec⟩
def nvRec1VL : VConstVal :=
  ⟨⟨1, nvRec1TypeL⟩, `Lean4Lean.NestedRepresentation.NVTree.rec_1⟩

def nvRulesL : List VDefEq :=
  [⟨1, nvRule0LhsL, nvRule0RhsL, nvRule0TypeL⟩,
   ⟨1, nvRule1LhsL, nvRule1RhsL, nvRule1TypeL⟩,
   ⟨1, nvRule2LhsL, nvRule2RhsL, nvRule2TypeL⟩]

theorem nvRecursors_eq : nvNestedC.recursors = [nvRecVL, nvRec1VL] := by
  native_decide

theorem nvRules_eq : nvNestedC.generatedRules = nvRulesL := by
  native_decide

def nvRecEnv09 : VEnv :=
  (nvCtorEnv09.addConst nvRecVL.name nvRecVL.toVConstant).get!
def nvRec1Env09 : VEnv :=
  (nvRecEnv09.addConst nvRec1VL.name nvRec1VL.toVConstant).get!
def nvFinalEnv09 : VEnv :=
  nvRulesL.foldl VEnv.addDefEq nvRec1Env09


/-! ## NV constant well-formedness and phase chains -/

macro "nv_hyps" e:term : tactic => `(tactic| (
  have hNat : VEnv.constants $e ``Nat = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hZero : VEnv.constants $e ``Nat.zero = some ⟨0, .const `Nat []⟩ := rfl
  have hSucc : VEnv.constants $e ``Nat.succ =
      some ⟨0, .forallE (.const `Nat []) (.const `Nat [])⟩ := rfl
  have hPVec : VEnv.constants $e ``PVec = some pvecFamilyVL.toVConstant := rfl
  have hPNil : VEnv.constants $e ``PVec.nil = some pvecNilVL.toVConstant := rfl
  have hPCons : VEnv.constants $e ``PVec.cons = some pvecConsVL.toVConstant := rfl))

theorem nvFamilyWF09 : nvFamilyV.toVConstant.WF pvecCtorEnv09 :=
  ⟨_, by type_tac⟩

theorem nvTypeEnv09_eq :
    pvecCtorEnv09.addConst nvFamilyV.name nvFamilyV.toVConstant =
      some nvTypeEnv09 := rfl

theorem nvTypeOrdered09 : nvTypeEnv09.Ordered :=
  .const pvecCtorOrdered09 nvFamilyWF09 nvTypeEnv09_eq

theorem nvNodeWF09 : nvNodeV.toVConstant.WF nvTypeEnv09 := by
  nv_hyps nvTypeEnv09
  have hNV : nvTypeEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  exact ⟨_, by type_tac⟩

theorem nvCtorEnv09_eq :
    nvTypeEnv09.addConst nvNodeV.name nvNodeV.toVConstant =
      some nvCtorEnv09 := rfl

theorem nvCtorOrdered09 : nvCtorEnv09.Ordered :=
  .const nvTypeOrdered09 nvNodeWF09 nvCtorEnv09_eq

set_option maxRecDepth 4000 in
theorem nvRecWF09 : (⟨1, nvRecTypeL⟩ : VConstant).WF nvCtorEnv09 := by
  nv_hyps nvCtorEnv09
  have hNV : nvCtorEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hNode : nvCtorEnv09.constants ``NVTree.node =
      some nvNodeV.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem nvRecEnv09_eq :
    nvCtorEnv09.addConst nvRecVL.name nvRecVL.toVConstant =
      some nvRecEnv09 := rfl

theorem nvRecOrdered09 : nvRecEnv09.Ordered :=
  .const nvCtorOrdered09 nvRecWF09 nvRecEnv09_eq

set_option maxRecDepth 4000 in
theorem nvRec1WF09 : (⟨1, nvRec1TypeL⟩ : VConstant).WF nvRecEnv09 := by
  nv_hyps nvRecEnv09
  have hNV : nvRecEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hNode : nvRecEnv09.constants ``NVTree.node =
      some nvNodeV.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem nvRec1Env09_eq :
    nvRecEnv09.addConst nvRec1VL.name nvRec1VL.toVConstant =
      some nvRec1Env09 := rfl

theorem nvRec1Ordered09 : nvRec1Env09.Ordered :=
  .const nvRecOrdered09 nvRec1WF09 nvRec1Env09_eq

section NVRuleWF

set_option maxRecDepth 8000

macro "nv_rule_hyps" e:term : tactic => `(tactic| (
  nv_hyps $e
  have hNV : VEnv.constants $e ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hNode : VEnv.constants $e ``NVTree.node = some nvNodeV.toVConstant := rfl
  have hRec : VEnv.constants $e ``NVTree.rec = some ⟨1, nvRecTypeL⟩ := rfl
  have hRec1 : VEnv.constants $e
      `Lean4Lean.NestedRepresentation.NVTree.rec_1 = some ⟨1, nvRec1TypeL⟩ := rfl))

def nvRuleEnv1 : VEnv := nvRec1Env09.addDefEq nvRulesL[0]
def nvRuleEnv2 : VEnv := nvRuleEnv1.addDefEq nvRulesL[1]

theorem nvRule0WF09 : nvRulesL[0].WF nvRec1Env09 := by
  constructor
  · nv_rule_hyps nvRec1Env09; type_tac
  · nv_rule_hyps nvRec1Env09; type_tac

theorem nvRule1WF09 : nvRulesL[1].WF nvRuleEnv1 := by
  constructor
  · nv_rule_hyps nvRuleEnv1; type_tac
  · nv_rule_hyps nvRuleEnv1; type_tac

theorem nvRule2WF09 : nvRulesL[2].WF nvRuleEnv2 := by
  constructor
  · nv_rule_hyps nvRuleEnv2; type_tac
  · nv_rule_hyps nvRuleEnv2; type_tac

end NVRuleWF


/-! ## NV semantic package -/

theorem nvTypesFold_eq :
    nvSourceV.blockTypeConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) pvecCtorEnv09 =
      some nvTypeEnv09 := rfl

theorem nvCtorsFold_eq :
    nvSourceV.blockConstructorConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) nvTypeEnv09 =
      some nvCtorEnv09 := rfl

theorem nvRecsFold_eq :
    nvNestedC.recursors.foldlM
      (fun env c => env.addConst c.name c.toVConstant) nvCtorEnv09 =
      some nvRec1Env09 := by
  rw [nvRecursors_eq]; rfl

theorem nvNestedWF09 : nvNestedC.WF pvecCtorEnv09 := by
  refine ⟨⟨nvFamilyWF09, fun env' h => ?_⟩, fun {typeEnv} h => ?_,
    fun {typeEnv ctorEnv} hT hC => ?_, fun {typeEnv ctorEnv recEnv} hT hC hR => ?_⟩
  · cases Option.some.inj (nvTypeEnv09_eq.symm.trans h)
    exact trivial
  · cases Option.some.inj (nvTypesFold_eq.symm.trans h)
    exact ⟨nvNodeWF09, fun env' h' => by
      cases Option.some.inj (nvCtorEnv09_eq.symm.trans h')
      exact trivial⟩
  · cases Option.some.inj (nvTypesFold_eq.symm.trans hT)
    cases Option.some.inj (nvCtorsFold_eq.symm.trans hC)
    rw [nvRecursors_eq]
    exact ⟨nvRecWF09, fun env' h' => by
      cases Option.some.inj (nvRecEnv09_eq.symm.trans h')
      exact ⟨nvRec1WF09, fun env'' h'' => by
        cases Option.some.inj (nvRec1Env09_eq.symm.trans h'')
        exact trivial⟩⟩
  · cases Option.some.inj (nvTypesFold_eq.symm.trans hT)
    cases Option.some.inj (nvCtorsFold_eq.symm.trans hC)
    cases Option.some.inj (nvRecsFold_eq.symm.trans hR)
    rw [nvRules_eq]
    exact ⟨nvRule0WF09, nvRule1WF09, nvRule2WF09, trivial⟩

/-! ## NV freshness and stored-metadata translations -/

theorem nvTypeFresh09 : pvecCtorMap09.find? ``NVTree = none := by
  rw [pvecCtorMap09, pvecNilMapWF09.find?_insert, pvecNilMap09,
    pvecTypeMapWF09.find?_insert, pvecTypeMap09,
    natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem nvTypeMapWF09 : nvTypeMap09.WF :=
  pvecCtorMapWF09.insert _ _ nvTypeFresh09

theorem nvNodeFresh09 : nvTypeMap09.find? ``NVTree.node = none := by
  rw [nvTypeMap09, pvecCtorMapWF09.find?_insert, pvecCtorMap09,
    pvecNilMapWF09.find?_insert, pvecNilMap09,
    pvecTypeMapWF09.find?_insert, pvecTypeMap09,
    natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem nvCtorMapWF09 : nvCtorMap09.WF :=
  nvTypeMapWF09.insert _ _ nvNodeFresh09

theorem nvRecFresh09 : nvCtorMap09.find? ``NVTree.rec = none := by
  rw [nvCtorMap09, nvTypeMapWF09.find?_insert, nvTypeMap09,
    pvecCtorMapWF09.find?_insert, pvecCtorMap09,
    pvecNilMapWF09.find?_insert, pvecNilMap09,
    pvecTypeMapWF09.find?_insert, pvecTypeMap09,
    natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem nvRecMapWF09 : nvRecMap09.WF :=
  nvCtorMapWF09.insert _ _ nvRecFresh09

theorem nvRec1Fresh09 :
    nvRecMap09.find? `Lean4Lean.NestedRepresentation.NVTree.rec_1 = none := by
  rw [nvRecMap09, nvCtorMapWF09.find?_insert, nvCtorMap09,
    nvTypeMapWF09.find?_insert, nvTypeMap09,
    pvecCtorMapWF09.find?_insert, pvecCtorMap09,
    pvecNilMapWF09.find?_insert, pvecNilMap09,
    pvecTypeMapWF09.find?_insert, pvecTypeMap09,
    natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem nvInfoTr09 : TrConstVal .safe pvecCtorEnv09 nvInfo09 nvFamilyV := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr pvecCtorEnv09 nvInfo09.levelParams []
      nvInfo09.type nvFamilyV.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS pvecCtorOrdered09 trivial ⟨_, by type_tac⟩

theorem nvNodeTr09 : TrConstVal .safe nvTypeEnv09 nvNodeInfo09 nvNodeV := by
  nv_hyps nvTypeEnv09
  have hNV : nvTypeEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr nvTypeEnv09 nvNodeInfo09.levelParams []
      nvNodeInfo09.type nvNodeV.toVConstant.type := by
    tr_type_expr_tac
  exact shape.to_trExprS nvTypeOrdered09 trivial ⟨_, by type_tac⟩

theorem nvRecTr09 : TrConstVal .safe nvCtorEnv09 nvRecInfo09 nvRecVL := by
  nv_hyps nvCtorEnv09
  have hNV : nvCtorEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hNode : nvCtorEnv09.constants ``NVTree.node = some nvNodeV.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr nvCtorEnv09 nvRecInfo09.levelParams []
      nvRecInfo09.type nvRecVL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := nvRecWF09
  exact shape.to_trExprS nvCtorOrdered09 trivial ⟨_, hty⟩

theorem nvRec1Tr09 : TrConstVal .safe nvRecEnv09 nvRec1Info09 nvRec1VL := by
  nv_hyps nvRecEnv09
  have hNV : nvRecEnv09.constants ``NVTree = some ⟨0, .sort (.succ .zero)⟩ := rfl
  have hNode : nvRecEnv09.constants ``NVTree.node = some nvNodeV.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr nvRecEnv09 nvRec1Info09.levelParams []
      nvRec1Info09.type nvRec1VL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := nvRec1WF09
  exact shape.to_trExprS nvRecOrdered09 trivial ⟨_, hty⟩

/-! ## NV recursor K metadata, trace, and `TrEnv'` drive -/

theorem nvKTarget09 : nvNestedC.generation.kTarget = false := by
  native_decide

theorem nvRecLookup09 : nvMap09.find? ``NVTree.rec = some nvRecInfo09 := by
  rw [nvMap09, nvRecMapWF09.find?_insert]
  simp [nvRecMap09, nvCtorMapWF09.find?_insert]

theorem nvRec1Lookup09 :
    nvMap09.find? `Lean4Lean.NestedRepresentation.NVTree.rec_1 =
      some nvRec1Info09 := by
  rw [nvMap09, nvRecMapWF09.find?_insert]
  simp

theorem nvRecK09 :
    RecursorMapKMatches nvMap09 nvNestedC.recursors
      nvNestedC.generation.kTarget := by
  rw [nvRecursors_eq, nvKTarget09]
  intro recursor hmem
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨nvRecInfo09, nvRecLookup09, by decide⟩
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨nvRec1Info09, nvRec1Lookup09, by decide⟩
  · cases hmem

def nvTrace09 :
    AddInductNestedTrace pvecCtorMap09 pvecCtorEnv09 nvSourceV
      nvMap09 nvFinalEnv09 where
  nested := nvNestedC
  nested_wf := nvNestedWF09
  typeMap := nvTypeMap09
  typeEnv := nvTypeEnv09
  ctorMap := nvCtorMap09
  ctorEnv := nvCtorEnv09
  recEnv := nvRec1Env09
  addTypes := .cons
    { info := nvInfo09
      kind_eq := trivial
      tr := nvInfoTr09
      map_fresh := nvTypeFresh09
      env_add := nvTypeEnv09_eq
      map_add := rfl } .nil
  addCtors := .cons
    { info := nvNodeInfo09
      kind_eq := trivial
      tr := nvNodeTr09
      map_fresh := nvNodeFresh09
      env_add := nvCtorEnv09_eq
      map_add := rfl } .nil
  addRecs := nvRecursors_eq ▸ .cons
    { info := nvRecInfo09
      kind_eq := trivial
      tr := nvRecTr09
      map_fresh := nvRecFresh09
      env_add := nvRecEnv09_eq
      map_add := rfl } (.cons
    { info := nvRec1Info09
      kind_eq := trivial
      tr := nvRec1Tr09
      map_fresh := nvRec1Fresh09
      env_add := nvRec1Env09_eq
      map_add := rfl } .nil)
  recK := nvRecK09
  addRules := ⟨by rw [nvRules_eq]; rfl⟩

theorem nvAddInductNested09 :
    AddInductNested pvecCtorMap09 pvecCtorEnv09 nvSourceV
      nvMap09 nvFinalEnv09 :=
  ⟨nvTrace09⟩

/-- The nested-indexed declaration, replayed from real stored metadata over
the staged `PVec` boundary through the nested alignment constructor. -/
theorem nvTrEnv09 : TrEnv' .safe nvMap09 false nvFinalEnv09 :=
  .inductNested nvAddInductNested09 pvecTrEnv09

theorem nvFinalOrdered09 : nvFinalEnv09.Ordered :=
  nvTrEnv09.wf.ordered

#guard nvNestedC.elim.numNested == 1


/--
info: 'Lean4Lean.NestedReplayFixtures.nvTrEnv09' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert,
 nvKTarget09._native.native_decide.ax_1_1,
 nvNestedC._native.native_decide.ax_1,
 nvRecursors_eq._native.native_decide.ax_1_1,
 nvRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms nvTrEnv09

end Lean4Lean.NestedReplayFixtures
