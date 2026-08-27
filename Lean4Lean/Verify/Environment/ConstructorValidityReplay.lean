import Lean4Lean.Verify.Environment.ConstructorValidityMatrix
import Lean4Lean.Verify.Environment.CandidateIdentityReplay

/-!
# L4L-05 accepted constructor-validity replay

The two accepted differential fixtures retain the exact executable
normalization candidate, close it through the staged D1--D4 owner, and route
the resulting generation certificate through both the Theory transaction and
the actual-kernel-metadata environment replay.
-/

-- These executable replay proofs intentionally retain explicit reduction
-- inventories; narrowed trust contracts can make individual entries redundant.
set_option linter.unusedSimpArgs false

namespace Lean4Lean.InductiveReplayFixtures
open Lean Meta Elab Term
open Lean4Lean.InductiveFixtures

local instance instInhabitedVEnvValidityReplay : Inhabited VEnv := ⟨.empty⟩

private theorem exceptUnit_eq_ok_of_isOk {error : Type}
    (result : Except error Unit) (h : result.isOk = true) :
    result = .ok () := by
  cases result with
  | error error =>
      change false = true at h
      contradiction
  | ok result =>
      cases result
      rfl

private theorem normalization_eq_of_view_eq
    {source : VInductDecl} {left right : VInductDecl.Normalization source}
    (view_eq : left.view = right.view) : left = right := by
  cases left with
  | mk leftView leftShape =>
      cases right with
      | mk rightView rightShape =>
          simp only [VInductDecl.Normalization.mk.injEq] at *
          exact view_eq

private theorem stagedPreFamily_transport_raw
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {kernelSource : InductiveType}
    {source : VInductDecl}
    {left right : AddInductive.NormalizationCandidate [kernelSource]}
    (candidate_eq : left = right)
    (input : VInductDecl.StagedNormalizationCandidatePreFamilyInput
      familyContext constructorContext env Us left source) :
    ((candidate_eq ▸ input :
      VInductDecl.StagedNormalizationCandidatePreFamilyInput
        familyContext constructorContext env Us right source)
      |>.postFamilyInput.universeInput.staged.raw) =
      input.postFamilyInput.universeInput.staged.raw := by
  cases candidate_eq
  rfl

def l4l05EmptyVEnvs : VEnvs where
  venv _ := VEnv.empty

theorem l4l05EmptyHasPrimitives : VEnv.HasPrimitives VEnv.empty := by
  apply VEnv.HasPrimitives.of_avoids
  intro name membership
  rfl

theorem cvmEmptySafePrimitives :
    constructorValidityMatrixContext.env.find? name = some info →
      Kernel.Environment.primitives.contains name →
      info.safety = .safe ∧ info.levelParams = [] := by
  intro hfind hprimitive
  change ({} : ConstMap).find?' name = some info at hfind
  rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at hfind
  simp [SMap.find?] at hfind

theorem cvmEmptyVEnvsWF :
    l4l05EmptyVEnvs.WF constructorValidityMatrixContext.env where
  tr := by
    intro safety
    change TrEnv' safety ({} : ConstMap) false VEnv.empty
    exact .empty
  hasPrimitives := l4l05EmptyHasPrimitives
  safePrimitives := cvmEmptySafePrimitives
  mono := fun _ => .rfl
  projectionReady := ProjectionResolutionReady.of_no_ctorInfo <| by
    intro name info h
    change ({} : ConstMap).find?' name = some (.ctorInfo info) at h
    rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at h
    simp [SMap.find?] at h
  structureEtaReady := StructureEtaReady.of_no_ctorInfo <| by
    intro name info h
    change ({} : ConstMap).find?' name = some (.ctorInfo info) at h
    rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at h
    simp [SMap.find?] at h

theorem prbEmptySafePrimitives :
    propRecursiveBoundaryContext.env.find? name = some info →
      Kernel.Environment.primitives.contains name →
      info.safety = .safe ∧ info.levelParams = [] := by
  intro hfind hprimitive
  change ({} : ConstMap).find?' name = some info at hfind
  rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at hfind
  simp [SMap.find?] at hfind

theorem prbEmptyVEnvsWF :
    l4l05EmptyVEnvs.WF propRecursiveBoundaryContext.env where
  tr := by
    intro safety
    change TrEnv' safety ({} : ConstMap) false VEnv.empty
    exact .empty
  hasPrimitives := l4l05EmptyHasPrimitives
  safePrimitives := prbEmptySafePrimitives
  mono := fun _ => .rfl
  projectionReady := ProjectionResolutionReady.of_no_ctorInfo <| by
    intro name info h
    change ({} : ConstMap).find?' name = some (.ctorInfo info) at h
    rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at h
    simp [SMap.find?] at h
  structureEtaReady := StructureEtaReady.of_no_ctorInfo <| by
    intro name info h
    change ({} : ConstMap).find?' name = some (.ctorInfo info) at h
    rw [SMap.WF.find?'_eq_find? SMap.WF.empty] at h
    simp [SMap.find?] at h

def cvmExecutionResult :=
  AddInductive.buildNormalizationCandidateExecution 2
    [constructorValidityMatrixKernelType] 0 false
    constructorValidityMatrixContext

theorem cvmExecutionResult_isOk : cvmExecutionResult.isOk = true := by
  native_decide

def cvmProducedExecution :
    { execution // cvmExecutionResult = .ok execution } :=
  match h : cvmExecutionResult with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := cvmExecutionResult_isOk
      rw [h] at hOk
      contradiction

def cvmExecution := cvmProducedExecution.val

def cvmCandidate := cvmExecution.candidate

open TypeChecker in
def cvmFamilyIdentityShape :
    CandidateExprIdentityReplay.Shaped constructorValidityMatrixContext
      constructorValidityMatrixKernelType.type 2
      (.sort (.succ (.param `u))) := by
  let aName := constructorValidityMatrixKernelType.type.bindingBody!
    |>.bindingDomain!.bindingName!
  change CandidateExprIdentityReplay.Shaped constructorValidityMatrixContext
    (.forallE `α (.sort (.succ (.param `u)))
      (.forallE `P
        (.forallE aName (.bvar 0) (.sort .zero) .default)
        (.sort (.succ (.param `u))) .default) .default)
    2 (.sort (.succ (.param `u)))
  let alphaContext := constructorValidityMatrixContext.pushLocalDecl
    `α .default (.sort (.succ (.param `u)))
  let alphaAnnotations := AddInductive.builtCandidateTypeAnnotations
    (Expr.sort (.succ (.param `u)))
  refine .forallE (expectedSpineLength := 1)
    constructorValidityMatrixContext `α
    (.sort (.succ (.param `u)))
    (.forallE `P
      (.forallE aName (.bvar 0) (.sort .zero) .default)
      (.sort (.succ (.param `u))) .default) .default
    (by rfl) alphaAnnotations
    (AddInductive.buildCandidateTypeAnnotations_built _) (by
      simpa [AddInductive.CandidateTypeAnnotationTrace.build] using
        (AddInductive.CandidateTypeAnnotationTrace.build_consumed
          (.sort (.succ (.param `u)))).symm)
    (.terminal _ _ (by rfl) rfl) ?_
  let pDomain := Expr.forallE aName
    constructorValidityMatrixContext.freshExpr
    (.sort .zero) .default
  have alphaFVarWhnf : AddInductive.CandidateWhnfStep.Valid
      ⟨alphaContext, constructorValidityMatrixContext.freshExpr,
        constructorValidityMatrixContext.freshExpr⟩ := by
    simpa [alphaContext] using
      TypeChecker.candidateWhnfPushedFVar_refl
        constructorValidityMatrixContext `α
        (.sort (.succ (.param `u))) .default 9999 (by rfl)
        (by
          change LocalContext.WF ⟨.empty, .empty, .empty⟩
          exact LocalContext.WF.nil)
        (by
          change (⟨.empty, .empty, .empty⟩ : LocalContext).find?
            constructorValidityMatrixContext.freshFVarId = none
          exact TypeChecker.emptyLocalContextFindNone _)
  have pDomainShape : CandidateExprIdentityReplay.Shaped alphaContext
      pDomain 1 (.sort .zero) := by
    let aAnnotations := AddInductive.builtCandidateTypeAnnotations
      constructorValidityMatrixContext.freshExpr
    refine .forallE (expectedSpineLength := 0) alphaContext aName
      constructorValidityMatrixContext.freshExpr (.sort .zero) .default
      (by rfl) aAnnotations
      (AddInductive.buildCandidateTypeAnnotations_built _) (by
        simpa [AddInductive.Context.freshExpr,
            AddInductive.CandidateTypeAnnotationTrace.build] using
          (AddInductive.CandidateTypeAnnotationTrace.build_consumed
            constructorValidityMatrixContext.freshExpr).symm)
      (.terminal _ _ alphaFVarWhnf rfl) ?_
    have terminal : CandidateExprIdentityReplay.Shaped
        (alphaContext.pushLocalDecl aName .default
          constructorValidityMatrixContext.freshExpr)
        (.sort .zero) 0 (.sort .zero) :=
      .terminal _ _ (by rfl) rfl
    simpa [aAnnotations, AddInductive.builtCandidateTypeAnnotations,
      AddInductive.CandidateTypeAnnotationTrace.build,
      AddInductive.Context.freshExpr,
      Expr.instantiate1_eq, Expr.instantiate1'] using terminal
  have alphaBody : CandidateExprIdentityReplay.Shaped alphaContext
      (.forallE `P pDomain (.sort (.succ (.param `u))) .default)
      1 (.sort (.succ (.param `u))) := by
    let pAnnotations := AddInductive.builtCandidateTypeAnnotations pDomain
    refine .forallE (expectedSpineLength := 0) alphaContext `P pDomain
      (.sort (.succ (.param `u))) .default (by rfl) pAnnotations
      (AddInductive.buildCandidateTypeAnnotations_built _) (by
        simpa [pDomain, AddInductive.Context.freshExpr,
            AddInductive.CandidateTypeAnnotationTrace.build] using
          (AddInductive.CandidateTypeAnnotationTrace.build_consumed
            pDomain).symm)
      pDomainShape.replay ?_
    have terminal : CandidateExprIdentityReplay.Shaped
        (alphaContext.pushLocalDecl `P .default pDomain)
        (.sort (.succ (.param `u))) 0
        (.sort (.succ (.param `u))) :=
      .terminal _ _ (by rfl) rfl
    simpa [pAnnotations, AddInductive.builtCandidateTypeAnnotations,
      AddInductive.CandidateTypeAnnotationTrace.build,
      Expr.instantiate1_eq, Expr.instantiate1'] using terminal
  simpa [alphaContext, alphaAnnotations, pDomain,
    AddInductive.builtCandidateTypeAnnotations,
    AddInductive.CandidateTypeAnnotationTrace.build,
    Expr.instantiate1_eq, Expr.instantiate1'] using alphaBody

def cvmFamilyIdentityReplay :
    TypeChecker.CandidateExprIdentityReplay
      constructorValidityMatrixContext
      constructorValidityMatrixKernelType.type :=
  cvmFamilyIdentityShape.replay

theorem cvmFamilyCandidateBuild :
    AddInductive.buildCandidateExpr constructorValidityMatrixKernelType.type
        constructorValidityMatrixContext =
      .ok cvmCandidate.families.singleton.familyType.type := by
  have produced := cvmExecution.familyTypes.produced
  rw [AddInductive.CandidateList.singleton_eta
    cvmExecution.familyTypes.candidates] at produced
  rw [← cvmExecution.families.produced.singleton_familyType] at produced
  have exactProduced : AddInductive.CandidateFamilyTypeListProduced
      constructorValidityMatrixContext
      (.cons cvmCandidate.families.singleton.familyType .nil) := by
    simpa [cvmCandidate,
      AddInductive.NormalizationCandidateExecution.candidate,
      constructorValidityMatrixContext] using produced
  exact exactProduced.singleton_build

theorem cvmFamilyIdentityEvidence :
    TypeChecker.CandidateExprIdentityReplay.Evidence
      cvmFamilyIdentityReplay
      cvmCandidate.families.singleton.familyType.type.trace :=
  cvmFamilyIdentityReplay.evidence_of_build cvmFamilyCandidateBuild

theorem cvmFamilyIdentityReplay_shape :
    cvmFamilyIdentityReplay.spineLength = 2 ∧
      cvmFamilyIdentityReplay.terminalSource =
        .sort (.succ (.param `u)) :=
  ⟨cvmFamilyIdentityShape.spineLength_eq,
    cvmFamilyIdentityShape.terminalSource_eq⟩

theorem cvmFamilyValidationAnnotations :
    cvmCandidate.families.singleton.familyType.type.trace
      |>.validationAnnotations := by
  have h := cvmExecution.familyTypes.produced
    |>.singleton_validationAnnotations
  rw [← cvmExecution.families.produced.singleton_familyType] at h
  simpa [cvmCandidate,
    AddInductive.NormalizationCandidateExecution.candidate] using h

private theorem cvmFamilyData_hasExprMVar_false :
    constructorValidityMatrixInfo.type.data.hasExprMVar = false := by
  change constructorValidityMatrixInfo.type.hasExprMVar = false
  simp [constructorValidityMatrixInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, Expr.bvar_hasExprMVar_of_le]

private theorem cvmFamilyData_hasLevelMVar_false :
    constructorValidityMatrixInfo.type.data.hasLevelMVar = false := by
  change constructorValidityMatrixInfo.type.hasLevelMVar = false
  simp [constructorValidityMatrixInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, Expr.bvar_hasLevelMVar_of_le,
    Level.hasMVar_eq, Level.hasMVar']

private theorem cvmFamilyData_hasFVar_false :
    constructorValidityMatrixInfo.type.data.hasFVar = false := by
  change constructorValidityMatrixInfo.type.hasFVar = false
  simp [constructorValidityMatrixInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, Expr.bvar_hasFVar_of_le]

private theorem cvmFamily_hasMVar_false :
    constructorValidityMatrixInfo.type.hasMVar = false := by
  change (constructorValidityMatrixInfo.type.data.hasExprMVar ||
    constructorValidityMatrixInfo.type.data.hasLevelMVar) = false
  rw [cvmFamilyData_hasExprMVar_false,
    cvmFamilyData_hasLevelMVar_false]
  rfl

private theorem cvmFamily_hasFVar_false :
    constructorValidityMatrixInfo.type.hasFVar = false :=
  cvmFamilyData_hasFVar_false

theorem cvmFamilyClosed :
    cvmCandidate.families.singleton.familyType.type.context.env.checkNoMVarNoFVar
        constructorValidityMatrixKernelType.name
        constructorValidityMatrixKernelType.type = .ok () := by
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar
  rw [show constructorValidityMatrixKernelType.type.hasMVar = false by
    simpa [constructorValidityMatrixKernelType] using
      cvmFamily_hasMVar_false]
  rw [show constructorValidityMatrixKernelType.type.hasFVar = false by
    simpa [constructorValidityMatrixKernelType] using
      cvmFamily_hasFVar_false]
  rfl

theorem cvmFamilyEnsureSort :
    TypeChecker.M.run
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext.safety
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lctx
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lparams
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext.fuel
        (TypeChecker.ensureSort (.sort (.succ (.param `u)))) =
      .ok (.sort (.succ (.param `u))) := by
  rfl

theorem cvmFamilySpineCount :
    2 ≤ cvmCandidate.families.singleton.familyType.type.trace.spineLength := by
  rw [cvmFamilyIdentityEvidence.spineLength_eq,
    cvmFamilyIdentityReplay_shape.1]
  decide

theorem cvmFamilySpineFuel :
    cvmCandidate.families.singleton.familyType.type.trace.spineLength <
      cvmCandidate.families.singleton.familyType.type.context.fuel.inductiveFuel := by
  have contextFuel := congrArg (fun context : AddInductive.Context =>
      context.fuel.inductiveFuel)
    (AddInductive.CandidateExpr.context_eq_of_build cvmFamilyCandidateBuild)
  rw [contextFuel]
  rw [cvmFamilyIdentityEvidence.spineLength_eq,
    cvmFamilyIdentityReplay_shape.1]
  decide

def cvmFamilyValidationRun :
    AddInductive.CandidateExprTrace.FamilyValidationRun
      constructorValidityMatrixKernelType
      cvmCandidate.families.singleton.familyType.type.trace where
  nparams := 2
  resultLevel := .succ (.param `u)
  stats :=
    cvmCandidate.families.singleton.familyType.type.trace
      |>.singletonCandidateInductiveStats
        constructorValidityMatrixKernelType 2 (.succ (.param `u))
  stats_eq := rfl
  terminal_eq := cvmFamilyIdentityEvidence.terminalResult_eq.trans
    cvmFamilyIdentityReplay_shape.2
  run := fun k =>
    AddInductive.CandidateExprTrace.checkInductiveTypes_singleton_of_candidate
      constructorValidityMatrixKernelType
      cvmCandidate.families.singleton.familyType.type.trace
      2 (.succ (.param `u)) k
      cvmFamilyClosed cvmFamilySpineCount cvmFamilySpineFuel
      cvmFamilyValidationAnnotations
      (cvmFamilyIdentityEvidence.terminalResult_eq.trans
        cvmFamilyIdentityReplay_shape.2)
      cvmFamilyEnsureSort

theorem cvmFamilyContext_eq :
    cvmCandidate.families.singleton.familyType.type.context =
      constructorValidityMatrixContext := by
  have h := cvmExecution.familyTypes.produced.singleton_context_eq
  rw [← cvmExecution.families.produced.singleton_familyType] at h
  simpa [cvmCandidate,
    AddInductive.NormalizationCandidateExecution.candidate,
    constructorValidityMatrixContext] using h

theorem cvmFamilyNparams_eq : cvmFamilyValidationRun.nparams = 2 := by
  rfl

theorem cvmFamilyValidationRun_exact : ∀ {alpha}
    (k : AddInductive.InductiveStats → AddInductive.M alpha),
    AddInductive.checkInductiveTypes 2 #[constructorValidityMatrixKernelType]
        k constructorValidityMatrixContext =
      k cvmFamilyValidationRun.stats
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext := by
  intro alpha k
  simpa only [cvmFamilyNparams_eq, cvmFamilyContext_eq] using
    cvmFamilyValidationRun.run k

theorem cvmAfterValidationRun :
    AddInductive.buildNormalizationCandidateExecutionAfterValidation 2
        [constructorValidityMatrixKernelType] 0 false
        constructorValidityMatrixContext cvmFamilyValidationRun.stats
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok cvmExecution := by
  have h := cvmProducedExecution.property
  change AddInductive.buildNormalizationCandidateExecution 2
      [constructorValidityMatrixKernelType] 0 false
      constructorValidityMatrixContext = .ok cvmExecution at h
  unfold AddInductive.buildNormalizationCandidateExecution at h
  rw [cvmFamilyValidationRun_exact] at h
  exact h

theorem cvmExecutionStats_eq :
    cvmExecution.stats = cvmFamilyValidationRun.stats :=
  (cvmExecution.fields_of_afterValidation cvmFamilyValidationRun.stats
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext
    cvmAfterValidationRun).1

theorem cvmExecutionValidationContext_eq :
    cvmExecution.validationContext =
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext :=
  (cvmExecution.fields_of_afterValidation cvmFamilyValidationRun.stats
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext
    cvmAfterValidationRun).2

theorem cvmExecutionValidationRun : ∀ {alpha}
    (k : AddInductive.InductiveStats → AddInductive.M alpha),
    AddInductive.checkInductiveTypes 2 #[constructorValidityMatrixKernelType]
        k constructorValidityMatrixContext =
      k cvmExecution.stats cvmExecution.validationContext := by
  intro alpha k
  rw [cvmFamilyValidationRun_exact, cvmExecutionStats_eq,
    cvmExecutionValidationContext_eq]

theorem cvmCandidate_produced :
    AddInductive.buildNormalizationCandidate 2
        [constructorValidityMatrixKernelType] 0 false
        constructorValidityMatrixContext = .ok cvmCandidate :=
  cvmExecution.produces cvmExecutionValidationRun

def cvmFamilyContext : AddInductive.Context :=
  { constructorValidityMatrixContext with lctx := {} }

def cvmConstructorContext : AddInductive.Context :=
  { constructorValidityMatrixContext with
    env := cvmExecution.familyEnv, lctx := {} }

theorem cvmFamilyCandidateContext_eq :
    cvmCandidate.families.singleton.familyType.type.context =
      cvmFamilyContext := by
  simpa [cvmFamilyContext, constructorValidityMatrixContext] using
    cvmFamilyContext_eq

theorem cvmConstructorCandidateContext_eq :
    cvmCandidate.families.singleton.constructors.singleton.type.context =
      cvmConstructorContext := by
  have h := cvmExecution.families.produced.singleton_constructors
    |>.singleton_context_eq
  simpa [cvmCandidate,
    AddInductive.NormalizationCandidateExecution.candidate,
    cvmConstructorContext] using h

theorem cvmFamilyPrefix_ne :
    cvmFamilyContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def cvmFamilyContextRun :
    TypeChecker.CandidateContextRun cvmFamilyContext :=
  TypeChecker.CandidateContextRun.root cvmEmptyVEnvsWF rfl
    cvmFamilyPrefix_ne

def cvmPreFamilyStage :
    TypeChecker.CandidateSemanticStage cvmFamilyContext VEnv.empty [`u] where
  contextRun := cvmFamilyContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

theorem cvmRawFamily_isType :
    VEnv.empty.IsType 1 [] constructorValidityMatrixType.type := by
  change VEnv.empty.IsType 1 []
    (.forallE (.sort (.succ (.param 0)))
      (.forallE (.forallE (.bvar 0) (.sort .zero))
        (.sort (.succ (.param 0)))))
  apply VEnv.IsType.forallE
  · exact ⟨_, VEnv.HasType.sort (by decide)⟩
  · apply VEnv.IsType.forallE
    · apply VEnv.IsType.forallE
      · exact ⟨_, by type_tac⟩
      · exact ⟨_, VEnv.HasType.sort (by decide)⟩
    · exact ⟨_, VEnv.HasType.sort (by decide)⟩

theorem cvmFamilySource_tr :
    TrExprS VEnv.empty [`u] [] constructorValidityMatrixKernelType.type
      constructorValidityMatrixType.type := by
  have shape : TrTypeExpr VEnv.empty [`u] []
      constructorValidityMatrixKernelType.type
      constructorValidityMatrixType.type := by
    tr_type_expr_tac
  obtain ⟨level, type⟩ := cvmRawFamily_isType
  exact shape.to_trExprS .empty trivial ⟨.sort level, type⟩

theorem cvmStatsNindices_eq :
    cvmFamilyValidationRun.stats.nindices = #[0] := by
  rw [cvmFamilyValidationRun.stats_eq]
  change #[cvmCandidate.families.singleton.familyType.type.trace.spineLength -
    2] = #[0]
  rw [cvmFamilyIdentityEvidence.spineLength_eq,
    cvmFamilyIdentityReplay_shape.1]

theorem cvmTerminalEnv_eq :
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env =
      constructorValidityMatrixContext.env := by
  calc
    _ = cvmCandidate.families.singleton.familyType.type.context.env :=
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext_env
    _ = cvmFamilyContext.env :=
      congrArg AddInductive.Context.env cvmFamilyCandidateContext_eq
    _ = constructorValidityMatrixContext.env := rfl

theorem cvmTerminalLparams_eq :
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lparams =
      constructorValidityMatrixContext.lparams := by
  calc
    _ = cvmCandidate.families.singleton.familyType.type.context.lparams :=
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext_lparams
    _ = cvmFamilyContext.lparams :=
      congrArg AddInductive.Context.lparams cvmFamilyCandidateContext_eq
    _ = constructorValidityMatrixContext.lparams := rfl

theorem cvmTerminalAllowPrimitive_eq :
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext.allowPrimitive =
      constructorValidityMatrixContext.allowPrimitive := by
  calc
    _ = cvmCandidate.families.singleton.familyType.type.context.allowPrimitive :=
      cvmCandidate.families.singleton.familyType.type.trace
        |>.terminalContext_allowPrimitive
    _ = cvmFamilyContext.allowPrimitive :=
      congrArg AddInductive.Context.allowPrimitive cvmFamilyCandidateContext_eq
    _ = constructorValidityMatrixContext.allowPrimitive := rfl

theorem cvmFamilyNameAbsent :
    constructorValidityMatrixContext.env.contains
      constructorValidityMatrixKernelType.name = false := by
  change ({} : ConstMap).contains
    constructorValidityMatrixKernelType.name = false
  rw [SMap.find?_isSome,
    SMap.WF.find?_eq SMap.WF.empty]
  simp [SMap.toList']

theorem cvmFamilyNameNotPrimitive :
    Kernel.Environment.primitives.contains
      constructorValidityMatrixKernelType.name = false := by
  simp [constructorValidityMatrixKernelType,
    constructorValidityMatrixInfo, Kernel.Environment.primitives,
    NameSet.ofList]
  simp +decide [NameSet.contains]

def cvmDeclaredInfo : ConstantInfo :=
  .inductInfo <| AddInductive.singletonDeclaredInfo
    cvmFamilyValidationRun.stats 2 0 constructorValidityMatrixKernelType
    0 false
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext

theorem cvmDeclaredInfo_isRec :
    (AddInductive.singletonDeclaredInfo
      cvmFamilyValidationRun.stats 2 0 constructorValidityMatrixKernelType
      0 false
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext).isRec =
      true := by
  simp only [AddInductive.singletonDeclaredInfo]
  rw [cvmFamilyValidationRun.stats_eq]
  simp [cvmFamilyValidationRun,
    AddInductive.CandidateExprTrace.singletonCandidateInductiveStats,
    AddInductive.isRec, AddInductive.isRec.loop,
    AddInductive.hasIndOcc,
    constructorValidityMatrixKernelType,
    constructorValidityMatrixKernelCtor,
    constructorValidityMatrixInfo, constructorValidityMatrixMkInfo,
    ConstantInfo.name, ConstantInfo.type, ConstantInfo.toConstantVal,
    Expr.constName!]

theorem cvmFamilyNames_eq :
    constructorValidityMatrixKernelType.name =
      constructorValidityMatrixType.name := by
  decide

theorem cvmFamilyMap_add :
    cvmExecution.familyEnv.constants =
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.insert
        constructorValidityMatrixType.name cvmDeclaredInfo := by
  have h := cvmExecution.declareRun
  rw [cvmExecutionStats_eq, cvmExecutionValidationContext_eq] at h
  rw [← cvmFamilyNames_eq]
  simpa [cvmDeclaredInfo] using
    AddInductive.declareInductiveTypes_singleton_constants
      cvmFamilyValidationRun.stats 2 0 constructorValidityMatrixKernelType
      0 false
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext
      cvmExecution.familyEnv cvmStatsNindices_eq h

theorem cvmConstructorContext_noProjectionReady (name : Name) :
    cvmConstructorContext.env.isProjectionReadyStructure name = false := by
  have hConstants :
      cvmConstructorContext.env.constants =
        ({} : ConstMap).insert constructorValidityMatrixType.name
          cvmDeclaredInfo := by
    simp only [cvmConstructorContext]
    rw [cvmFamilyMap_add, cvmTerminalEnv_eq]
    rfl
  have hMap :
      (({} : ConstMap).insert constructorValidityMatrixType.name
        cvmDeclaredInfo).WF :=
    SMap.WF.empty.insert _ _ (by simp [SMap.find?])
  by_cases hName : constructorValidityMatrixType.name = name
  · subst name
    apply Kernel.Environment.isProjectionReadyStructure_false_of_no_ctorInfo
      (info := AddInductive.singletonDeclaredInfo
        cvmFamilyValidationRun.stats 2 0 constructorValidityMatrixKernelType
        0 false
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext)
    · rw [hConstants, hMap.find?'_eq_find?,
        SMap.WF.find?_insert
          (s := ({} : ConstMap)) SMap.WF.empty]
      simp [cvmDeclaredInfo]
    · intro ctor ctorInfo hctor
      rw [hConstants, hMap.find?'_eq_find?,
        SMap.WF.find?_insert
          (s := ({} : ConstMap)) SMap.WF.empty] at hctor
      split at hctor
      · cases hctor
      · simp [SMap.find?] at hctor
  · apply Kernel.Environment.isProjectionReadyStructure_false_of_not_found
    rw [hConstants, hMap.find?'_eq_find?,
      SMap.WF.find?_insert
        (s := ({} : ConstMap)) SMap.WF.empty]
    simp [hName, SMap.find?]

theorem cvmConstructorContext_noCtorInfo (name : Name)
    (info : ConstructorVal) :
    cvmConstructorContext.env.find? name ≠ some (.ctorInfo info) := by
  intro h
  have hConstants :
      cvmConstructorContext.env.constants =
        ({} : ConstMap).insert constructorValidityMatrixType.name
          cvmDeclaredInfo := by
    simp only [cvmConstructorContext]
    rw [cvmFamilyMap_add, cvmTerminalEnv_eq]
    rfl
  have hMap :
      (({} : ConstMap).insert constructorValidityMatrixType.name
        cvmDeclaredInfo).WF :=
    SMap.WF.empty.insert _ _ (by simp [SMap.find?])
  change cvmConstructorContext.env.constants.find?' name =
    some (.ctorInfo info) at h
  rw [hConstants, hMap.find?'_eq_find?,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty] at h
  split at h
  · cases h
  · simp [SMap.find?] at h

def cvmTypeEnv : VEnv :=
  (VEnv.empty.addConst constructorValidityMatrixType.name
    constructorValidityMatrixType.toVConstant).get!

theorem cvmTypeEnv_add :
    VEnv.empty.addConst constructorValidityMatrixType.name
        constructorValidityMatrixType.toVConstant = some cvmTypeEnv := by
  rfl

theorem cvmDeclaredInfo_tr :
    TrConstVal .safe VEnv.empty cvmDeclaredInfo
      constructorValidityMatrixType.toVConstVal := by
  refine ⟨⟨by decide, ?_, ?_⟩, rfl⟩
  · change
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lparams.length =
        constructorValidityMatrixType.uvars
    rw [cvmTerminalLparams_eq]
    rfl
  · change TrExprS VEnv.empty
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lparams
      [] constructorValidityMatrixKernelType.type
      constructorValidityMatrixType.type
    rw [cvmTerminalLparams_eq]
    exact cvmFamilySource_tr

def cvmAddType :
    AddInductConstant .induct cvmFamilyContext.env.constants VEnv.empty
      constructorValidityMatrixType.toVConstVal
      cvmConstructorContext.env.constants cvmTypeEnv where
  info := cvmDeclaredInfo
  kind_eq := by simp [cvmDeclaredInfo, InductConstantKind.Matches]
  tr := cvmDeclaredInfo_tr
  map_fresh := by
    change ({} : ConstMap).find?
      constructorValidityMatrixType.name = none
    rw [SMap.WF.find?_eq SMap.WF.empty]
    simp [SMap.toList']
  env_add := cvmTypeEnv_add
  map_add := by
    simpa [cvmFamilyContext, cvmConstructorContext,
      cvmTerminalEnv_eq] using cvmFamilyMap_add

theorem cvmFamilyWhnfDepth :
    cvmCandidate.families.singleton.familyType.type.context.fuel.recDepth =
      9999 + 1 := by
  rw [cvmFamilyCandidateContext_eq]
  rfl

def cvmFamilyStage :
    VInductDecl.CandidateFamilyStagedInput
      cvmFamilyContext cvmConstructorContext VEnv.empty [`u]
      cvmCandidate.families.singleton.familyType
      constructorValidityMatrixType cvmPreFamilyStage where
  name_eq := cvmFamilyNames_eq
  uvars_eq := rfl
  type := {
    context_eq := cvmFamilyCandidateContext_eq.symm
    source_tr := cvmFamilySource_tr
    whnfFuel := 9999
    whnfDepth := cvmFamilyWhnfDepth }
  validation := cvmFamilyValidationRun
  typeEnv := cvmTypeEnv
  addInduct := cvmAddType
  projectionReady := ProjectionResolutionReady.of_no_ctorInfo
    cvmConstructorContext_noCtorInfo
  structureEtaReady := StructureEtaReady.of_no_ctorInfo
    cvmConstructorContext_noCtorInfo
  family_lctx_eq := rfl
  constructorContext_eq := rfl
  quotInit_eq := by
    have h := cvmExecution.declareRun
    rw [cvmExecutionStats_eq, cvmExecutionValidationContext_eq] at h
    simpa [cvmConstructorContext, cvmFamilyContext,
      cvmTerminalEnv_eq] using
      AddInductive.declareInductiveTypes_singleton_quotInit
        cvmFamilyValidationRun.stats 2 0 constructorValidityMatrixKernelType
        0 false
        cvmCandidate.families.singleton.familyType.type.trace.terminalContext
        cvmExecution.familyEnv cvmStatsNindices_eq h
  name_not_reflected := by decide
  name_not_primitive := by
    rw [← cvmFamilyNames_eq]
    exact cvmFamilyNameNotPrimitive

def cvmCtorAlphaDomain : Expr :=
  constructorValidityMatrixKernelCtor.type.bindingDomain!

def cvmCtorAlphaContext : AddInductive.Context :=
  cvmConstructorContext.pushLocalDecl `α .implicit cvmCtorAlphaDomain

def cvmCtorAfterAlpha : Expr :=
  constructorValidityMatrixKernelCtor.type.bindingBody!.instantiate1
    cvmConstructorContext.freshExpr

def cvmCtorPDomain : Expr := cvmCtorAfterAlpha.bindingDomain!

def cvmCtorPContext : AddInductive.Context :=
  cvmCtorAlphaContext.pushLocalDecl `P .implicit cvmCtorPDomain

def cvmCtorAfterP : Expr :=
  cvmCtorAfterAlpha.bindingBody!.instantiate1
    cvmCtorAlphaContext.freshExpr

def cvmCtorXDomain : Expr := cvmCtorAfterP.bindingDomain!

def cvmCtorXContext : AddInductive.Context :=
  cvmCtorPContext.pushLocalDecl `x .default cvmCtorXDomain

def cvmCtorAfterX : Expr :=
  cvmCtorAfterP.bindingBody!.instantiate1 cvmCtorPContext.freshExpr

def cvmCtorProofDomain : Expr := cvmCtorAfterX.bindingDomain!

def cvmCtorProofContext : AddInductive.Context :=
  cvmCtorXContext.pushLocalDecl `proof .default cvmCtorProofDomain

def cvmCtorAfterProof : Expr :=
  cvmCtorAfterX.bindingBody!.instantiate1 cvmCtorXContext.freshExpr

def cvmCtorDirectDomain : Expr := cvmCtorAfterProof.bindingDomain!

def cvmCtorDirectContext : AddInductive.Context :=
  cvmCtorProofContext.pushLocalDecl `direct .default cvmCtorDirectDomain

def cvmCtorAfterDirect : Expr :=
  cvmCtorAfterProof.bindingBody!.instantiate1 cvmCtorProofContext.freshExpr

def cvmCtorFunctionDomain : Expr := cvmCtorAfterDirect.bindingDomain!

def cvmCtorFunctionContext : AddInductive.Context :=
  cvmCtorDirectContext.pushLocalDecl `function .default cvmCtorFunctionDomain

def cvmCtorAfterFunction : Expr :=
  cvmCtorAfterDirect.bindingBody!.instantiate1
    cvmCtorDirectContext.freshExpr

def cvmCtorLaterDomain : Expr := cvmCtorAfterFunction.bindingDomain!

def cvmCtorLaterContext : AddInductive.Context :=
  cvmCtorFunctionContext.pushLocalDecl `later .default cvmCtorLaterDomain

def cvmCtorAfterLater : Expr :=
  cvmCtorAfterFunction.bindingBody!.instantiate1
    cvmCtorFunctionContext.freshExpr

def cvmCtorLaterProofDomain : Expr := cvmCtorAfterLater.bindingDomain!

def cvmCtorLaterProofContext : AddInductive.Context :=
  cvmCtorLaterContext.pushLocalDecl `laterProof .default
    cvmCtorLaterProofDomain

def cvmCtorTerminal : Expr :=
  cvmCtorAfterLater.bindingBody!.instantiate1
    cvmCtorLaterContext.freshExpr

def cvmCtorPArgContext : AddInductive.Context :=
  cvmCtorAlphaContext.pushLocalDecl cvmCtorPDomain.bindingName!
    .default cvmCtorPDomain.bindingDomain!

def cvmCtorFunctionArgContext : AddInductive.Context :=
  cvmCtorDirectContext.pushLocalDecl `y .default
    cvmCtorFunctionDomain.bindingDomain!

theorem cvmCtorRootLocalRun :
    TypeChecker.CandidateLocalContextRun cvmConstructorContext :=
  .empty _ rfl

theorem cvmCtorAlphaLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorAlphaContext :=
  cvmCtorRootLocalRun.push `α .implicit cvmCtorAlphaDomain

theorem cvmCtorPLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorPContext :=
  cvmCtorAlphaLocalRun.push `P .implicit cvmCtorPDomain

theorem cvmCtorXLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorXContext :=
  cvmCtorPLocalRun.push `x .default cvmCtorXDomain

theorem cvmCtorProofLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorProofContext :=
  cvmCtorXLocalRun.push `proof .default cvmCtorProofDomain

theorem cvmCtorDirectLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorDirectContext :=
  cvmCtorProofLocalRun.push `direct .default cvmCtorDirectDomain

theorem cvmCtorFunctionLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorFunctionContext :=
  cvmCtorDirectLocalRun.push `function .default cvmCtorFunctionDomain

theorem cvmCtorLaterLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorLaterContext :=
  cvmCtorFunctionLocalRun.push `later .default cvmCtorLaterDomain

theorem cvmCtorLaterProofLocalRun :
    TypeChecker.CandidateLocalContextRun cvmCtorLaterProofContext :=
  cvmCtorLaterLocalRun.push `laterProof .default cvmCtorLaterProofDomain

theorem cvmCtorAlphaFindInAlpha :
    cvmCtorAlphaContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorRootLocalRun.push_findNew `α .implicit cvmCtorAlphaDomain

theorem cvmCtorAlphaFindInP :
    cvmCtorPContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorAlphaLocalRun.push_findOld `P .implicit cvmCtorPDomain
    cvmCtorAlphaFindInAlpha

theorem cvmCtorAlphaFindInX :
    cvmCtorXContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorPLocalRun.push_findOld `x .default cvmCtorXDomain
    cvmCtorAlphaFindInP

theorem cvmCtorAlphaFindInProof :
    cvmCtorProofContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorXLocalRun.push_findOld `proof .default cvmCtorProofDomain
    cvmCtorAlphaFindInX

theorem cvmCtorAlphaFindInDirect :
    cvmCtorDirectContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorProofLocalRun.push_findOld `direct .default cvmCtorDirectDomain
    cvmCtorAlphaFindInProof

theorem cvmCtorAlphaFindInFunction :
    cvmCtorFunctionContext.lctx.find? cvmConstructorContext.freshFVarId =
      some (.cdecl cvmConstructorContext.lctx.decls.size
        cvmConstructorContext.freshFVarId `α cvmCtorAlphaDomain
        .implicit .default) :=
  cvmCtorDirectLocalRun.push_findOld `function .default
    cvmCtorFunctionDomain cvmCtorAlphaFindInDirect

theorem cvmCtorPFindInP :
    cvmCtorPContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorAlphaLocalRun.push_findNew `P .implicit cvmCtorPDomain

theorem cvmCtorPFindInX :
    cvmCtorXContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorPLocalRun.push_findOld `x .default cvmCtorXDomain
    cvmCtorPFindInP

theorem cvmCtorPFindInProof :
    cvmCtorProofContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorXLocalRun.push_findOld `proof .default cvmCtorProofDomain
    cvmCtorPFindInX

theorem cvmCtorPFindInDirect :
    cvmCtorDirectContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorProofLocalRun.push_findOld `direct .default cvmCtorDirectDomain
    cvmCtorPFindInProof

theorem cvmCtorPFindInFunction :
    cvmCtorFunctionContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorDirectLocalRun.push_findOld `function .default
    cvmCtorFunctionDomain cvmCtorPFindInDirect

theorem cvmCtorPFindInLater :
    cvmCtorLaterContext.lctx.find? cvmCtorAlphaContext.freshFVarId =
      some (.cdecl cvmCtorAlphaContext.lctx.decls.size
        cvmCtorAlphaContext.freshFVarId `P cvmCtorPDomain
        .implicit .default) :=
  cvmCtorFunctionLocalRun.push_findOld `later .default cvmCtorLaterDomain
    cvmCtorPFindInFunction

theorem cvmCtorFamilyLookup :
    cvmConstructorContext.env.find?
        constructorValidityMatrixKernelType.name =
      some cvmDeclaredInfo := by
  change cvmExecution.familyEnv.constants.find?'
      constructorValidityMatrixKernelType.name = some cvmDeclaredInfo
  rw [show cvmExecution.familyEnv.constants =
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.insert
        constructorValidityMatrixType.name cvmDeclaredInfo from cvmFamilyMap_add]
  have hbase :
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.WF := by
    rw [cvmTerminalEnv_eq]
    exact SMap.WF.empty
  have hfresh :
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.find?
        constructorValidityMatrixType.name = none := by
    rw [cvmTerminalEnv_eq]
    change ({} : ConstMap).find? constructorValidityMatrixType.name = none
    rw [SMap.WF.find?_eq SMap.WF.empty]
    simp [SMap.toList']
  have hinsert := hbase.insert constructorValidityMatrixType.name
    cvmDeclaredInfo hfresh
  rw [SMap.WF.find?'_eq_find? hinsert]
  rw [hbase.find?_insert]
  simp [cvmFamilyNames_eq]

theorem cvmCtorFamilyWhnf
    (context : AddInductive.Context)
    (arg1 arg2 : FVarId)
    (henv : context.env = cvmConstructorContext.env)
    (hdepth : context.fuel.recDepth = 10000)
    (hwhnf : context.fuel.whnf = 100000)
    (hquot : context.env.quotInit = false) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨context,
        .app
          (.app (.const ``ConstructorValidityMatrix [.param `u])
            (.fvar arg1))
          (.fvar arg2),
        .app
          (.app (.const ``ConstructorValidityMatrix [.param `u])
            (.fvar arg1))
          (.fvar arg2)⟩ := by
  apply TypeChecker.candidateWhnfConstFVarFVar_refl context
    ``ConstructorValidityMatrix [.param `u] arg1 arg2
    (AddInductive.singletonDeclaredInfo
      cvmFamilyValidationRun.stats 2 0 constructorValidityMatrixKernelType
      0 false
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext)
  · exact hdepth
  · exact hwhnf
  · exact hquot
  · rw [henv]
    simpa [cvmDeclaredInfo, constructorValidityMatrixKernelType,
      constructorValidityMatrixInfo, ConstantInfo.name,
      ConstantInfo.toConstantVal] using cvmCtorFamilyLookup
  · rfl

def cvmCtorFamilyApp : Expr :=
  .app
    (.app (.const ``ConstructorValidityMatrix [.param `u])
      cvmConstructorContext.freshExpr)
    cvmCtorAlphaContext.freshExpr

macro "simp_cvm_ctor_expr" : tactic =>
  `(tactic| simp [cvmCtorTerminal, cvmCtorLaterProofContext,
    cvmCtorPArgContext, cvmCtorFunctionArgContext,
    cvmCtorLaterProofDomain, cvmCtorAfterLater, cvmCtorLaterContext,
    cvmCtorLaterDomain, cvmCtorAfterFunction, cvmCtorFunctionContext,
    cvmCtorFunctionDomain, cvmCtorAfterDirect, cvmCtorDirectContext,
    cvmCtorDirectDomain, cvmCtorAfterProof, cvmCtorProofContext,
    cvmCtorProofDomain, cvmCtorAfterX, cvmCtorXContext,
    cvmCtorXDomain, cvmCtorAfterP, cvmCtorPContext, cvmCtorPDomain,
    cvmCtorAfterAlpha, cvmCtorAlphaContext, cvmCtorAlphaDomain,
    cvmCtorFamilyApp, cvmConstructorContext,
    constructorValidityMatrixKernelCtor,
    constructorValidityMatrixKernelType,
    constructorValidityMatrixMkInfo, constructorValidityMatrixInfo,
    ConstantInfo.type, ConstantInfo.toConstantVal,
    AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    Expr.bindingDomain!, Expr.bindingBody!, Expr.bindingName!,
    Expr.bindingInfo!, Expr.isForall,
    Expr.instantiate1_eq, Expr.instantiate1',
    Expr.liftLooseBVars_zero,
    AddInductive.CandidateTypeAnnotationTrace.build])

macro "simpa_cvm_ctor_expr" " using " t:term : tactic =>
  `(tactic| simpa [cvmCtorTerminal, cvmCtorLaterProofContext,
      cvmCtorPArgContext, cvmCtorFunctionArgContext,
      cvmCtorLaterProofDomain, cvmCtorAfterLater, cvmCtorLaterContext,
      cvmCtorLaterDomain, cvmCtorAfterFunction, cvmCtorFunctionContext,
      cvmCtorFunctionDomain, cvmCtorAfterDirect, cvmCtorDirectContext,
      cvmCtorDirectDomain, cvmCtorAfterProof, cvmCtorProofContext,
      cvmCtorProofDomain, cvmCtorAfterX, cvmCtorXContext,
      cvmCtorXDomain, cvmCtorAfterP, cvmCtorPContext, cvmCtorPDomain,
      cvmCtorAfterAlpha, cvmCtorAlphaContext, cvmCtorAlphaDomain,
      cvmCtorFamilyApp, cvmConstructorContext,
      constructorValidityMatrixKernelCtor,
      constructorValidityMatrixKernelType,
      constructorValidityMatrixMkInfo, constructorValidityMatrixInfo,
      ConstantInfo.type, ConstantInfo.toConstantVal,
      AddInductive.Context.pushLocalDecl,
      AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
      Expr.bindingDomain!, Expr.bindingBody!, Expr.bindingName!,
      Expr.bindingInfo!, Expr.isForall,
      Expr.instantiate1_eq, Expr.instantiate1',
      Expr.liftLooseBVars_zero,
      AddInductive.CandidateTypeAnnotationTrace.build] using $t)


theorem cvmCtorQuotInit :
    cvmConstructorContext.env.quotInit = false := by
  rw [cvmFamilyStage.quotInit_eq]
  rfl

theorem cvmCtorFamilyAppWhnf
    (context : AddInductive.Context)
    (henv : context.env = cvmConstructorContext.env)
    (hdepth : context.fuel.recDepth = 10000)
    (hwhnf : context.fuel.whnf = 100000) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨context, cvmCtorFamilyApp, cvmCtorFamilyApp⟩ := by
  have hquot : context.env.quotInit = false := by
    rw [henv]
    exact cvmCtorQuotInit
  simpa [cvmCtorFamilyApp, AddInductive.Context.freshExpr,
      constructorValidityMatrixKernelType,
      constructorValidityMatrixInfo, ConstantInfo.name] using
    cvmCtorFamilyWhnf context cvmConstructorContext.freshFVarId
      cvmCtorAlphaContext.freshFVarId henv hdepth hwhnf hquot

open TypeChecker in
def cvmCtorIdentityShape :
    CandidateExprIdentityReplay.Shaped cvmConstructorContext
      constructorValidityMatrixKernelCtor.type 8 cvmCtorFamilyApp := by
  have alphaInAlpha : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorAlphaContext, cvmConstructorContext.freshExpr,
        cvmConstructorContext.freshExpr⟩ := by
    simpa [cvmCtorAlphaContext, cvmCtorAlphaDomain] using
      TypeChecker.candidateWhnfPushedFVar_refl
        cvmConstructorContext `α cvmCtorAlphaDomain .implicit 9999
        (by rfl) cvmCtorRootLocalRun.wf cvmCtorRootLocalRun.fresh
  have alphaInP : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorPContext, cvmConstructorContext.freshExpr,
        cvmConstructorContext.freshExpr⟩ := by
    apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
    · rfl
    · unfold TypeChecker.Inner.isLetFVar
      rw [cvmCtorAlphaFindInP]
  have alphaInDirect : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorDirectContext, cvmConstructorContext.freshExpr,
        cvmConstructorContext.freshExpr⟩ := by
    apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
    · rfl
    · unfold TypeChecker.Inner.isLetFVar
      rw [cvmCtorAlphaFindInDirect]
  have alphaInFunction : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorFunctionContext, cvmConstructorContext.freshExpr,
        cvmConstructorContext.freshExpr⟩ := by
    apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
    · rfl
    · unfold TypeChecker.Inner.isLetFVar
      rw [cvmCtorAlphaFindInFunction]
  have proofDomainWhnf : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorXContext, cvmCtorProofDomain,
        cvmCtorProofDomain⟩ := by
    have run := TypeChecker.candidateWhnfFVarAppFVar_refl
      cvmCtorXContext cvmCtorAlphaContext.freshFVarId
      cvmCtorPContext.freshFVarId (by rfl) (by rfl)
      (by
        change cvmConstructorContext.env.quotInit = false
        exact cvmCtorQuotInit) (by
        unfold TypeChecker.Inner.isLetFVar
        rw [cvmCtorPFindInX])
    rw [show cvmCtorProofDomain =
      .app cvmCtorAlphaContext.freshExpr cvmCtorPContext.freshExpr by
        simp_cvm_ctor_expr]
    exact run
  have laterProofDomainWhnf : AddInductive.CandidateWhnfStep.Valid
      ⟨cvmCtorLaterContext, cvmCtorLaterProofDomain,
        cvmCtorLaterProofDomain⟩ := by
    have run := TypeChecker.candidateWhnfFVarAppFVar_refl
      cvmCtorLaterContext cvmCtorAlphaContext.freshFVarId
      cvmCtorFunctionContext.freshFVarId (by rfl) (by rfl)
      (by
        change cvmConstructorContext.env.quotInit = false
        exact cvmCtorQuotInit) (by
        unfold TypeChecker.Inner.isLetFVar
        rw [cvmCtorPFindInLater])
    rw [show cvmCtorLaterProofDomain =
      .app cvmCtorAlphaContext.freshExpr
        cvmCtorFunctionContext.freshExpr by simp_cvm_ctor_expr]
    exact run
  have terminalShape : CandidateExprIdentityReplay.Shaped
      cvmCtorLaterProofContext cvmCtorTerminal 0
      cvmCtorFamilyApp := by
    rw [show cvmCtorTerminal = cvmCtorFamilyApp by simp_cvm_ctor_expr]
    exact .terminal _ _
      (cvmCtorFamilyAppWhnf _ rfl rfl rfl) rfl
  have laterProofShape : CandidateExprIdentityReplay.Shaped
      cvmCtorLaterContext cvmCtorAfterLater 1
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorLaterContext cvmCtorAfterLater
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _
          laterProofDomainWhnf (by simp_cvm_ctor_expr)).replay)
    · simpa_cvm_ctor_expr using terminalShape
  have laterShape : CandidateExprIdentityReplay.Shaped
      cvmCtorFunctionContext cvmCtorAfterFunction 2
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorFunctionContext cvmCtorAfterFunction
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _
          alphaInFunction rfl).replay)
    · simpa_cvm_ctor_expr using laterProofShape
  have functionArgTerminal : CandidateExprIdentityReplay.Shaped
      cvmCtorFunctionArgContext cvmCtorFamilyApp 0
      cvmCtorFamilyApp :=
    .terminal _ _ (cvmCtorFamilyAppWhnf _ rfl rfl rfl) rfl
  have functionDomainShape : CandidateExprIdentityReplay.Shaped
      cvmCtorDirectContext cvmCtorFunctionDomain 1
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorDirectContext cvmCtorFunctionDomain
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _
          alphaInDirect rfl).replay)
    · simpa_cvm_ctor_expr using functionArgTerminal
  have functionShape : CandidateExprIdentityReplay.Shaped
      cvmCtorDirectContext cvmCtorAfterDirect 3
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorDirectContext cvmCtorAfterDirect
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using functionDomainShape.replay
    · simpa_cvm_ctor_expr using laterShape
  have directDomainShape : CandidateExprIdentityReplay.Shaped
      cvmCtorProofContext cvmCtorDirectDomain 0
      cvmCtorFamilyApp := by
    rw [show cvmCtorDirectDomain = cvmCtorFamilyApp by simp_cvm_ctor_expr]
    exact .terminal _ _ (cvmCtorFamilyAppWhnf _ rfl rfl rfl) rfl
  have directShape : CandidateExprIdentityReplay.Shaped
      cvmCtorProofContext cvmCtorAfterProof 4
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorProofContext cvmCtorAfterProof
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · have consumeDirect : AddInductive.consumeTypeAnnotations
          cvmCtorDirectDomain = cvmCtorDirectDomain := by
        rw [show cvmCtorDirectDomain = cvmCtorFamilyApp by simp_cvm_ctor_expr]
        simpa [cvmCtorFamilyApp,
            AddInductive.CandidateTypeAnnotationTrace.build] using
          (AddInductive.CandidateTypeAnnotationTrace.build_consumed
            cvmCtorFamilyApp).symm
      simpa only [cvmCtorDirectDomain] using consumeDirect
    · simpa_cvm_ctor_expr using directDomainShape.replay
    · simpa_cvm_ctor_expr using functionShape
  have proofShape : CandidateExprIdentityReplay.Shaped
      cvmCtorXContext cvmCtorAfterX 5 cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorXContext cvmCtorAfterX
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _
          proofDomainWhnf (by simp_cvm_ctor_expr)).replay)
    · simpa_cvm_ctor_expr using directShape
  have xShape : CandidateExprIdentityReplay.Shaped
      cvmCtorPContext cvmCtorAfterP 6 cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorPContext cvmCtorAfterP
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _ alphaInP rfl).replay)
    · simpa_cvm_ctor_expr using proofShape
  have pArgTerminal : CandidateExprIdentityReplay.Shaped
      cvmCtorPArgContext (.sort .zero) 0 (.sort .zero) :=
    .terminal _ _ (by rfl) rfl
  have pDomainShape : CandidateExprIdentityReplay.Shaped
      cvmCtorAlphaContext cvmCtorPDomain 1 (.sort .zero) := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorAlphaContext cvmCtorPDomain
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using
        ((CandidateExprIdentityReplay.Shaped.terminal _ _
          alphaInAlpha rfl).replay)
    · simpa_cvm_ctor_expr using pArgTerminal
  have pShape : CandidateExprIdentityReplay.Shaped
      cvmCtorAlphaContext cvmCtorAfterAlpha 7
      cvmCtorFamilyApp := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
      cvmCtorAlphaContext cvmCtorAfterAlpha
    · simp_cvm_ctor_expr
    · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
        _ _ 9999 (by rfl)
      simp_cvm_ctor_expr
    · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
      simp_cvm_ctor_expr
    · simpa_cvm_ctor_expr using pDomainShape.replay
    · simpa_cvm_ctor_expr using xShape
  apply CandidateExprIdentityReplay.Shaped.forallEBuiltOfSource
    cvmConstructorContext constructorValidityMatrixKernelCtor.type
  · simp_cvm_ctor_expr
  · apply CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
      _ _ 9999 (by rfl)
    simp_cvm_ctor_expr
  · rw [← AddInductive.CandidateTypeAnnotationTrace.build_consumed]
    simp_cvm_ctor_expr
  · have alphaDomainWhnf : AddInductive.CandidateWhnfStep.Valid
        ⟨cvmConstructorContext, cvmCtorAlphaDomain,
          cvmCtorAlphaDomain⟩ := by
      change AddInductive.CandidateWhnfStep.Valid
        ⟨cvmConstructorContext, .sort (.succ (.param `u)),
          .sort (.succ (.param `u))⟩
      rfl
    exact (CandidateExprIdentityReplay.Shaped.terminal _ _
      alphaDomainWhnf rfl).replay
  · simpa_cvm_ctor_expr using pShape

theorem cvmCtorCandidateBuild :
    AddInductive.buildCandidateExpr constructorValidityMatrixKernelCtor.type
        cvmConstructorContext =
      .ok cvmCandidate.families.singleton.constructors.singleton.type := by
  have produced := cvmExecution.families.produced.singleton_constructors
  rw [AddInductive.CandidateList.singleton_eta
    cvmExecution.families.candidates.singleton.constructors] at produced
  have exactProduced : AddInductive.CandidateConstructorListProduced
      cvmConstructorContext
      (.cons cvmCandidate.families.singleton.constructors.singleton .nil) := by
    simpa [cvmCandidate,
      AddInductive.NormalizationCandidateExecution.candidate,
      cvmConstructorContext, constructorValidityMatrixKernelType] using produced
  exact exactProduced.singleton_build

def cvmCtorIdentityReplay :
    TypeChecker.CandidateExprIdentityReplay cvmConstructorContext
      constructorValidityMatrixKernelCtor.type :=
  cvmCtorIdentityShape.replay

theorem cvmCtorIdentityEvidence :
    TypeChecker.CandidateExprIdentityReplay.Evidence
      cvmCtorIdentityReplay
      cvmCandidate.families.singleton.constructors.singleton.type.trace :=
  cvmCtorIdentityReplay.evidence_of_build cvmCtorCandidateBuild

theorem cvmCtorIdentityReplay_shape :
    cvmCtorIdentityReplay.spineLength = 8 ∧
      cvmCtorIdentityReplay.terminalSource = cvmCtorFamilyApp :=
  ⟨cvmCtorIdentityShape.spineLength_eq,
    cvmCtorIdentityShape.terminalSource_eq⟩

theorem cvmTypeEnv_ordered : cvmTypeEnv.Ordered :=
  .const (n := constructorValidityMatrixType.name)
    (ci := constructorValidityMatrixType.toVConstant)
    .empty cvmRawFamily_isType cvmTypeEnv_add

theorem cvmRawCtor_isType :
    cvmTypeEnv.IsType 1 [] constructorValidityMatrixType.ctors[0].type := by
  have hFamily : cvmTypeEnv.constants constructorValidityMatrixType.name =
      some constructorValidityMatrixType.toVConstant :=
    VEnv.addConst_self cvmTypeEnv_add
  exact ⟨_, by type_tac⟩

theorem cvmCtorSource_tr :
    TrExprS cvmTypeEnv [`u] [] constructorValidityMatrixKernelCtor.type
      constructorValidityMatrixType.ctors[0].type := by
  have shape : TrTypeExpr cvmTypeEnv [`u] []
      constructorValidityMatrixKernelCtor.type
      constructorValidityMatrixType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨level, type⟩ := cvmRawCtor_isType
  exact shape.to_trExprS cvmTypeEnv_ordered trivial ⟨.sort level, type⟩

theorem cvmCtorNames_eq :
    constructorValidityMatrixKernelCtor.name =
      constructorValidityMatrixType.ctors[0].name := by
  decide

theorem cvmCtorWhnfDepth :
    cvmCandidate.families.singleton.constructors.singleton.type.context.fuel.recDepth =
      9999 + 1 := by
  rw [cvmConstructorCandidateContext_eq]
  rfl

theorem cvmRawCtors_eq :
    constructorValidityMatrixType.ctors =
      [constructorValidityMatrixType.ctors[0]] := by
  rfl

def cvmCtorStagedInput :
    VInductDecl.CandidateConstructorStagedInput
      cvmFamilyStage.postFamily
      cvmCandidate.families.singleton.constructors.singleton
      constructorValidityMatrixType.ctors[0] where
  name_eq := cvmCtorNames_eq
  uvars_eq := rfl
  type := {
    context_eq := cvmConstructorCandidateContext_eq.symm
    source_tr := cvmCtorSource_tr
    whnfFuel := 9999
    whnfDepth := cvmCtorWhnfDepth }

def cvmConstructorsStage :
    VInductDecl.CandidateConstructorStagedListInput
      cvmFamilyStage.postFamily
      cvmCandidate.families.singleton.constructors
      constructorValidityMatrixType.ctors := by
  rw [AddInductive.CandidateList.singleton_eta
    cvmCandidate.families.singleton.constructors, cvmRawCtors_eq]
  exact .cons cvmCtorStagedInput .nil

theorem cvmFamilyTypesProduced :
    AddInductive.CandidateFamilyTypeListProduced cvmFamilyContext
      (.cons cvmCandidate.families.singleton.familyType .nil) := by
  have h := cvmExecution.familyTypes.produced
  rw [AddInductive.CandidateList.singleton_eta
    cvmExecution.familyTypes.candidates] at h
  rw [← cvmExecution.families.produced.singleton_familyType] at h
  simpa [cvmCandidate, cvmFamilyContext,
    AddInductive.NormalizationCandidateExecution.candidate] using h

theorem cvmFamiliesProduced :
    AddInductive.CandidateFamilyListProduced cvmConstructorContext
      (.cons cvmCandidate.families.singleton.familyType .nil)
      cvmCandidate.families := by
  simpa [cvmCandidate, cvmConstructorContext,
    AddInductive.NormalizationCandidateExecution.candidate] using
    cvmExecution.families.produced.singleton_reindex

theorem cvmCheckConstructorsRun :
    AddInductive.checkConstructors #[constructorValidityMatrixKernelType]
        cvmFamilyValidationRun.stats false
        { cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
          env := cvmConstructorContext.env } = .ok () := by
  have h := cvmExecution.constructorRun
  rw [cvmExecutionStats_eq, cvmExecutionValidationContext_eq] at h
  simpa [cvmConstructorContext] using h

/- The CVM D2--D4 stages are reconstructed structurally after the shared
PRB replay helpers below. -/

def prbExecutionResult :=
  AddInductive.buildNormalizationCandidateExecution 1
    [propRecursiveBoundaryKernelType] 0 false
    propRecursiveBoundaryContext

theorem prbExecutionResult_isOk : prbExecutionResult.isOk = true := by
  native_decide

def prbProducedExecution :
    { execution // prbExecutionResult = .ok execution } :=
  match h : prbExecutionResult with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := prbExecutionResult_isOk
      rw [h] at hOk
      contradiction

def prbExecution := prbProducedExecution.val

def prbCandidate := prbExecution.candidate

open TypeChecker in
def prbFamilyIdentityShape :
    CandidateExprIdentityReplay.Shaped propRecursiveBoundaryContext
      propRecursiveBoundaryKernelType.type 2 (.sort .zero) := by
  let aName := propRecursiveBoundaryKernelType.type.bindingBody!.bindingName!
  change CandidateExprIdentityReplay.Shaped propRecursiveBoundaryContext
    (.forallE `α (.sort (.succ (.param `u)))
      (.forallE aName (.bvar 0) (.sort .zero) .default) .default)
    2 (.sort .zero)
  let alphaContext := propRecursiveBoundaryContext.pushLocalDecl
    `α .default (.sort (.succ (.param `u)))
  let alphaAnnotations := AddInductive.builtCandidateTypeAnnotations
    (Expr.sort (.succ (.param `u)))
  refine .forallE (expectedSpineLength := 1)
    propRecursiveBoundaryContext `α
    (.sort (.succ (.param `u)))
    (.forallE aName (.bvar 0) (.sort .zero) .default) .default
    (by rfl) alphaAnnotations
    (AddInductive.buildCandidateTypeAnnotations_built _) (by
      simpa [AddInductive.CandidateTypeAnnotationTrace.build] using
        (AddInductive.CandidateTypeAnnotationTrace.build_consumed
          (.sort (.succ (.param `u)))).symm)
    (.terminal _ _ (by rfl) rfl) ?_
  have alphaFVarWhnf : AddInductive.CandidateWhnfStep.Valid
      ⟨alphaContext, propRecursiveBoundaryContext.freshExpr,
        propRecursiveBoundaryContext.freshExpr⟩ := by
    simpa [alphaContext] using
      TypeChecker.candidateWhnfPushedFVar_refl
        propRecursiveBoundaryContext `α
        (.sort (.succ (.param `u))) .default 9999 (by rfl)
        (by
          change LocalContext.WF ⟨.empty, .empty, .empty⟩
          exact LocalContext.WF.nil)
        (by
          change (⟨.empty, .empty, .empty⟩ : LocalContext).find?
            propRecursiveBoundaryContext.freshFVarId = none
          exact TypeChecker.emptyLocalContextFindNone _)
  have alphaBody : CandidateExprIdentityReplay.Shaped alphaContext
      (.forallE aName propRecursiveBoundaryContext.freshExpr
        (.sort .zero) .default) 1 (.sort .zero) := by
    let aAnnotations := AddInductive.builtCandidateTypeAnnotations
      propRecursiveBoundaryContext.freshExpr
    refine .forallE (expectedSpineLength := 0) alphaContext aName
      propRecursiveBoundaryContext.freshExpr (.sort .zero) .default
      (by rfl) aAnnotations
      (AddInductive.buildCandidateTypeAnnotations_built _) (by
        simpa [AddInductive.Context.freshExpr,
            AddInductive.CandidateTypeAnnotationTrace.build] using
          (AddInductive.CandidateTypeAnnotationTrace.build_consumed
            propRecursiveBoundaryContext.freshExpr).symm)
      (.terminal _ _ alphaFVarWhnf rfl) ?_
    have terminal : CandidateExprIdentityReplay.Shaped
        (alphaContext.pushLocalDecl aName .default
          propRecursiveBoundaryContext.freshExpr)
        (.sort .zero) 0 (.sort .zero) :=
      .terminal _ _ (by rfl) rfl
    simpa [aAnnotations, AddInductive.builtCandidateTypeAnnotations,
      AddInductive.CandidateTypeAnnotationTrace.build,
      AddInductive.Context.freshExpr,
      Expr.instantiate1_eq, Expr.instantiate1'] using terminal
  simpa [alphaContext, alphaAnnotations,
    AddInductive.builtCandidateTypeAnnotations,
    AddInductive.CandidateTypeAnnotationTrace.build,
    Expr.instantiate1_eq, Expr.instantiate1'] using alphaBody

def prbFamilyIdentityReplay :
    TypeChecker.CandidateExprIdentityReplay propRecursiveBoundaryContext
      propRecursiveBoundaryKernelType.type :=
  prbFamilyIdentityShape.replay

theorem prbFamilyCandidateBuild :
    AddInductive.buildCandidateExpr propRecursiveBoundaryKernelType.type
        propRecursiveBoundaryContext =
      .ok prbCandidate.families.singleton.familyType.type := by
  have produced := prbExecution.familyTypes.produced
  rw [AddInductive.CandidateList.singleton_eta
    prbExecution.familyTypes.candidates] at produced
  rw [← prbExecution.families.produced.singleton_familyType] at produced
  have exactProduced : AddInductive.CandidateFamilyTypeListProduced
      propRecursiveBoundaryContext
      (.cons prbCandidate.families.singleton.familyType .nil) := by
    simpa [prbCandidate,
      AddInductive.NormalizationCandidateExecution.candidate,
      propRecursiveBoundaryContext] using produced
  exact exactProduced.singleton_build

theorem prbFamilyIdentityEvidence :
    TypeChecker.CandidateExprIdentityReplay.Evidence
      prbFamilyIdentityReplay
      prbCandidate.families.singleton.familyType.type.trace :=
  prbFamilyIdentityReplay.evidence_of_build prbFamilyCandidateBuild

theorem prbFamilyIdentityReplay_shape :
    prbFamilyIdentityReplay.spineLength = 2 ∧
      prbFamilyIdentityReplay.terminalSource = .sort .zero :=
  ⟨prbFamilyIdentityShape.spineLength_eq,
    prbFamilyIdentityShape.terminalSource_eq⟩

theorem prbFamilyValidationAnnotations :
    prbCandidate.families.singleton.familyType.type.trace
      |>.validationAnnotations := by
  have h := prbExecution.familyTypes.produced
    |>.singleton_validationAnnotations
  rw [← prbExecution.families.produced.singleton_familyType] at h
  simpa [prbCandidate,
    AddInductive.NormalizationCandidateExecution.candidate] using h

private theorem prbFamilyData_hasExprMVar_false :
    propRecursiveBoundaryInfo.type.data.hasExprMVar = false := by
  change propRecursiveBoundaryInfo.type.hasExprMVar = false
  simp [propRecursiveBoundaryInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, Expr.bvar_hasExprMVar_of_le]

private theorem prbFamilyData_hasLevelMVar_false :
    propRecursiveBoundaryInfo.type.data.hasLevelMVar = false := by
  change propRecursiveBoundaryInfo.type.hasLevelMVar = false
  simp [propRecursiveBoundaryInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, Expr.bvar_hasLevelMVar_of_le,
    Level.hasMVar_eq, Level.hasMVar']

private theorem prbFamilyData_hasFVar_false :
    propRecursiveBoundaryInfo.type.data.hasFVar = false := by
  change propRecursiveBoundaryInfo.type.hasFVar = false
  simp [propRecursiveBoundaryInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, Expr.bvar_hasFVar_of_le]

private theorem prbFamily_hasMVar_false :
    propRecursiveBoundaryInfo.type.hasMVar = false := by
  change (propRecursiveBoundaryInfo.type.data.hasExprMVar ||
    propRecursiveBoundaryInfo.type.data.hasLevelMVar) = false
  rw [prbFamilyData_hasExprMVar_false,
    prbFamilyData_hasLevelMVar_false]
  rfl

private theorem prbFamily_hasFVar_false :
    propRecursiveBoundaryInfo.type.hasFVar = false :=
  prbFamilyData_hasFVar_false

theorem prbFamilyClosed :
    prbCandidate.families.singleton.familyType.type.context.env.checkNoMVarNoFVar
        propRecursiveBoundaryKernelType.name
        propRecursiveBoundaryKernelType.type = .ok () := by
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar
  rw [show propRecursiveBoundaryKernelType.type.hasMVar = false by
    simpa [propRecursiveBoundaryKernelType] using
      prbFamily_hasMVar_false]
  rw [show propRecursiveBoundaryKernelType.type.hasFVar = false by
    simpa [propRecursiveBoundaryKernelType] using
      prbFamily_hasFVar_false]
  rfl

theorem prbFamilyEnsureSort :
    TypeChecker.M.run
        prbCandidate.families.singleton.familyType.type.trace.terminalContext.env
        prbCandidate.families.singleton.familyType.type.trace.terminalContext.safety
        prbCandidate.families.singleton.familyType.type.trace.terminalContext.lctx
        prbCandidate.families.singleton.familyType.type.trace.terminalContext.lparams
        prbCandidate.families.singleton.familyType.type.trace.terminalContext.fuel
        (TypeChecker.ensureSort (.sort .zero)) =
      .ok (.sort .zero) := by
  rfl

theorem prbFamilySpineCount :
    1 ≤ prbCandidate.families.singleton.familyType.type.trace.spineLength := by
  rw [prbFamilyIdentityEvidence.spineLength_eq,
    prbFamilyIdentityReplay_shape.1]
  decide

theorem prbFamilySpineFuel :
    prbCandidate.families.singleton.familyType.type.trace.spineLength <
      prbCandidate.families.singleton.familyType.type.context.fuel.inductiveFuel := by
  have contextFuel := congrArg (fun context : AddInductive.Context =>
      context.fuel.inductiveFuel)
    (AddInductive.CandidateExpr.context_eq_of_build prbFamilyCandidateBuild)
  rw [contextFuel]
  rw [prbFamilyIdentityEvidence.spineLength_eq,
    prbFamilyIdentityReplay_shape.1]
  decide

def prbFamilyValidationRun :
    AddInductive.CandidateExprTrace.FamilyValidationRun
      propRecursiveBoundaryKernelType
      prbCandidate.families.singleton.familyType.type.trace where
  nparams := 1
  resultLevel := .zero
  stats :=
    prbCandidate.families.singleton.familyType.type.trace
      |>.singletonCandidateInductiveStats
        propRecursiveBoundaryKernelType 1 .zero
  stats_eq := rfl
  terminal_eq := prbFamilyIdentityEvidence.terminalResult_eq.trans
    prbFamilyIdentityReplay_shape.2
  run := fun k =>
    AddInductive.CandidateExprTrace.checkInductiveTypes_singleton_of_candidate
      propRecursiveBoundaryKernelType
      prbCandidate.families.singleton.familyType.type.trace
      1 .zero k
      prbFamilyClosed prbFamilySpineCount prbFamilySpineFuel
      prbFamilyValidationAnnotations
      (prbFamilyIdentityEvidence.terminalResult_eq.trans
        prbFamilyIdentityReplay_shape.2)
      prbFamilyEnsureSort

theorem prbFamilyContext_eq :
    prbCandidate.families.singleton.familyType.type.context =
      propRecursiveBoundaryContext := by
  have h := prbExecution.familyTypes.produced.singleton_context_eq
  rw [← prbExecution.families.produced.singleton_familyType] at h
  simpa [prbCandidate,
    AddInductive.NormalizationCandidateExecution.candidate,
    propRecursiveBoundaryContext] using h

theorem prbFamilyNparams_eq : prbFamilyValidationRun.nparams = 1 := by
  rfl

theorem prbFamilyValidationRun_exact : ∀ {alpha}
    (k : AddInductive.InductiveStats → AddInductive.M alpha),
    AddInductive.checkInductiveTypes 1 #[propRecursiveBoundaryKernelType]
        k propRecursiveBoundaryContext =
      k prbFamilyValidationRun.stats
        prbCandidate.families.singleton.familyType.type.trace.terminalContext := by
  intro alpha k
  simpa only [prbFamilyNparams_eq, prbFamilyContext_eq] using
    prbFamilyValidationRun.run k

theorem prbAfterValidationRun :
    AddInductive.buildNormalizationCandidateExecutionAfterValidation 1
        [propRecursiveBoundaryKernelType] 0 false
        propRecursiveBoundaryContext prbFamilyValidationRun.stats
        prbCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok prbExecution := by
  have h := prbProducedExecution.property
  change AddInductive.buildNormalizationCandidateExecution 1
      [propRecursiveBoundaryKernelType] 0 false
      propRecursiveBoundaryContext = .ok prbExecution at h
  unfold AddInductive.buildNormalizationCandidateExecution at h
  rw [prbFamilyValidationRun_exact] at h
  exact h

theorem prbExecutionStats_eq :
    prbExecution.stats = prbFamilyValidationRun.stats :=
  (prbExecution.fields_of_afterValidation prbFamilyValidationRun.stats
    prbCandidate.families.singleton.familyType.type.trace.terminalContext
    prbAfterValidationRun).1

theorem prbExecutionValidationContext_eq :
    prbExecution.validationContext =
      prbCandidate.families.singleton.familyType.type.trace.terminalContext :=
  (prbExecution.fields_of_afterValidation prbFamilyValidationRun.stats
    prbCandidate.families.singleton.familyType.type.trace.terminalContext
    prbAfterValidationRun).2

theorem prbExecutionValidationRun : ∀ {alpha}
    (k : AddInductive.InductiveStats → AddInductive.M alpha),
    AddInductive.checkInductiveTypes 1 #[propRecursiveBoundaryKernelType]
        k propRecursiveBoundaryContext =
      k prbExecution.stats prbExecution.validationContext := by
  intro alpha k
  rw [prbFamilyValidationRun_exact, prbExecutionStats_eq,
    prbExecutionValidationContext_eq]

theorem prbCandidate_produced :
    AddInductive.buildNormalizationCandidate 1
        [propRecursiveBoundaryKernelType] 0 false
        propRecursiveBoundaryContext = .ok prbCandidate :=
  prbExecution.produces prbExecutionValidationRun

def prbFamilyContext : AddInductive.Context :=
  { propRecursiveBoundaryContext with lctx := {} }

def prbConstructorContext : AddInductive.Context :=
  { propRecursiveBoundaryContext with
    env := prbExecution.familyEnv, lctx := {} }

theorem prbFamilyCandidateContext_eq :
    prbCandidate.families.singleton.familyType.type.context =
      prbFamilyContext := by
  simpa [prbFamilyContext, propRecursiveBoundaryContext] using
    prbFamilyContext_eq

theorem prbConstructorCandidateContext_eq :
    prbCandidate.families.singleton.constructors.singleton.type.context =
      prbConstructorContext := by
  have h := prbExecution.families.produced.singleton_constructors
    |>.singleton_context_eq
  simpa [prbCandidate,
    AddInductive.NormalizationCandidateExecution.candidate,
    prbConstructorContext] using h

/-- The retained singleton family spine selects exactly its first generated
local as the sole kernel parameter.  This is derived from the structural
identity witness, not by evaluating the opaque outer producer again. -/
theorem prbStatsParams_eq :
    prbFamilyValidationRun.stats.params =
      #[prbFamilyContext.freshExpr] := by
  rw [prbFamilyValidationRun.stats_eq]
  change
    (prbCandidate.families.singleton.familyType.type.trace.parameterList 1).toArray =
      #[prbFamilyContext.freshExpr]
  have identity := prbFamilyIdentityEvidence.identity
  have spineLength := prbFamilyIdentityEvidence.spineLength_eq
  generalize htrace :
    prbCandidate.families.singleton.familyType.type.trace = trace at identity spineLength ⊢
  cases identity with
  | terminal result_eq =>
      simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
      rw [prbFamilyIdentityReplay_shape.1] at spineLength
      omega
  | forallE domainCandidate bodyCandidate source_eq consumed_eq
      domainIdentity bodyIdentity =>
      simp only [AddInductive.CandidateExprTrace.parameterList]
      rw [prbFamilyCandidateContext_eq]

theorem prbFamilyPrefix_ne :
    prbFamilyContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def prbFamilyContextRun :
    TypeChecker.CandidateContextRun prbFamilyContext :=
  TypeChecker.CandidateContextRun.root prbEmptyVEnvsWF rfl
    prbFamilyPrefix_ne

def prbPreFamilyStage :
    TypeChecker.CandidateSemanticStage prbFamilyContext VEnv.empty [`u] where
  contextRun := prbFamilyContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

theorem prbRawFamily_isType :
    VEnv.empty.IsType 1 [] propRecursiveBoundaryType.type := by
  change VEnv.empty.IsType 1 []
    (.forallE (.sort (.succ (.param 0)))
      (.forallE (.bvar 0) (.sort .zero)))
  apply VEnv.IsType.forallE
  · exact ⟨_, VEnv.HasType.sort (by decide)⟩
  · apply VEnv.IsType.forallE
    · exact ⟨_, by type_tac⟩
    · exact ⟨_, VEnv.HasType.sort (by decide)⟩

theorem prbFamilySource_tr :
    TrExprS VEnv.empty [`u] [] propRecursiveBoundaryKernelType.type
      propRecursiveBoundaryType.type := by
  have shape : TrTypeExpr VEnv.empty [`u] []
      propRecursiveBoundaryKernelType.type
      propRecursiveBoundaryType.type := by
    tr_type_expr_tac
  obtain ⟨level, type⟩ := prbRawFamily_isType
  exact shape.to_trExprS .empty trivial ⟨.sort level, type⟩

theorem prbStatsNindices_eq :
    prbFamilyValidationRun.stats.nindices = #[1] := by
  rw [prbFamilyValidationRun.stats_eq]
  change #[prbCandidate.families.singleton.familyType.type.trace.spineLength -
    1] = #[1]
  rw [prbFamilyIdentityEvidence.spineLength_eq,
    prbFamilyIdentityReplay_shape.1]

theorem prbFamilyNames_eq :
    propRecursiveBoundaryKernelType.name =
      propRecursiveBoundaryType.name := by
  decide

theorem prbFamilyNameAbsent :
    propRecursiveBoundaryContext.env.contains
      propRecursiveBoundaryKernelType.name = false := by
  change ({} : ConstMap).contains
    propRecursiveBoundaryKernelType.name = false
  rw [SMap.find?_isSome,
    SMap.WF.find?_eq SMap.WF.empty]
  simp [SMap.toList']

theorem prbFamilyNameNotPrimitive :
    Kernel.Environment.primitives.contains
      propRecursiveBoundaryKernelType.name = false := by
  simp [propRecursiveBoundaryKernelType,
    propRecursiveBoundaryInfo, Kernel.Environment.primitives,
    NameSet.ofList]
  simp +decide [NameSet.contains]

def prbDeclaredInfo : ConstantInfo :=
  .inductInfo <| AddInductive.singletonDeclaredInfo
    prbFamilyValidationRun.stats 1 1 propRecursiveBoundaryKernelType
    0 false
    prbCandidate.families.singleton.familyType.type.trace.terminalContext

theorem prbFamilyMap_add :
    prbExecution.familyEnv.constants =
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.insert
        propRecursiveBoundaryType.name prbDeclaredInfo := by
  have h := prbExecution.declareRun
  rw [prbExecutionStats_eq, prbExecutionValidationContext_eq] at h
  rw [← prbFamilyNames_eq]
  simpa [prbDeclaredInfo] using
    AddInductive.declareInductiveTypes_singleton_constants
      prbFamilyValidationRun.stats 1 1 propRecursiveBoundaryKernelType
      0 false
      prbCandidate.families.singleton.familyType.type.trace.terminalContext
      prbExecution.familyEnv prbStatsNindices_eq h

def prbTypeEnv : VEnv :=
  (VEnv.empty.addConst propRecursiveBoundaryType.name
    propRecursiveBoundaryType.toVConstant).get!

theorem prbTypeEnv_add :
    VEnv.empty.addConst propRecursiveBoundaryType.name
        propRecursiveBoundaryType.toVConstant = some prbTypeEnv := by
  rfl

theorem prbTerminalLparams_eq :
    prbCandidate.families.singleton.familyType.type.trace.terminalContext.lparams =
      propRecursiveBoundaryContext.lparams := by
  calc
    _ = prbCandidate.families.singleton.familyType.type.context.lparams :=
      prbCandidate.families.singleton.familyType.type.trace.terminalContext_lparams
    _ = prbFamilyContext.lparams :=
      congrArg AddInductive.Context.lparams prbFamilyCandidateContext_eq
    _ = propRecursiveBoundaryContext.lparams := rfl

theorem prbTerminalEnv_eq :
    prbCandidate.families.singleton.familyType.type.trace.terminalContext.env =
      propRecursiveBoundaryContext.env := by
  calc
    _ = prbCandidate.families.singleton.familyType.type.context.env :=
      prbCandidate.families.singleton.familyType.type.trace.terminalContext_env
    _ = prbFamilyContext.env :=
      congrArg AddInductive.Context.env prbFamilyCandidateContext_eq
    _ = propRecursiveBoundaryContext.env := rfl

theorem prbConstructorContext_noProjectionReady (name : Name) :
    prbConstructorContext.env.isProjectionReadyStructure name = false := by
  have hConstants :
      prbConstructorContext.env.constants =
        ({} : ConstMap).insert propRecursiveBoundaryType.name
          prbDeclaredInfo := by
    simp only [prbConstructorContext]
    rw [prbFamilyMap_add, prbTerminalEnv_eq]
    rfl
  have hMap :
      (({} : ConstMap).insert propRecursiveBoundaryType.name
        prbDeclaredInfo).WF :=
    SMap.WF.empty.insert _ _ (by simp [SMap.find?])
  by_cases hName : propRecursiveBoundaryType.name = name
  · subst name
    apply Kernel.Environment.isProjectionReadyStructure_false_of_numIndices_ne
      (info := AddInductive.singletonDeclaredInfo
        prbFamilyValidationRun.stats 1 1 propRecursiveBoundaryKernelType
        0 false
        prbCandidate.families.singleton.familyType.type.trace.terminalContext)
    · rw [hConstants, hMap.find?'_eq_find?,
        SMap.WF.find?_insert
          (s := ({} : ConstMap)) SMap.WF.empty]
      simp [prbDeclaredInfo]
    · simp [AddInductive.singletonDeclaredInfo]
  · apply Kernel.Environment.isProjectionReadyStructure_false_of_not_found
    rw [hConstants, hMap.find?'_eq_find?,
      SMap.WF.find?_insert
        (s := ({} : ConstMap)) SMap.WF.empty]
    simp [hName, SMap.find?]

theorem prbConstructorContext_noCtorInfo (name : Name)
    (info : ConstructorVal) :
    prbConstructorContext.env.find? name ≠ some (.ctorInfo info) := by
  intro h
  have hConstants :
      prbConstructorContext.env.constants =
        ({} : ConstMap).insert propRecursiveBoundaryType.name
          prbDeclaredInfo := by
    simp only [prbConstructorContext]
    rw [prbFamilyMap_add, prbTerminalEnv_eq]
    rfl
  have hMap :
      (({} : ConstMap).insert propRecursiveBoundaryType.name
        prbDeclaredInfo).WF :=
    SMap.WF.empty.insert _ _ (by simp [SMap.find?])
  change prbConstructorContext.env.constants.find?' name =
    some (.ctorInfo info) at h
  rw [hConstants, hMap.find?'_eq_find?,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty] at h
  split at h
  · cases h
  · simp [SMap.find?] at h

theorem prbDeclaredInfo_tr :
    TrConstVal .safe VEnv.empty prbDeclaredInfo
      propRecursiveBoundaryType.toVConstVal := by
  refine ⟨⟨by decide, ?_, ?_⟩, rfl⟩
  · change
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.lparams.length =
        propRecursiveBoundaryType.uvars
    rw [prbTerminalLparams_eq]
    rfl
  · change TrExprS VEnv.empty
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.lparams
      [] propRecursiveBoundaryKernelType.type propRecursiveBoundaryType.type
    rw [prbTerminalLparams_eq]
    exact prbFamilySource_tr

def prbAddType :
    AddInductConstant .induct prbFamilyContext.env.constants VEnv.empty
      propRecursiveBoundaryType.toVConstVal
      prbConstructorContext.env.constants prbTypeEnv where
  info := prbDeclaredInfo
  kind_eq := by simp [prbDeclaredInfo, InductConstantKind.Matches]
  tr := prbDeclaredInfo_tr
  map_fresh := by
    change ({} : ConstMap).find?
      propRecursiveBoundaryType.name = none
    rw [SMap.WF.find?_eq SMap.WF.empty]
    simp [SMap.toList']
  env_add := prbTypeEnv_add
  map_add := by
    simpa [prbFamilyContext, prbConstructorContext,
      prbTerminalEnv_eq] using prbFamilyMap_add

theorem prbFamilyWhnfDepth :
    prbCandidate.families.singleton.familyType.type.context.fuel.recDepth =
      9999 + 1 := by
  rw [prbFamilyCandidateContext_eq]
  rfl

def prbFamilyStage :
    VInductDecl.CandidateFamilyStagedInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCandidate.families.singleton.familyType
      propRecursiveBoundaryType prbPreFamilyStage where
  name_eq := prbFamilyNames_eq
  uvars_eq := rfl
  type := {
    context_eq := prbFamilyCandidateContext_eq.symm
    source_tr := prbFamilySource_tr
    whnfFuel := 9999
    whnfDepth := prbFamilyWhnfDepth }
  validation := prbFamilyValidationRun
  typeEnv := prbTypeEnv
  addInduct := prbAddType
  projectionReady := ProjectionResolutionReady.of_no_ctorInfo
    prbConstructorContext_noCtorInfo
  structureEtaReady := StructureEtaReady.of_no_ctorInfo
    prbConstructorContext_noCtorInfo
  family_lctx_eq := rfl
  constructorContext_eq := rfl
  quotInit_eq := by
    have h := prbExecution.declareRun
    rw [prbExecutionStats_eq, prbExecutionValidationContext_eq] at h
    simpa [prbConstructorContext, prbFamilyContext,
      prbTerminalEnv_eq] using
      AddInductive.declareInductiveTypes_singleton_quotInit
        prbFamilyValidationRun.stats 1 1 propRecursiveBoundaryKernelType
        0 false
        prbCandidate.families.singleton.familyType.type.trace.terminalContext
        prbExecution.familyEnv prbStatsNindices_eq h
  name_not_reflected := by decide
  name_not_primitive := by
    rw [← prbFamilyNames_eq]
    exact prbFamilyNameNotPrimitive

def prbCtorAlphaContext := prbConstructorContext.pushLocalDecl `α .implicit
  (.sort (.succ (.param `u)))

def prbCtorAContext := prbCtorAlphaContext.pushLocalDecl `a .default
  prbConstructorContext.freshExpr

def prbCtorNextDomain : Expr :=
  .forallE `b prbConstructorContext.freshExpr
    (.app
      (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
        (.fvar prbConstructorContext.freshFVarId))
      (.bvar 0)) .default

def prbCtorNextContext := prbCtorAContext.pushLocalDecl `next .default
  prbCtorNextDomain

def prbCtorBContext := prbCtorAContext.pushLocalDecl `b .default
  prbConstructorContext.freshExpr

theorem prbCtorFamilyLookup :
    prbConstructorContext.env.find?
        propRecursiveBoundaryKernelType.name =
      some prbDeclaredInfo := by
  change prbExecution.familyEnv.constants.find?'
      propRecursiveBoundaryKernelType.name = some prbDeclaredInfo
  rw [show prbExecution.familyEnv.constants =
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.insert
        propRecursiveBoundaryType.name prbDeclaredInfo from prbFamilyMap_add]
  have hbase :
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.WF := by
    rw [prbTerminalEnv_eq]
    exact SMap.WF.empty
  have hfresh :
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.env.constants.find?
        propRecursiveBoundaryType.name = none := by
    rw [prbTerminalEnv_eq]
    change ({} : ConstMap).find? propRecursiveBoundaryType.name = none
    rw [SMap.WF.find?_eq SMap.WF.empty]
    simp [SMap.toList']
  have hinsert := hbase.insert propRecursiveBoundaryType.name
    prbDeclaredInfo hfresh
  rw [SMap.WF.find?'_eq_find? hinsert]
  rw [hbase.find?_insert]
  simp [prbFamilyNames_eq]

theorem prbCtorFamilyWhnf
    (context : AddInductive.Context)
    (arg1 arg2 : FVarId)
    (henv : context.env = prbConstructorContext.env)
    (hdepth : context.fuel.recDepth = 10000)
    (hwhnf : context.fuel.whnf = 100000)
    (hquot : context.env.quotInit = false) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨context,
        .app
          (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
            (.fvar arg1))
          (.fvar arg2),
        .app
          (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
            (.fvar arg1))
          (.fvar arg2)⟩ := by
  apply TypeChecker.candidateWhnfConstFVarFVar_refl context
    propRecursiveBoundaryKernelType.name [.param `u] arg1 arg2
    (AddInductive.singletonDeclaredInfo
      prbFamilyValidationRun.stats 1 1 propRecursiveBoundaryKernelType
      0 false
      prbCandidate.families.singleton.familyType.type.trace.terminalContext)
  · exact hdepth
  · exact hwhnf
  · exact hquot
  · rw [henv]
    simpa [prbDeclaredInfo] using prbCtorFamilyLookup
  · rfl

theorem prbCtorRootWF : prbConstructorContext.lctx.WF := by
  change LocalContext.WF ⟨.empty, .empty, .empty⟩
  exact LocalContext.WF.nil

theorem prbCtorRootFresh :
    prbConstructorContext.lctx.find?
      prbConstructorContext.freshFVarId = none := by
  change (⟨.empty, .empty, .empty⟩ : LocalContext).find?
    prbConstructorContext.freshFVarId = none
  exact TypeChecker.emptyLocalContextFindNone _

theorem prbCtorAlphaContextWF : prbCtorAlphaContext.lctx.WF := by
  simpa [prbCtorAlphaContext, AddInductive.Context.pushLocalDecl] using
    (LocalContext.WF.mkLocalDecl prbCtorRootWF prbCtorRootFresh)

theorem prbCtorAlphaContextFresh :
    prbCtorAlphaContext.lctx.find?
      prbCtorAlphaContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := prbCtorAlphaContext.freshFVarId) prbCtorAlphaContextWF
  rw [h]
  simp only [prbCtorAlphaContext, prbConstructorContext,
    propRecursiveBoundaryContext, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp [LocalDecl.fvarId, NameGenerator.next, NameGenerator.curr]
  exact LocalContext.WF.nil.decls_wf

theorem prbCtorAlphaFindInA :
    prbCtorAContext.lctx.find? prbConstructorContext.freshFVarId =
      some (.cdecl 0 prbConstructorContext.freshFVarId `α
        (.sort (.succ (.param `u))) .implicit .default) := by
  have hnew := TypeChecker.localContextFindNew
    prbConstructorContext.lctx prbConstructorContext.freshFVarId
    `α (.sort (.succ (.param `u))) .implicit .default
    prbCtorRootWF prbCtorRootFresh
  have hold := TypeChecker.localContextFindOld
      prbCtorAlphaContext.lctx prbConstructorContext.freshFVarId
      prbCtorAlphaContext.freshFVarId `a
      prbConstructorContext.freshExpr .default .default
      (.cdecl prbConstructorContext.lctx.decls.size
        prbConstructorContext.freshFVarId `α
        (.sort (.succ (.param `u))) .implicit .default)
      prbCtorAlphaContextWF prbCtorAlphaContextFresh (by
        simpa [prbCtorAlphaContext, AddInductive.Context.pushLocalDecl]
          using hnew)
  simpa [prbCtorAContext, prbCtorAlphaContext,
    prbConstructorContext, propRecursiveBoundaryContext,
    AddInductive.Context.pushLocalDecl] using hold

open TypeChecker in
def prbCtorIdentityShape :
    CandidateExprIdentityReplay.Shaped prbConstructorContext
      propRecursiveBoundaryKernelCtor.type 3
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId)) := by
  change CandidateExprIdentityReplay.Shaped prbConstructorContext
    (.forallE `α (.sort (.succ (.param `u)))
      (.forallE `a (.bvar 0)
        (.forallE `next
          (.forallE `b (.bvar 1)
            (.app
              (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
                (.bvar 2))
              (.bvar 0)) .default)
          (.app
            (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
              (.bvar 2))
            (.bvar 1)) .default) .default) .implicit)
    3
    (.app
      (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
        (.fvar prbConstructorContext.freshFVarId))
      (.fvar prbCtorAlphaContext.freshFVarId))
  have alphaInAlpha : AddInductive.CandidateWhnfStep.Valid
      ⟨prbCtorAlphaContext, prbConstructorContext.freshExpr,
        prbConstructorContext.freshExpr⟩ := by
    simpa [prbCtorAlphaContext] using
      TypeChecker.candidateWhnfPushedFVar_refl
        prbConstructorContext `α (.sort (.succ (.param `u)))
        .implicit 9999 (by rfl) prbCtorRootWF prbCtorRootFresh
  have alphaInA : AddInductive.CandidateWhnfStep.Valid
      ⟨prbCtorAContext, prbConstructorContext.freshExpr,
        prbConstructorContext.freshExpr⟩ := by
    apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
    · rfl
    · unfold TypeChecker.Inner.isLetFVar
      rw [prbCtorAlphaFindInA]
  have bBody : CandidateExprIdentityReplay.Shaped prbCtorBContext
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAContext.freshFVarId))
      0
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAContext.freshFVarId)) :=
    .terminal _ _ (prbCtorFamilyWhnf _ _ _ rfl rfl rfl (by
      rw [show prbCtorBContext.env = prbConstructorContext.env by rfl]
      rw [prbFamilyStage.quotInit_eq]
      rfl)) rfl
  have nextDomainShape : CandidateExprIdentityReplay.Shaped prbCtorAContext
      prbCtorNextDomain 1
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAContext.freshFVarId)) := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuilt prbCtorAContext `b
      prbConstructorContext.freshExpr
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.bvar 0)) .default (by rfl)
    · simpa [AddInductive.Context.freshExpr,
          AddInductive.CandidateTypeAnnotationTrace.build] using
        (AddInductive.CandidateTypeAnnotationTrace.build_consumed
          prbConstructorContext.freshExpr).symm
    · exact (CandidateExprIdentityReplay.Shaped.terminal
        _ _ alphaInA rfl).replay
    · simpa [prbCtorBContext, prbCtorNextDomain,
        AddInductive.Context.freshExpr,
        Expr.instantiate1_eq, Expr.instantiate1'] using bBody
  have resultShape : CandidateExprIdentityReplay.Shaped prbCtorNextContext
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId))
      0
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId)) :=
    .terminal _ _ (prbCtorFamilyWhnf _ _ _ rfl rfl rfl (by
      rw [show prbCtorNextContext.env = prbConstructorContext.env by rfl]
      rw [prbFamilyStage.quotInit_eq]
      rfl)) rfl
  have nextShape : CandidateExprIdentityReplay.Shaped prbCtorAContext
      (.forallE `next prbCtorNextDomain
        (.app
          (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
            (.fvar prbConstructorContext.freshFVarId))
          (.fvar prbCtorAlphaContext.freshFVarId)) .default)
      1
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId)) := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuilt
      prbCtorAContext `next prbCtorNextDomain
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId)) .default (by rfl)
    · simpa [prbCtorNextDomain,
          AddInductive.Context.freshExpr,
          AddInductive.CandidateTypeAnnotationTrace.build] using
        (AddInductive.CandidateTypeAnnotationTrace.build_consumed
          prbCtorNextDomain).symm
    · exact nextDomainShape.replay
    · simpa [prbCtorNextContext, Expr.instantiate1_eq,
        Expr.instantiate1'] using resultShape
  have aShape : CandidateExprIdentityReplay.Shaped prbCtorAlphaContext
      (.forallE `a prbConstructorContext.freshExpr
        (.forallE `next
          (.forallE `b prbConstructorContext.freshExpr
            (.app
              (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
                (.fvar prbConstructorContext.freshFVarId))
              (.bvar 0)) .default)
          (.app
            (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
              (.fvar prbConstructorContext.freshFVarId))
            (.bvar 1)) .default) .default)
      2
      (.app
        (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
          (.fvar prbConstructorContext.freshFVarId))
        (.fvar prbCtorAlphaContext.freshFVarId)) := by
    apply CandidateExprIdentityReplay.Shaped.forallEBuilt
      prbCtorAlphaContext `a
      prbConstructorContext.freshExpr
      (.forallE `next
        (.forallE `b prbConstructorContext.freshExpr
          (.app
            (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
              (.fvar prbConstructorContext.freshFVarId))
            (.bvar 0)) .default)
          (.app
            (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
              (.fvar prbConstructorContext.freshFVarId))
            (.bvar 1)) .default) .default (by rfl)
    · simpa [AddInductive.Context.freshExpr,
          AddInductive.CandidateTypeAnnotationTrace.build] using
        (AddInductive.CandidateTypeAnnotationTrace.build_consumed
          prbConstructorContext.freshExpr).symm
    · exact (CandidateExprIdentityReplay.Shaped.terminal
        _ _ alphaInAlpha rfl).replay
    · simpa [prbCtorAContext, prbCtorNextDomain,
        AddInductive.Context.freshExpr,
        Expr.instantiate1_eq, Expr.instantiate1',
        Expr.liftLooseBVars_zero] using nextShape
  apply CandidateExprIdentityReplay.Shaped.forallEBuilt
    prbConstructorContext `α
    (.sort (.succ (.param `u)))
    (.forallE `a (.bvar 0)
      (.forallE `next
        (.forallE `b (.bvar 1)
          (.app
            (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
              (.bvar 2))
            (.bvar 0)) .default)
        (.app
          (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
            (.bvar 2))
          (.bvar 1)) .default) .default) .implicit (by rfl)
  · simpa [AddInductive.CandidateTypeAnnotationTrace.build] using
      (AddInductive.CandidateTypeAnnotationTrace.build_consumed
        (.sort (.succ (.param `u)))).symm
  · exact (CandidateExprIdentityReplay.Shaped.terminal
      _ _ (by rfl) rfl).replay
  · simpa [prbCtorAlphaContext, Expr.instantiate1_eq,
      Expr.instantiate1', Expr.liftLooseBVars_zero,
      AddInductive.Context.freshExpr] using aShape

theorem prbCtorCandidateBuild :
    AddInductive.buildCandidateExpr propRecursiveBoundaryKernelCtor.type
        prbConstructorContext =
      .ok prbCandidate.families.singleton.constructors.singleton.type := by
  have produced := prbExecution.families.produced.singleton_constructors
  rw [AddInductive.CandidateList.singleton_eta
    prbExecution.families.candidates.singleton.constructors] at produced
  have exactProduced : AddInductive.CandidateConstructorListProduced
      prbConstructorContext
      (.cons prbCandidate.families.singleton.constructors.singleton .nil) := by
    simpa [prbCandidate,
      AddInductive.NormalizationCandidateExecution.candidate,
      prbConstructorContext, propRecursiveBoundaryKernelType] using produced
  exact exactProduced.singleton_build

def prbCtorIdentityReplay :
    TypeChecker.CandidateExprIdentityReplay prbConstructorContext
      propRecursiveBoundaryKernelCtor.type :=
  prbCtorIdentityShape.replay

theorem prbCtorIdentityEvidence :
    TypeChecker.CandidateExprIdentityReplay.Evidence
      prbCtorIdentityReplay
      prbCandidate.families.singleton.constructors.singleton.type.trace :=
  prbCtorIdentityReplay.evidence_of_build prbCtorCandidateBuild

/-- The structurally identity-normalizing constructor candidate reconstructs
the exact closed kernel constructor type.  In particular, later alignment can
inspect the retained view without a separate computation oracle. -/
theorem prbCtorView_eq :
    prbCandidate.families.singleton.constructors.singleton.type.view =
      propRecursiveBoundaryKernelCtor.type := by
  apply prbCtorIdentityEvidence.identity.view_eq_source
  · apply TypeChecker.CandidateLocalContextRun.empty
    rw [prbConstructorCandidateContext_eq]
    rfl
  · rw [prbConstructorCandidateContext_eq]
    simp [propRecursiveBoundaryKernelCtor,
      propRecursiveBoundaryMkInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, FVarsIn, Level.hasMVar',
      Expr.looseBVarRange']
  · rfl

theorem prbCtorIdentityReplay_shape :
    prbCtorIdentityReplay.spineLength = 3 ∧
      prbCtorIdentityReplay.terminalSource =
        (.app
          (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
            (.fvar prbConstructorContext.freshFVarId))
          (.fvar prbCtorAlphaContext.freshFVarId)) :=
  ⟨prbCtorIdentityShape.spineLength_eq,
    prbCtorIdentityShape.terminalSource_eq⟩

theorem prbTypeEnv_ordered : prbTypeEnv.Ordered :=
  .const (n := propRecursiveBoundaryType.name)
    (ci := propRecursiveBoundaryType.toVConstant)
    .empty prbRawFamily_isType prbTypeEnv_add

theorem prbRawCtor_isType :
    prbTypeEnv.IsType 1 [] propRecursiveBoundaryType.ctors[0].type := by
  have hFamily : prbTypeEnv.constants propRecursiveBoundaryType.name =
      some propRecursiveBoundaryType.toVConstant :=
    VEnv.addConst_self prbTypeEnv_add
  exact ⟨_, by type_tac⟩

theorem prbCtorSource_tr :
    TrExprS prbTypeEnv [`u] [] propRecursiveBoundaryKernelCtor.type
      propRecursiveBoundaryType.ctors[0].type := by
  have shape : TrTypeExpr prbTypeEnv [`u] []
      propRecursiveBoundaryKernelCtor.type
      propRecursiveBoundaryType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨level, type⟩ := prbRawCtor_isType
  exact shape.to_trExprS prbTypeEnv_ordered trivial ⟨.sort level, type⟩

theorem prbCtorNames_eq :
    propRecursiveBoundaryKernelCtor.name =
      propRecursiveBoundaryType.ctors[0].name := by
  decide

theorem prbCtorWhnfDepth :
    prbCandidate.families.singleton.constructors.singleton.type.context.fuel.recDepth =
      9999 + 1 := by
  rw [prbConstructorCandidateContext_eq]
  rfl

theorem prbRawCtors_eq :
    propRecursiveBoundaryType.ctors =
      [propRecursiveBoundaryType.ctors[0]] := by
  rfl

def prbCtorStagedInput :
    VInductDecl.CandidateConstructorStagedInput
      prbFamilyStage.postFamily
      prbCandidate.families.singleton.constructors.singleton
      propRecursiveBoundaryType.ctors[0] where
  name_eq := prbCtorNames_eq
  uvars_eq := rfl
  type := {
    context_eq := prbConstructorCandidateContext_eq.symm
    source_tr := prbCtorSource_tr
    whnfFuel := 9999
    whnfDepth := prbCtorWhnfDepth }

def prbConstructorsStage :
    VInductDecl.CandidateConstructorStagedListInput
      prbFamilyStage.postFamily
      prbCandidate.families.singleton.constructors
      propRecursiveBoundaryType.ctors := by
  rw [AddInductive.CandidateList.singleton_eta
    prbCandidate.families.singleton.constructors, prbRawCtors_eq]
  exact .cons prbCtorStagedInput .nil

theorem prbFamilyTypesProduced :
    AddInductive.CandidateFamilyTypeListProduced prbFamilyContext
      (.cons prbCandidate.families.singleton.familyType .nil) := by
  have h := prbExecution.familyTypes.produced
  rw [AddInductive.CandidateList.singleton_eta
    prbExecution.familyTypes.candidates] at h
  rw [← prbExecution.families.produced.singleton_familyType] at h
  simpa [prbCandidate, prbFamilyContext,
    AddInductive.NormalizationCandidateExecution.candidate] using h

theorem prbFamiliesProduced :
    AddInductive.CandidateFamilyListProduced prbConstructorContext
      (.cons prbCandidate.families.singleton.familyType .nil)
      prbCandidate.families := by
  simpa [prbCandidate, prbConstructorContext,
    AddInductive.NormalizationCandidateExecution.candidate] using
    prbExecution.families.produced.singleton_reindex

theorem prbCheckConstructorsRun :
    AddInductive.checkConstructors #[propRecursiveBoundaryKernelType]
        prbFamilyValidationRun.stats false
        { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
          env := prbConstructorContext.env } = .ok () := by
  have h := prbExecution.constructorRun
  rw [prbExecutionStats_eq, prbExecutionValidationContext_eq] at h
  simpa [prbConstructorContext] using h

theorem prbUniverseRun :
    AddInductive.checkConstructorUniverseListSemantics
        prbFamilyValidationRun.stats propRecursiveBoundaryKernelType.ctors
        { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
          env := prbConstructorContext.env } = .ok () := by
  let validation : AddInductive.ConstructorValidationRun
      propRecursiveBoundaryKernelType prbFamilyValidationRun.stats false
      { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
        env := prbConstructorContext.env } :=
    AddInductive.ConstructorValidationRun.of_run prbCheckConstructorsRun
  apply validation.trace.universeRun_of_semantics
  apply validation.trace.universeSemantics_of_resultLevel_isZero
  rfl

def prbValidationAlphaContext : AddInductive.Context :=
  prbFamilyContext.pushLocalDecl `α .default (.sort (.succ (.param `u)))

def prbValidationAName : Name :=
  propRecursiveBoundaryKernelType.type.bindingBody!.bindingName!

def prbValidationFamilyContext : AddInductive.Context :=
  prbValidationAlphaContext.pushLocalDecl prbValidationAName .default
    prbFamilyContext.freshExpr

theorem prbFamilyTerminalContext_eq :
    prbCandidate.families.singleton.familyType.type.trace.terminalContext =
      prbValidationFamilyContext := by
  have identity := prbFamilyIdentityEvidence.identity
  have spineLength := prbFamilyIdentityEvidence.spineLength_eq
  generalize htrace :
    prbCandidate.families.singleton.familyType.type.trace = trace at identity spineLength ⊢
  cases identity with
  | terminal result_eq =>
      simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
      rw [prbFamilyIdentityReplay_shape.1] at spineLength
      omega
  | forallE domainCandidate bodyCandidate source_eq consumed_eq
      domainIdentity bodyIdentity =>
      simp only [AddInductive.CandidateExprTrace.terminalContext]
      cases bodyIdentity with
      | terminal result_eq =>
          simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
          rw [prbFamilyIdentityReplay_shape.1] at spineLength
          omega
      | forallE domainCandidate' bodyCandidate' source_eq' consumed_eq'
          domainIdentity' bodyIdentity' =>
          cases bodyIdentity' with
          | terminal result_eq =>
              simp only [AddInductive.CandidateExprTrace.terminalContext]
              simp [propRecursiveBoundaryKernelType,
                propRecursiveBoundaryInfo, ConstantInfo.type,
                ConstantInfo.toConstantVal] at source_eq
              rcases source_eq with ⟨rfl, rfl, rfl, rfl⟩
              simp [Expr.instantiate1_eq, Expr.instantiate1'] at source_eq'
              rcases source_eq' with ⟨rfl, rfl, rfl, rfl⟩
              rw [consumed_eq, consumed_eq', prbFamilyCandidateContext_eq]
              rfl
          | forallE domainCandidate'' bodyCandidate'' source_eq'' consumed_eq''
              domainIdentity'' bodyIdentity'' =>
              simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
              rw [prbFamilyIdentityReplay_shape.1] at spineLength
              omega

def prbConstructorValidationContext : AddInductive.Context :=
  { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
    env := prbConstructorContext.env }

theorem prbConstructorValidationContext_eq :
    prbConstructorValidationContext =
      { prbValidationFamilyContext with env := prbConstructorContext.env } := by
  rw [prbConstructorValidationContext, prbFamilyTerminalContext_eq]

theorem prbValidationAlphaLocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationAlphaContext :=
  (TypeChecker.CandidateLocalContextRun.empty prbFamilyContext rfl).push
    `α .default (.sort (.succ (.param `u)))

theorem prbValidationFamilyLocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationFamilyContext :=
  prbValidationAlphaLocalRun.push prbValidationAName .default
    prbFamilyContext.freshExpr

def prbValidationRootContext : AddInductive.Context :=
  { prbValidationFamilyContext with env := prbConstructorContext.env }

theorem prbValidationRootLocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationRootContext where
  wf := prbValidationFamilyLocalRun.wf
  reserves := prbValidationFamilyLocalRun.reserves

def prbValidationAlphaId : FVarId := prbFamilyContext.freshFVarId
def prbValidationAlpha : Expr := prbFamilyContext.freshExpr
def prbValidationIndexId : FVarId := prbValidationAlphaContext.freshFVarId

theorem prbValidationAlphaFind :
    prbValidationRootContext.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  have first :=
    (TypeChecker.CandidateLocalContextRun.empty prbFamilyContext rfl).push_findNew
      `α .default (.sort (.succ (.param `u)))
  have old := prbValidationAlphaLocalRun.push_findOld
    prbValidationAName .default prbFamilyContext.freshExpr first
  simpa [prbValidationRootContext, prbValidationFamilyContext,
    prbValidationAlphaContext, prbValidationAlphaId, prbFamilyContext,
    propRecursiveBoundaryContext, AddInductive.Context.pushLocalDecl] using old

theorem prbValidationIndexFind :
    prbValidationRootContext.lctx.find? prbValidationIndexId =
      some (.cdecl prbValidationAlphaContext.lctx.decls.size
        prbValidationIndexId prbValidationAName
        prbValidationAlpha .default .default) := by
  have found := prbValidationAlphaLocalRun.push_findNew
    prbValidationAName .default prbFamilyContext.freshExpr
  simpa [prbValidationRootContext, prbValidationFamilyContext,
    prbValidationAlphaContext, prbValidationIndexId, prbValidationAlpha,
    prbValidationAlphaId, prbFamilyContext, propRecursiveBoundaryContext,
    AddInductive.Context.pushLocalDecl, AddInductive.Context.freshExpr] using found

theorem prbCandidateCheckTypeFVar
    (context : AddInductive.Context) (id : FVarId) (type : Expr)
    (hdepth : context.fuel.recDepth = 10000)
    (hfind : context.lctx.find? id =
      some (.cdecl index id name type bi kind)) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .fvar id, type⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel (TypeChecker.checkType (.fvar id)) =
      .ok type
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.fvar id) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      ({} : TypeChecker.State)) = .ok type
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange',
    TypeChecker.Inner.inferFVar, AddInductive.Context.toTypeChecker, hfind,
    LocalDecl.type, Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rfl

@[simp] theorem prbValidationAlpha_shape :
    prbValidationAlpha = .fvar prbValidationAlphaId := by
  rfl

theorem prbValidationGetTypeAlpha :
    AddInductive.getType prbValidationAlpha prbValidationRootContext =
      .ok (.sort (.succ (.param `u))) := by
  unfold AddInductive.getType
  simp only [getLCtx, ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  change Except.ok ((prbValidationRootContext.lctx.get!
    prbValidationAlpha.fvarId!).type) = _
  rw [show prbValidationAlpha.fvarId! = prbValidationAlphaId by
    rw [prbValidationAlpha_shape]
    rfl]
  simp [LocalContext.get!, prbValidationAlphaFind, LocalDecl.type]

@[simp] theorem prbValidationCheckLevelSuccParam :
    TypeChecker.Inner.checkLevel prbValidationRootContext.toTypeChecker
      (.succ (.param `u)) = .ok () := by
  simp [TypeChecker.Inner.checkLevel, prbValidationRootContext,
    prbValidationFamilyContext, prbValidationAlphaContext,
    prbFamilyContext, propRecursiveBoundaryContext,
    AddInductive.Context.toTypeChecker, Level.getUndefParam,
    Level.forEach, Level.hasParam_eq, Level.hasParam']
  rfl

theorem prbValidationSortCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationRootContext, .sort (.succ (.param `u)),
        .sort (.succ (.succ (.param `u)))⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run prbValidationRootContext.env
    prbValidationRootContext.safety prbValidationRootContext.lctx
    prbValidationRootContext.lparams prbValidationRootContext.fuel
    (TypeChecker.checkType (.sort (.succ (.param `u)))) = _
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 9999)
      prbValidationRootContext.toTypeChecker
      ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange',
    prbValidationCheckLevelSuccParam, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]
  rfl

def prbValidationSortChecked : AddInductive.ConstructorCheckedExpr
    prbValidationRootContext (.sort (.succ (.param `u))) :=
  .ofRun (by simp [FVarsIn, Level.hasMVar'])
    (by simp [Expr.hasMVar_eq_cache, Level.hasMVar_eq, Level.hasMVar'])
    prbValidationSortCheckValid

def prbValidationFamilyApp (arg : Expr) : Expr :=
  .app
    (.app (.const propRecursiveBoundaryKernelType.name [.param `u])
      prbValidationAlpha)
    arg

def prbValidationNextDomain : Expr :=
  .forallE `b prbValidationAlpha
    (prbValidationFamilyApp (.bvar 0)) .default

def prbValidationAfterParam : Expr :=
  .forallE `a prbValidationAlpha
    (.forallE `next prbValidationNextDomain
      (prbValidationFamilyApp (.bvar 1)) .default) .default

def prbValidationAId : FVarId := prbValidationRootContext.freshFVarId
def prbValidationAExpr : Expr := prbValidationRootContext.freshExpr
def prbValidationAContext : AddInductive.Context :=
  prbValidationRootContext.pushLocalDecl `a .default prbValidationAlpha

def prbValidationAfterA : Expr :=
  .forallE `next prbValidationNextDomain
    (prbValidationFamilyApp prbValidationAExpr) .default

def prbValidationNextContext : AddInductive.Context :=
  prbValidationAContext.pushLocalDecl `next .default prbValidationNextDomain

def prbValidationBId : FVarId := prbValidationAContext.freshFVarId
def prbValidationBExpr : Expr := prbValidationAContext.freshExpr
def prbValidationBContext : AddInductive.Context :=
  prbValidationAContext.pushLocalDecl `b .default prbValidationAlpha

@[simp] theorem prbValidationAExpr_shape :
    prbValidationAExpr = .fvar prbValidationAId := by
  rfl

@[simp] theorem prbValidationBExpr_shape :
    prbValidationBExpr = .fvar prbValidationBId := by
  rfl

def prbValidationTerminal : Expr :=
  prbValidationFamilyApp prbValidationAExpr

def prbValidationTarget : Expr :=
  prbValidationFamilyApp prbValidationBExpr

theorem prbValidationAfterParam_shape :
    (propRecursiveBoundaryKernelCtor.type.bindingBody!.instantiate1
      prbValidationAlpha) = prbValidationAfterParam := by
  simp [propRecursiveBoundaryKernelCtor, propRecursiveBoundaryMkInfo,
    ConstantInfo.type, ConstantInfo.toConstantVal,
    prbValidationAfterParam, prbValidationNextDomain,
    prbValidationFamilyApp, prbValidationAlpha,
    prbFamilyContext, propRecursiveBoundaryContext,
    AddInductive.Context.freshExpr,
    propRecursiveBoundaryKernelType, propRecursiveBoundaryInfo,
    ConstantInfo.name,
    TypeChecker.candidateLiftLooseBVarsFVar,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1',
    Expr.liftLooseBVars_zero]

theorem prbValidationAfterA_shape :
    prbValidationAfterParam.bindingBody!.instantiate1
      prbValidationAExpr = prbValidationAfterA := by
  simp [prbValidationAfterParam, prbValidationAfterA, prbValidationNextDomain,
    prbValidationFamilyApp, prbValidationAExpr, prbValidationRootContext,
    prbValidationFamilyContext, prbValidationAlphaContext, prbFamilyContext,
    propRecursiveBoundaryContext, AddInductive.Context.freshExpr,
    TypeChecker.candidateLiftLooseBVarsFVar, Expr.bindingBody!, Expr.instantiate1_eq,
    Expr.instantiate1']

theorem prbValidationTerminal_shape :
    prbValidationAfterA.bindingBody!.instantiate1
      prbValidationAContext.freshExpr = prbValidationTerminal := by
  simp [prbValidationAfterA, prbValidationTerminal, prbValidationFamilyApp, prbValidationAExpr,
    prbValidationRootContext, prbValidationAContext, prbValidationFamilyContext,
    prbValidationAlphaContext, prbFamilyContext, propRecursiveBoundaryContext,
    AddInductive.Context.freshExpr, Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem prbValidationTarget_shape :
    prbValidationNextDomain.bindingBody!.instantiate1
      prbValidationBExpr = prbValidationTarget := by
  simp [prbValidationNextDomain, prbValidationTarget,
    prbValidationFamilyApp, Expr.bindingBody!,
    Expr.instantiate1_eq, Expr.instantiate1']

theorem prbValidationALocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationAContext :=
  prbValidationRootLocalRun.push `a .default prbValidationAlpha

theorem prbValidationNextLocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationNextContext :=
  prbValidationALocalRun.push `next .default prbValidationNextDomain

theorem prbValidationBLocalRun :
    TypeChecker.CandidateLocalContextRun prbValidationBContext :=
  prbValidationALocalRun.push `b .default prbValidationAlpha

theorem prbValidationAlphaFindInA :
    prbValidationAContext.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) :=
  prbValidationRootLocalRun.push_findOld `a .default prbValidationAlpha
    prbValidationAlphaFind

theorem prbValidationAlphaFindInNext :
    prbValidationNextContext.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) :=
  prbValidationALocalRun.push_findOld `next .default
    prbValidationNextDomain prbValidationAlphaFindInA

theorem prbValidationAlphaFindInB :
    prbValidationBContext.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) :=
  prbValidationALocalRun.push_findOld `b .default prbValidationAlpha
    prbValidationAlphaFindInA

theorem prbValidationAFind :
    prbValidationAContext.lctx.find? prbValidationAId =
      some (.cdecl prbValidationRootContext.lctx.decls.size
        prbValidationAId `a prbValidationAlpha .default .default) := by
  simpa [prbValidationAContext, prbValidationAId, prbValidationAExpr] using
    prbValidationRootLocalRun.push_findNew `a .default prbValidationAlpha

theorem prbValidationAFindInNext :
    prbValidationNextContext.lctx.find? prbValidationAId =
      some (.cdecl prbValidationRootContext.lctx.decls.size
        prbValidationAId `a prbValidationAlpha .default .default) :=
  prbValidationALocalRun.push_findOld `next .default
    prbValidationNextDomain prbValidationAFind

theorem prbValidationAFindInB :
    prbValidationBContext.lctx.find? prbValidationAId =
      some (.cdecl prbValidationRootContext.lctx.decls.size
        prbValidationAId `a prbValidationAlpha .default .default) :=
  prbValidationALocalRun.push_findOld `b .default prbValidationAlpha
    prbValidationAFind

theorem prbValidationBFind :
    prbValidationBContext.lctx.find? prbValidationBId =
      some (.cdecl prbValidationAContext.lctx.decls.size
        prbValidationBId `b prbValidationAlpha .default .default) := by
  simpa [prbValidationBContext, prbValidationBId, prbValidationBExpr] using
    prbValidationALocalRun.push_findNew `b .default prbValidationAlpha

theorem prbValidationRootFresh :
    prbValidationRootContext.lctx.find?
      prbValidationRootContext.freshFVarId = none :=
  prbValidationRootLocalRun.fresh

theorem prbValidationAFresh :
    prbValidationAContext.lctx.find?
      prbValidationAContext.freshFVarId = none :=
  prbValidationALocalRun.fresh

theorem prbValidationNextFresh :
    prbValidationNextContext.lctx.find?
      prbValidationNextContext.freshFVarId = none :=
  prbValidationNextLocalRun.fresh

theorem prbValidationBFresh :
    prbValidationBContext.lctx.find?
      prbValidationBContext.freshFVarId = none :=
  prbValidationBLocalRun.fresh

theorem prbValidationFamilyGet :
    prbConstructorContext.env.get propRecursiveBoundaryKernelType.name =
      .ok prbDeclaredInfo := by
  unfold Kernel.Environment.get
  rw [prbCtorFamilyLookup]
  rfl

@[simp] theorem prbValidationCheckLevelParam
    (context : AddInductive.Context)
    (hlparams : context.lparams = [`u]) :
    TypeChecker.Inner.checkLevel context.toTypeChecker (.param `u) =
      .ok () := by
  simp [TypeChecker.Inner.checkLevel, AddInductive.Context.toTypeChecker,
    hlparams, Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] theorem prbValidationInferConstantFamily
    (context : AddInductive.Context)
    (henv : context.env = prbConstructorContext.env)
    (hlparams : context.lparams = [`u])
    (hsafety : context.safety = .safe) :
    TypeChecker.Inner.inferConstant context.toTypeChecker
        propRecursiveBoundaryKernelType.name [.param `u] false =
      .ok propRecursiveBoundaryKernelType.type := by
  unfold TypeChecker.Inner.inferConstant
  simp only [AddInductive.Context.toTypeChecker]
  rw [henv, prbValidationFamilyGet]
  have terminalLparams :
      prbCandidate.families.singleton.familyType.type.trace.terminalContext.lparams =
        [`u] := by
    rw [prbTerminalLparams_eq]
    rfl
  unfold prbDeclaredInfo AddInductive.singletonDeclaredInfo
  rw [terminalLparams]
  have hlevel : TypeChecker.Inner.checkLevel
      ({ env := prbConstructorContext.env
         lctx := context.lctx
         safety := .safe
         lparams := [`u]
         fuel := context.fuel } : TypeChecker.Context)
      (.param `u) = .ok () := by
    simp [TypeChecker.Inner.checkLevel,
      Level.getUndefParam, Level.forEach,
      Level.hasParam_eq, Level.hasParam']
    rfl
  simp [propRecursiveBoundaryKernelType, propRecursiveBoundaryInfo, ConstantInfo.levelParams,
    ConstantInfo.isUnsafe, ConstantInfo.instantiateTypeLevelParamsCpp,
    ConstantInfo.type, ConstantInfo.toConstantVal,
    Expr.instantiateLevelParamsCpp_eq, hsafety, hlparams,
    hlevel, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [Expr.instantiateLevelParamsCoreCpp', Level.substParamsCpp', ConstantInfo.type,
    ConstantInfo.toConstantVal]

def prbValidationFamilyTail (alpha : Expr) : Expr :=
  .forallE prbValidationAName alpha (.sort .zero) .default

def prbValidationFirstApp (alpha : Expr) : Expr :=
  .app (.const propRecursiveBoundaryKernelType.name [.param `u]) alpha

def prbReplayInsert (state : TypeChecker.State) (source type : Expr) :
    TypeChecker.State :=
  { state with inferTypeC := state.inferTypeC.insert source type }

@[simp] theorem prbEnsureForallExact
    (name : Name) (domain body : Expr) (bi : BinderInfo)
    (source : Expr) (fuel : Nat) (context : TypeChecker.Context)
    (state : TypeChecker.State) :
    TypeChecker.Inner.ensureForallCore (.forallE name domain body bi)
      source (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.forallE name domain body bi, state) := by
  rfl

theorem prbSelfDefEq (source : Expr) fuel context state :
    TypeChecker.Inner.isDefEq source source
      (TypeChecker.Methods.withFuel fuel) context state = .ok (true, state) := by
  unfold TypeChecker.Inner.isDefEq
  rw [if_pos (Expr.eqv_refl _)]
  rfl

@[simp] theorem prbConstBeqFVar (name : Name) (levels : List Level)
    (id : FVarId) :
    ((.const name levels : Expr) == .fvar id) = false := by
  change Expr.eqv (.const name levels) (.fvar id) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem prbAppBeqFVar (fn arg : Expr) (id : FVarId) :
    ((.app fn arg : Expr) == .fvar id) = false := by
  change Expr.eqv (.app fn arg) (.fvar id) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem prbFVarBeqConst (id : FVarId) (name : Name)
    (levels : List Level) :
    ((.fvar id : Expr) == .const name levels) = false := by
  change Expr.eqv (.fvar id) (.const name levels) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem prbFVarBeqApp (id : FVarId) (fn arg : Expr) :
    ((.fvar id : Expr) == .app fn arg) = false := by
  change Expr.eqv (.fvar id) (.app fn arg) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem prbConstBeqApp (name : Name) (levels : List Level)
    (fn arg : Expr) :
    ((.const name levels : Expr) == .app fn arg) = false := by
  change Expr.eqv (.const name levels) (.app fn arg) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] theorem prbAppBeqConst (fn arg : Expr) (name : Name)
    (levels : List Level) :
    ((.app fn arg : Expr) == .const name levels) = false := by
  change Expr.eqv (.app fn arg) (.const name levels) = false
  rw [Expr.eqv_eq]
  rfl

theorem prbInferAppCoreOf
    (fuel : Nat) (context : TypeChecker.Context)
    (state stateFn stateArg : TypeChecker.State)
    (fn arg domain body : Expr) (name : Name) (bi : BinderInfo)
    (hclosed : (.app fn arg : Expr).hasLooseBVars = false)
    (hcache : state.inferTypeC[(.app fn arg : Expr)]? = none)
    (hfn : TypeChecker.Inner.inferType' fn false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.forallE name domain body bi, stateFn))
    (harg : TypeChecker.Inner.inferType' arg false
      (TypeChecker.Methods.withFuel fuel) context stateFn =
        .ok (domain, stateArg))
    (heager : arg.isAppOfArity ``eagerReduce 2 = false) :
    TypeChecker.Inner.inferType' (.app fn arg) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (body.instantiate1 arg,
          { stateArg with inferTypeC :=
              (stateArg.inferTypeC.insert
                (.app fn arg) (body.instantiate1 arg)) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [hclosed, hcache, hfn, harg, heager, prbSelfDefEq, Expr.instantiate1_eq, Bind.bind,
    ReaderT.bind, StateT.bind, Except.bind]

theorem prbInferTypeForallCore
    (fuel : Nat) (context : TypeChecker.Context)
    (state finalState : TypeChecker.State)
    (name : Name) (domain body result : Expr) (bi : BinderInfo)
    (hclosed : (.forallE name domain body bi : Expr).hasLooseBVars = false)
    (hcache : state.inferTypeC[
      (.forallE name domain body bi : Expr)]? = none)
    (hforall : TypeChecker.Inner.inferForall
      (.forallE name domain body bi) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (result, finalState)) :
    TypeChecker.Inner.inferType'
      (.forallE name domain body bi) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (result, { finalState with inferTypeC :=
          (finalState.inferTypeC.insert
            (.forallE name domain body bi) result) }) := by
  unfold TypeChecker.Inner.inferType'
  simp [hclosed, hcache, hforall, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

@[simp] theorem prbMkLevelIMaxSuccParamZero :
    mkLevelIMaxCpp (.succ (.param `u)) .zero = .zero := by
  simp [mkLevelIMaxCpp, mkLevelIMaxCoreCpp, Level.isNeverZero,
    Level.isZero]

def prbValidationConstState (state : TypeChecker.State) : TypeChecker.State :=
  prbReplayInsert state
    (.const propRecursiveBoundaryKernelType.name [.param `u])
    propRecursiveBoundaryKernelType.type

def prbValidationAlphaState (state : TypeChecker.State)
    (alphaId : FVarId) : TypeChecker.State :=
  prbReplayInsert (prbValidationConstState state)
    (.fvar alphaId) (.sort (.succ (.param `u)))

def prbValidationFirstAppState (state : TypeChecker.State)
    (alphaId : FVarId) : TypeChecker.State :=
  prbReplayInsert
    (prbValidationAlphaState state alphaId)
    (prbValidationFirstApp (.fvar alphaId))
    (prbValidationFamilyTail (.fvar alphaId))

def prbValidationArgumentState (state : TypeChecker.State)
    (alphaId argId : FVarId) : TypeChecker.State :=
  prbReplayInsert
    (prbValidationFirstAppState state alphaId)
    (.fvar argId) (.fvar alphaId)

def prbValidationFamilyAppState (state : TypeChecker.State)
    (alphaId argId : FVarId) : TypeChecker.State :=
  prbReplayInsert
    (prbValidationArgumentState state alphaId argId)
    (prbValidationFamilyApp (.fvar argId)) (.sort .zero)

def prbValidationCachedFirstAppState (state : TypeChecker.State)
    (alphaId : FVarId) : TypeChecker.State :=
  prbReplayInsert (prbValidationConstState state)
    (prbValidationFirstApp (.fvar alphaId))
    (prbValidationFamilyTail (.fvar alphaId))

def prbValidationCachedArgumentState (state : TypeChecker.State)
    (alphaId argId : FVarId) : TypeChecker.State :=
  prbReplayInsert (prbValidationCachedFirstAppState state alphaId)
    (.fvar argId) (.fvar alphaId)

def prbValidationCachedFamilyAppState (state : TypeChecker.State)
    (alphaId argId : FVarId) : TypeChecker.State :=
  prbReplayInsert (prbValidationCachedArgumentState state alphaId argId)
    (prbValidationFamilyApp (.fvar argId)) (.sort .zero)

theorem prbWithLocalDeclEq
    {α} (name : Name) (bi : BinderInfo) (type : Expr)
    (k : Expr → TypeChecker.RecM α)
    (methods : TypeChecker.Methods)
    (context : TypeChecker.Context)
    (state : TypeChecker.State) :
    (withLocalDecl (m := TypeChecker.RecM) name bi type k)
        methods context state =
      k (.fvar ⟨state.ngen.curr⟩) methods
        { context with lctx :=
            context.lctx.mkLocalDecl ⟨state.ngen.curr⟩ name type bi }
        { state with ngen := state.ngen.next } := by
  rfl

@[simp] theorem prbEnsureSortExact
    (level : Level) (source : Expr) (fuel : Nat)
    (context : TypeChecker.Context) (state : TypeChecker.State) :
    TypeChecker.Inner.ensureSortCore (.sort level) source
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.sort level, state) := by
  rfl

def prbValidationNextAlphaState : TypeChecker.State :=
  prbReplayInsert ({} : TypeChecker.State) prbValidationAlpha
    (.sort (.succ (.param `u)))

def prbValidationNextInternalBId : FVarId :=
  ⟨prbValidationNextAlphaState.ngen.curr⟩

def prbValidationNextInternalLctx : LocalContext :=
  prbValidationAContext.lctx.mkLocalDecl prbValidationNextInternalBId `b
    prbValidationAlpha .default

def prbValidationNextInternalContext : AddInductive.Context :=
  { prbValidationAContext with lctx := prbValidationNextInternalLctx }

def prbValidationNextBodyState : TypeChecker.State :=
  { prbValidationNextAlphaState with
    ngen := prbValidationNextAlphaState.ngen.next }

theorem prbValidationNextInternalFresh :
    prbValidationAContext.lctx.find? prbValidationNextInternalBId = none := by
  rw [prbValidationALocalRun.wf.find?_eq_find?_toList,
    List.find?_eq_none]
  intro decl membership equal
  simp only [prbValidationAContext,
    AddInductive.Context.pushLocalDecl] at membership
  rw [LocalContext.mkLocalDecl_toList
    prbValidationRootLocalRun.wf.decls_wf] at membership
  simp only [List.mem_cons] at membership
  simp only [prbValidationRootContext, prbValidationFamilyContext,
    AddInductive.Context.pushLocalDecl] at membership
  rw [LocalContext.mkLocalDecl_toList
    prbValidationAlphaLocalRun.wf.decls_wf] at membership
  simp only [List.mem_cons] at membership
  simp only [prbValidationAlphaContext,
    AddInductive.Context.pushLocalDecl] at membership
  rw [LocalContext.mkLocalDecl_toList
    (TypeChecker.CandidateLocalContextRun.empty
      prbFamilyContext rfl).wf.decls_wf] at membership
  simp only [List.mem_cons] at membership
  rw [show prbFamilyContext.lctx.toList = [] by rfl] at membership
  simp only [List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl
  all_goals
    simp [LocalDecl.fvarId, prbValidationNextInternalBId, prbValidationNextAlphaState,
      prbReplayInsert, prbValidationAlpha, prbFamilyContext, propRecursiveBoundaryContext,
      AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId] at equal
  all_goals injection equal
  all_goals simp [NameGenerator.next] at *

theorem prbValidationAlphaFindInternal :
    prbValidationNextInternalContext.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  exact TypeChecker.localContextFindOld prbValidationAContext.lctx
    prbValidationAlphaId prbValidationNextInternalBId `b
    prbValidationAlpha .default .default _ prbValidationALocalRun.wf
    prbValidationNextInternalFresh prbValidationAlphaFindInA

theorem prbValidationNextInternalBFind :
    prbValidationNextInternalContext.lctx.find?
        prbValidationNextInternalBId =
      some (.cdecl prbValidationAContext.lctx.decls.size
        prbValidationNextInternalBId `b prbValidationAlpha
        .default .default) := by
  exact TypeChecker.localContextFindNew prbValidationAContext.lctx
    prbValidationNextInternalBId `b prbValidationAlpha .default .default
    prbValidationALocalRun.wf prbValidationNextInternalFresh

theorem prbValidationAlphaNeNextInternalB :
    prbValidationAlphaId ≠ prbValidationNextInternalBId := by
  intro equal
  have fresh := prbValidationNextInternalFresh
  rw [← equal, prbValidationAlphaFindInA] at fresh
  contradiction

theorem prbValidationAlphaNeA :
    prbValidationAlphaId ≠ prbValidationAId := by
  intro equal
  have fresh : prbValidationRootContext.lctx.find?
      prbValidationAId = none := by
    simpa [prbValidationAId] using prbValidationRootFresh
  rw [← equal, prbValidationAlphaFind] at fresh
  contradiction

theorem prbValidationAlphaNeB :
    prbValidationAlphaId ≠ prbValidationBId := by
  intro equal
  have fresh : prbValidationAContext.lctx.find?
      prbValidationBId = none := by
    simpa [prbValidationBId] using prbValidationAFresh
  rw [← equal, prbValidationAlphaFindInA] at fresh
  contradiction

@[simp] theorem prbValidationConsumeAlpha :
    AddInductive.consumeTypeAnnotations prbValidationAlpha =
      prbValidationAlpha := by
  rw [prbValidationAlpha_shape]
  simp [AddInductive.consumeTypeAnnotations]

@[simp] theorem prbValidationConsumeNextDomain :
    AddInductive.consumeTypeAnnotations prbValidationNextDomain =
      prbValidationNextDomain := by
  simp [prbValidationNextDomain,
    AddInductive.consumeTypeAnnotations]

theorem prbValidationInferTypeFamilyCore
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State)
    (hcache : state.inferTypeC[
      (.const propRecursiveBoundaryKernelType.name [.param `u] : Expr)]? =
        none)
    (henv : context.env = prbConstructorContext.env)
    (hlparams : context.lparams = [`u])
    (hsafety : context.safety = .safe) :
    TypeChecker.Inner.inferType'
        (.const propRecursiveBoundaryKernelType.name [.param `u]) false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (propRecursiveBoundaryKernelType.type,
        prbValidationConstState state) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange', hcache,
    prbValidationConstState, prbReplayInsert,
    prbValidationInferConstantFamily context henv hlparams hsafety,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem prbValidationInferTypeFVarCore
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (id : FVarId) (type : Expr)
    (hcache : state.inferTypeC[(.fvar id : Expr)]? = none)
    (hfind : context.lctx.find? id =
      some (.cdecl index id name type bi kind)) :
    TypeChecker.Inner.inferType' (.fvar id) false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (type, prbReplayInsert state (.fvar id) type) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange', hcache,
    TypeChecker.Inner.inferFVar, AddInductive.Context.toTypeChecker,
    hfind, LocalDecl.type, prbReplayInsert,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem prbValidationInferTypeCachedCore
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (source type : Expr)
    (hclosed : source.hasLooseBVars = false)
    (hcache : state.inferTypeC[source]? = some type) :
    TypeChecker.Inner.inferType' source false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (type, state) := by
  unfold TypeChecker.Inner.inferType'
  simp [hclosed, hcache]

theorem prbValidationInferFirstAppAlphaCachedCore
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (alphaId : FVarId)
    (halpha : state.inferTypeC[(.fvar alphaId : Expr)]? =
      some (.sort (.succ (.param `u))))
    (hconst : state.inferTypeC[
      (.const propRecursiveBoundaryKernelType.name [.param `u] : Expr)]? =
        none)
    (happ : state.inferTypeC[
      prbValidationFirstApp (.fvar alphaId)]? = none)
    (henv : context.env = prbConstructorContext.env)
    (hlparams : context.lparams = [`u])
    (hsafety : context.safety = .safe) :
    TypeChecker.Inner.inferType'
        (prbValidationFirstApp (.fvar alphaId)) false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (prbValidationFamilyTail (.fvar alphaId),
        prbValidationCachedFirstAppState state alphaId) := by
  have constRun := prbValidationInferTypeFamilyCore fuel context state hconst
    henv hlparams hsafety
  have alphaCache : (prbValidationConstState state).inferTypeC[
      (.fvar alphaId : Expr)]? =
        some (.sort (.succ (.param `u))) := by
    simp only [prbValidationConstState, prbReplayInsert,
      Std.HashMap.getElem?_insert]
    rw [prbConstBeqFVar]
    exact halpha
  have alphaRun := prbValidationInferTypeCachedCore fuel context
    (prbValidationConstState state) (.fvar alphaId)
    (.sort (.succ (.param `u)))
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange']) alphaCache
  have appRun := prbInferAppCoreOf fuel context.toTypeChecker state
    (prbValidationConstState state) (prbValidationConstState state)
    (.const propRecursiveBoundaryKernelType.name [.param `u])
    (.fvar alphaId) (.sort (.succ (.param `u)))
    (.forallE prbValidationAName (.bvar 0) (.sort .zero) .default)
    `α .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [Expr.looseBVarRange']) happ
    (by simpa [prbValidationAName, propRecursiveBoundaryKernelType,
      propRecursiveBoundaryInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, Expr.bindingBody!,
      Expr.bindingName!] using constRun)
    alphaRun (by rfl)
  simpa [prbValidationCachedFirstAppState,
    prbValidationFirstApp, prbValidationFamilyTail, prbReplayInsert,
    Expr.instantiate1_eq, Expr.instantiate1'] using appRun

theorem prbValidationNextBodyInferExists :
    ∃ finalState : TypeChecker.State,
      TypeChecker.Inner.inferType'
          (prbValidationFamilyApp
            (.fvar prbValidationNextInternalBId)) false
          (TypeChecker.Methods.withFuel 9998)
          prbValidationNextInternalContext.toTypeChecker
          prbValidationNextBodyState =
        .ok (.sort .zero, finalState) := by
  have alphaCache : prbValidationNextBodyState.inferTypeC[
      (.fvar prbValidationAlphaId : Expr)]? =
        some (.sort (.succ (.param `u))) := by
    simp [prbValidationNextBodyState, prbValidationNextAlphaState,
      prbReplayInsert]
  have constMiss : prbValidationNextBodyState.inferTypeC[
      (.const propRecursiveBoundaryKernelType.name [.param `u] : Expr)]? =
        none := by
    simp only [prbValidationNextBodyState, prbValidationNextAlphaState,
      prbReplayInsert, Std.HashMap.getElem?_insert]
    rw [prbValidationAlpha_shape, prbFVarBeqConst]
    exact Std.HashMap.getElem?_empty
  have firstMiss : prbValidationNextBodyState.inferTypeC[
      prbValidationFirstApp (.fvar prbValidationAlphaId)]? = none := by
    simp only [prbValidationNextBodyState, prbValidationNextAlphaState,
      prbReplayInsert, Std.HashMap.getElem?_insert]
    rw [prbValidationAlpha_shape, prbValidationFirstApp,
      prbFVarBeqApp]
    exact Std.HashMap.getElem?_empty
  have firstRun : TypeChecker.Inner.inferType'
      (prbValidationFirstApp (.fvar prbValidationAlphaId)) false
      (TypeChecker.Methods.withFuel 9998)
      prbValidationNextInternalContext.toTypeChecker
      prbValidationNextBodyState =
        .ok (prbValidationFamilyTail (.fvar prbValidationAlphaId),
          prbValidationCachedFirstAppState
            prbValidationNextBodyState prbValidationAlphaId) := by
    apply prbValidationInferFirstAppAlphaCachedCore
    · exact alphaCache
    · exact constMiss
    · exact firstMiss
    · rfl
    · rfl
    · rfl
  have idBeq : ((.fvar prbValidationAlphaId : Expr) ==
      .fvar prbValidationNextInternalBId) = false := by
    change Expr.eqv (.fvar prbValidationAlphaId)
      (.fvar prbValidationNextInternalBId) = false
    rw [Expr.eqv_eq]
    simp [Expr.eqv', prbValidationAlphaNeNextInternalB]
  have argMiss : (prbValidationCachedFirstAppState
      prbValidationNextBodyState prbValidationAlphaId).inferTypeC[
        (.fvar prbValidationNextInternalBId : Expr)]? = none := by
    simp only [prbValidationCachedFirstAppState,
      prbValidationConstState, prbValidationNextBodyState,
      prbValidationNextAlphaState, prbReplayInsert,
      Std.HashMap.getElem?_insert]
    rw [prbValidationFirstApp, prbAppBeqFVar, prbConstBeqFVar,
      prbValidationAlpha_shape, idBeq]
    exact Std.HashMap.getElem?_empty
  have argRun : TypeChecker.Inner.inferType'
      (.fvar prbValidationNextInternalBId) false
      (TypeChecker.Methods.withFuel 9998)
      prbValidationNextInternalContext.toTypeChecker
      (prbValidationCachedFirstAppState
        prbValidationNextBodyState prbValidationAlphaId) =
        .ok (.fvar prbValidationAlphaId,
          prbValidationCachedArgumentState prbValidationNextBodyState
            prbValidationAlphaId prbValidationNextInternalBId) := by
    simpa [prbValidationCachedArgumentState,
      prbValidationAlpha_shape] using
      prbValidationInferTypeFVarCore 9998
        prbValidationNextInternalContext
        (prbValidationCachedFirstAppState
          prbValidationNextBodyState prbValidationAlphaId)
        prbValidationNextInternalBId (.fvar prbValidationAlphaId)
        argMiss prbValidationNextInternalBFind
  have appMiss : prbValidationNextBodyState.inferTypeC[
      prbValidationFamilyApp
        (.fvar prbValidationNextInternalBId)]? = none := by
    simp only [prbValidationNextBodyState, prbValidationNextAlphaState,
      prbReplayInsert, Std.HashMap.getElem?_insert]
    rw [prbValidationAlpha_shape, prbValidationFamilyApp,
      prbFVarBeqApp]
    exact Std.HashMap.getElem?_empty
  have appRun := prbInferAppCoreOf 9998
    prbValidationNextInternalContext.toTypeChecker
    prbValidationNextBodyState
    (prbValidationCachedFirstAppState
      prbValidationNextBodyState prbValidationAlphaId)
    (prbValidationCachedArgumentState prbValidationNextBodyState
      prbValidationAlphaId prbValidationNextInternalBId)
    (prbValidationFirstApp (.fvar prbValidationAlphaId))
    (.fvar prbValidationNextInternalBId)
    (.fvar prbValidationAlphaId) (.sort .zero)
    prbValidationAName .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [prbValidationFirstApp, Expr.looseBVarRange'])
    appMiss firstRun argRun (by rfl)
  refine ⟨prbValidationCachedFamilyAppState prbValidationNextBodyState
    prbValidationAlphaId prbValidationNextInternalBId, ?_⟩
  simpa [prbValidationFamilyApp, prbValidationFirstApp,
    prbValidationFamilyTail, prbValidationCachedFamilyAppState,
    prbReplayInsert, Expr.instantiate1_eq, Expr.instantiate1'] using appRun

theorem prbValidationNextDomainCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationAContext, prbValidationNextDomain,
        .sort .zero⟩ := by
  obtain ⟨bodyFinalState, bodyRun⟩ :=
    prbValidationNextBodyInferExists
  have domainRun : TypeChecker.Inner.inferType'
      prbValidationAlpha false (TypeChecker.Methods.withFuel 9998)
      prbValidationAContext.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          prbValidationNextAlphaState) := by
    simpa [prbValidationNextAlphaState, prbValidationAlpha_shape] using
      prbValidationInferTypeFVarCore 9998 prbValidationAContext
        ({} : TypeChecker.State) prbValidationAlphaId
        (.sort (.succ (.param `u))) Std.HashMap.getElem?_empty
        prbValidationAlphaFindInA
  have forallRun : TypeChecker.Inner.inferForall
      prbValidationNextDomain false
      (TypeChecker.Methods.withFuel 9999)
      prbValidationAContext.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort .zero, bodyFinalState) := by
    unfold prbValidationNextDomain TypeChecker.Inner.inferForall
    simp only [TypeChecker.Inner.inferForall.loop]
    rw [show prbValidationAlpha.instantiateRev #[] =
        prbValidationAlpha by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType prbValidationAlpha false
        (TypeChecker.Methods.withFuel 9999)
        prbValidationAContext.toTypeChecker ({} : TypeChecker.State) =
          TypeChecker.Inner.inferType' prbValidationAlpha false
            (TypeChecker.Methods.withFuel 9998)
            prbValidationAContext.toTypeChecker
            ({} : TypeChecker.State) by rfl]
    rw [domainRun]
    simp only [prbEnsureSortExact]
    rw [prbWithLocalDeclEq]
    change TypeChecker.Inner.inferForall.loop
      false
      #[Expr.fvar prbValidationNextInternalBId]
      #[Level.succ (.param `u)]
      (prbValidationFamilyApp (.bvar 0))
      (TypeChecker.Methods.withFuel 9999)
      prbValidationNextInternalContext.toTypeChecker
      prbValidationNextBodyState =
        .ok (Expr.sort .zero, bodyFinalState)
    simp only [prbValidationFamilyApp,
      TypeChecker.Inner.inferForall.loop]
    rw [show (((.const propRecursiveBoundaryKernelType.name
          [.param `u] : Expr).app prbValidationAlpha).app (.bvar 0)
          ).instantiateRev #[Expr.fvar prbValidationNextInternalBId] =
          prbValidationFamilyApp
            (.fvar prbValidationNextInternalBId) by
      simp only [Expr.instantiateRev_eq]
      rw [Expr.instantiate_eq _ _ (Or.inr (by
        intro expression membership
        simp at membership
        subst expression
        rfl))]
      simp [prbValidationFamilyApp, Expr.instantiateList,
        Expr.instantiate1']]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType
        (prbValidationFamilyApp
          (.fvar prbValidationNextInternalBId)) false
        (TypeChecker.Methods.withFuel 9999)
        prbValidationNextInternalContext.toTypeChecker
        prbValidationNextBodyState =
          TypeChecker.Inner.inferType'
            (prbValidationFamilyApp
              (.fvar prbValidationNextInternalBId)) false
            (TypeChecker.Methods.withFuel 9998)
            prbValidationNextInternalContext.toTypeChecker
            prbValidationNextBodyState by rfl]
    rw [bodyRun]
    simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
      StateT.pure, Except.pure]
  have outerRun := prbInferTypeForallCore 9999
    prbValidationAContext.toTypeChecker ({} : TypeChecker.State)
    bodyFinalState `b prbValidationAlpha
    (prbValidationFamilyApp (.bvar 0)) (.sort .zero) .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [prbValidationFamilyApp, Expr.looseBVarRange'])
    Std.HashMap.getElem?_empty
    (by simpa [prbValidationNextDomain] using forallRun)
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run prbValidationAContext.env
    prbValidationAContext.safety prbValidationAContext.lctx
    prbValidationAContext.lparams prbValidationAContext.fuel
      (TypeChecker.checkType prbValidationNextDomain) = .ok (.sort .zero)
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' prbValidationNextDomain false
      (TypeChecker.Methods.withFuel 9999)
      prbValidationAContext.toTypeChecker ({} : TypeChecker.State)) =
        .ok (.sort .zero)
  simpa [prbValidationNextDomain, Functor.map, Except.map] using
    congrArg (Except.map (fun x : Expr × TypeChecker.State => x.1)) outerRun

theorem prbValidationInferFirstAppCore
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (alphaId : FVarId)
    (hconst : state.inferTypeC[
      (.const propRecursiveBoundaryKernelType.name [.param `u] : Expr)]? =
        none)
    (halpha : (prbValidationConstState state).inferTypeC[
      (.fvar alphaId : Expr)]? = none)
    (happ : state.inferTypeC[
      prbValidationFirstApp (.fvar alphaId)]? = none)
    (hfind : context.lctx.find? alphaId =
      some (.cdecl index alphaId name
        (.sort (.succ (.param `u))) bi kind))
    (henv : context.env = prbConstructorContext.env)
    (hlparams : context.lparams = [`u])
    (hsafety : context.safety = .safe) :
    TypeChecker.Inner.inferType'
        (prbValidationFirstApp (.fvar alphaId)) false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (prbValidationFamilyTail (.fvar alphaId),
        prbValidationFirstAppState state alphaId) := by
  have constRun := prbValidationInferTypeFamilyCore fuel context state hconst
    henv hlparams hsafety
  have alphaRun := prbValidationInferTypeFVarCore fuel context
    (prbValidationConstState state) alphaId
    (.sort (.succ (.param `u))) halpha hfind
  have appRun := prbInferAppCoreOf fuel context.toTypeChecker state
    (prbValidationConstState state) (prbValidationAlphaState state alphaId)
    (.const propRecursiveBoundaryKernelType.name [.param `u])
    (.fvar alphaId) (.sort (.succ (.param `u)))
    (.forallE prbValidationAName (.bvar 0) (.sort .zero) .default)
    `α .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [Expr.looseBVarRange']) happ
    (by simpa [prbValidationAName, propRecursiveBoundaryKernelType,
      propRecursiveBoundaryInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, Expr.bindingBody!,
      Expr.bindingName!] using constRun)
    (by simpa [prbValidationAlphaState] using alphaRun) (by rfl)
  simpa [prbValidationFirstAppState, prbValidationFirstApp,
    prbValidationFamilyTail, prbReplayInsert,
    Expr.instantiate1_eq, Expr.instantiate1'] using appRun

theorem prbValidationFamilyAppCheckValid
    (context : AddInductive.Context) (alphaId argId : FVarId)
    (hne : alphaId ≠ argId)
    (halphaExpr : (.fvar alphaId : Expr) = prbValidationAlpha)
    (halpha : context.lctx.find? alphaId =
      some (.cdecl alphaIndex alphaId alphaName
        (.sort (.succ (.param `u))) alphaBi alphaKind))
    (harg : context.lctx.find? argId =
      some (.cdecl argIndex argId argName (.fvar alphaId) argBi argKind))
    (henv : context.env = prbConstructorContext.env)
    (hlparams : context.lparams = [`u])
    (hsafety : context.safety = .safe)
    (hdepth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, prbValidationFamilyApp (.fvar argId), .sort .zero⟩ := by
  let initial := ({} : TypeChecker.State)
  have firstRun : TypeChecker.Inner.inferType'
      (prbValidationFirstApp (.fvar alphaId)) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker initial =
      .ok (prbValidationFamilyTail (.fvar alphaId),
        prbValidationFirstAppState initial alphaId) := by
    apply prbValidationInferFirstAppCore
    · simp [initial]
    · simp [initial, prbValidationConstState,
        prbReplayInsert]
    · simp [initial, prbValidationFirstApp]
    · exact halpha
    · exact henv
    · exact hlparams
    · exact hsafety
  have argMiss : (prbValidationFirstAppState initial alphaId).inferTypeC[
      (.fvar argId : Expr)]? = none := by
    have initialMiss : initial.inferTypeC[(.fvar argId : Expr)]? = none := by
      simp [initial]
    have idBeq : ((.fvar alphaId : Expr) == .fvar argId) = false := by
      change Expr.eqv (.fvar alphaId) (.fvar argId) = false
      rw [Expr.eqv_eq]
      simp [Expr.eqv', hne]
    simp [prbValidationFirstAppState, prbValidationAlphaState, prbValidationConstState,
      prbReplayInsert, prbValidationFirstApp, idBeq]
    intro hmem
    have hsome := Std.HashMap.mem_iff_isSome_getElem?.mp hmem
    simp [initialMiss] at hsome
  have argRun : TypeChecker.Inner.inferType' (.fvar argId) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      (prbValidationFirstAppState initial alphaId) =
      .ok (.fvar alphaId,
        prbValidationArgumentState initial alphaId argId) := by
    simpa [prbValidationArgumentState] using
      prbValidationInferTypeFVarCore 9999 context
        (prbValidationFirstAppState initial alphaId) argId
        (.fvar alphaId) argMiss harg
  have appRun := prbInferAppCoreOf 9999 context.toTypeChecker initial
    (prbValidationFirstAppState initial alphaId)
    (prbValidationArgumentState initial alphaId argId)
    (prbValidationFirstApp (.fvar alphaId)) (.fvar argId)
    (.fvar alphaId) (.sort .zero) prbValidationAName .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [prbValidationFirstApp, Expr.looseBVarRange'])
    (by simp [initial]) firstRun argRun (by rfl)
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel
      (TypeChecker.checkType (prbValidationFamilyApp (.fvar argId))) =
        .ok (.sort .zero)
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (prbValidationFamilyApp (.fvar argId))
      false (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State)) = .ok (.sort .zero)
  simpa [prbValidationFamilyApp, prbValidationFirstApp, halphaExpr, initial,
    Expr.instantiate1_eq, Expr.instantiate1', Functor.map, Except.map] using
    congrArg (Except.map (fun x : Expr × TypeChecker.State => x.1)) appRun

theorem prbValidationAlphaRootCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationRootContext, prbValidationAlpha,
        .sort (.succ (.param `u))⟩ := by
  simpa [prbValidationAlpha_shape] using
    prbCandidateCheckTypeFVar prbValidationRootContext
      prbValidationAlphaId (.sort (.succ (.param `u)))
      (by rfl) prbValidationAlphaFind

theorem prbValidationAlphaACheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationAContext, prbValidationAlpha,
        .sort (.succ (.param `u))⟩ := by
  simpa [prbValidationAlpha_shape] using
    prbCandidateCheckTypeFVar prbValidationAContext
      prbValidationAlphaId (.sort (.succ (.param `u)))
      (by rfl) prbValidationAlphaFindInA

theorem prbValidationTerminalCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationNextContext, prbValidationTerminal,
        .sort .zero⟩ := by
  simpa [prbValidationTerminal,
    prbValidationAExpr_shape, prbValidationAlpha_shape] using
    prbValidationFamilyAppCheckValid prbValidationNextContext
      prbValidationAlphaId prbValidationAId
      prbValidationAlphaNeA rfl prbValidationAlphaFindInNext
      prbValidationAFindInNext rfl rfl rfl rfl

theorem prbValidationTargetCheckValid :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨prbValidationBContext, prbValidationTarget,
        .sort .zero⟩ := by
  simpa [prbValidationTarget,
    prbValidationBExpr_shape, prbValidationAlpha_shape] using
    prbValidationFamilyAppCheckValid prbValidationBContext
      prbValidationAlphaId prbValidationBId
      prbValidationAlphaNeB rfl prbValidationAlphaFindInB
      prbValidationBFind rfl rfl rfl rfl

private def prbCheckedOfValid
    (context : AddInductive.Context) (source inferred : Expr)
    (fvars : source.FVarsIn
      (fun fv => (context.lctx.find? fv).isSome = true))
    (noMVar : source.hasMVar = false)
    (valid : AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, source, inferred⟩) :
    AddInductive.ConstructorCheckedExpr context source :=
  .ofRun fvars noMVar valid

private def prbValidationAlphaRootChecked :
    AddInductive.ConstructorCheckedExpr prbValidationRootContext
      prbValidationAlpha :=
  prbCheckedOfValid _ _ _ (by
    rw [prbValidationAlpha_shape]
    change (prbValidationRootContext.lctx.find?
      prbValidationAlphaId).isSome = true
    rw [prbValidationAlphaFind]
    rfl)
    (by simp [prbValidationAlpha_shape, Expr.hasMVar_eq_cache])
    prbValidationAlphaRootCheckValid

private def prbValidationAlphaAChecked :
    AddInductive.ConstructorCheckedExpr prbValidationAContext
      prbValidationAlpha :=
  prbCheckedOfValid _ _ _ (by
    rw [prbValidationAlpha_shape]
    change (prbValidationAContext.lctx.find?
      prbValidationAlphaId).isSome = true
    rw [prbValidationAlphaFindInA]
    rfl)
    (by simp [prbValidationAlpha_shape, Expr.hasMVar_eq_cache])
    prbValidationAlphaACheckValid

private def prbValidationAlphaAConsumedChecked :
    AddInductive.ConstructorCheckedExpr prbValidationAContext
      (AddInductive.consumeTypeAnnotations prbValidationAlpha) :=
  prbCheckedOfValid _ _ (.sort (.succ (.param `u))) (by
    rw [prbValidationConsumeAlpha]
    exact prbValidationAlphaAChecked.fvars)
    (by
      rw [prbValidationConsumeAlpha]
      exact prbValidationAlphaAChecked.noMVar)
    (by simpa only [prbValidationConsumeAlpha] using
      prbValidationAlphaACheckValid)

private def prbValidationNextDomainChecked :
    AddInductive.ConstructorCheckedExpr prbValidationAContext
      prbValidationNextDomain :=
  prbCheckedOfValid _ _ _ (by
    simp [prbValidationNextDomain, prbValidationFamilyApp,
      prbValidationAlpha, FVarsIn, Level.hasMVar']
    change (prbValidationAContext.lctx.find?
      prbValidationAlphaId).isSome = true
    rw [prbValidationAlphaFindInA]
    rfl)
    (by
      simp [prbValidationNextDomain, prbValidationFamilyApp,
        prbValidationAlpha, AddInductive.Context.freshExpr,
        Expr.hasMVar_eq_cache, Level.hasMVar_eq, Level.hasMVar'])
    prbValidationNextDomainCheckValid

private def prbValidationTerminalChecked :
    AddInductive.ConstructorCheckedExpr prbValidationNextContext
      prbValidationTerminal :=
  prbCheckedOfValid _ _ _ (by
    simp [prbValidationTerminal, prbValidationFamilyApp,
      prbValidationAlpha, prbValidationAExpr,
      FVarsIn, Level.hasMVar']
    constructor
    · change (prbValidationNextContext.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbValidationAlphaFindInNext]
      rfl
    · change (prbValidationNextContext.lctx.find?
      prbValidationAId).isSome = true
      rw [prbValidationAFindInNext]
      rfl)
    (by
      simp [prbValidationTerminal, prbValidationFamilyApp,
        prbValidationAlpha, prbValidationAExpr,
        AddInductive.Context.freshExpr, Expr.hasMVar_eq_cache,
        Level.hasMVar_eq, Level.hasMVar'])
    prbValidationTerminalCheckValid

private def prbValidationTargetChecked :
    AddInductive.ConstructorCheckedExpr prbValidationBContext
      prbValidationTarget :=
  prbCheckedOfValid _ _ _ (by
    simp [prbValidationTarget, prbValidationFamilyApp,
      prbValidationAlpha, prbValidationBExpr,
      FVarsIn, Level.hasMVar']
    constructor
    · change (prbValidationBContext.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbValidationAlphaFindInB]
      rfl
    · change (prbValidationBContext.lctx.find?
      prbValidationBId).isSome = true
      rw [prbValidationBFind]
      rfl)
    (by
      simp [prbValidationTarget, prbValidationFamilyApp,
        prbValidationAlpha, prbValidationBExpr,
        AddInductive.Context.freshExpr, Expr.hasMVar_eq_cache,
        Level.hasMVar_eq, Level.hasMVar'])
    prbValidationTargetCheckValid

private theorem prbValidationAlphaRootWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨prbValidationRootContext, prbValidationAlpha,
        prbValidationAlpha⟩ := by
  rw [prbValidationAlpha_shape]
  apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
  · rfl
  · unfold TypeChecker.Inner.isLetFVar
    rw [prbValidationAlphaFind]

private theorem prbValidationAlphaAWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨prbValidationAContext, prbValidationAlpha,
        prbValidationAlpha⟩ := by
  rw [prbValidationAlpha_shape]
  apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
  · rfl
  · unfold TypeChecker.Inner.isLetFVar
    rw [prbValidationAlphaFindInA]

private theorem prbValidationNextDomainWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨prbValidationAContext, prbValidationNextDomain,
        prbValidationNextDomain⟩ := by
  apply TypeChecker.CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
    _ _ 9999
  · rfl
  · rfl

private theorem prbValidationTargetWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨prbValidationBContext, prbValidationTarget,
        prbValidationTarget⟩ := by
  rw [prbValidationTarget, prbValidationFamilyApp,
    prbValidationAlpha_shape, prbValidationBExpr_shape]
  apply prbCtorFamilyWhnf prbValidationBContext prbValidationAlphaId
    prbValidationBId rfl rfl rfl
  rw [show prbValidationBContext.env = prbConstructorContext.env by rfl]
  rw [prbFamilyStage.quotInit_eq]
  rfl

private theorem prbValidationTerminalWhnfSelf :
    AddInductive.CandidateWhnfStep.Valid
      ⟨prbValidationNextContext, prbValidationTerminal,
        prbValidationTerminal⟩ := by
  rw [prbValidationTerminal, prbValidationFamilyApp,
    prbValidationAlpha_shape, prbValidationAExpr_shape]
  apply prbCtorFamilyWhnf prbValidationNextContext prbValidationAlphaId
    prbValidationAId rfl rfl rfl
  rw [show prbValidationNextContext.env = prbConstructorContext.env by rfl]
  rw [prbFamilyStage.quotInit_eq]
  rfl

private theorem prbCandidateWhnfResult_eq
    (self : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (other : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, result⟩) :
    result = source := by
  unfold AddInductive.CandidateWhnfStep.Valid at self other
  rw [self] at other
  exact (Except.ok.inj other).symm

def prbConstructorValidation :
    AddInductive.ConstructorValidationRun propRecursiveBoundaryKernelType
      prbFamilyValidationRun.stats false
      prbConstructorValidationContext :=
  AddInductive.ConstructorValidationRun.of_run (by
    simpa [prbConstructorValidationContext] using prbCheckConstructorsRun)

def prbStagedUniverseInput :
    VInductDecl.StagedNormalizationCandidateUniverseInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCandidate propRecursiveBoundaryDecl where
  staged := {
    raw := propRecursiveBoundaryType
    raw_types_eq := rfl
    declaration_uvars_eq := rfl
    preFamily := prbPreFamilyStage
    family := prbFamilyStage
    validation_nparams_eq := rfl
    constructorValidation := prbConstructorValidation
    constructors := prbConstructorsStage
    familyTypesProduced := prbFamilyTypesProduced
    familiesProduced := prbFamiliesProduced }
  universeRun := by
    simpa [prbFamilyStage, prbConstructorValidationContext] using
      prbUniverseRun

theorem prbStagedStats_eq :
    prbStagedUniverseInput.staged.family.validation.stats =
      prbFamilyValidationRun.stats := by
  rfl

private theorem prbStagedIndConsts_eq :
    prbStagedUniverseInput.staged.family.validation.stats.indConsts =
      #[.const propRecursiveBoundaryKernelType.name [.param `u]] := by
  rw [prbStagedStats_eq, prbFamilyValidationRun.stats_eq]
  simp only [prbFamilyValidationRun,
    AddInductive.CandidateExprTrace.singletonCandidateInductiveStats]
  rw [show
    prbCandidate.families.singleton.familyType.type.context.lparams = [`u] by
      rw [prbFamilyCandidateContext_eq]
      rfl]
  rfl

private theorem prbValidationAlphaHasNoIndOcc :
    AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      prbValidationAlpha = false := by
  rw [prbStagedIndConsts_eq]
  simp [AddInductive.hasIndOcc, prbValidationAlpha_shape]

private theorem prbValidationNextDomainHasIndOcc :
    AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      prbValidationNextDomain = true := by
  rw [prbStagedIndConsts_eq]
  simp [AddInductive.hasIndOcc, prbValidationNextDomain,
    prbValidationFamilyApp, Expr.constName!]

private theorem prbValidationTargetHasIndOcc :
    AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      prbValidationTarget = true := by
  rw [prbStagedIndConsts_eq]
  simp [AddInductive.hasIndOcc, prbValidationTarget,
    prbValidationFamilyApp, Expr.constName!]

private def prbValidationAlphaRootAnnotations :
    AddInductive.CandidateIsDefEqObservation prbValidationRootContext
      prbValidationAlpha prbValidationAlpha :=
  ⟨AddInductive.candidateIsDefEqRefl prbValidationRootContext
    prbValidationAlpha⟩

private def prbValidationAlphaAAnnotations :
    AddInductive.CandidateIsDefEqObservation prbValidationAContext
      prbValidationAlpha prbValidationAlpha :=
  ⟨AddInductive.candidateIsDefEqRefl prbValidationAContext
    prbValidationAlpha⟩

private def prbValidationNextDomainAnnotations :
    AddInductive.CandidateIsDefEqObservation prbValidationAContext
      prbValidationNextDomain prbValidationNextDomain :=
  ⟨AddInductive.candidateIsDefEqRefl prbValidationAContext
    prbValidationNextDomain⟩

private def prbValidationAlphaPositivityAlignment
    (trace : AddInductive.ConstructorPositivityModeTrace
      prbStagedUniverseInput.staged.family.validation.stats false
      propRecursiveBoundaryKernelCtor.name 1 prbValidationRootContext
      prbValidationAlpha) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationAlphaRootWhnfSelf whnf
          subst result
          exact .absent prbValidationAlphaRootChecked
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationAlphaRootWhnfSelf whnf
          have impossible := congrArg Expr.isForall result_eq
          simp [prbValidationAlpha_shape, Expr.isForall] at impossible
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationAlphaRootWhnfSelf whnf
          subst result
          rw [prbValidationAlphaHasNoIndOcc] at occurs
          contradiction

private def prbTransportPositivityTrace
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source fuel) :
    AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context' source' fuel := by
  subst context'
  subst source'
  exact trace

private def prbTransportPositivityAlignment
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source fuel)
    (alignment : AddInductive.ConstructorPositivityAlignmentTrace
      (prbTransportPositivityTrace context_eq source_eq trace)) :
    AddInductive.ConstructorPositivityAlignmentTrace trace := by
  subst context'
  subst source'
  exact alignment

private def prbValidationNextPositivityAlignment
    (trace : AddInductive.ConstructorPositivityModeTrace
      prbStagedUniverseInput.staged.family.validation.stats false
      propRecursiveBoundaryKernelCtor.name 2 prbValidationAContext
      prbValidationNextDomain) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationNextDomainWhnfSelf whnf
          subst result
          rw [prbValidationNextDomainHasIndOcc] at occurs
          contradiction
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationNextDomainWhnfSelf whnf
          change (Expr.forallE name domain body binderInfo) =
            (Expr.forallE `b prbValidationAlpha
              (prbValidationFamilyApp (.bvar 0)) .default) at result_eq
          injection result_eq with name_eq domain_eq body_eq binderInfo_eq
          subst name
          subst domain
          subst body
          subst binderInfo
          have tailContext_eq :
              prbValidationAContext.pushLocalDecl `b .default
                  (AddInductive.consumeTypeAnnotations prbValidationAlpha) =
                prbValidationBContext := by
            rw [prbValidationConsumeAlpha]
            rfl
          have tailSource_eq :
              (prbValidationFamilyApp (.bvar 0)).instantiate1
                  prbValidationAContext.freshExpr =
                prbValidationTarget := by
            simpa [prbValidationNextDomain, Expr.bindingBody!,
              prbValidationBExpr] using prbValidationTarget_shape
          let tailNormalized := prbTransportPositivityTrace
            tailContext_eq tailSource_eq tail
          have tailNormalizedAlignment :
              AddInductive.ConstructorPositivityAlignmentTrace
                tailNormalized := by
            cases htail : tailNormalized with
            | absent context source result fuel whnf occurs =>
                have result_eq := prbCandidateWhnfResult_eq
                  prbValidationTargetWhnfSelf whnf
                subst result
                rw [prbValidationTargetHasIndOcc] at occurs
                contradiction
            | forallE context source fuel name domain body binderInfo whnf
                occurs domainFree tail =>
                have result_eq := prbCandidateWhnfResult_eq
                  prbValidationTargetWhnfSelf whnf
                have impossible := congrArg Expr.isForall result_eq
                simp [prbValidationTarget, prbValidationFamilyApp,
                  Expr.isForall] at impossible
            | target context source result fuel targetIdx whnf occurs
                terminal valid =>
                have result_eq := prbCandidateWhnfResult_eq
                  prbValidationTargetWhnfSelf whnf
                subst result
                exact .target prbValidationTargetChecked
          have tailAlignment := prbTransportPositivityAlignment
            tailContext_eq tailSource_eq tail tailNormalizedAlignment
          exact .forallE prbValidationNextDomainChecked
            prbValidationAlphaAChecked
            prbValidationAlphaAConsumedChecked
            (.succ (.param `u)) rfl prbValidationAFresh
            (by simpa only [prbValidationConsumeAlpha] using
              prbValidationAlphaAAnnotations)
            tail tailAlignment
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have result_eq := prbCandidateWhnfResult_eq
            prbValidationNextDomainWhnfSelf whnf
          subst result
          simp [prbValidationNextDomain, Expr.isForall] at terminal

private def prbTransportValidationTrace
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    AddInductive.ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context' source' argIdx fuel := by
  subst context'
  subst source'
  exact trace

private def prbTransportViewAlignment
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' view view' : Expr}
    (source_eq : source = source') (view_eq : view = view')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel)
    (alignment : AddInductive.ConstructorViewAlignmentTrace
      (prbTransportValidationTrace context_eq source_eq trace) view') :
    AddInductive.ConstructorViewAlignmentTrace trace view := by
  subst context'
  subst source'
  subst view'
  exact alignment

@[simp] private theorem prbTransportValidationTrace_spineLength
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    (prbTransportValidationTrace context_eq source_eq trace).spineLength =
      trace.spineLength := by
  subst context'
  subst source'
  rfl

private def prbTransportValidationTraceIndexed
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    {argIdx argIdx' : Nat} (argIdx_eq : argIdx = argIdx')
    {fuel fuel' : Nat} (fuel_eq : fuel = fuel')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    AddInductive.ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context' source' argIdx' fuel' := by
  subst context'
  subst source'
  subst argIdx'
  subst fuel'
  exact trace

private def prbTransportViewAlignmentIndexed
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' view view' : Expr}
    (source_eq : source = source') (view_eq : view = view')
    {argIdx argIdx' : Nat} (argIdx_eq : argIdx = argIdx')
    {fuel fuel' : Nat} (fuel_eq : fuel = fuel')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel)
    (alignment : AddInductive.ConstructorViewAlignmentTrace
      (prbTransportValidationTraceIndexed context_eq source_eq argIdx_eq
        fuel_eq trace) view') :
    AddInductive.ConstructorViewAlignmentTrace trace view := by
  subst context'
  subst source'
  subst view'
  subst argIdx'
  subst fuel'
  exact alignment

@[simp] private theorem prbTransportValidationTraceIndexed_spineLength
    {context context' : AddInductive.Context}
    (context_eq : context = context')
    {source source' : Expr} (source_eq : source = source')
    {argIdx argIdx' : Nat} (argIdx_eq : argIdx = argIdx')
    {fuel fuel' : Nat} (fuel_eq : fuel = fuel')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    (prbTransportValidationTraceIndexed context_eq source_eq argIdx_eq
      fuel_eq trace).spineLength = trace.spineLength := by
  subst context'
  subst source'
  subst argIdx'
  subst fuel'
  rfl

set_option pp.universes false in
set_option pp.all false in
def prbStagedPostFamilyInput :
    VInductDecl.StagedNormalizationCandidatePostFamilyInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCandidate propRecursiveBoundaryDecl where
  universeInput := prbStagedUniverseInput
  alignment := by
    rw [AddInductive.CandidateList.singleton_eta
      prbCandidate.families.singleton.constructors]
    change AddInductive.ConstructorCandidateAlignmentTrace
      prbStagedUniverseInput.staged.family.validation.stats false 0
      { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
        env := prbConstructorContext.env }
      prbStagedUniverseInput.staged.constructorValidation.trace
      (.cons prbCandidate.families.singleton.constructors.singleton .nil)
    generalize htrace :
      prbStagedUniverseInput.staged.constructorValidation.trace = trace
    cases trace with
    | cons seen head constructors fresh closed rootCheck typeTrace tailTrace =>
      clear htrace
      have rootContext_eq :
          { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
              env := prbConstructorContext.env } =
            prbValidationRootContext := by
        rw [prbFamilyTerminalContext_eq]
        rfl
      have rootFuel_eq :
          { prbCandidate.families.singleton.familyType.type.trace.terminalContext with
              env := prbConstructorContext.env }.fuel.inductiveFuel = 1000 := by
        rw [prbFamilyTerminalContext_eq]
        rfl
      let rootNormalized :
          AddInductive.ConstructorTypeValidationTrace
            prbStagedUniverseInput.staged.family.validation.stats false 0
            propRecursiveBoundaryKernelCtor.name prbValidationRootContext
            propRecursiveBoundaryKernelCtor.type 0 1000 :=
        prbTransportValidationTraceIndexed rootContext_eq (by rfl)
          (by rfl) rootFuel_eq typeTrace
      let rootNormalizedTrace := rootNormalized
      have rootSpine : typeTrace.spineLength =
          rootNormalizedTrace.spineLength := by
        exact (prbTransportValidationTraceIndexed_spineLength rootContext_eq
          (by rfl) (by rfl) rootFuel_eq typeTrace).symm
      cases hroot : rootNormalizedTrace with
      | parameter context fuel argIdx name domain body binderInfo param
          parameterType parameterAt parameterTypeRun defeq tail =>
        simp [hroot,
          AddInductive.ConstructorTypeValidationTrace.spineLength] at rootSpine
        rw [prbStagedStats_eq, prbStatsParams_eq] at parameterAt
        simp at parameterAt
        subst param
        change AddInductive.getType prbValidationAlpha
          prbValidationRootContext = .ok parameterType at parameterTypeRun
        rw [prbValidationGetTypeAlpha] at parameterTypeRun
        injection parameterTypeRun with parameterType_eq
        subst parameterType
        let afterParamNormalized := prbTransportValidationTrace (by rfl)
          prbValidationAfterParam_shape tail
        let afterParamNormalizedTrace := afterParamNormalized
        have afterParamSpine : tail.spineLength =
            afterParamNormalizedTrace.spineLength := by
          exact (prbTransportValidationTrace_spineLength (by rfl)
            prbValidationAfterParam_shape tail).symm
        cases hafterParam : afterParamNormalizedTrace with
        | parameter context fuel argIdx name domain body binderInfo param
            parameterType parameterAt parameterTypeRun defeq tail =>
            rw [prbStagedStats_eq, prbStatsParams_eq] at parameterAt
            simp at parameterAt
        | ordinary context fuel argIdx name domain body binderInfo sortResult
            noParameter ensureType universeTrace positivity afterATrace =>
            simp [hafterParam,
              AddInductive.ConstructorTypeValidationTrace.spineLength]
              at afterParamSpine
            have aContext_eq :
                prbValidationRootContext.pushLocalDecl `a .default
                    (AddInductive.consumeTypeAnnotations
                      prbValidationAlpha) =
                  prbValidationAContext := by
              rw [prbValidationConsumeAlpha]
              rfl
            let afterANormalized :
                AddInductive.ConstructorTypeValidationTrace
                  prbStagedUniverseInput.staged.family.validation.stats
                  false 0 propRecursiveBoundaryKernelCtor.name
                  prbValidationAContext prbValidationAfterA 2 998 :=
              prbTransportValidationTrace aContext_eq
                prbValidationAfterA_shape afterATrace
            let afterANormalizedTrace := afterANormalized
            have afterASpine : afterATrace.spineLength =
                afterANormalizedTrace.spineLength := by
              exact (prbTransportValidationTrace_spineLength aContext_eq
                prbValidationAfterA_shape afterATrace).symm
            cases hafterA : afterANormalizedTrace with
            | parameter context fuel argIdx name domain body binderInfo param
                parameterType parameterAt parameterTypeRun defeq tail =>
                rw [prbStagedStats_eq, prbStatsParams_eq] at parameterAt
                simp at parameterAt
            | ordinary context fuel argIdx name domain body binderInfo
                sortResult noParameter ensureType universeTrace
                nextPositivity terminalTrace =>
                simp [hafterA,
                  AddInductive.ConstructorTypeValidationTrace.spineLength]
                  at afterASpine
                have nextPositivityAlignment :=
                  prbValidationNextPositivityAlignment nextPositivity
                have terminalContext_eq :
                    prbValidationAContext.pushLocalDecl `next .default
                        (AddInductive.consumeTypeAnnotations
                          prbValidationNextDomain) =
                      prbValidationNextContext := by
                  rw [prbValidationConsumeNextDomain]
                  rfl
                let terminalNormalized :
                    AddInductive.ConstructorTypeValidationTrace
                      prbStagedUniverseInput.staged.family.validation.stats
                      false 0 propRecursiveBoundaryKernelCtor.name
                      prbValidationNextContext prbValidationTerminal 3 997 :=
                  prbTransportValidationTrace terminalContext_eq
                    prbValidationTerminal_shape terminalTrace
                let terminalNormalizedTrace := terminalNormalized
                have terminalSpine : terminalTrace.spineLength =
                    terminalNormalizedTrace.spineLength := by
                  exact (prbTransportValidationTrace_spineLength
                    terminalContext_eq prbValidationTerminal_shape
                    terminalTrace).symm
                cases hterminal : terminalNormalizedTrace with
                | terminal context source fuel argIdx terminal valid =>
                    simp [hterminal,
                      AddInductive.ConstructorTypeValidationTrace.spineLength]
                      at terminalSpine
                    have terminalNormalizedAlignment :
                        AddInductive.ConstructorViewAlignmentTrace
                          terminalNormalizedTrace prbValidationTerminal := by
                      rw [hterminal]
                      exact .terminal prbValidationTerminalChecked
                        prbValidationTerminalChecked terminal valid
                    have terminalAlignment := prbTransportViewAlignment
                      terminalContext_eq prbValidationTerminal_shape
                      prbValidationTerminal_shape terminalTrace
                      terminalNormalizedAlignment
                    have afterANormalizedAlignment :
                        AddInductive.ConstructorViewAlignmentTrace
                          afterANormalizedTrace prbValidationAfterA := by
                      rw [hafterA]
                      exact .ordinary prbValidationNextDomainChecked
                        prbValidationNextDomainChecked
                        prbValidationNextDomainAnnotations
                        (by simpa only [prbValidationConsumeNextDomain] using
                          prbValidationNextDomainChecked)
                        nextPositivity nextPositivityAlignment
                        prbValidationAFresh
                        (by simpa only [prbValidationConsumeNextDomain] using
                          prbValidationNextDomainAnnotations)
                        terminalTrace terminalAlignment
                    have afterAAlignment := prbTransportViewAlignment
                      aContext_eq prbValidationAfterA_shape
                      prbValidationAfterA_shape afterATrace
                      afterANormalizedAlignment
                    have afterParamNormalizedAlignment :
                        AddInductive.ConstructorViewAlignmentTrace
                          afterParamNormalizedTrace
                          prbValidationAfterParam := by
                      rw [hafterParam]
                      exact .ordinary prbValidationAlphaRootChecked
                        prbValidationAlphaRootChecked
                        prbValidationAlphaRootAnnotations
                        (by simpa only [prbValidationConsumeAlpha] using
                          prbValidationAlphaRootChecked)
                        positivity
                        (prbValidationAlphaPositivityAlignment positivity)
                        prbValidationRootFresh
                        (by simpa only [prbValidationConsumeAlpha] using
                          prbValidationAlphaRootAnnotations)
                        afterATrace afterAAlignment
                    have afterParamAlignment := prbTransportViewAlignment
                      (by rfl) prbValidationAfterParam_shape
                      prbValidationAfterParam_shape tail
                      afterParamNormalizedAlignment
                    have rootNormalizedAlignment :
                        AddInductive.ConstructorViewAlignmentTrace
                          rootNormalizedTrace
                          propRecursiveBoundaryKernelCtor.type := by
                      rw [hroot]
                      exact .parameter prbValidationSortChecked
                        prbValidationSortChecked prbValidationSortChecked
                        prbValidationAlpha_shape
                        (by rw [prbValidationAlphaFind]; rfl)
                        tail afterParamAlignment
                    have headAlignment := prbTransportViewAlignmentIndexed
                      rootContext_eq (by rfl) prbCtorView_eq (by rfl)
                      rootFuel_eq typeTrace rootNormalizedAlignment
                    let rootScope :
                        AddInductive.ConstructorCheckedExpr
                          ({ prbCandidate.families.singleton.familyType.type.trace.terminalContext with
                            env := prbConstructorContext.env }).withEmptyLocalContext
                          propRecursiveBoundaryKernelCtor.type :=
                      AddInductive.ConstructorCheckedExpr.ofClosedRoot
                        closed rootCheck
                    cases tailTrace with
                    | nil finalSeen =>
                        exact
                          AddInductive.ConstructorCandidateAlignmentTrace.cons
                            rootScope
                            (by
                              change
                                prbCandidate.families.singleton.constructors.singleton.type.trace.storedSpine =
                                  true
                              exact prbCtorIdentityEvidence.identity.storedSpine)
                            (by
                              change
                                prbCandidate.families.singleton.constructors.singleton.type.trace.spineLength =
                                  typeTrace.spineLength
                              have candidateSpine :=
                                prbCtorIdentityEvidence.spineLength_eq.trans
                                  prbCtorIdentityReplay_shape.1
                              omega)
                            (by
                              rw [prbCtorWhnfDepth, rootContext_eq]
                              rfl)
                            headAlignment
                            (AddInductive.ConstructorCandidateAlignmentTrace.nil
                              ((∅ : NameSet).insert
                                propRecursiveBoundaryKernelCtor.name))
            | terminal context source fuel argIdx terminal valid =>
                simp [prbValidationAfterA, Expr.isForall] at terminal
        | terminal context source fuel argIdx terminal valid =>
            simp [prbValidationAfterParam, Expr.isForall] at terminal
      | ordinary context fuel argIdx name domain body binderInfo sortResult
          noParameter ensureType universeTrace positivity tail =>
        rw [prbStagedStats_eq, prbStatsParams_eq] at noParameter
        simp at noParameter
      | terminal context source fuel argIdx terminal valid =>
        simp [propRecursiveBoundaryKernelCtor, propRecursiveBoundaryMkInfo, ConstantInfo.type,
          ConstantInfo.toConstantVal, Expr.isForall] at terminal

def prbPreFamilyContextReplay : AddInductive.Context :=
  prbValidationFamilyContext

def prbPreFamilyAContextReplay : AddInductive.Context :=
  prbPreFamilyContextReplay.pushLocalDecl `a .default prbValidationAlpha

def prbPreFamilyBContextReplay : AddInductive.Context :=
  prbPreFamilyAContextReplay.pushLocalDecl `b .default prbValidationAlpha

def prbPreFamilyResultContextReplay : AddInductive.Context :=
  prbPreFamilyAContextReplay.advanceFresh

def prbPreFamilyIndexTelescopeReplay : Expr :=
  .forallE prbValidationAName prbValidationAlpha (.sort .zero) .default

theorem prbPreFamilyContextReplay_eq :
    prbPreFamilyContextReplay = prbValidationFamilyContext := by
  rfl

theorem prbPreFamilyAContextReplay_eq :
    prbPreFamilyAContextReplay =
      { prbValidationAContext with env := prbPreFamilyContextReplay.env } := by
  rw [prbPreFamilyAContextReplay, prbValidationAContext,
    prbValidationRootContext, prbPreFamilyContextReplay_eq]
  rfl

theorem prbPreFamilyBContextReplay_eq :
    prbPreFamilyBContextReplay =
      { prbValidationBContext with env := prbPreFamilyContextReplay.env } := by
  rw [prbPreFamilyBContextReplay, prbPreFamilyAContextReplay_eq,
    prbValidationBContext]
  rfl

theorem prbPreFamilyResultContextReplay_eq :
    prbPreFamilyResultContextReplay =
      { prbValidationAContext.advanceFresh with
        env := prbPreFamilyContextReplay.env } := by
  rw [prbPreFamilyResultContextReplay, prbPreFamilyAContextReplay_eq]
  rfl

theorem prbFamilyViewReplay_eq :
    prbCandidate.families.singleton.familyType.type.view =
      propRecursiveBoundaryKernelType.type := by
  apply prbFamilyIdentityEvidence.identity.view_eq_source
  · apply TypeChecker.CandidateLocalContextRun.empty
    rw [prbFamilyCandidateContext_eq]
    rfl
  · rw [prbFamilyCandidateContext_eq]
    simp [propRecursiveBoundaryKernelType,
      propRecursiveBoundaryInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, FVarsIn, Level.hasMVar']
  · rfl

theorem prbStagedParamsReplay_eq :
    prbStagedUniverseInput.staged.family.validation.stats.params =
      #[prbValidationAlpha] := by
  rw [prbStagedStats_eq, prbStatsParams_eq]
  rfl

theorem prbStagedNindicesReplay_eq :
    prbStagedUniverseInput.staged.family.validation.stats.nindices = #[1] := by
  rw [prbStagedStats_eq, prbStatsNindices_eq]

theorem prbStagedIndConstsReplay_eq :
    prbStagedUniverseInput.staged.family.validation.stats.indConsts =
      #[.const propRecursiveBoundaryKernelType.name [.param `u]] := by
  rw [prbStagedStats_eq, prbFamilyValidationRun.stats_eq]
  simp only [prbFamilyValidationRun,
    AddInductive.CandidateExprTrace.singletonCandidateInductiveStats]
  rw [show
    prbCandidate.families.singleton.familyType.type.context.lparams = [`u] by
      rw [prbFamilyCandidateContext_eq]
      rfl]
  rfl

def prbPreFamilyFVarInferOnlyStateReplay
    (id : FVarId) (type : Expr) : TypeChecker.State :=
  { ({} : TypeChecker.State) with
    inferTypeI := ({} : TypeChecker.State).inferTypeI.insert
      (.fvar id) type }

theorem prbPreFamilyFVarInferOnlyReplay
    (context : AddInductive.Context) (id : FVarId) (type : Expr)
    (find : context.lctx.find? id =
      some (.cdecl index id name type bi kind))
    (depth : context.fuel.recDepth = 10000) :
    TypeChecker.Inner.inferType (.fvar id) true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (type, prbPreFamilyFVarInferOnlyStateReplay id type) := by
  rw [depth]
  change TypeChecker.Inner.inferType' (.fvar id) true
    (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
    ({} : TypeChecker.State) = _
  unfold TypeChecker.Inner.inferType'
  simp [prbPreFamilyFVarInferOnlyStateReplay,
    Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange',
    TypeChecker.Inner.inferFVar, AddInductive.Context.toTypeChecker,
    find, LocalDecl.type, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem prbPreFamilyFVarEnsureValidReplay
    (context : AddInductive.Context) (id : FVarId) (level : Level)
    (find : context.lctx.find? id =
      some (.cdecl index id name (.sort level) bi kind))
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨context, .fvar id, .sort level⟩ := by
  unfold AddInductive.ConstructorEnsureTypeStep.Valid
    TypeChecker.ensureType TypeChecker.inferType TypeChecker.ensureSort
    TypeChecker.RecM.run TypeChecker.M.run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, StateT.run',
    Functor.map, Except.map]
  rw [show TypeChecker.Inner.inferType (.fvar id) true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      { env := context.env, lctx := context.lctx,
        safety := context.safety, lparams := context.lparams,
        fuel := context.fuel }
      ({} : TypeChecker.State) =
        .ok (.sort level,
          prbPreFamilyFVarInferOnlyStateReplay id (.sort level)) by
    simpa [AddInductive.Context.toTypeChecker] using
      prbPreFamilyFVarInferOnlyReplay context id (.sort level) find depth]
  rfl

theorem prbPreFamilyCheckLevelSuccParamReplay
    (context : AddInductive.Context)
    (lparams : context.lparams = [`u]) :
    TypeChecker.Inner.checkLevel context.toTypeChecker
      (.succ (.param `u)) = .ok () := by
  simp [TypeChecker.Inner.checkLevel, AddInductive.Context.toTypeChecker,
    lparams, Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

theorem prbPreFamilySortCheckValidReplay
    (context : AddInductive.Context)
    (lparams : context.lparams = [`u])
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .sort (.succ (.param `u)),
        .sort (.succ (.succ (.param `u)))⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel
    (TypeChecker.checkType (.sort (.succ (.param `u)))) = _
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [depth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange',
    prbPreFamilyCheckLevelSuccParamReplay context lparams,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rfl

theorem prbPreFamilySortZeroCheckValidReplay
    (context : AddInductive.Context)
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, .sort .zero, .sort (.succ .zero)⟩ := by
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel (TypeChecker.checkType (.sort .zero)) = _
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [depth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.sort .zero) false
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange',
    TypeChecker.Inner.checkLevel, Level.getUndefParam,
    Level.hasParam_eq,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rfl

@[simp] theorem prbPreFamilyCheckLevelZeroReplay
    (context : TypeChecker.Context) :
    TypeChecker.Inner.checkLevel context .zero = .ok () := by
  simp [TypeChecker.Inner.checkLevel, Level.getUndefParam,
    Level.forEach, Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] theorem prbFVarBeqSortReplay (id : FVarId) (level : Level) :
    ((.fvar id : Expr) == .sort level) = false := by
  change Expr.eqv (.fvar id) (.sort level) = false
  rw [Expr.eqv_eq]
  rfl

def prbPreFamilyTelescopeAlphaStateReplay : TypeChecker.State :=
  prbReplayInsert ({} : TypeChecker.State) prbValidationAlpha
    (.sort (.succ (.param `u)))

def prbPreFamilyTelescopeInternalIdReplay : FVarId :=
  ⟨prbPreFamilyTelescopeAlphaStateReplay.ngen.curr⟩

def prbPreFamilyTelescopeInternalStateReplay : TypeChecker.State :=
  { prbPreFamilyTelescopeAlphaStateReplay with
    ngen := prbPreFamilyTelescopeAlphaStateReplay.ngen.next }

def prbPreFamilyTelescopeFinalStateReplay : TypeChecker.State :=
  prbReplayInsert prbPreFamilyTelescopeInternalStateReplay
    (.sort .zero) (.sort (.succ .zero))

theorem prbPreFamilyInferSortZeroCoreReplay
    (fuel : Nat) (context : TypeChecker.Context)
    (state : TypeChecker.State)
    (miss : state.inferTypeC[(.sort .zero : Expr)]? = none) :
    TypeChecker.Inner.inferType' (.sort .zero) false
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (.sort (.succ .zero),
          prbReplayInsert state (.sort .zero) (.sort (.succ .zero))) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange', miss, prbReplayInsert, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

theorem prbPreFamilyIndexTelescopeCheckValidReplay
    (context : AddInductive.Context)
    (alphaFind : context.lctx.find? prbValidationAlphaId =
      some (.cdecl alphaIndex prbValidationAlphaId alphaName
        (.sort (.succ (.param `u))) alphaBi alphaKind))
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, prbPreFamilyIndexTelescopeReplay,
        .sort (mkLevelIMaxCpp (.succ (.param `u)) (.succ .zero))⟩ := by
  have domainRun : TypeChecker.Inner.inferType'
      prbValidationAlpha false (TypeChecker.Methods.withFuel 9998)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          prbPreFamilyTelescopeAlphaStateReplay) := by
    simpa [prbPreFamilyTelescopeAlphaStateReplay,
      prbValidationAlpha_shape] using
      prbValidationInferTypeFVarCore 9998 context
        ({} : TypeChecker.State) prbValidationAlphaId
        (.sort (.succ (.param `u))) Std.HashMap.getElem?_empty alphaFind
  have bodyMiss : prbPreFamilyTelescopeInternalStateReplay.inferTypeC[
      (.sort .zero : Expr)]? = none := by
    simp [prbPreFamilyTelescopeInternalStateReplay,
      prbPreFamilyTelescopeAlphaStateReplay, prbReplayInsert,
      prbValidationAlpha_shape]
  have bodyRun : TypeChecker.Inner.inferType'
      (.sort .zero) false (TypeChecker.Methods.withFuel 9998)
      { context.toTypeChecker with
        lctx := context.lctx.mkLocalDecl
          prbPreFamilyTelescopeInternalIdReplay prbValidationAName
          prbValidationAlpha .default }
      prbPreFamilyTelescopeInternalStateReplay =
        .ok (.sort (.succ .zero),
          prbPreFamilyTelescopeFinalStateReplay) := by
    simpa [prbPreFamilyTelescopeFinalStateReplay] using
      prbPreFamilyInferSortZeroCoreReplay 9998 _
        prbPreFamilyTelescopeInternalStateReplay bodyMiss
  have forallRun : TypeChecker.Inner.inferForall
      prbPreFamilyIndexTelescopeReplay false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort
          (mkLevelIMaxCpp (.succ (.param `u)) (.succ .zero)),
          prbPreFamilyTelescopeFinalStateReplay) := by
    unfold prbPreFamilyIndexTelescopeReplay TypeChecker.Inner.inferForall
    simp only [TypeChecker.Inner.inferForall.loop]
    rw [show prbValidationAlpha.instantiateRev #[] =
        prbValidationAlpha by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType prbValidationAlpha false
        (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
        ({} : TypeChecker.State) =
          TypeChecker.Inner.inferType' prbValidationAlpha false
            (TypeChecker.Methods.withFuel 9998) context.toTypeChecker
            ({} : TypeChecker.State) by rfl]
    rw [domainRun]
    simp only [prbEnsureSortExact]
    rw [prbWithLocalDeclEq]
    change TypeChecker.Inner.inferForall.loop false
      #[Expr.fvar prbPreFamilyTelescopeInternalIdReplay]
      #[Level.succ (.param `u)] (.sort .zero)
      (TypeChecker.Methods.withFuel 9999)
      { context.toTypeChecker with
        lctx := context.lctx.mkLocalDecl
          prbPreFamilyTelescopeInternalIdReplay prbValidationAName
          prbValidationAlpha .default }
      prbPreFamilyTelescopeInternalStateReplay = _
    simp only [TypeChecker.Inner.inferForall.loop]
    rw [show (.sort .zero : Expr).instantiateRev
        #[Expr.fvar prbPreFamilyTelescopeInternalIdReplay] =
          .sort .zero by
      simp only [Expr.instantiateRev_eq]
      exact Expr.instantiate_eq_self (by rfl)]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType (.sort .zero) false
        (TypeChecker.Methods.withFuel 9999) _
        prbPreFamilyTelescopeInternalStateReplay =
          TypeChecker.Inner.inferType' (.sort .zero) false
            (TypeChecker.Methods.withFuel 9998) _
            prbPreFamilyTelescopeInternalStateReplay by rfl]
    rw [bodyRun]
    simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
      StateT.pure, Except.pure]
  have outerRun := prbInferTypeForallCore 9999 context.toTypeChecker
    ({} : TypeChecker.State) prbPreFamilyTelescopeFinalStateReplay
    prbValidationAName prbValidationAlpha (.sort .zero)
    (.sort (mkLevelIMaxCpp (.succ (.param `u)) (.succ .zero)))
    .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [prbValidationAlpha_shape, Expr.looseBVarRange'])
    Std.HashMap.getElem?_empty forallRun
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel
      (TypeChecker.checkType prbPreFamilyIndexTelescopeReplay) = _
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [depth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' prbPreFamilyIndexTelescopeReplay false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      ({} : TypeChecker.State)) = _
  simpa [prbPreFamilyIndexTelescopeReplay,
    Functor.map, Except.map] using
    congrArg (Except.map (fun x : Expr × TypeChecker.State => x.1))
      outerRun

theorem prbPreFamilyAlphaFindReplay :
    prbPreFamilyContextReplay.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  rw [prbPreFamilyContextReplay_eq]
  simpa [prbValidationRootContext] using prbValidationAlphaFind

theorem prbPreFamilyAlphaFindInAReplay :
    prbPreFamilyAContextReplay.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  rw [prbPreFamilyAContextReplay_eq]
  exact prbValidationAlphaFindInA

theorem prbPreFamilyAlphaFindInBReplay :
    prbPreFamilyBContextReplay.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  rw [prbPreFamilyBContextReplay_eq]
  exact prbValidationAlphaFindInB

theorem prbPreFamilyAlphaFindInResultReplay :
    prbPreFamilyResultContextReplay.lctx.find? prbValidationAlphaId =
      some (.cdecl 0 prbValidationAlphaId `α
        (.sort (.succ (.param `u))) .default .default) := by
  rw [prbPreFamilyResultContextReplay_eq]
  simpa [AddInductive.Context.advanceFresh] using
    prbValidationAlphaFindInA

theorem prbPreFamilyAFindInResultReplay :
    prbPreFamilyResultContextReplay.lctx.find? prbValidationAId =
      some (.cdecl prbValidationRootContext.lctx.decls.size
        prbValidationAId `a prbValidationAlpha .default .default) := by
  rw [prbPreFamilyResultContextReplay_eq]
  simpa [AddInductive.Context.advanceFresh] using prbValidationAFind

theorem prbPreFamilyBFindReplay :
    prbPreFamilyBContextReplay.lctx.find? prbValidationBId =
      some (.cdecl prbValidationAContext.lctx.decls.size
        prbValidationBId `b prbValidationAlpha .default .default) := by
  rw [prbPreFamilyBContextReplay_eq]
  exact prbValidationBFind

theorem prbPreFamilyRootFreshReplay :
    prbPreFamilyContextReplay.lctx.find?
      prbPreFamilyContextReplay.freshFVarId = none := by
  rw [prbPreFamilyContextReplay_eq]
  simpa [prbValidationRootContext,
    AddInductive.Context.freshFVarId] using prbValidationRootFresh

theorem prbPreFamilyAFreshReplay :
    prbPreFamilyAContextReplay.lctx.find?
      prbPreFamilyAContextReplay.freshFVarId = none := by
  rw [prbPreFamilyAContextReplay_eq]
  exact prbValidationAFresh

theorem prbPreFamilyBFreshReplay :
    prbPreFamilyBContextReplay.lctx.find?
      prbPreFamilyBContextReplay.freshFVarId = none := by
  rw [prbPreFamilyBContextReplay_eq]
  exact prbValidationBFresh

theorem prbPreFamilyRootDepthReplay :
    prbPreFamilyContextReplay.fuel.recDepth = 10000 := by
  rw [prbPreFamilyContextReplay_eq]
  rfl

theorem prbPreFamilyADepthReplay :
    prbPreFamilyAContextReplay.fuel.recDepth = 10000 := by
  rw [prbPreFamilyAContextReplay_eq]
  rfl

theorem prbPreFamilyBDepthReplay :
    prbPreFamilyBContextReplay.fuel.recDepth = 10000 := by
  rw [prbPreFamilyBContextReplay_eq]
  rfl

theorem prbPreFamilyResultDepthReplay :
    prbPreFamilyResultContextReplay.fuel.recDepth = 10000 := by
  rw [prbPreFamilyResultContextReplay_eq]
  rfl

theorem prbPreFamilyRootInductiveFuelReplay :
    prbPreFamilyContextReplay.fuel.inductiveFuel = 1000 := by
  rw [prbPreFamilyContextReplay_eq]
  rfl

theorem prbPreFamilyAInductiveFuelReplay :
    prbPreFamilyAContextReplay.fuel.inductiveFuel = 1000 := by
  rw [prbPreFamilyAContextReplay_eq]
  rfl

theorem prbPreFamilyAFreshExprReplay :
    prbPreFamilyAContextReplay.freshExpr = prbValidationBExpr := by
  rw [prbPreFamilyAContextReplay_eq]
  rfl

theorem prbPreFamilyRootFreshExprReplay :
    prbPreFamilyContextReplay.freshExpr = prbValidationAExpr := by
  rfl

theorem prbPreFamilyAlphaHasNoIndOccReplay :
    AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      prbValidationAlpha = false := by
  rw [prbStagedIndConstsReplay_eq]
  simp [AddInductive.hasIndOcc, prbValidationAlpha_shape]

theorem prbPreFamilyNextDomainHasIndOccReplay :
    AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      prbValidationNextDomain = true := by
  rw [prbStagedIndConstsReplay_eq]
  simp [AddInductive.hasIndOcc, prbValidationNextDomain,
    prbValidationFamilyApp, Expr.constName!]

@[simp] theorem prbValidationFamilyAppGetAppFnReplay (arg : Expr) :
    (prbValidationFamilyApp arg).getAppFn =
      .const propRecursiveBoundaryKernelType.name [.param `u] := by
  rfl

@[simp] theorem prbValidationFamilyAppGetAppArgsReplay (arg : Expr) :
    (prbValidationFamilyApp arg).getAppArgs =
      #[prbValidationAlpha, arg] := by
  rfl

@[simp] theorem prbExprBneSelfReplay (source : Expr) :
    (source != source) = false := by
  change (!Expr.eqv source source) = false
  rw [show Expr.eqv source source = true by exact Expr.eqv_refl source]
  rfl

theorem prbPreFamilyFamilyAppValidReplay (arg : Expr)
    (argFree : AddInductive.hasIndOcc
      prbStagedUniverseInput.staged.family.validation.stats.indConsts
      arg = false) :
    AddInductive.isValidIndAppIdx
      prbStagedUniverseInput.staged.family.validation.stats
      (prbValidationFamilyApp arg) 0 = true := by
  have parameterSelf : (prbValidationAlpha != prbValidationAlpha) = false := by
    change (!Expr.eqv prbValidationAlpha prbValidationAlpha) = false
    rw [show Expr.eqv prbValidationAlpha prbValidationAlpha = true by
      exact Expr.eqv_refl prbValidationAlpha]
    rfl
  have argFree' : AddInductive.hasIndOcc
      #[.const propRecursiveBoundaryKernelType.name [.param `u]] arg =
        false := by
    simpa [prbStagedIndConstsReplay_eq] using argFree
  simp +decide [AddInductive.isValidIndAppIdx, prbStagedParamsReplay_eq, prbStagedNindicesReplay_eq,
    prbStagedIndConstsReplay_eq, prbValidationFamilyAppGetAppFnReplay,
    prbValidationFamilyAppGetAppArgsReplay, prbExprBneSelfReplay, argFree']

theorem prbPreFamilyTargetValidReplay :
    AddInductive.isValidIndAppIdx
      prbStagedUniverseInput.staged.family.validation.stats
      prbValidationTarget 0 = true := by
  apply prbPreFamilyFamilyAppValidReplay
  rw [prbStagedIndConstsReplay_eq]
  simp [AddInductive.hasIndOcc, prbValidationBExpr_shape]

theorem prbPreFamilyTerminalValidReplay :
    AddInductive.isValidIndAppIdx
      prbStagedUniverseInput.staged.family.validation.stats
      prbValidationTerminal 0 = true := by
  apply prbPreFamilyFamilyAppValidReplay
  rw [prbStagedIndConstsReplay_eq]
  simp [AddInductive.hasIndOcc, prbValidationAExpr_shape]

theorem prbPreFamilyAIdNeRemovedReplay :
    prbValidationAId ≠ prbPreFamilyAContextReplay.freshFVarId := by
  intro equality
  have fresh := prbPreFamilyAFreshReplay
  rw [← equality] at fresh
  have found : prbPreFamilyAContextReplay.lctx.find? prbValidationAId =
      some (.cdecl prbValidationRootContext.lctx.decls.size
        prbValidationAId `a prbValidationAlpha .default .default) := by
    rw [prbPreFamilyAContextReplay_eq]
    exact prbValidationAFind
  rw [found] at fresh
  contradiction

theorem prbPreFamilyAlphaIdNeRemovedReplay :
    prbValidationAlphaId ≠ prbPreFamilyAContextReplay.freshFVarId := by
  intro equality
  have fresh := prbPreFamilyAFreshReplay
  rw [← equality, prbPreFamilyAlphaFindInAReplay] at fresh
  contradiction

theorem prbSafetyRunDirect :
    AddInductive.checkConstructorPreFamilySafety
        prbStagedUniverseInput.staged.family.validation.stats
        prbCandidate.families.singleton.familyType.type.view
        prbCandidate.families.singleton.constructors
        prbCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok () := by
  rw [prbFamilyViewReplay_eq]
  rw [AddInductive.CandidateList.singleton_eta
    prbCandidate.families.singleton.constructors]
  rw [prbFamilyTerminalContext_eq]
  change AddInductive.checkConstructorPreFamilySafety
    prbStagedUniverseInput.staged.family.validation.stats
    propRecursiveBoundaryKernelType.type
    (.cons prbCandidate.families.singleton.constructors.singleton .nil)
    prbPreFamilyContextReplay = .ok ()
  let rootAlpha : AddInductive.ConstructorCheckedExpr
      prbPreFamilyContextReplay prbValidationAlpha :=
    .ofRun (by
      rw [prbValidationAlpha_shape]
      change (prbPreFamilyContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindReplay]
      rfl)
      (by simp [prbValidationAlpha_shape, Expr.hasMVar_eq_cache])
      (by
        simpa [prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyContextReplay
            prbValidationAlphaId (.sort (.succ (.param `u)))
            prbPreFamilyRootDepthReplay prbPreFamilyAlphaFindReplay)
  let rootAlphaEnsure : AddInductive.ConstructorEnsureTypeObservation
      prbPreFamilyContextReplay prbValidationAlpha :=
    ⟨.sort (.succ (.param `u)), by
      simpa [prbValidationAlpha_shape] using
        prbPreFamilyFVarEnsureValidReplay prbPreFamilyContextReplay
          prbValidationAlphaId (.succ (.param `u))
          prbPreFamilyAlphaFindReplay prbPreFamilyRootDepthReplay⟩
  let rootAlphaConsumed : AddInductive.ConstructorCheckedExpr
      prbPreFamilyContextReplay
        (AddInductive.consumeTypeAnnotations prbValidationAlpha) := by
    rw [prbValidationConsumeAlpha]
    exact rootAlpha
  let rootAlphaAnnotations : AddInductive.CandidateIsDefEqObservation
      prbPreFamilyContextReplay prbValidationAlpha
        (AddInductive.consumeTypeAnnotations prbValidationAlpha) := by
    rw [prbValidationConsumeAlpha]
    exact ⟨AddInductive.candidateIsDefEqRefl
      prbPreFamilyContextReplay prbValidationAlpha⟩
  let aAlpha : AddInductive.ConstructorCheckedExpr
      prbPreFamilyAContextReplay prbValidationAlpha :=
    .ofRun (by
      rw [prbValidationAlpha_shape]
      change (prbPreFamilyAContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindInAReplay]
      rfl)
      (by simp [prbValidationAlpha_shape, Expr.hasMVar_eq_cache])
      (by
        simpa [prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyAContextReplay
            prbValidationAlphaId (.sort (.succ (.param `u)))
            prbPreFamilyADepthReplay prbPreFamilyAlphaFindInAReplay)
  let aAlphaEnsure : AddInductive.ConstructorEnsureTypeObservation
      prbPreFamilyAContextReplay prbValidationAlpha :=
    ⟨.sort (.succ (.param `u)), by
      simpa [prbValidationAlpha_shape] using
        prbPreFamilyFVarEnsureValidReplay prbPreFamilyAContextReplay
          prbValidationAlphaId (.succ (.param `u))
          prbPreFamilyAlphaFindInAReplay prbPreFamilyADepthReplay⟩
  let aAlphaConsumed : AddInductive.ConstructorCheckedExpr
      prbPreFamilyAContextReplay
        (AddInductive.consumeTypeAnnotations prbValidationAlpha) := by
    rw [prbValidationConsumeAlpha]
    exact aAlpha
  let aAlphaAnnotations : AddInductive.CandidateIsDefEqObservation
      prbPreFamilyAContextReplay prbValidationAlpha
        (AddInductive.consumeTypeAnnotations prbValidationAlpha) := by
    rw [prbValidationConsumeAlpha]
    exact ⟨AddInductive.candidateIsDefEqRefl
      prbPreFamilyAContextReplay prbValidationAlpha⟩
  let bTelescope : AddInductive.ConstructorCheckedExpr
      prbPreFamilyBContextReplay prbPreFamilyIndexTelescopeReplay :=
    .ofRun (by
      simp [prbPreFamilyIndexTelescopeReplay,
        prbValidationAlpha_shape, FVarsIn, Level.hasMVar']
      change (prbPreFamilyBContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindInBReplay]
      rfl)
      (by
        simp [prbPreFamilyIndexTelescopeReplay,
          prbValidationAlpha_shape, Expr.hasMVar_eq_cache,
          Level.hasMVar_eq, Level.hasMVar'])
      (prbPreFamilyIndexTelescopeCheckValidReplay
        prbPreFamilyBContextReplay prbPreFamilyAlphaFindInBReplay
          prbPreFamilyBDepthReplay)
  let bArgument : AddInductive.ConstructorCheckedExpr
      prbPreFamilyBContextReplay prbValidationBExpr :=
    .ofRun (by
      rw [prbValidationBExpr_shape]
      change (prbPreFamilyBContextReplay.lctx.find?
        prbValidationBId).isSome = true
      rw [prbPreFamilyBFindReplay]
      rfl)
      (by simp [prbValidationBExpr_shape, Expr.hasMVar_eq_cache])
      (by
        simpa [prbValidationBExpr_shape, prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyBContextReplay
            prbValidationBId prbValidationAlpha prbPreFamilyBDepthReplay
            prbPreFamilyBFindReplay)
  let bAlpha : AddInductive.ConstructorCheckedExpr
      prbPreFamilyBContextReplay prbValidationAlpha :=
    .ofRun (by
      rw [prbValidationAlpha_shape]
      change (prbPreFamilyBContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindInBReplay]
      rfl)
      (by simp [prbValidationAlpha_shape, Expr.hasMVar_eq_cache])
      (by
        simpa [prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyBContextReplay
            prbValidationAlphaId (.sort (.succ (.param `u)))
            prbPreFamilyBDepthReplay prbPreFamilyAlphaFindInBReplay)
  let bSortZero : AddInductive.ConstructorCheckedExpr
      prbPreFamilyBContextReplay (.sort .zero) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (by simp [Expr.hasMVar_eq_cache, Level.hasMVar_eq, Level.hasMVar'])
      (prbPreFamilySortZeroCheckValidReplay
        prbPreFamilyBContextReplay prbPreFamilyBDepthReplay)
  let bComparison : AddInductive.CandidateIsDefEqObservation
      prbPreFamilyBContextReplay prbValidationAlpha prbValidationAlpha :=
    ⟨AddInductive.candidateIsDefEqRefl
      prbPreFamilyBContextReplay prbValidationAlpha⟩
  let targetSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
      prbPreFamilyBContextReplay prbPreFamilyIndexTelescopeReplay
        [prbValidationBExpr] := by
    unfold prbPreFamilyIndexTelescopeReplay
    exact .cons prbPreFamilyBContextReplay prbValidationAName
      prbValidationAlpha (.sort .zero) .default
      prbValidationBExpr [] bTelescope
      ⟨bArgument, bAlpha, bComparison⟩
      (by
        simpa [Expr.instantiate1_eq, Expr.instantiate1'] using
          (AddInductive.ConstructorPreFamilyIndexSpineTrace.nil
            prbPreFamilyBContextReplay (.sort .zero) bSortZero rfl))
  have targetArgs : prbValidationTarget.getAppArgs.toList.drop
      prbStagedUniverseInput.staged.family.validation.stats.params.size =
        [prbValidationBExpr] := by
    rw [prbStagedParamsReplay_eq]
    simp [prbValidationTarget,
      prbValidationFamilyAppGetAppArgsReplay]
  obtain ⟨targetSpineExact, targetSpineRun⟩ :
      ∃ targetSpineExact :
          AddInductive.ConstructorPreFamilyIndexSpineTrace
            prbPreFamilyBContextReplay prbPreFamilyIndexTelescopeReplay
            (prbValidationTarget.getAppArgs.toList.drop
              prbStagedUniverseInput.staged.family.validation.stats.params.size),
        AddInductive.ConstructorPreFamilyIndexSpineTrace.build
            prbPreFamilyBContextReplay prbPreFamilyIndexTelescopeReplay
            (prbValidationTarget.getAppArgs.toList.drop
              prbStagedUniverseInput.staged.family.validation.stats.params.size) =
          .ok targetSpineExact := by
    rw [targetArgs]
    exact ⟨targetSpine, targetSpine.build_eq⟩
  let targetTrace : AddInductive.ConstructorPreFamilyRecursiveTrace
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyBContextReplay
      prbValidationTarget 999 :=
    .target prbPreFamilyBContextReplay prbValidationTarget
      prbPreFamilyTargetValidReplay targetSpineExact
  have targetRun : AddInductive.ConstructorPreFamilyRecursiveTrace.build
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyBContextReplay
      prbValidationTarget 999 = .ok targetTrace := by
    exact AddInductive.ConstructorPreFamilyRecursiveTrace.target_build_eq
      (fuel := 998) rfl prbPreFamilyTargetValidReplay targetSpineExact
  obtain ⟨recursiveTargetTrace, recursiveTargetRun⟩ :
      ∃ recursiveTargetTrace : AddInductive.ConstructorPreFamilyRecursiveTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyBContextReplay
          (prbValidationNextDomain.bindingBody!.instantiate1
            prbPreFamilyAContextReplay.freshExpr) 999,
        AddInductive.ConstructorPreFamilyRecursiveTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyBContextReplay
            (prbValidationNextDomain.bindingBody!.instantiate1
              prbPreFamilyAContextReplay.freshExpr) 999 =
          .ok recursiveTargetTrace := by
    rw [show prbValidationNextDomain.bindingBody!.instantiate1
        prbPreFamilyAContextReplay.freshExpr = prbValidationTarget by
      rw [prbPreFamilyAFreshExprReplay]
      exact prbValidationTarget_shape]
    exact ⟨targetTrace, targetRun⟩
  have recursiveTailContext_eq :
      prbPreFamilyAContextReplay.pushLocalDecl `b .default
          (AddInductive.consumeTypeAnnotations prbValidationAlpha) =
        prbPreFamilyBContextReplay := by
    rw [prbValidationConsumeAlpha]
    rfl
  have recursiveTailSource_eq :
      (prbValidationFamilyApp (.bvar 0)).instantiate1
          prbPreFamilyAContextReplay.freshExpr =
        prbValidationTarget := by
    rw [prbPreFamilyAFreshExprReplay]
    simpa [prbValidationNextDomain, Expr.bindingBody!] using
      prbValidationTarget_shape
  let recursiveTailSpineExact :
      AddInductive.ConstructorPreFamilyIndexSpineTrace
        (prbPreFamilyAContextReplay.pushLocalDecl `b .default
          (AddInductive.consumeTypeAnnotations prbValidationAlpha))
        prbPreFamilyIndexTelescopeReplay
        (((prbValidationFamilyApp (.bvar 0)).instantiate1
          prbPreFamilyAContextReplay.freshExpr).getAppArgs.toList.drop
            prbStagedUniverseInput.staged.family.validation.stats.params.size) := by
    rw [recursiveTailContext_eq, recursiveTailSource_eq]
    exact targetSpineExact
  have recursiveTailValid : AddInductive.isValidIndAppIdx
      prbStagedUniverseInput.staged.family.validation.stats
      ((prbValidationFamilyApp (.bvar 0)).instantiate1
        prbPreFamilyAContextReplay.freshExpr) 0 = true := by
    rw [recursiveTailSource_eq]
    exact prbPreFamilyTargetValidReplay
  let recursiveTargetTraceExact :
      AddInductive.ConstructorPreFamilyRecursiveTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay
        (prbPreFamilyAContextReplay.pushLocalDecl `b .default
          (AddInductive.consumeTypeAnnotations prbValidationAlpha))
        ((prbValidationFamilyApp (.bvar 0)).instantiate1
          prbPreFamilyAContextReplay.freshExpr) 999 :=
    .target _ _ recursiveTailValid recursiveTailSpineExact
  have recursiveTargetRunExact :
      AddInductive.ConstructorPreFamilyRecursiveTrace.build
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay
        (prbPreFamilyAContextReplay.pushLocalDecl `b .default
          (AddInductive.consumeTypeAnnotations prbValidationAlpha))
        ((prbValidationFamilyApp (.bvar 0)).instantiate1
          prbPreFamilyAContextReplay.freshExpr) 999 =
        .ok recursiveTargetTraceExact := by
    exact AddInductive.ConstructorPreFamilyRecursiveTrace.target_build_eq
      (fuel := 998) (by rw [recursiveTailSource_eq]; rfl)
      recursiveTailValid recursiveTailSpineExact
  let recursiveFieldTrace :
      AddInductive.ConstructorPreFamilyRecursiveTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
        prbValidationNextDomain 1000 :=
    .forallE prbPreFamilyAContextReplay `b prbValidationAlpha
      (prbValidationFamilyApp (.bvar 0)) .default aAlpha aAlphaEnsure
      aAlphaConsumed aAlphaAnnotations prbPreFamilyAFreshReplay
      recursiveTargetTraceExact
  have recursiveFieldRun :
      AddInductive.ConstructorPreFamilyRecursiveTrace.build
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
        prbValidationNextDomain 1000 = .ok recursiveFieldTrace := by
    unfold prbValidationNextDomain
    exact AddInductive.ConstructorPreFamilyRecursiveTrace.forallE_build_eq
      aAlpha aAlphaEnsure aAlphaConsumed aAlphaAnnotations
      prbPreFamilyAFreshReplay recursiveTargetTraceExact
      recursiveTargetRunExact
  obtain ⟨recursiveFieldTraceAtContext, recursiveFieldRunAtContext⟩ :
      ∃ recursiveFieldTraceAtContext :
          AddInductive.ConstructorPreFamilyRecursiveTrace
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
            prbValidationNextDomain
            prbPreFamilyAContextReplay.fuel.inductiveFuel,
        AddInductive.ConstructorPreFamilyRecursiveTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
            prbValidationNextDomain
            prbPreFamilyAContextReplay.fuel.inductiveFuel =
          .ok recursiveFieldTraceAtContext := by
    rw [prbPreFamilyAInductiveFuelReplay]
    exact ⟨recursiveFieldTrace, recursiveFieldRun⟩
  let resultTelescope : AddInductive.ConstructorCheckedExpr
      prbPreFamilyResultContextReplay prbPreFamilyIndexTelescopeReplay :=
    .ofRun (by
      simp [prbPreFamilyIndexTelescopeReplay,
        prbValidationAlpha_shape, FVarsIn, Level.hasMVar']
      change (prbPreFamilyResultContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindInResultReplay]
      rfl)
      (by
        simp [prbPreFamilyIndexTelescopeReplay,
          prbValidationAlpha_shape, Expr.hasMVar_eq_cache,
          Level.hasMVar_eq, Level.hasMVar'])
      (prbPreFamilyIndexTelescopeCheckValidReplay
        prbPreFamilyResultContextReplay prbPreFamilyAlphaFindInResultReplay
          prbPreFamilyResultDepthReplay)
  let resultArgument : AddInductive.ConstructorCheckedExpr
      prbPreFamilyResultContextReplay prbValidationAExpr :=
    .ofRun (by
      rw [prbValidationAExpr_shape]
      change (prbPreFamilyResultContextReplay.lctx.find?
        prbValidationAId).isSome = true
      rw [prbPreFamilyAFindInResultReplay]
      rfl)
      (by simp [prbValidationAExpr_shape, Expr.hasMVar_eq_cache])
      (by
        simpa [prbValidationAExpr_shape, prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyResultContextReplay
            prbValidationAId prbValidationAlpha
            prbPreFamilyResultDepthReplay prbPreFamilyAFindInResultReplay)
  let resultAlpha : AddInductive.ConstructorCheckedExpr
      prbPreFamilyResultContextReplay prbValidationAlpha :=
    .ofRun (by
      rw [prbValidationAlpha_shape]
      change (prbPreFamilyResultContextReplay.lctx.find?
        prbValidationAlphaId).isSome = true
      rw [prbPreFamilyAlphaFindInResultReplay]
      rfl)
      (by simp [prbValidationAlpha_shape, Expr.hasMVar_eq_cache])
      (by
        simpa [prbValidationAlpha_shape] using
          prbCandidateCheckTypeFVar prbPreFamilyResultContextReplay
            prbValidationAlphaId (.sort (.succ (.param `u)))
            prbPreFamilyResultDepthReplay
            prbPreFamilyAlphaFindInResultReplay)
  let resultSortZero : AddInductive.ConstructorCheckedExpr
      prbPreFamilyResultContextReplay (.sort .zero) :=
    .ofRun (by simp [FVarsIn, Level.hasMVar'])
      (by simp [Expr.hasMVar_eq_cache, Level.hasMVar_eq, Level.hasMVar'])
      (prbPreFamilySortZeroCheckValidReplay
        prbPreFamilyResultContextReplay prbPreFamilyResultDepthReplay)
  let resultComparison : AddInductive.CandidateIsDefEqObservation
      prbPreFamilyResultContextReplay prbValidationAlpha
        prbValidationAlpha :=
    ⟨AddInductive.candidateIsDefEqRefl
      prbPreFamilyResultContextReplay prbValidationAlpha⟩
  let resultSpine : AddInductive.ConstructorPreFamilyIndexSpineTrace
      prbPreFamilyResultContextReplay prbPreFamilyIndexTelescopeReplay
        [prbValidationAExpr] := by
    unfold prbPreFamilyIndexTelescopeReplay
    exact .cons prbPreFamilyResultContextReplay prbValidationAName
      prbValidationAlpha (.sort .zero) .default
      prbValidationAExpr [] resultTelescope
      ⟨resultArgument, resultAlpha, resultComparison⟩
      (by
        simpa [Expr.instantiate1_eq, Expr.instantiate1'] using
          (AddInductive.ConstructorPreFamilyIndexSpineTrace.nil
            prbPreFamilyResultContextReplay (.sort .zero)
            resultSortZero rfl))
  have resultArgs : prbValidationTerminal.getAppArgs.toList.drop
      prbStagedUniverseInput.staged.family.validation.stats.params.size =
        [prbValidationAExpr] := by
    rw [prbStagedParamsReplay_eq]
    simp [prbValidationTerminal,
      prbValidationFamilyAppGetAppArgsReplay]
  obtain ⟨resultSpineExact, resultSpineRun⟩ :
      ∃ resultSpineExact :
          AddInductive.ConstructorPreFamilyIndexSpineTrace
            prbPreFamilyResultContextReplay prbPreFamilyIndexTelescopeReplay
            (prbValidationTerminal.getAppArgs.toList.drop
              prbStagedUniverseInput.staged.family.validation.stats.params.size),
        AddInductive.ConstructorPreFamilyIndexSpineTrace.build
            prbPreFamilyResultContextReplay prbPreFamilyIndexTelescopeReplay
            (prbValidationTerminal.getAppArgs.toList.drop
              prbStagedUniverseInput.staged.family.validation.stats.params.size) =
          .ok resultSpineExact := by
    rw [resultArgs]
    exact ⟨resultSpine, resultSpine.build_eq⟩
  have resultIndependent : AddInductive.constructorIndependentOf
      prbValidationTerminal
      [prbPreFamilyAContextReplay.freshFVarId] = true := by
    simp [AddInductive.constructorIndependentOf,
      prbValidationTerminal, prbValidationFamilyApp,
      Expr.fvarsList, prbValidationAlpha_shape,
      prbValidationAExpr_shape,
      prbPreFamilyAlphaIdNeRemovedReplay,
      prbPreFamilyAIdNeRemovedReplay]
  let resultTrace : AddInductive.ConstructorPreFamilyViewTrace
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyResultContextReplay
      prbValidationTerminal 3
      [prbPreFamilyAContextReplay.freshFVarId] true :=
    .terminal prbPreFamilyResultContextReplay prbValidationTerminal 3
      [prbPreFamilyAContextReplay.freshFVarId] true
      prbPreFamilyTerminalValidReplay resultIndependent resultSpineExact
  have resultRun : AddInductive.ConstructorPreFamilyViewTrace.build
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyResultContextReplay
      prbValidationTerminal 3
      [prbPreFamilyAContextReplay.freshFVarId] true 997 =
        .ok resultTrace := by
    exact AddInductive.ConstructorPreFamilyViewTrace.terminal_build_eq
      (fuel := 996) rfl prbPreFamilyTerminalValidReplay resultIndependent
      resultSpineExact
  obtain ⟨recursiveViewTailTrace, recursiveViewTailRun⟩ :
      ∃ recursiveViewTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay
          prbPreFamilyAContextReplay.advanceFresh
          (prbValidationAfterA.bindingBody!.instantiate1
            prbPreFamilyAContextReplay.freshExpr) 3
          [prbPreFamilyAContextReplay.freshFVarId] true,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay
            prbPreFamilyAContextReplay.advanceFresh
            (prbValidationAfterA.bindingBody!.instantiate1
              prbPreFamilyAContextReplay.freshExpr) 3
            [prbPreFamilyAContextReplay.freshFVarId] true 997 =
          .ok recursiveViewTailTrace := by
    rw [show prbPreFamilyAContextReplay.advanceFresh =
        prbPreFamilyResultContextReplay by rfl]
    rw [show prbValidationAfterA.bindingBody!.instantiate1
        prbPreFamilyAContextReplay.freshExpr = prbValidationTerminal by
      simp [prbValidationAfterA, prbValidationTerminal,
        prbValidationFamilyApp, Expr.bindingBody!,
        Expr.instantiate1_eq, Expr.instantiate1']]
    exact ⟨resultTrace, resultRun⟩
  obtain ⟨recursiveViewTailTraceExact, recursiveViewTailRunExact⟩ :
      ∃ recursiveViewTailTraceExact :
          AddInductive.ConstructorPreFamilyViewTrace
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay
            prbPreFamilyAContextReplay.advanceFresh
            ((prbValidationFamilyApp prbValidationAExpr).instantiate1
              prbPreFamilyAContextReplay.freshExpr) 3
            [prbPreFamilyAContextReplay.freshFVarId] true,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay
            prbPreFamilyAContextReplay.advanceFresh
            ((prbValidationFamilyApp prbValidationAExpr).instantiate1
              prbPreFamilyAContextReplay.freshExpr) 3
            [prbPreFamilyAContextReplay.freshFVarId] true 997 =
          .ok recursiveViewTailTraceExact := by
    change ∃ recursiveViewTailTraceExact :
        AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay
          prbPreFamilyAContextReplay.advanceFresh
          (prbValidationAfterA.bindingBody!.instantiate1
            prbPreFamilyAContextReplay.freshExpr) 3
          [prbPreFamilyAContextReplay.freshFVarId] true,
      AddInductive.ConstructorPreFamilyViewTrace.build
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay
          prbPreFamilyAContextReplay.advanceFresh
          (prbValidationAfterA.bindingBody!.instantiate1
            prbPreFamilyAContextReplay.freshExpr) 3
          [prbPreFamilyAContextReplay.freshFVarId] true 997 =
        .ok recursiveViewTailTraceExact
    exact ⟨recursiveViewTailTrace, recursiveViewTailRun⟩
  have noParameterTwo :
      prbStagedUniverseInput.staged.family.validation.stats.params[2]? =
        none := by
    rw [prbStagedParamsReplay_eq]
    rfl
  have recursiveIndependent : AddInductive.constructorIndependentOf
      prbValidationNextDomain [] = true := by
    simp [AddInductive.constructorIndependentOf]
  let recursiveViewTrace : AddInductive.ConstructorPreFamilyViewTrace
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
      (.forallE `next prbValidationNextDomain
        (prbValidationFamilyApp prbValidationAExpr) .default)
      2 [] false :=
    .recursive prbPreFamilyAContextReplay 2 [] false `next
      prbValidationNextDomain (prbValidationFamilyApp prbValidationAExpr)
      .default noParameterTwo prbPreFamilyNextDomainHasIndOccReplay
      recursiveIndependent recursiveFieldTraceAtContext
      prbPreFamilyAFreshReplay recursiveViewTailTraceExact
  have recursiveViewRun : AddInductive.ConstructorPreFamilyViewTrace.build
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
      (.forallE `next prbValidationNextDomain
        (prbValidationFamilyApp prbValidationAExpr) .default)
      2 [] false 998 =
        .ok recursiveViewTrace := by
    simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [noParameterTwo] at parameterAt
      contradiction
    · split
      · rename_i nonrecursive
        rw [prbPreFamilyNextDomainHasIndOccReplay] at nonrecursive
        contradiction
      · rw [dif_pos recursiveIndependent]
        rw [recursiveFieldRunAtContext]
        simp only [Bind.bind, Except.bind]
        rw [dif_pos prbPreFamilyAFreshReplay]
        rw [recursiveViewTailRunExact]
        rfl
  obtain ⟨afterATrace, afterARun⟩ :
      ∃ afterATrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
          prbValidationAfterA 2 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
            prbValidationAfterA 2 [] false 998 = .ok afterATrace := by
    change ∃ afterATrace : AddInductive.ConstructorPreFamilyViewTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
        (.forallE `next prbValidationNextDomain
          (prbValidationFamilyApp prbValidationAExpr) .default)
        2 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyAContextReplay
          (.forallE `next prbValidationNextDomain
            (prbValidationFamilyApp prbValidationAExpr) .default)
          2 [] false 998 = .ok afterATrace
    exact ⟨recursiveViewTrace, recursiveViewRun⟩
  obtain ⟨ordinaryTailTrace, ordinaryTailRun⟩ :
      ∃ ordinaryTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay
          (prbPreFamilyContextReplay.pushLocalDecl `a .default
            (AddInductive.consumeTypeAnnotations prbValidationAlpha))
          (prbValidationAfterParam.bindingBody!.instantiate1
            prbPreFamilyContextReplay.freshExpr) 2 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay
            (prbPreFamilyContextReplay.pushLocalDecl `a .default
              (AddInductive.consumeTypeAnnotations prbValidationAlpha))
            (prbValidationAfterParam.bindingBody!.instantiate1
              prbPreFamilyContextReplay.freshExpr) 2 [] false 998 =
          .ok ordinaryTailTrace := by
    rw [prbValidationConsumeAlpha]
    rw [show prbPreFamilyContextReplay.pushLocalDecl `a .default
        prbValidationAlpha = prbPreFamilyAContextReplay by rfl]
    rw [show prbValidationAfterParam.bindingBody!.instantiate1
        prbPreFamilyContextReplay.freshExpr = prbValidationAfterA by
      rw [prbPreFamilyRootFreshExprReplay]
      exact prbValidationAfterA_shape]
    exact ⟨afterATrace, afterARun⟩
  have noParameterOne :
      prbStagedUniverseInput.staged.family.validation.stats.params[1]? =
        none := by
    rw [prbStagedParamsReplay_eq]
    rfl
  have rootIndependent : AddInductive.constructorIndependentOf
      prbValidationAlpha [] = true := by
    simp [AddInductive.constructorIndependentOf]
  let ordinaryViewTrace : AddInductive.ConstructorPreFamilyViewTrace
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
      (.forallE `a prbValidationAlpha
        (.forallE `next prbValidationNextDomain
          (prbValidationFamilyApp (.bvar 1)) .default) .default)
      1 [] false :=
    .ordinary prbPreFamilyContextReplay 1 [] false `a
      prbValidationAlpha
      (.forallE `next prbValidationNextDomain
        (prbValidationFamilyApp (.bvar 1)) .default)
      .default noParameterOne prbPreFamilyAlphaHasNoIndOccReplay
      rootIndependent rootAlpha rootAlphaEnsure rootAlphaConsumed
      rootAlphaAnnotations prbPreFamilyRootFreshReplay ordinaryTailTrace
  have ordinaryViewRun : AddInductive.ConstructorPreFamilyViewTrace.build
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
      (.forallE `a prbValidationAlpha
        (.forallE `next prbValidationNextDomain
          (prbValidationFamilyApp (.bvar 1)) .default) .default)
      1 [] false 999 = .ok ordinaryViewTrace := by
    simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [noParameterOne] at parameterAt
      contradiction
    · split
      · rw [dif_pos rootIndependent]
        rw [rootAlpha.check_eq, rootAlphaEnsure.observe_eq,
          rootAlphaConsumed.check_eq]
        simp only [Bind.bind, Except.bind]
        rw [rootAlphaAnnotations.observe_eq]
        simp only []
        rw [dif_pos prbPreFamilyRootFreshReplay]
        have ordinaryTailRun' :
            AddInductive.ConstructorPreFamilyViewTrace.build
                prbStagedUniverseInput.staged.family.validation.stats 0
                prbPreFamilyIndexTelescopeReplay
                (prbPreFamilyContextReplay.pushLocalDecl `a .default
                  (AddInductive.consumeTypeAnnotations prbValidationAlpha))
                ((Expr.forallE `next prbValidationNextDomain
                  (prbValidationFamilyApp (.bvar 1)) .default).instantiate1
                    prbPreFamilyContextReplay.freshExpr)
                2 [] false 998 = .ok ordinaryTailTrace := by
          simpa only [prbValidationAfterParam, Expr.bindingBody!] using
            ordinaryTailRun
        rw [ordinaryTailRun']
        rfl
      · rename_i recursive
        rw [prbPreFamilyAlphaHasNoIndOccReplay] at recursive
        contradiction
  obtain ⟨afterParamTrace, afterParamRun⟩ :
      ∃ afterParamTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          prbValidationAfterParam 1 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
            prbValidationAfterParam 1 [] false 999 =
          .ok afterParamTrace := by
    change ∃ afterParamTrace : AddInductive.ConstructorPreFamilyViewTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
        (.forallE `a prbValidationAlpha
          (.forallE `next prbValidationNextDomain
            (prbValidationFamilyApp (.bvar 1)) .default) .default)
        1 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          (.forallE `a prbValidationAlpha
            (.forallE `next prbValidationNextDomain
              (prbValidationFamilyApp (.bvar 1)) .default) .default)
          1 [] false 999 = .ok afterParamTrace
    exact ⟨ordinaryViewTrace, ordinaryViewRun⟩
  obtain ⟨parameterTailTrace, parameterTailRun⟩ :
      ∃ parameterTailTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          (propRecursiveBoundaryKernelCtor.type.bindingBody!.instantiate1
            prbValidationAlpha) 1 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
            (propRecursiveBoundaryKernelCtor.type.bindingBody!.instantiate1
              prbValidationAlpha) 1 [] false 999 =
          .ok parameterTailTrace := by
    rw [prbValidationAfterParam_shape]
    exact ⟨afterParamTrace, afterParamRun⟩
  have parameterAtZero :
      prbStagedUniverseInput.staged.family.validation.stats.params[0]? =
        some prbValidationAlpha := by
    rw [prbStagedParamsReplay_eq]
    rfl
  obtain ⟨rawViewTrace, rawViewRun⟩ :
      ∃ rawViewTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          propRecursiveBoundaryKernelCtor.type 0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
            propRecursiveBoundaryKernelCtor.type 0 [] false 1000 =
          .ok rawViewTrace := by
    change ∃ rawViewTrace : AddInductive.ConstructorPreFamilyViewTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
        (.forallE `α (.sort (.succ (.param `u)))
          propRecursiveBoundaryKernelCtor.type.bindingBody! .implicit)
        0 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          (.forallE `α (.sort (.succ (.param `u)))
            propRecursiveBoundaryKernelCtor.type.bindingBody! .implicit)
          0 [] false 1000 = .ok rawViewTrace
    let rawViewTrace : AddInductive.ConstructorPreFamilyViewTrace
        prbStagedUniverseInput.staged.family.validation.stats 0
        prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
        (.forallE `α (.sort (.succ (.param `u)))
          propRecursiveBoundaryKernelCtor.type.bindingBody! .implicit)
        0 [] false :=
      .parameter prbPreFamilyContextReplay 0 [] false `α
        (.sort (.succ (.param `u)))
        propRecursiveBoundaryKernelCtor.type.bindingBody! .implicit
        prbValidationAlpha parameterAtZero parameterTailTrace
    refine ⟨rawViewTrace, ?_⟩
    simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
    split
    · rename_i parameter parameterAt
      rw [parameterAtZero] at parameterAt
      cases parameterAt
      rw [parameterTailRun]
      rfl
    · rename_i noParameter
      rw [parameterAtZero] at noParameter
      contradiction
  obtain ⟨headTrace, headRun⟩ :
      ∃ headTrace : AddInductive.ConstructorPreFamilyViewTrace
          prbStagedUniverseInput.staged.family.validation.stats 0
          prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
          prbCandidate.families.singleton.constructors.singleton.type.view
          0 [] false,
        AddInductive.ConstructorPreFamilyViewTrace.build
            prbStagedUniverseInput.staged.family.validation.stats 0
            prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
            prbCandidate.families.singleton.constructors.singleton.type.view
            0 [] false 1000 = .ok headTrace := by
    rw [prbCtorView_eq]
    exact ⟨rawViewTrace, rawViewRun⟩
  let listTrace : AddInductive.ConstructorPreFamilyListTrace
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
      (.cons prbCandidate.families.singleton.constructors.singleton .nil) :=
    .cons headTrace .nil
  have listRun : AddInductive.ConstructorPreFamilyListTrace.build
      prbStagedUniverseInput.staged.family.validation.stats 0
      prbPreFamilyIndexTelescopeReplay prbPreFamilyContextReplay
      (.cons prbCandidate.families.singleton.constructors.singleton .nil) =
        .ok listTrace := by
    exact AddInductive.ConstructorPreFamilyListTrace.cons_build_eq
      headTrace (by
        rw [prbPreFamilyRootInductiveFuelReplay]
        exact headRun)
      .nil rfl
  have parametersRun : AddInductive.instantiateFamilyParameters
      propRecursiveBoundaryKernelType.type
      prbStagedUniverseInput.staged.family.validation.stats.params.toList =
        .ok prbPreFamilyIndexTelescopeReplay := by
    rw [prbStagedParamsReplay_eq]
    simp [propRecursiveBoundaryKernelType,
      propRecursiveBoundaryInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal,
      AddInductive.instantiateFamilyParameters,
      prbPreFamilyIndexTelescopeReplay, prbValidationAlpha,
      prbValidationAName, Expr.bindingName!,
      Expr.instantiate1_eq, Expr.instantiate1',
      Pure.pure, Except.pure]
  unfold AddInductive.checkConstructorPreFamilySafety
  have translationUnique :
      (AddInductive.theoryTranslationUnique
          propRecursiveBoundaryKernelType.type &&
        (AddInductive.CandidateList.cons
          prbCandidate.families.singleton.constructors.singleton
          (AddInductive.CandidateList.nil : AddInductive.CandidateList
            AddInductive.CandidateConstructor [])).viewTranslationUnique) =
        true := by
    change (AddInductive.theoryTranslationUnique
      propRecursiveBoundaryKernelType.type &&
      (prbCandidate.families.singleton.constructors.singleton.type.trace.viewTranslationUnique &&
        true)) = true
    rw [prbCandidate.families.singleton.constructors.singleton.type.trace.viewTranslationUnique_eq]
    change (AddInductive.theoryTranslationUnique
      propRecursiveBoundaryKernelType.type &&
      (AddInductive.theoryTranslationUnique
        prbCandidate.families.singleton.constructors.singleton.type.view &&
        true)) = true
    rw [prbCtorView_eq]
    simp [AddInductive.theoryTranslationUnique,
      propRecursiveBoundaryKernelType, propRecursiveBoundaryKernelCtor,
      propRecursiveBoundaryInfo, propRecursiveBoundaryMkInfo,
      ConstantInfo.type, ConstantInfo.toConstantVal]
  rw [if_pos translationUnique]
  rw [parametersRun]
  simp only [Bind.bind, Except.bind]
  rw [listRun]
  rfl

theorem prbSafetyRun :
    AddInductive.checkConstructorPreFamilySafety
        prbStagedPostFamilyInput.universeInput.staged.family.validation.stats
        prbCandidate.families.singleton.familyType.type.view
        prbCandidate.families.singleton.constructors
        prbCandidate.families.singleton.familyType.type.trace.terminalContext =
      .ok () := by
  simpa [prbStagedPostFamilyInput,
    VInductDecl.StagedNormalizationCandidatePostFamilyInput.ofRun] using
    prbSafetyRunDirect

def prbStagedPreFamilyInput :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCandidate propRecursiveBoundaryDecl :=
  VInductDecl.StagedNormalizationCandidatePreFamilyInput.ofRun
    prbStagedPostFamilyInput prbSafetyRun

/-! ## Structural CVM constructor-validity replay -/

def cvmValidationAlphaContextTest : AddInductive.Context :=
  cvmFamilyContext.pushLocalDecl `α .default (.sort (.succ (.param `u)))

def cvmValidationIndexNameTest : Name :=
  constructorValidityMatrixKernelType.type.bindingBody!
    |>.bindingDomain!.bindingName!

def cvmValidationPDomainTest : Expr :=
  .forallE cvmValidationIndexNameTest cvmFamilyContext.freshExpr
    (.sort .zero) .default

def cvmValidationFamilyContextTest : AddInductive.Context :=
  cvmValidationAlphaContextTest.pushLocalDecl `P .default
    cvmValidationPDomainTest

theorem cvmFamilyTerminalContextTest_eq :
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext =
      cvmValidationFamilyContextTest := by
  have identity := cvmFamilyIdentityEvidence.identity
  have spineLength := cvmFamilyIdentityEvidence.spineLength_eq
  generalize htrace :
    cvmCandidate.families.singleton.familyType.type.trace = trace at identity spineLength ⊢
  cases identity with
  | terminal result_eq =>
      simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
      rw [cvmFamilyIdentityReplay_shape.1] at spineLength
      omega
  | forallE domainCandidate bodyCandidate source_eq consumed_eq
      domainIdentity bodyIdentity =>
      simp only [AddInductive.CandidateExprTrace.terminalContext]
      cases bodyIdentity with
      | terminal result_eq =>
          simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
          rw [cvmFamilyIdentityReplay_shape.1] at spineLength
          omega
      | forallE domainCandidate' bodyCandidate' source_eq' consumed_eq'
          domainIdentity' bodyIdentity' =>
          cases bodyIdentity' with
          | terminal result_eq =>
              simp only [AddInductive.CandidateExprTrace.terminalContext]
              simp [constructorValidityMatrixKernelType,
                constructorValidityMatrixInfo, ConstantInfo.type,
                ConstantInfo.toConstantVal] at source_eq
              rcases source_eq with ⟨rfl, rfl, rfl, rfl⟩
              simp [Expr.instantiate1_eq, Expr.instantiate1'] at source_eq'
              rcases source_eq' with ⟨rfl, rfl, rfl, rfl⟩
              rw [consumed_eq, consumed_eq', cvmFamilyCandidateContext_eq]
              rfl
          | forallE domainCandidate'' bodyCandidate'' source_eq'' consumed_eq''
              domainIdentity'' bodyIdentity'' =>
              simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
              rw [cvmFamilyIdentityReplay_shape.1] at spineLength
              omega

def cvmConstructorValidationContextTest : AddInductive.Context :=
  { cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
    env := cvmConstructorContext.env }

theorem cvmConstructorValidationContextTest_eq :
    cvmConstructorValidationContextTest =
      { cvmValidationFamilyContextTest with env := cvmConstructorContext.env } := by
  rw [cvmConstructorValidationContextTest, cvmFamilyTerminalContextTest_eq]

def cvmValidationRootContextTest : AddInductive.Context :=
  { cvmValidationFamilyContextTest with env := cvmConstructorContext.env }

theorem cvmConstructorValidationContextTest_root :
    cvmConstructorValidationContextTest = cvmValidationRootContextTest := by
  rw [cvmConstructorValidationContextTest_eq]
  rfl

theorem cvmValidationAlphaLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmValidationAlphaContextTest :=
  (TypeChecker.CandidateLocalContextRun.empty cvmFamilyContext rfl).push
    `α .default (.sort (.succ (.param `u)))

theorem cvmValidationFamilyLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmValidationFamilyContextTest :=
  cvmValidationAlphaLocalRunTest.push `P .default cvmValidationPDomainTest

theorem cvmValidationRootLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmValidationRootContextTest where
  wf := cvmValidationFamilyLocalRunTest.wf
  reserves := cvmValidationFamilyLocalRunTest.reserves

def cvmValidationAlphaIdTest : FVarId := cvmFamilyContext.freshFVarId

def cvmValidationPIdTest : FVarId :=
  cvmValidationAlphaContextTest.freshFVarId

theorem cvmValidationPDomainShapeTest :
    cvmValidationPDomainTest =
      .forallE cvmValidationIndexNameTest
        (.fvar cvmValidationAlphaIdTest) (.sort .zero) .default := by
  rfl

theorem cvmValidationAlphaFindTest :
    cvmValidationRootContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) := by
  have first :=
    (TypeChecker.CandidateLocalContextRun.empty cvmFamilyContext rfl).push_findNew
      `α .default (.sort (.succ (.param `u)))
  have old := cvmValidationAlphaLocalRunTest.push_findOld
    `P .default cvmValidationPDomainTest first
  simpa [cvmValidationRootContextTest, cvmValidationFamilyContextTest,
    cvmValidationAlphaContextTest, cvmValidationAlphaIdTest,
    cvmFamilyContext, constructorValidityMatrixContext,
    AddInductive.Context.pushLocalDecl] using old

theorem cvmValidationPFindTest :
    cvmValidationRootContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) := by
  have found := cvmValidationAlphaLocalRunTest.push_findNew
    `P .default cvmValidationPDomainTest
  simpa [cvmValidationRootContextTest, cvmValidationFamilyContextTest,
    cvmValidationPIdTest] using found

theorem cvmValidationRootDepthTest :
    cvmValidationRootContextTest.fuel.recDepth = 10000 := by
  rw [← cvmConstructorValidationContextTest_root]
  rw [cvmConstructorValidationContextTest,
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext_fuel,
    cvmFamilyContext_eq]
  rfl

theorem cvmValidationRootLparamsTest :
    cvmValidationRootContextTest.lparams = [`u] := by
  rw [← cvmConstructorValidationContextTest_root]
  rw [cvmConstructorValidationContextTest, cvmTerminalLparams_eq]
  rfl

theorem cvmStatsResultLevelTest :
    cvmFamilyValidationRun.stats.resultLevel = .succ (.param `u) := by
  rfl

theorem cvmCtorXDomainValidationShapeTest :
    cvmCtorXDomain = .fvar cvmValidationAlphaIdTest := by
  simp_cvm_ctor_expr
  rfl

theorem cvmValidationXEnsureTest :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨cvmValidationRootContextTest, cvmCtorXDomain,
        .sort (.succ (.param `u))⟩ := by
  rw [cvmCtorXDomainValidationShapeTest]
  exact prbPreFamilyFVarEnsureValidReplay
    cvmValidationRootContextTest cvmValidationAlphaIdTest
      (.succ (.param `u)) cvmValidationAlphaFindTest
      cvmValidationRootDepthTest

theorem cvmEnsureTypeResultEqTest
    (actual : AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨context, source, result⟩)
    (expected : AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨context, source, expectedResult⟩) :
    result = expectedResult := by
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel (TypeChecker.ensureType source) =
      .ok result at actual
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel (TypeChecker.ensureType source) =
      .ok expectedResult at expected
  rw [expected] at actual
  exact (Except.ok.inj actual).symm

def cvmValidationXContextTest : AddInductive.Context :=
  cvmValidationRootContextTest.pushLocalDecl `x .default
    (AddInductive.consumeTypeAnnotations cvmCtorXDomain)

theorem cvmValidationRootFreshEqTest :
    cvmValidationRootContextTest.freshExpr =
      cvmCtorPContext.freshExpr := by
  simp [cvmValidationRootContextTest, cvmValidationFamilyContextTest,
    cvmValidationAlphaContextTest, cvmValidationPDomainTest,
    cvmCtorPContext, cvmCtorAlphaContext, cvmCtorAlphaDomain,
    cvmFamilyContext, cvmConstructorContext,
    constructorValidityMatrixContext,
    AddInductive.Context.pushLocalDecl, AddInductive.Context.freshExpr,
    AddInductive.Context.freshFVarId]

theorem cvmFirstFieldSourceTest :
    cvmCtorAfterP.bindingBody!.instantiate1
        cvmValidationRootContextTest.freshExpr = cvmCtorAfterX := by
  unfold cvmCtorAfterX
  rw [cvmValidationRootFreshEqTest]

theorem cvmCtorAfterXForallTest :
    cvmCtorAfterX = .forallE `proof cvmCtorProofDomain
      cvmCtorAfterX.bindingBody! .default := by
  simp_cvm_ctor_expr

theorem cvmUniverseSemanticsCastSourceTest
    {source source' : Expr}
    (sourceEq : source = source')
    (trace : AddInductive.ConstructorTypeValidationTrace
      stats isUnsafe familyIdx ctor context source argIdx fuel) :
    (sourceEq ▸ trace).universeSemantics = trace.universeSemantics := by
  cases sourceEq
  rfl

theorem cvmConstructorValidationFuelTest :
    cvmConstructorValidationContextTest.fuel.inductiveFuel = 1000 := by
  rw [cvmConstructorValidationContextTest,
    cvmCandidate.families.singleton.familyType.type.trace.terminalContext_fuel,
    cvmFamilyContext_eq]
  rfl

theorem cvmStatsParamsTest :
    cvmFamilyValidationRun.stats.params =
      #[cvmFamilyContext.freshExpr,
        (cvmFamilyContext.pushLocalDecl `α .default
          (.sort (.succ (.param `u)))).freshExpr] := by
  rw [cvmFamilyValidationRun.stats_eq]
  change
    (cvmCandidate.families.singleton.familyType.type.trace.parameterList 2).toArray = _
  have identity := cvmFamilyIdentityEvidence.identity
  have spineLength := cvmFamilyIdentityEvidence.spineLength_eq
  generalize htrace :
    cvmCandidate.families.singleton.familyType.type.trace = trace at identity spineLength ⊢
  cases identity with
  | terminal result_eq =>
      simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
      rw [cvmFamilyIdentityReplay_shape.1] at spineLength
      omega
  | forallE domainCandidate bodyCandidate source_eq consumed_eq
      domainIdentity bodyIdentity =>
      cases bodyIdentity with
      | terminal result_eq =>
          simp only [AddInductive.CandidateExprTrace.spineLength] at spineLength
          rw [cvmFamilyIdentityReplay_shape.1] at spineLength
          omega
      | forallE domainCandidate' bodyCandidate' source_eq' consumed_eq'
          domainIdentity' bodyIdentity' =>
          simp only [AddInductive.CandidateExprTrace.parameterList]
          rw [cvmFamilyCandidateContext_eq, consumed_eq]
          rfl

theorem cvmFirstParameterSourceTest :
    constructorValidityMatrixKernelCtor.type.bindingBody!.instantiate1
        cvmFamilyContext.freshExpr = cvmCtorAfterAlpha := by
  simp_cvm_ctor_expr
  rfl

theorem cvmCtorAfterAlphaForallTest :
    cvmCtorAfterAlpha =
      .forallE `P cvmCtorPDomain cvmCtorAfterAlpha.bindingBody! .implicit := by
  simp_cvm_ctor_expr

theorem cvmSecondParameterSourceTest :
    cvmCtorAfterAlpha.bindingBody!.instantiate1
        cvmValidationAlphaContextTest.freshExpr = cvmCtorAfterP := by
  simp_cvm_ctor_expr
  rfl

theorem cvmCtorAfterPForallTest :
    cvmCtorAfterP =
      .forallE `x cvmCtorXDomain cvmCtorAfterP.bindingBody! .default := by
  simp_cvm_ctor_expr

def cvmInferOnlyInsertTest
    (state : TypeChecker.State) (source type : Expr) : TypeChecker.State :=
  { state with inferTypeI := state.inferTypeI.insert source type }

theorem cvmInferTypeFVarOnlyCoreTest
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (id : FVarId) (type : Expr)
    (hcache : state.inferTypeI[(.fvar id : Expr)]? = none)
    (hfind : context.lctx.find? id =
      some (.cdecl index id name type bi kind)) :
    TypeChecker.Inner.inferType' (.fvar id) true
      (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
        .ok (type, cvmInferOnlyInsertTest state (.fvar id) type) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange', hcache,
    TypeChecker.Inner.inferFVar, AddInductive.Context.toTypeChecker,
    hfind, LocalDecl.type, cvmInferOnlyInsertTest,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem cvmEnsureTypeOfInferOnlyTest
    (context : AddInductive.Context) (source : Expr) (level : Level)
    (finalState : TypeChecker.State)
    (run : TypeChecker.Inner.inferType source true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort level, finalState)) :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨context, source, .sort level⟩ := by
  unfold AddInductive.ConstructorEnsureTypeStep.Valid
    TypeChecker.ensureType TypeChecker.inferType TypeChecker.ensureSort
    TypeChecker.RecM.run TypeChecker.M.run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure, StateT.run',
    Functor.map, Except.map]
  rw [show TypeChecker.Inner.inferType source true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      { env := context.env, lctx := context.lctx,
        safety := context.safety, lparams := context.lparams,
        fuel := context.fuel }
      ({} : TypeChecker.State) = .ok (.sort level, finalState) by
    simpa [AddInductive.Context.toTypeChecker] using run]
  rfl

theorem cvmValidationXLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmValidationXContextTest :=
  cvmValidationRootLocalRunTest.push `x .default
    (AddInductive.consumeTypeAnnotations cvmCtorXDomain)

def cvmValidationXIdTest : FVarId :=
  cvmValidationRootContextTest.freshFVarId

theorem cvmValidationPFindInXTest :
    cvmValidationXContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmValidationRootLocalRunTest.push_findOld `x .default
    (AddInductive.consumeTypeAnnotations cvmCtorXDomain)
    cvmValidationPFindTest

theorem cvmCtorProofDomainValidationShapeTest :
    cvmCtorProofDomain =
      .app (.fvar cvmValidationPIdTest) (.fvar cvmValidationXIdTest) := by
  simp [cvmCtorProofDomain, cvmCtorAfterX, cvmCtorAfterP,
    cvmCtorAfterAlpha, cvmValidationPIdTest, cvmValidationXIdTest,
    cvmValidationRootContextTest, cvmValidationFamilyContextTest,
    cvmValidationAlphaContextTest, cvmFamilyContext,
    cvmCtorPContext, cvmCtorAlphaContext, cvmConstructorContext,
    constructorValidityMatrixContext,
    constructorValidityMatrixKernelCtor, constructorValidityMatrixMkInfo,
    ConstantInfo.type, ConstantInfo.toConstantVal,
    AddInductive.Context.pushLocalDecl, AddInductive.Context.freshExpr,
    AddInductive.Context.freshFVarId, Expr.bindingDomain!, Expr.bindingBody!,
    Expr.instantiate1_eq, Expr.instantiate1']

def cvmValidationProofPStateTest : TypeChecker.State :=
  cvmInferOnlyInsertTest ({} : TypeChecker.State)
    (.fvar cvmValidationPIdTest) cvmValidationPDomainTest

def cvmValidationProofFinalStateTest : TypeChecker.State :=
  cvmInferOnlyInsertTest cvmValidationProofPStateTest cvmCtorProofDomain
    (.sort .zero)

theorem cvmValidationProofInferOnlyTest :
    TypeChecker.Inner.inferType cvmCtorProofDomain true
      (TypeChecker.Methods.withFuel cvmValidationXContextTest.fuel.recDepth)
      cvmValidationXContextTest.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort .zero, cvmValidationProofFinalStateTest) := by
  rw [cvmCtorProofDomainValidationShapeTest]
  change TypeChecker.Inner.inferType'
    (.app (.fvar cvmValidationPIdTest) (.fvar cvmValidationXIdTest)) true
    (TypeChecker.Methods.withFuel 9999)
    cvmValidationXContextTest.toTypeChecker ({} : TypeChecker.State) = _
  have pRun : TypeChecker.Inner.inferType'
      (.fvar cvmValidationPIdTest) true
      (TypeChecker.Methods.withFuel 9998)
      cvmValidationXContextTest.toTypeChecker ({} : TypeChecker.State) =
        .ok (cvmValidationPDomainTest, cvmValidationProofPStateTest) := by
    simpa [cvmValidationProofPStateTest] using
      cvmInferTypeFVarOnlyCoreTest 9998 cvmValidationXContextTest
        ({} : TypeChecker.State) cvmValidationPIdTest
        cvmValidationPDomainTest Std.HashMap.getElem?_empty
        cvmValidationPFindInXTest
  have appFn :
      ((.app (.fvar cvmValidationPIdTest)
        (.fvar cvmValidationXIdTest) : Expr).getAppFn) =
          .fvar cvmValidationPIdTest := by
    rfl
  have appArgs :
      ((.app (.fvar cvmValidationPIdTest)
        (.fvar cvmValidationXIdTest) : Expr).getAppArgs) =
          #[.fvar cvmValidationXIdTest] := by
    rfl
  have closedApp :
      (.app (.fvar cvmValidationPIdTest)
        (.fvar cvmValidationXIdTest) : Expr).hasLooseBVars = false := by
    apply Expr.hasLooseBVars_eq_false_of_bounded <;>
      simp [Expr.looseBVarRange']
  have resultInstantiate :
      (.sort .zero : Expr).instantiate
          #[.fvar cvmValidationXIdTest] = .sort .zero :=
    Expr.instantiate_eq_self (by rfl)
  unfold TypeChecker.Inner.inferType'
  simp [closedApp, TypeChecker.Inner.inferApp,
    TypeChecker.Inner.inferApp.loop, appFn, appArgs, pRun, cvmValidationPDomainTest,
    cvmValidationProofFinalStateTest, cvmValidationProofPStateTest, cvmInferOnlyInsertTest,
    cvmCtorProofDomainValidationShapeTest, Expr.instantiateRevRange_eq,
    Expr.instantiateRev_eq, resultInstantiate,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem cvmValidationProofEnsureTest :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨cvmValidationXContextTest, cvmCtorProofDomain, .sort .zero⟩ :=
  cvmEnsureTypeOfInferOnlyTest cvmValidationXContextTest
    cvmCtorProofDomain .zero cvmValidationProofFinalStateTest
    cvmValidationProofInferOnlyTest

def cvmValidationProofContextTest : AddInductive.Context :=
  cvmValidationXContextTest.pushLocalDecl `proof .default
    (AddInductive.consumeTypeAnnotations cvmCtorProofDomain)

theorem cvmValidationXFreshEqTest :
    cvmValidationXContextTest.freshExpr = cvmCtorXContext.freshExpr := by
  simp [cvmValidationXContextTest, cvmValidationRootContextTest,
    cvmValidationFamilyContextTest, cvmValidationAlphaContextTest,
    cvmValidationPDomainTest, cvmCtorXContext, cvmCtorPContext,
    cvmCtorAlphaContext, cvmCtorXDomain, cvmCtorAfterP,
    cvmCtorAfterAlpha, cvmFamilyContext, cvmConstructorContext,
    constructorValidityMatrixContext, constructorValidityMatrixKernelCtor,
    constructorValidityMatrixMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    AddInductive.consumeTypeAnnotations, Expr.bindingDomain!,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem cvmSecondFieldSourceTest :
    cvmCtorAfterX.bindingBody!.instantiate1
        cvmValidationXContextTest.freshExpr = cvmCtorAfterProof := by
  unfold cvmCtorAfterProof
  rw [cvmValidationXFreshEqTest]

theorem cvmCtorAfterProofForallTest :
    cvmCtorAfterProof = .forallE `direct cvmCtorDirectDomain
      cvmCtorAfterProof.bindingBody! .default := by
  simp_cvm_ctor_expr

@[simp] theorem cvmInferConstantFamilyOnlyTest
    (context : AddInductive.Context)
    (envEq : context.env = cvmConstructorContext.env) :
    TypeChecker.Inner.inferConstant context.toTypeChecker
        constructorValidityMatrixKernelType.name [.param `u] true =
      .ok constructorValidityMatrixKernelType.type := by
  have familyGet : cvmConstructorContext.env.get
      constructorValidityMatrixKernelType.name = .ok cvmDeclaredInfo := by
    unfold Kernel.Environment.get
    rw [cvmCtorFamilyLookup]
    rfl
  unfold TypeChecker.Inner.inferConstant
  simp only [AddInductive.Context.toTypeChecker]
  rw [envEq, familyGet]
  have terminalLparams :
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lparams =
        [`u] := by
    exact cvmTerminalLparams_eq
  unfold cvmDeclaredInfo AddInductive.singletonDeclaredInfo
  rw [terminalLparams]
  simp [constructorValidityMatrixKernelType, constructorValidityMatrixInfo,
    ConstantInfo.levelParams, ConstantInfo.instantiateTypeLevelParamsCpp,
    ConstantInfo.type, ConstantInfo.toConstantVal,
    Expr.instantiateLevelParamsCpp_eq, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  simp [Expr.instantiateLevelParamsCoreCpp', Level.substParamsCpp', ConstantInfo.type,
    ConstantInfo.toConstantVal]

theorem cvmKernelFamilyTypeShapeTest :
    constructorValidityMatrixKernelType.type =
      .forallE `α (.sort (.succ (.param `u)))
        (.forallE `P
          (.forallE cvmValidationIndexNameTest (.bvar 0) (.sort .zero)
            .default)
          (.sort (.succ (.param `u))) .default)
        .default := by
  rfl

@[simp] theorem cvmMkLevelIMaxSuccParamSelfTest :
    mkLevelIMaxCpp (.succ (.param `u)) (.succ (.param `u)) =
      .succ (.param `u) := by
  simp [mkLevelIMaxCpp, mkLevelIMaxCoreCpp, mkLevelMaxCpp,
    mkLevelMaxCoreCpp]

def cvmValidationFamilyOnlyStateTest : TypeChecker.State :=
  cvmInferOnlyInsertTest ({} : TypeChecker.State)
    (.const constructorValidityMatrixKernelType.name [.param `u])
    constructorValidityMatrixKernelType.type

theorem cvmInferTypeFamilyOnlyCoreTest
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State)
    (cacheMiss : state.inferTypeI[
      (.const constructorValidityMatrixKernelType.name
        [.param `u] : Expr)]? = none)
    (envEq : context.env = cvmConstructorContext.env) :
    TypeChecker.Inner.inferType'
      (.const constructorValidityMatrixKernelType.name [.param `u]) true
      (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
        .ok (constructorValidityMatrixKernelType.type,
          cvmInferOnlyInsertTest state
            (.const constructorValidityMatrixKernelType.name [.param `u])
            constructorValidityMatrixKernelType.type) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange', cacheMiss,
    cvmInferConstantFamilyOnlyTest context envEq,
    cvmInferOnlyInsertTest, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

def cvmValidationFamilyApplicationTest (alpha predicate : Expr) : Expr :=
  .app
    (.app (.const constructorValidityMatrixKernelType.name [.param `u]) alpha)
    predicate

def cvmValidationFamilyApplicationStateTest
    (alpha predicate : Expr) : TypeChecker.State :=
  cvmInferOnlyInsertTest cvmValidationFamilyOnlyStateTest
    (cvmValidationFamilyApplicationTest alpha predicate)
    (.sort (.succ (.param `u)))

theorem cvmInferTypeFamilyApplicationOnlyTest
    (context : AddInductive.Context) (alpha predicate : Expr)
    (envEq : context.env = cvmConstructorContext.env)
    (depth : context.fuel.recDepth = 10000)
    (closed :
      (cvmValidationFamilyApplicationTest alpha predicate).hasLooseBVars =
        false) :
    TypeChecker.Inner.inferType
      (cvmValidationFamilyApplicationTest alpha predicate) true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFamilyApplicationStateTest alpha predicate) := by
  rw [depth]
  unfold cvmValidationFamilyApplicationTest at closed ⊢
  change TypeChecker.Inner.inferType'
    (.app
      (.app (.const constructorValidityMatrixKernelType.name [.param `u])
        alpha) predicate) true
    (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
    ({} : TypeChecker.State) = _
  have familyRun : TypeChecker.Inner.inferType'
      (.const constructorValidityMatrixKernelType.name [.param `u]) true
      (TypeChecker.Methods.withFuel 9998) context.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (constructorValidityMatrixKernelType.type,
          cvmValidationFamilyOnlyStateTest) := by
    simpa [cvmValidationFamilyOnlyStateTest] using
      cvmInferTypeFamilyOnlyCoreTest 9998 context
        ({} : TypeChecker.State) Std.HashMap.getElem?_empty envEq
  have appFn :
      ((.app
        (.app (.const constructorValidityMatrixKernelType.name [.param `u])
          alpha) predicate : Expr).getAppFn) =
        .const constructorValidityMatrixKernelType.name [.param `u] := by
    rfl
  have appArgs :
      ((.app
        (.app (.const constructorValidityMatrixKernelType.name [.param `u])
          alpha) predicate : Expr).getAppArgs) =
        #[alpha, predicate] := by
    rfl
  have resultInstantiate :
      (.sort (.succ (.param `u)) : Expr).instantiate
          #[predicate, alpha] = .sort (.succ (.param `u)) :=
    Expr.instantiate_eq_self (by rfl)
  unfold TypeChecker.Inner.inferType'
  rw [closed]
  simp [TypeChecker.Inner.inferApp, TypeChecker.Inner.inferApp.loop,
    appFn, appArgs, familyRun,
    cvmValidationFamilyApplicationTest,
    cvmValidationFamilyApplicationStateTest,
    cvmValidationFamilyOnlyStateTest, cvmInferOnlyInsertTest,
    cvmKernelFamilyTypeShapeTest,
    Expr.instantiateRevRange_eq, Expr.instantiateRev_eq,
    resultInstantiate,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

def cvmValidationFamilyOnlyStateFromTest
    (state : TypeChecker.State) : TypeChecker.State :=
  cvmInferOnlyInsertTest state
    (.const constructorValidityMatrixKernelType.name [.param `u])
    constructorValidityMatrixKernelType.type

def cvmValidationFamilyApplicationStateFromTest
    (state : TypeChecker.State) (alpha predicate : Expr) :
    TypeChecker.State :=
  cvmInferOnlyInsertTest (cvmValidationFamilyOnlyStateFromTest state)
    (cvmValidationFamilyApplicationTest alpha predicate)
    (.sort (.succ (.param `u)))

theorem cvmInferTypeFamilyApplicationOnlyCoreTest
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (alpha predicate : Expr)
    (familyMiss : state.inferTypeI[
      (.const constructorValidityMatrixKernelType.name
        [.param `u] : Expr)]? = none)
    (applicationMiss : state.inferTypeI[
      cvmValidationFamilyApplicationTest alpha predicate]? = none)
    (envEq : context.env = cvmConstructorContext.env)
    (closed :
      (cvmValidationFamilyApplicationTest alpha predicate).hasLooseBVars =
        false) :
    TypeChecker.Inner.inferType'
      (cvmValidationFamilyApplicationTest alpha predicate) true
      (TypeChecker.Methods.withFuel (fuel + 1)) context.toTypeChecker state =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFamilyApplicationStateFromTest state alpha predicate) := by
  have familyRun : TypeChecker.Inner.inferType'
      (.const constructorValidityMatrixKernelType.name [.param `u]) true
      (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
        .ok (constructorValidityMatrixKernelType.type,
          cvmValidationFamilyOnlyStateFromTest state) := by
    simpa [cvmValidationFamilyOnlyStateFromTest] using
      cvmInferTypeFamilyOnlyCoreTest fuel context state familyMiss envEq
  unfold cvmValidationFamilyApplicationTest at applicationMiss closed ⊢
  have appFn :
      ((.app
        (.app (.const constructorValidityMatrixKernelType.name [.param `u])
          alpha) predicate : Expr).getAppFn) =
        .const constructorValidityMatrixKernelType.name [.param `u] := by
    rfl
  have appArgs :
      ((.app
        (.app (.const constructorValidityMatrixKernelType.name [.param `u])
        alpha) predicate : Expr).getAppArgs) = #[alpha, predicate] := by
    rfl
  have resultInstantiate :
      (.sort (.succ (.param `u)) : Expr).instantiate
          #[predicate, alpha] = .sort (.succ (.param `u)) :=
    Expr.instantiate_eq_self (by rfl)
  unfold TypeChecker.Inner.inferType'
  rw [closed]
  simp [applicationMiss, TypeChecker.Inner.inferApp,
    TypeChecker.Inner.inferApp.loop, appFn, appArgs, familyRun,
    cvmValidationFamilyApplicationTest,
    cvmValidationFamilyApplicationStateFromTest,
    cvmValidationFamilyOnlyStateFromTest, cvmInferOnlyInsertTest,
    cvmKernelFamilyTypeShapeTest,
    Expr.instantiateRevRange_eq, Expr.instantiateRev_eq,
    resultInstantiate,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem cvmInferTypeForallOnlyCoreTest
    (fuel : Nat) (context : TypeChecker.Context)
    (state finalState : TypeChecker.State)
    (name : Name) (domain body result : Expr) (bi : BinderInfo)
    (closed : (.forallE name domain body bi : Expr).hasLooseBVars = false)
    (cacheMiss : state.inferTypeI[
      (.forallE name domain body bi : Expr)]? = none)
    (forallRun : TypeChecker.Inner.inferForall
      (.forallE name domain body bi) true
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (result, finalState)) :
    TypeChecker.Inner.inferType'
      (.forallE name domain body bi) true
      (TypeChecker.Methods.withFuel fuel) context state =
        .ok (result, cvmInferOnlyInsertTest finalState
          (.forallE name domain body bi) result) := by
  unfold TypeChecker.Inner.inferType'
  simp [closed, cacheMiss, forallRun, cvmInferOnlyInsertTest,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem cvmCtorDirectDomainValidationShapeTest :
    cvmCtorDirectDomain = cvmValidationFamilyApplicationTest
      (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest) := by
  simp [cvmCtorDirectDomain, cvmCtorAfterProof, cvmCtorAfterX,
    cvmCtorAfterP, cvmCtorAfterAlpha, cvmValidationFamilyApplicationTest,
    cvmValidationAlphaIdTest, cvmValidationPIdTest,
    cvmValidationAlphaContextTest, cvmFamilyContext,
    cvmCtorXContext, cvmCtorPContext, cvmCtorAlphaContext,
    cvmConstructorContext, constructorValidityMatrixContext,
    constructorValidityMatrixKernelCtor, constructorValidityMatrixKernelType,
    constructorValidityMatrixMkInfo, constructorValidityMatrixInfo,
    ConstantInfo.name, ConstantInfo.type, ConstantInfo.toConstantVal,
    AddInductive.Context.pushLocalDecl, AddInductive.Context.freshExpr,
    AddInductive.Context.freshFVarId, Expr.bindingDomain!,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem cvmValidationProofEnvTest :
    cvmValidationProofContextTest.env = cvmConstructorContext.env := by
  rfl

theorem cvmValidationProofDepthTest :
    cvmValidationProofContextTest.fuel.recDepth = 10000 := by
  rfl

theorem cvmValidationDirectEnsureTest :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨cvmValidationProofContextTest, cvmCtorDirectDomain,
        .sort (.succ (.param `u))⟩ := by
  rw [cvmCtorDirectDomainValidationShapeTest]
  exact cvmEnsureTypeOfInferOnlyTest cvmValidationProofContextTest
    (cvmValidationFamilyApplicationTest (.fvar cvmValidationAlphaIdTest)
      (.fvar cvmValidationPIdTest)) (.succ (.param `u))
    (cvmValidationFamilyApplicationStateTest
      (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
    (cvmInferTypeFamilyApplicationOnlyTest cvmValidationProofContextTest
      (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest)
      cvmValidationProofEnvTest cvmValidationProofDepthTest
      (by
        apply Expr.hasLooseBVars_eq_false_of_bounded <;>
          simp [cvmValidationFamilyApplicationTest,
            Expr.looseBVarRange']))

def cvmValidationDirectContextTest : AddInductive.Context :=
  cvmValidationProofContextTest.pushLocalDecl `direct .default
    (AddInductive.consumeTypeAnnotations cvmCtorDirectDomain)

theorem cvmValidationProofFreshEqTest :
    cvmValidationProofContextTest.freshExpr =
      cvmCtorProofContext.freshExpr := by
  simp [cvmValidationProofContextTest, cvmValidationXContextTest,
    cvmValidationRootContextTest, cvmValidationFamilyContextTest,
    cvmValidationAlphaContextTest, cvmValidationPDomainTest,
    cvmCtorProofContext, cvmCtorXContext, cvmCtorPContext,
    cvmCtorAlphaContext, cvmCtorProofDomain, cvmCtorAfterX,
    cvmCtorAfterP, cvmCtorAfterAlpha, cvmCtorXDomain,
    cvmFamilyContext, cvmConstructorContext,
    constructorValidityMatrixContext, constructorValidityMatrixKernelCtor,
    constructorValidityMatrixMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    AddInductive.consumeTypeAnnotations, Expr.bindingDomain!,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem cvmThirdFieldSourceTest :
    cvmCtorAfterProof.bindingBody!.instantiate1
        cvmValidationProofContextTest.freshExpr = cvmCtorAfterDirect := by
  unfold cvmCtorAfterDirect
  rw [cvmValidationProofFreshEqTest]

theorem cvmCtorAfterDirectForallTest :
    cvmCtorAfterDirect = .forallE `function cvmCtorFunctionDomain
      cvmCtorAfterDirect.bindingBody! .default := by
  simp_cvm_ctor_expr

theorem cvmValidationProofLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmValidationProofContextTest :=
  cvmValidationXLocalRunTest.push `proof .default
    (AddInductive.consumeTypeAnnotations cvmCtorProofDomain)

theorem cvmValidationDirectLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmValidationDirectContextTest :=
  cvmValidationProofLocalRunTest.push `direct .default
    (AddInductive.consumeTypeAnnotations cvmCtorDirectDomain)

theorem cvmValidationAlphaFindInXTest :
    cvmValidationXContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmValidationRootLocalRunTest.push_findOld `x .default
    (AddInductive.consumeTypeAnnotations cvmCtorXDomain)
    cvmValidationAlphaFindTest

theorem cvmValidationAlphaFindInProofTest :
    cvmValidationProofContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmValidationXLocalRunTest.push_findOld `proof .default
    (AddInductive.consumeTypeAnnotations cvmCtorProofDomain)
    cvmValidationAlphaFindInXTest

theorem cvmValidationAlphaFindInDirectTest :
    cvmValidationDirectContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmValidationProofLocalRunTest.push_findOld `direct .default
    (AddInductive.consumeTypeAnnotations cvmCtorDirectDomain)
    cvmValidationAlphaFindInProofTest

theorem cvmCtorFunctionDomainValidationShapeTest :
    cvmCtorFunctionDomain =
      .forallE `y (.fvar cvmValidationAlphaIdTest)
        (cvmValidationFamilyApplicationTest
          (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
        .default := by
  simp [cvmCtorFunctionDomain, cvmCtorAfterDirect, cvmCtorAfterProof,
    cvmCtorAfterX, cvmCtorAfterP, cvmCtorAfterAlpha,
    cvmValidationFamilyApplicationTest, cvmValidationAlphaIdTest,
    cvmValidationPIdTest, cvmValidationAlphaContextTest,
    cvmFamilyContext, cvmCtorProofContext, cvmCtorXContext,
    cvmCtorPContext, cvmCtorAlphaContext, cvmConstructorContext,
    constructorValidityMatrixContext, constructorValidityMatrixKernelCtor,
    constructorValidityMatrixKernelType, constructorValidityMatrixMkInfo,
    constructorValidityMatrixInfo, ConstantInfo.name, ConstantInfo.type,
    ConstantInfo.toConstantVal, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    Expr.bindingDomain!, Expr.bindingBody!, Expr.instantiate1_eq,
    Expr.instantiate1']

def cvmValidationFunctionAlphaStateTest : TypeChecker.State :=
  cvmInferOnlyInsertTest ({} : TypeChecker.State)
    (.fvar cvmValidationAlphaIdTest) (.sort (.succ (.param `u)))

def cvmValidationFunctionInternalIdTest : FVarId :=
  ⟨cvmValidationFunctionAlphaStateTest.ngen.curr⟩

def cvmValidationFunctionInternalStateTest : TypeChecker.State :=
  { cvmValidationFunctionAlphaStateTest with
    ngen := cvmValidationFunctionAlphaStateTest.ngen.next }

def cvmValidationFunctionInternalContextTest : AddInductive.Context :=
  { cvmValidationDirectContextTest with
    lctx := cvmValidationDirectContextTest.lctx.mkLocalDecl
      cvmValidationFunctionInternalIdTest `y
      (.fvar cvmValidationAlphaIdTest) .default }

def cvmValidationFunctionBodyFinalStateTest : TypeChecker.State :=
  cvmValidationFamilyApplicationStateFromTest
    cvmValidationFunctionInternalStateTest
    (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest)

def cvmValidationFunctionFinalStateTest : TypeChecker.State :=
  cvmInferOnlyInsertTest cvmValidationFunctionBodyFinalStateTest
    cvmCtorFunctionDomain (.sort (.succ (.param `u)))

theorem cvmValidationFunctionInferOnlyTest :
    TypeChecker.Inner.inferType cvmCtorFunctionDomain true
      (TypeChecker.Methods.withFuel
        cvmValidationDirectContextTest.fuel.recDepth)
      cvmValidationDirectContextTest.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFunctionFinalStateTest) := by
  have domainRun : TypeChecker.Inner.inferType'
      (.fvar cvmValidationAlphaIdTest) true
      (TypeChecker.Methods.withFuel 9998)
      cvmValidationDirectContextTest.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFunctionAlphaStateTest) := by
    simpa [cvmValidationFunctionAlphaStateTest] using
      cvmInferTypeFVarOnlyCoreTest 9998 cvmValidationDirectContextTest
        ({} : TypeChecker.State) cvmValidationAlphaIdTest
        (.sort (.succ (.param `u))) Std.HashMap.getElem?_empty
        cvmValidationAlphaFindInDirectTest
  have familyMiss : cvmValidationFunctionInternalStateTest.inferTypeI[
      (.const constructorValidityMatrixKernelType.name
        [.param `u] : Expr)]? = none := by
    simp [cvmValidationFunctionInternalStateTest,
      cvmValidationFunctionAlphaStateTest, cvmInferOnlyInsertTest]
  have applicationMiss :
      cvmValidationFunctionInternalStateTest.inferTypeI[
        cvmValidationFamilyApplicationTest
          (.fvar cvmValidationAlphaIdTest)
          (.fvar cvmValidationPIdTest)]? = none := by
    simp [cvmValidationFunctionInternalStateTest,
      cvmValidationFunctionAlphaStateTest, cvmInferOnlyInsertTest,
      cvmValidationFamilyApplicationTest]
  have bodyRun : TypeChecker.Inner.inferType'
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest)) true
      (TypeChecker.Methods.withFuel 9998)
      cvmValidationFunctionInternalContextTest.toTypeChecker
      cvmValidationFunctionInternalStateTest =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFunctionBodyFinalStateTest) := by
    simpa [cvmValidationFunctionBodyFinalStateTest] using
      cvmInferTypeFamilyApplicationOnlyCoreTest 9997
        cvmValidationFunctionInternalContextTest
        cvmValidationFunctionInternalStateTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest)
        familyMiss applicationMiss (by rfl)
        (by
          apply Expr.hasLooseBVars_eq_false_of_bounded <;>
            simp [cvmValidationFamilyApplicationTest,
              Expr.looseBVarRange'])
  have forallRun : TypeChecker.Inner.inferForall
      (.forallE `y (.fvar cvmValidationAlphaIdTest)
        (cvmValidationFamilyApplicationTest
          (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
        .default) true
      (TypeChecker.Methods.withFuel 9999)
      cvmValidationDirectContextTest.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFunctionBodyFinalStateTest) := by
    unfold TypeChecker.Inner.inferForall
    simp only [cvmValidationFamilyApplicationTest,
      TypeChecker.Inner.inferForall.loop]
    rw [show (.fvar cvmValidationAlphaIdTest : Expr).instantiateRev #[] =
        .fvar cvmValidationAlphaIdTest by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType
        (.fvar cvmValidationAlphaIdTest) true
        (TypeChecker.Methods.withFuel 9999)
        cvmValidationDirectContextTest.toTypeChecker
        ({} : TypeChecker.State) =
          TypeChecker.Inner.inferType'
            (.fvar cvmValidationAlphaIdTest) true
            (TypeChecker.Methods.withFuel 9998)
            cvmValidationDirectContextTest.toTypeChecker
            ({} : TypeChecker.State) by rfl]
    rw [domainRun]
    simp only [prbEnsureSortExact]
    rw [prbWithLocalDeclEq]
    change TypeChecker.Inner.inferForall.loop true
      #[Expr.fvar cvmValidationFunctionInternalIdTest]
      #[Level.succ (.param `u)]
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
      (TypeChecker.Methods.withFuel 9999)
      cvmValidationFunctionInternalContextTest.toTypeChecker
      cvmValidationFunctionInternalStateTest = _
    simp only [cvmValidationFamilyApplicationTest,
      TypeChecker.Inner.inferForall.loop]
    rw [show (((.const constructorValidityMatrixKernelType.name
          [.param `u] : Expr).app (.fvar cvmValidationAlphaIdTest)).app
          (.fvar cvmValidationPIdTest)).instantiateRev
          #[Expr.fvar cvmValidationFunctionInternalIdTest] =
        ((.const constructorValidityMatrixKernelType.name
          [.param `u] : Expr).app (.fvar cvmValidationAlphaIdTest)).app
          (.fvar cvmValidationPIdTest) by
      simp only [Expr.instantiateRev_eq]
      exact Expr.instantiate_eq_self (by
        simp [Expr.looseBVarRange'])]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    have bodyRunExplicit : TypeChecker.Inner.inferType'
        (((.const constructorValidityMatrixKernelType.name
          [.param `u] : Expr).app (.fvar cvmValidationAlphaIdTest)).app
          (.fvar cvmValidationPIdTest)) true
        (TypeChecker.Methods.withFuel 9998)
        cvmValidationFunctionInternalContextTest.toTypeChecker
        cvmValidationFunctionInternalStateTest =
          .ok (.sort (.succ (.param `u)),
            cvmValidationFunctionBodyFinalStateTest) := by
      simpa [cvmValidationFamilyApplicationTest] using bodyRun
    rw [show TypeChecker.Inner.inferType
        (((.const constructorValidityMatrixKernelType.name
          [.param `u] : Expr).app (.fvar cvmValidationAlphaIdTest)).app
          (.fvar cvmValidationPIdTest)) true
        (TypeChecker.Methods.withFuel 9999)
        cvmValidationFunctionInternalContextTest.toTypeChecker
        cvmValidationFunctionInternalStateTest =
          TypeChecker.Inner.inferType'
            (((.const constructorValidityMatrixKernelType.name
              [.param `u] : Expr).app
              (.fvar cvmValidationAlphaIdTest)).app
              (.fvar cvmValidationPIdTest)) true
            (TypeChecker.Methods.withFuel 9998)
            cvmValidationFunctionInternalContextTest.toTypeChecker
            cvmValidationFunctionInternalStateTest by rfl]
    rw [bodyRunExplicit]
    simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
      StateT.pure, Except.pure]
  have outerRun := cvmInferTypeForallOnlyCoreTest 9999
    cvmValidationDirectContextTest.toTypeChecker
    ({} : TypeChecker.State) cvmValidationFunctionBodyFinalStateTest
    `y (.fvar cvmValidationAlphaIdTest)
    (cvmValidationFamilyApplicationTest
      (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
    (.sort (.succ (.param `u))) .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [cvmValidationFamilyApplicationTest,
          Expr.looseBVarRange'])
    Std.HashMap.getElem?_empty forallRun
  change TypeChecker.Inner.inferType' cvmCtorFunctionDomain true
    (TypeChecker.Methods.withFuel 9999)
    cvmValidationDirectContextTest.toTypeChecker
    ({} : TypeChecker.State) = _
  simpa [cvmCtorFunctionDomainValidationShapeTest,
    cvmValidationFunctionFinalStateTest] using outerRun

theorem cvmValidationFunctionEnsureTest :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨cvmValidationDirectContextTest, cvmCtorFunctionDomain,
        .sort (.succ (.param `u))⟩ :=
  cvmEnsureTypeOfInferOnlyTest cvmValidationDirectContextTest
    cvmCtorFunctionDomain (.succ (.param `u))
    cvmValidationFunctionFinalStateTest
    cvmValidationFunctionInferOnlyTest

def cvmValidationFunctionContextTest : AddInductive.Context :=
  cvmValidationDirectContextTest.pushLocalDecl `function .default
    (AddInductive.consumeTypeAnnotations cvmCtorFunctionDomain)

theorem cvmValidationDirectFreshEqTest :
    cvmValidationDirectContextTest.freshExpr =
      cvmCtorDirectContext.freshExpr := by
  simp [cvmValidationDirectContextTest, cvmValidationProofContextTest,
    cvmValidationXContextTest, cvmValidationRootContextTest,
    cvmValidationFamilyContextTest, cvmValidationAlphaContextTest,
    cvmValidationPDomainTest, cvmCtorDirectContext,
    cvmCtorProofContext, cvmCtorXContext, cvmCtorPContext,
    cvmCtorAlphaContext, cvmCtorDirectDomain, cvmCtorAfterProof,
    cvmCtorProofDomain, cvmCtorAfterX, cvmCtorXDomain, cvmCtorAfterP,
    cvmCtorAfterAlpha, cvmFamilyContext, cvmConstructorContext,
    constructorValidityMatrixContext, constructorValidityMatrixKernelCtor,
    constructorValidityMatrixMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    AddInductive.consumeTypeAnnotations, Expr.bindingDomain!,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem cvmFourthFieldSourceTest :
    cvmCtorAfterDirect.bindingBody!.instantiate1
        cvmValidationDirectContextTest.freshExpr = cvmCtorAfterFunction := by
  unfold cvmCtorAfterFunction
  rw [cvmValidationDirectFreshEqTest]

theorem cvmCtorAfterFunctionForallTest :
    cvmCtorAfterFunction = .forallE `later cvmCtorLaterDomain
      cvmCtorAfterFunction.bindingBody! .default := by
  simp_cvm_ctor_expr

theorem cvmValidationFunctionLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmValidationFunctionContextTest :=
  cvmValidationDirectLocalRunTest.push `function .default
    (AddInductive.consumeTypeAnnotations cvmCtorFunctionDomain)

theorem cvmValidationAlphaFindInFunctionTest :
    cvmValidationFunctionContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmValidationDirectLocalRunTest.push_findOld `function .default
    (AddInductive.consumeTypeAnnotations cvmCtorFunctionDomain)
    cvmValidationAlphaFindInDirectTest

theorem cvmCtorLaterDomainValidationShapeTest :
    cvmCtorLaterDomain = .fvar cvmValidationAlphaIdTest := by
  simp [cvmCtorLaterDomain, cvmCtorAfterFunction, cvmCtorAfterDirect,
    cvmCtorAfterProof, cvmCtorAfterX, cvmCtorAfterP, cvmCtorAfterAlpha,
    cvmValidationAlphaIdTest, cvmFamilyContext,
    cvmCtorDirectContext, cvmCtorProofContext, cvmCtorXContext,
    cvmCtorPContext, cvmCtorAlphaContext, cvmConstructorContext,
    constructorValidityMatrixContext, constructorValidityMatrixKernelCtor,
    constructorValidityMatrixMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    Expr.bindingDomain!, Expr.bindingBody!, Expr.instantiate1_eq,
    Expr.instantiate1']

theorem cvmValidationFunctionDepthTest :
    cvmValidationFunctionContextTest.fuel.recDepth = 10000 := by
  rfl

theorem cvmValidationLaterEnsureTest :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨cvmValidationFunctionContextTest, cvmCtorLaterDomain,
        .sort (.succ (.param `u))⟩ := by
  rw [cvmCtorLaterDomainValidationShapeTest]
  exact prbPreFamilyFVarEnsureValidReplay
    cvmValidationFunctionContextTest cvmValidationAlphaIdTest
    (.succ (.param `u)) cvmValidationAlphaFindInFunctionTest
    cvmValidationFunctionDepthTest

def cvmValidationLaterContextTest : AddInductive.Context :=
  cvmValidationFunctionContextTest.pushLocalDecl `later .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain)

theorem cvmValidationFunctionFreshEqTest :
    cvmValidationFunctionContextTest.freshExpr =
      cvmCtorFunctionContext.freshExpr := by
  simp [cvmValidationFunctionContextTest, cvmValidationDirectContextTest,
    cvmValidationProofContextTest, cvmValidationXContextTest,
    cvmValidationRootContextTest, cvmValidationFamilyContextTest,
    cvmValidationAlphaContextTest, cvmValidationPDomainTest,
    cvmCtorFunctionContext, cvmCtorDirectContext,
    cvmCtorProofContext, cvmCtorXContext, cvmCtorPContext,
    cvmCtorAlphaContext, cvmCtorFunctionDomain, cvmCtorAfterDirect,
    cvmCtorDirectDomain, cvmCtorAfterProof, cvmCtorProofDomain,
    cvmCtorAfterX, cvmCtorXDomain, cvmCtorAfterP, cvmCtorAfterAlpha,
    cvmFamilyContext, cvmConstructorContext,
    constructorValidityMatrixContext, constructorValidityMatrixKernelCtor,
    constructorValidityMatrixMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    AddInductive.consumeTypeAnnotations, Expr.bindingDomain!,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem cvmFifthFieldSourceTest :
    cvmCtorAfterFunction.bindingBody!.instantiate1
        cvmValidationFunctionContextTest.freshExpr = cvmCtorAfterLater := by
  unfold cvmCtorAfterLater
  rw [cvmValidationFunctionFreshEqTest]

theorem cvmCtorAfterLaterForallTest :
    cvmCtorAfterLater = .forallE `laterProof cvmCtorLaterProofDomain
      cvmCtorAfterLater.bindingBody! .default := by
  simp_cvm_ctor_expr

def cvmValidationPredicateApplicationTest
    (predicate : FVarId) (argument : Expr) : Expr :=
  .app (.fvar predicate) argument

def cvmValidationPredicateStateTest
    (predicate : FVarId) : TypeChecker.State :=
  cvmInferOnlyInsertTest ({} : TypeChecker.State) (.fvar predicate)
    cvmValidationPDomainTest

def cvmValidationPredicateApplicationStateTest
    (predicate : FVarId) (argument : Expr) : TypeChecker.State :=
  cvmInferOnlyInsertTest (cvmValidationPredicateStateTest predicate)
    (cvmValidationPredicateApplicationTest predicate argument)
    (.sort .zero)

theorem cvmInferTypePredicateApplicationOnlyTest
    (context : AddInductive.Context) (predicate : FVarId)
    (argument : Expr)
    (find : context.lctx.find? predicate =
      some (.cdecl index predicate name cvmValidationPDomainTest bi kind))
    (depth : context.fuel.recDepth = 10000)
    (closed :
      (cvmValidationPredicateApplicationTest predicate argument).hasLooseBVars =
        false) :
    TypeChecker.Inner.inferType
      (cvmValidationPredicateApplicationTest predicate argument) true
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (.sort .zero,
          cvmValidationPredicateApplicationStateTest predicate argument) := by
  rw [depth]
  unfold cvmValidationPredicateApplicationTest at closed ⊢
  change TypeChecker.Inner.inferType'
    (.app (.fvar predicate) argument) true
    (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
    ({} : TypeChecker.State) = _
  have predicateRun : TypeChecker.Inner.inferType'
      (.fvar predicate) true (TypeChecker.Methods.withFuel 9998)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (cvmValidationPDomainTest,
          cvmValidationPredicateStateTest predicate) := by
    simpa [cvmValidationPredicateStateTest] using
      cvmInferTypeFVarOnlyCoreTest 9998 context
        ({} : TypeChecker.State) predicate cvmValidationPDomainTest
        Std.HashMap.getElem?_empty find
  have appFn : ((.app (.fvar predicate) argument : Expr).getAppFn) =
      .fvar predicate := by
    rfl
  have appArgs : ((.app (.fvar predicate) argument : Expr).getAppArgs) =
      #[argument] := by
    rfl
  have resultInstantiate :
      (.sort .zero : Expr).instantiate #[argument] = .sort .zero :=
    Expr.instantiate_eq_self (by rfl)
  unfold TypeChecker.Inner.inferType'
  rw [closed]
  simp [TypeChecker.Inner.inferApp, TypeChecker.Inner.inferApp.loop, appFn, appArgs, predicateRun,
    cvmValidationPDomainTest, cvmValidationPredicateApplicationTest,
    cvmValidationPredicateApplicationStateTest, cvmValidationPredicateStateTest,
    cvmInferOnlyInsertTest, Expr.instantiateRevRange_eq,
    Expr.instantiateRev_eq, resultInstantiate,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

theorem cvmValidationPFindInProofTest :
    cvmValidationProofContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmValidationXLocalRunTest.push_findOld `proof .default
    (AddInductive.consumeTypeAnnotations cvmCtorProofDomain)
    cvmValidationPFindInXTest

theorem cvmValidationPFindInDirectTest :
    cvmValidationDirectContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmValidationProofLocalRunTest.push_findOld `direct .default
    (AddInductive.consumeTypeAnnotations cvmCtorDirectDomain)
    cvmValidationPFindInProofTest

theorem cvmValidationPFindInFunctionTest :
    cvmValidationFunctionContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmValidationDirectLocalRunTest.push_findOld `function .default
    (AddInductive.consumeTypeAnnotations cvmCtorFunctionDomain)
    cvmValidationPFindInDirectTest

theorem cvmValidationLaterLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmValidationLaterContextTest :=
  cvmValidationFunctionLocalRunTest.push `later .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain)

theorem cvmValidationPFindInLaterTest :
    cvmValidationLaterContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmValidationFunctionLocalRunTest.push_findOld `later .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain)
    cvmValidationPFindInFunctionTest

def cvmValidationLaterIdTest : FVarId :=
  cvmValidationFunctionContextTest.freshFVarId

theorem cvmCtorLaterProofDomainValidationShapeTest :
    cvmCtorLaterProofDomain = cvmValidationPredicateApplicationTest
      cvmValidationPIdTest (.fvar cvmValidationLaterIdTest) := by
  simp [cvmCtorLaterProofDomain, cvmCtorAfterLater, cvmCtorAfterFunction, cvmCtorAfterDirect,
    cvmCtorAfterProof, cvmCtorAfterX, cvmCtorAfterP, cvmCtorAfterAlpha,
    cvmValidationPredicateApplicationTest, cvmValidationPIdTest, cvmValidationLaterIdTest,
    cvmValidationFunctionContextTest, cvmValidationDirectContextTest, cvmValidationProofContextTest,
    cvmValidationXContextTest, cvmValidationRootContextTest, cvmValidationFamilyContextTest,
    cvmValidationAlphaContextTest, cvmValidationPDomainTest, cvmFamilyContext,
    cvmCtorFunctionContext, cvmCtorDirectContext, cvmCtorProofContext, cvmCtorXContext,
    cvmCtorPContext, cvmCtorAlphaContext, cvmConstructorContext, constructorValidityMatrixContext,
    constructorValidityMatrixKernelCtor, constructorValidityMatrixMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, AddInductive.Context.pushLocalDecl, AddInductive.Context.freshExpr,
    AddInductive.Context.freshFVarId, Expr.bindingDomain!, Expr.bindingBody!, Expr.instantiate1_eq,
    Expr.instantiate1']

theorem cvmValidationLaterDepthTest :
    cvmValidationLaterContextTest.fuel.recDepth = 10000 := by
  rfl

theorem cvmValidationLaterProofEnsureTest :
    AddInductive.ConstructorEnsureTypeStep.Valid
      ⟨cvmValidationLaterContextTest, cvmCtorLaterProofDomain,
        .sort .zero⟩ := by
  rw [cvmCtorLaterProofDomainValidationShapeTest]
  exact cvmEnsureTypeOfInferOnlyTest cvmValidationLaterContextTest
    (cvmValidationPredicateApplicationTest cvmValidationPIdTest
      (.fvar cvmValidationLaterIdTest)) .zero
    (cvmValidationPredicateApplicationStateTest cvmValidationPIdTest
      (.fvar cvmValidationLaterIdTest))
    (cvmInferTypePredicateApplicationOnlyTest cvmValidationLaterContextTest
      cvmValidationPIdTest (.fvar cvmValidationLaterIdTest)
      cvmValidationPFindInLaterTest cvmValidationLaterDepthTest
      (by
        apply Expr.hasLooseBVars_eq_false_of_bounded <;>
          simp [cvmValidationPredicateApplicationTest,
            Expr.looseBVarRange']))

def cvmValidationLaterProofContextTest : AddInductive.Context :=
  cvmValidationLaterContextTest.pushLocalDecl `laterProof .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain)

theorem cvmValidationLaterFreshEqTest :
    cvmValidationLaterContextTest.freshExpr =
      cvmCtorLaterContext.freshExpr := by
  simp [cvmValidationLaterContextTest, cvmValidationFunctionContextTest,
    cvmValidationDirectContextTest, cvmValidationProofContextTest,
    cvmValidationXContextTest, cvmValidationRootContextTest,
    cvmValidationFamilyContextTest, cvmValidationAlphaContextTest,
    cvmValidationPDomainTest, cvmCtorLaterContext,
    cvmCtorFunctionContext, cvmCtorDirectContext,
    cvmCtorProofContext, cvmCtorXContext, cvmCtorPContext,
    cvmCtorAlphaContext, cvmCtorLaterDomain, cvmCtorAfterFunction,
    cvmCtorFunctionDomain, cvmCtorAfterDirect, cvmCtorDirectDomain,
    cvmCtorAfterProof, cvmCtorProofDomain, cvmCtorAfterX,
    cvmCtorXDomain, cvmCtorAfterP, cvmCtorAfterAlpha,
    cvmFamilyContext, cvmConstructorContext,
    constructorValidityMatrixContext, constructorValidityMatrixKernelCtor,
    constructorValidityMatrixMkInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    AddInductive.consumeTypeAnnotations, Expr.bindingDomain!,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

theorem cvmSixthFieldSourceTest :
    cvmCtorAfterLater.bindingBody!.instantiate1
        cvmValidationLaterContextTest.freshExpr = cvmCtorTerminal := by
  unfold cvmCtorTerminal
  rw [cvmValidationLaterFreshEqTest]

theorem cvmCtorTerminalValidationShapeTest :
    cvmCtorTerminal = cvmValidationFamilyApplicationTest
      (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest) := by
  simp [cvmCtorTerminal, cvmCtorAfterLater, cvmCtorAfterFunction,
    cvmCtorAfterDirect, cvmCtorAfterProof, cvmCtorAfterX,
    cvmCtorAfterP, cvmCtorAfterAlpha,
    cvmValidationFamilyApplicationTest, cvmValidationAlphaIdTest,
    cvmValidationPIdTest, cvmValidationAlphaContextTest,
    cvmFamilyContext, cvmCtorLaterContext, cvmCtorFunctionContext,
    cvmCtorDirectContext, cvmCtorProofContext, cvmCtorXContext,
    cvmCtorPContext, cvmCtorAlphaContext, cvmConstructorContext,
    constructorValidityMatrixContext, constructorValidityMatrixKernelCtor,
    constructorValidityMatrixKernelType, constructorValidityMatrixMkInfo,
    constructorValidityMatrixInfo, ConstantInfo.name, ConstantInfo.type,
    ConstantInfo.toConstantVal, AddInductive.Context.pushLocalDecl,
    AddInductive.Context.freshExpr, AddInductive.Context.freshFVarId,
    Expr.bindingBody!, Expr.instantiate1_eq, Expr.instantiate1']

def cvmConstructorValidationTest :
    AddInductive.ConstructorValidationRun
      constructorValidityMatrixKernelType cvmFamilyValidationRun.stats false
      cvmValidationRootContextTest :=
  AddInductive.ConstructorValidationRun.of_run (by
    have run : AddInductive.checkConstructors
        #[constructorValidityMatrixKernelType]
        cvmFamilyValidationRun.stats false
        cvmConstructorValidationContextTest = .ok () := by
      simpa [cvmConstructorValidationContextTest] using cvmCheckConstructorsRun
    rw [cvmConstructorValidationContextTest_root] at run
    exact run)

theorem cvmUniverseSemanticsTest :
    cvmConstructorValidationTest.trace.universeSemantics = true := by
  generalize htrace : cvmConstructorValidationTest.trace = trace
  cases trace with
  | cons seen head tail freshName closed rootCheck typeTrace tailTrace =>
      cases tailTrace with
      | nil finalSeen =>
          simp only [AddInductive.ConstructorListValidationTrace.universeSemantics,
            Bool.and_true]
          cases typeTrace with
          | parameter context fuel argIdx name domain body binderInfo parameter
              parameterType parameterAt parameterTypeRun defeq tail =>
              rw [cvmStatsParamsTest] at parameterAt
              simp at parameterAt
              cases parameterAt
              simp only [AddInductive.ConstructorTypeValidationTrace.universeSemantics]
              change AddInductive.ConstructorTypeValidationTrace
                cvmFamilyValidationRun.stats false 0
                constructorValidityMatrixKernelCtor.name
                cvmValidationRootContextTest
                (constructorValidityMatrixKernelCtor.type.bindingBody!.instantiate1
                  cvmFamilyContext.freshExpr) 1 999 at tail
              let sourceEq := cvmFirstParameterSourceTest.trans
                cvmCtorAfterAlphaForallTest
              let tail' := sourceEq ▸ tail
              refine (cvmUniverseSemanticsCastSourceTest sourceEq tail).symm.trans ?_
              change tail'.universeSemantics = true
              cases tail' with
              | parameter context fuel argIdx name domain body binderInfo parameter
                  parameterType parameterAt parameterTypeRun defeq tail =>
                  rw [cvmStatsParamsTest] at parameterAt
                  simp at parameterAt
                  cases parameterAt
                  simp only [AddInductive.ConstructorTypeValidationTrace.universeSemantics]
                  change AddInductive.ConstructorTypeValidationTrace
                    cvmFamilyValidationRun.stats false 0
                    constructorValidityMatrixKernelCtor.name
                    cvmValidationRootContextTest
                    (cvmCtorAfterAlpha.bindingBody!.instantiate1
                      cvmValidationAlphaContextTest.freshExpr) 2 998 at tail
                  let sourceEq := cvmSecondParameterSourceTest.trans
                    cvmCtorAfterPForallTest
                  let tail' := sourceEq ▸ tail
                  refine (cvmUniverseSemanticsCastSourceTest sourceEq tail).symm.trans ?_
                  change tail'.universeSemantics = true
                  cases tail' with
                  | parameter context fuel argIdx name domain body binderInfo parameter
                      parameterType parameterAt parameterTypeRun defeq tail =>
                      rw [cvmStatsParamsTest] at parameterAt
                      simp at parameterAt
                  | ordinary context fuel argIdx name domain body binderInfo sortResult
                      noParameter ensureType universeTrace positivity tail =>
                      have ensureTypeRoot :
                          AddInductive.ConstructorEnsureTypeStep.Valid
                            ⟨cvmValidationRootContextTest, cvmCtorXDomain,
                              sortResult⟩ := by
                        exact ensureType
                      have sortResultEq :
                          sortResult = .sort (.succ (.param `u)) :=
                        cvmEnsureTypeResultEqTest ensureTypeRoot
                          cvmValidationXEnsureTest
                      subst sortResult
                      simp only [AddInductive.ConstructorTypeValidationTrace.universeSemantics]
                      have universeSemantic : universeTrace.semantic = true := by
                        unfold AddInductive.ConstructorUniverseTrace.semantic
                        rw [cvmStatsResultLevelTest]
                        simp [Expr.sortLevel!, AddInductive.constructorUniverseSemanticGe,
                          AddInductive.levelStructGe, AddInductive.levelStructEq]
                      rw [universeSemantic]
                      simp only [Bool.true_and]
                      let sourceEq := cvmFirstFieldSourceTest.trans
                        cvmCtorAfterXForallTest
                      let tail' := sourceEq ▸ tail
                      refine (cvmUniverseSemanticsCastSourceTest sourceEq tail).symm.trans ?_
                      change tail'.universeSemantics = true
                      cases tail' with
                      | parameter context fuel argIdx name domain body binderInfo parameter
                          parameterType parameterAt parameterTypeRun defeq tail =>
                          rw [cvmStatsParamsTest] at parameterAt
                          simp at parameterAt
                      | ordinary context fuel argIdx name domain body binderInfo sortResult
                          noParameter ensureType universeTrace positivity tail =>
                          have ensureTypeProof :
                              AddInductive.ConstructorEnsureTypeStep.Valid
                                ⟨cvmValidationXContextTest,
                                  cvmCtorProofDomain, sortResult⟩ := by
                            exact ensureType
                          have sortResultEq : sortResult = .sort .zero :=
                            cvmEnsureTypeResultEqTest ensureTypeProof
                              cvmValidationProofEnsureTest
                          subst sortResult
                          simp only [AddInductive.ConstructorTypeValidationTrace.universeSemantics]
                          have universeSemantic : universeTrace.semantic = true := by
                            unfold AddInductive.ConstructorUniverseTrace.semantic
                            rw [cvmStatsResultLevelTest]
                            simp [Expr.sortLevel!, AddInductive.constructorUniverseSemanticGe,
                              AddInductive.levelStructGe]
                          rw [universeSemantic]
                          simp only [Bool.true_and]
                          let sourceEq := cvmSecondFieldSourceTest.trans
                            cvmCtorAfterProofForallTest
                          let tail' := sourceEq ▸ tail
                          refine (cvmUniverseSemanticsCastSourceTest
                            sourceEq tail).symm.trans ?_
                          change tail'.universeSemantics = true
                          cases tail' with
                          | parameter context fuel argIdx name domain body binderInfo
                              parameter parameterType parameterAt parameterTypeRun defeq tail =>
                              rw [cvmStatsParamsTest] at parameterAt
                              simp at parameterAt
                          | ordinary context fuel argIdx name domain body binderInfo
                              sortResult noParameter ensureType universeTrace positivity tail =>
                              have ensureTypeDirect :
                                  AddInductive.ConstructorEnsureTypeStep.Valid
                                    ⟨cvmValidationProofContextTest,
                                      cvmCtorDirectDomain, sortResult⟩ := by
                                exact ensureType
                              have sortResultEq :
                                  sortResult = .sort (.succ (.param `u)) :=
                                cvmEnsureTypeResultEqTest ensureTypeDirect
                                  cvmValidationDirectEnsureTest
                              subst sortResult
                              simp only [AddInductive.ConstructorTypeValidationTrace.universeSemantics]
                              have universeSemantic : universeTrace.semantic = true := by
                                unfold AddInductive.ConstructorUniverseTrace.semantic
                                rw [cvmStatsResultLevelTest]
                                simp [Expr.sortLevel!,
                                  AddInductive.constructorUniverseSemanticGe,
                                  AddInductive.levelStructGe,
                                  AddInductive.levelStructEq]
                              rw [universeSemantic]
                              simp only [Bool.true_and]
                              let sourceEq := cvmThirdFieldSourceTest.trans
                                cvmCtorAfterDirectForallTest
                              let tail' := sourceEq ▸ tail
                              refine (cvmUniverseSemanticsCastSourceTest
                                sourceEq tail).symm.trans ?_
                              change tail'.universeSemantics = true
                              cases tail' with
                              | parameter context fuel argIdx name domain body binderInfo
                                  parameter parameterType parameterAt parameterTypeRun defeq tail =>
                                  rw [cvmStatsParamsTest] at parameterAt
                                  simp at parameterAt
                              | ordinary context fuel argIdx name domain body binderInfo
                                  sortResult noParameter ensureType universeTrace positivity tail =>
                                  have ensureTypeFunction :
                                      AddInductive.ConstructorEnsureTypeStep.Valid
                                        ⟨cvmValidationDirectContextTest,
                                          cvmCtorFunctionDomain, sortResult⟩ := by
                                    exact ensureType
                                  have sortResultEq :
                                      sortResult = .sort (.succ (.param `u)) :=
                                    cvmEnsureTypeResultEqTest ensureTypeFunction
                                      cvmValidationFunctionEnsureTest
                                  subst sortResult
                                  simp only [AddInductive.ConstructorTypeValidationTrace.universeSemantics]
                                  have universeSemantic : universeTrace.semantic = true := by
                                    unfold AddInductive.ConstructorUniverseTrace.semantic
                                    rw [cvmStatsResultLevelTest]
                                    simp [Expr.sortLevel!,
                                      AddInductive.constructorUniverseSemanticGe,
                                      AddInductive.levelStructGe,
                                      AddInductive.levelStructEq]
                                  rw [universeSemantic]
                                  simp only [Bool.true_and]
                                  let sourceEq := cvmFourthFieldSourceTest.trans
                                    cvmCtorAfterFunctionForallTest
                                  let tail' := sourceEq ▸ tail
                                  refine (cvmUniverseSemanticsCastSourceTest
                                    sourceEq tail).symm.trans ?_
                                  change tail'.universeSemantics = true
                                  cases tail' with
                                  | parameter context fuel argIdx name domain body binderInfo
                                      parameter parameterType parameterAt parameterTypeRun defeq tail =>
                                      rw [cvmStatsParamsTest] at parameterAt
                                      simp at parameterAt
                                  | ordinary context fuel argIdx name domain body binderInfo
                                      sortResult noParameter ensureType universeTrace positivity tail =>
                                      have ensureTypeLater :
                                          AddInductive.ConstructorEnsureTypeStep.Valid
                                            ⟨cvmValidationFunctionContextTest,
                                              cvmCtorLaterDomain, sortResult⟩ := by
                                        exact ensureType
                                      have sortResultEq :
                                          sortResult = .sort (.succ (.param `u)) :=
                                        cvmEnsureTypeResultEqTest ensureTypeLater
                                          cvmValidationLaterEnsureTest
                                      subst sortResult
                                      simp only [AddInductive.ConstructorTypeValidationTrace.universeSemantics]
                                      have universeSemantic : universeTrace.semantic = true := by
                                        unfold AddInductive.ConstructorUniverseTrace.semantic
                                        rw [cvmStatsResultLevelTest]
                                        simp [Expr.sortLevel!,
                                          AddInductive.constructorUniverseSemanticGe,
                                          AddInductive.levelStructGe,
                                          AddInductive.levelStructEq]
                                      rw [universeSemantic]
                                      simp only [Bool.true_and]
                                      let sourceEq := cvmFifthFieldSourceTest.trans
                                        cvmCtorAfterLaterForallTest
                                      let tail' := sourceEq ▸ tail
                                      refine (cvmUniverseSemanticsCastSourceTest
                                        sourceEq tail).symm.trans ?_
                                      change tail'.universeSemantics = true
                                      cases tail' with
                                      | parameter context fuel argIdx name domain body binderInfo
                                          parameter parameterType parameterAt parameterTypeRun defeq tail =>
                                          rw [cvmStatsParamsTest] at parameterAt
                                          simp at parameterAt
                                      | ordinary context fuel argIdx name domain body binderInfo
                                          sortResult noParameter ensureType universeTrace positivity tail =>
                                          have ensureTypeLaterProof :
                                              AddInductive.ConstructorEnsureTypeStep.Valid
                                                ⟨cvmValidationLaterContextTest,
                                                  cvmCtorLaterProofDomain, sortResult⟩ := by
                                            exact ensureType
                                          have sortResultEq :
                                              sortResult = .sort .zero :=
                                            cvmEnsureTypeResultEqTest
                                              ensureTypeLaterProof
                                              cvmValidationLaterProofEnsureTest
                                          subst sortResult
                                          simp only [AddInductive.ConstructorTypeValidationTrace.universeSemantics]
                                          have universeSemantic : universeTrace.semantic = true := by
                                            unfold AddInductive.ConstructorUniverseTrace.semantic
                                            rw [cvmStatsResultLevelTest]
                                            simp [Expr.sortLevel!,
                                              AddInductive.constructorUniverseSemanticGe,
                                              AddInductive.levelStructGe]
                                          rw [universeSemantic]
                                          simp only [Bool.true_and]
                                          let sourceEq := cvmSixthFieldSourceTest.trans
                                            cvmCtorTerminalValidationShapeTest
                                          let tail' := sourceEq ▸ tail
                                          refine (cvmUniverseSemanticsCastSourceTest
                                            sourceEq tail).symm.trans ?_
                                          change tail'.universeSemantics = true
                                          cases tail' with
                                          | terminal context source fuel argIdx terminal valid =>
                                              rfl
                                      | terminal context source fuel argIdx terminal valid =>
                                          simp [Expr.isForall] at terminal
                                  | terminal context source fuel argIdx terminal valid =>
                                      simp [Expr.isForall] at terminal
                              | terminal context source fuel argIdx terminal valid =>
                                  simp [Expr.isForall] at terminal
                          | terminal context source fuel argIdx terminal valid =>
                              simp [Expr.isForall] at terminal
                      | terminal context source fuel argIdx terminal valid =>
                          simp [Expr.isForall] at terminal
                  | terminal context source fuel argIdx terminal valid =>
                      simp [Expr.isForall] at terminal
              | ordinary context fuel argIdx name domain body binderInfo sortResult
                  noParameter ensureType universeTrace positivity tail =>
                  rw [cvmStatsParamsTest] at noParameter
                  simp at noParameter
              | terminal context source fuel argIdx terminal valid =>
                  simp [Expr.isForall] at terminal
          | ordinary context fuel argIdx name domain body binderInfo sortResult
              noParameter ensureType universeTrace positivity tail =>
              rw [cvmStatsParamsTest] at noParameter
              contradiction
          | terminal context source fuel argIdx terminal valid =>
              simp [constructorValidityMatrixKernelCtor,
                constructorValidityMatrixMkInfo, ConstantInfo.type,
                ConstantInfo.toConstantVal, Expr.isForall] at terminal

theorem cvmUniverseRunTest :
    AddInductive.checkConstructorUniverseListSemantics
        cvmFamilyValidationRun.stats constructorValidityMatrixKernelType.ctors
        cvmValidationRootContextTest = .ok () :=
  cvmConstructorValidationTest.trace.universeRun_of_semantics
    cvmUniverseSemanticsTest

theorem cvmValidationGetTypeAlphaTest :
    AddInductive.getType (.fvar cvmValidationAlphaIdTest)
      cvmValidationRootContextTest =
        .ok (.sort (.succ (.param `u))) := by
  unfold AddInductive.getType
  simp only [getLCtx, ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  change Except.ok ((cvmValidationRootContextTest.lctx.get!
    cvmValidationAlphaIdTest).type) = _
  simp [LocalContext.get!, cvmValidationAlphaFindTest, LocalDecl.type]

theorem cvmValidationGetTypePTest :
    AddInductive.getType (.fvar cvmValidationPIdTest)
      cvmValidationRootContextTest = .ok cvmValidationPDomainTest := by
  unfold AddInductive.getType
  simp only [getLCtx, ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  change Except.ok ((cvmValidationRootContextTest.lctx.get!
    cvmValidationPIdTest).type) = _
  simp [LocalContext.get!, cvmValidationPFindTest, LocalDecl.type]

theorem cvmValidationRootSortCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationRootContextTest, .sort (.succ (.param `u)),
        .sort (.succ (.succ (.param `u)))⟩ :=
  prbPreFamilySortCheckValidReplay cvmValidationRootContextTest
    cvmValidationRootLparamsTest cvmValidationRootDepthTest

def cvmValidationPDomainAlphaStateTest : TypeChecker.State :=
  prbReplayInsert ({} : TypeChecker.State)
    (.fvar cvmValidationAlphaIdTest) (.sort (.succ (.param `u)))

def cvmValidationPDomainInternalIdTest : FVarId :=
  ⟨cvmValidationPDomainAlphaStateTest.ngen.curr⟩

def cvmValidationPDomainInternalStateTest : TypeChecker.State :=
  { cvmValidationPDomainAlphaStateTest with
    ngen := cvmValidationPDomainAlphaStateTest.ngen.next }

def cvmValidationPDomainFinalStateTest : TypeChecker.State :=
  prbReplayInsert cvmValidationPDomainInternalStateTest
    (.sort .zero) (.sort (.succ .zero))

theorem cvmValidationAlphaToPropCheckTest (indexName : Name) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationRootContextTest,
        .forallE indexName (.fvar cvmValidationAlphaIdTest)
          (.sort .zero) .default,
        .sort (mkLevelIMaxCpp (.succ (.param `u)) (.succ .zero))⟩ := by
  have domainRun : TypeChecker.Inner.inferType'
      (.fvar cvmValidationAlphaIdTest) false
      (TypeChecker.Methods.withFuel 9998)
      cvmValidationRootContextTest.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          cvmValidationPDomainAlphaStateTest) := by
    simpa [cvmValidationPDomainAlphaStateTest] using
      prbValidationInferTypeFVarCore 9998 cvmValidationRootContextTest
        ({} : TypeChecker.State) cvmValidationAlphaIdTest
        (.sort (.succ (.param `u))) Std.HashMap.getElem?_empty
        cvmValidationAlphaFindTest
  have bodyMiss : cvmValidationPDomainInternalStateTest.inferTypeC[
      (.sort .zero : Expr)]? = none := by
    simp [cvmValidationPDomainInternalStateTest,
      cvmValidationPDomainAlphaStateTest, prbReplayInsert]
  have bodyRun : TypeChecker.Inner.inferType'
      (.sort .zero) false (TypeChecker.Methods.withFuel 9998)
      { cvmValidationRootContextTest.toTypeChecker with
        lctx := cvmValidationRootContextTest.lctx.mkLocalDecl
          cvmValidationPDomainInternalIdTest indexName
          (.fvar cvmValidationAlphaIdTest) .default }
      cvmValidationPDomainInternalStateTest =
        .ok (.sort (.succ .zero), cvmValidationPDomainFinalStateTest) := by
    simpa [cvmValidationPDomainFinalStateTest] using
      prbPreFamilyInferSortZeroCoreReplay 9998 _
        cvmValidationPDomainInternalStateTest bodyMiss
  have forallRun : TypeChecker.Inner.inferForall
      (.forallE indexName
        (.fvar cvmValidationAlphaIdTest) (.sort .zero) .default) false
      (TypeChecker.Methods.withFuel 9999)
      cvmValidationRootContextTest.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort
          (mkLevelIMaxCpp (.succ (.param `u)) (.succ .zero)),
          cvmValidationPDomainFinalStateTest) := by
    unfold TypeChecker.Inner.inferForall
    simp only [TypeChecker.Inner.inferForall.loop]
    rw [show (.fvar cvmValidationAlphaIdTest : Expr).instantiateRev #[] =
        .fvar cvmValidationAlphaIdTest by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType
        (.fvar cvmValidationAlphaIdTest) false
        (TypeChecker.Methods.withFuel 9999)
        cvmValidationRootContextTest.toTypeChecker
        ({} : TypeChecker.State) =
          TypeChecker.Inner.inferType'
            (.fvar cvmValidationAlphaIdTest) false
            (TypeChecker.Methods.withFuel 9998)
            cvmValidationRootContextTest.toTypeChecker
            ({} : TypeChecker.State) by rfl]
    rw [domainRun]
    simp only [prbEnsureSortExact]
    rw [prbWithLocalDeclEq]
    change TypeChecker.Inner.inferForall.loop false
      #[Expr.fvar cvmValidationPDomainInternalIdTest]
      #[Level.succ (.param `u)] (.sort .zero)
      (TypeChecker.Methods.withFuel 9999)
      { cvmValidationRootContextTest.toTypeChecker with
        lctx := cvmValidationRootContextTest.lctx.mkLocalDecl
          cvmValidationPDomainInternalIdTest indexName
          (.fvar cvmValidationAlphaIdTest) .default }
      cvmValidationPDomainInternalStateTest = _
    simp only [TypeChecker.Inner.inferForall.loop]
    rw [show (.sort .zero : Expr).instantiateRev
        #[Expr.fvar cvmValidationPDomainInternalIdTest] = .sort .zero by
      simp only [Expr.instantiateRev_eq]
      exact Expr.instantiate_eq_self (by rfl)]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType (.sort .zero) false
        (TypeChecker.Methods.withFuel 9999) _
        cvmValidationPDomainInternalStateTest =
          TypeChecker.Inner.inferType' (.sort .zero) false
            (TypeChecker.Methods.withFuel 9998) _
            cvmValidationPDomainInternalStateTest by rfl]
    rw [bodyRun]
    simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
      StateT.pure, Except.pure]
  have outerRun := prbInferTypeForallCore 9999
    cvmValidationRootContextTest.toTypeChecker ({} : TypeChecker.State)
    cvmValidationPDomainFinalStateTest indexName
    (.fvar cvmValidationAlphaIdTest) (.sort .zero)
    (.sort (mkLevelIMaxCpp (.succ (.param `u)) (.succ .zero))) .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [Expr.looseBVarRange']) Std.HashMap.getElem?_empty
    forallRun
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run cvmValidationRootContextTest.env
    cvmValidationRootContextTest.safety cvmValidationRootContextTest.lctx
    cvmValidationRootContextTest.lparams cvmValidationRootContextTest.fuel
    (TypeChecker.checkType (.forallE indexName
      (.fvar cvmValidationAlphaIdTest) (.sort .zero) .default)) = _
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [cvmValidationRootDepthTest]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.forallE indexName
      (.fvar cvmValidationAlphaIdTest) (.sort .zero) .default) false
      (TypeChecker.Methods.withFuel 9999)
      cvmValidationRootContextTest.toTypeChecker
      ({} : TypeChecker.State)) = _
  simpa [Functor.map, Except.map] using
    congrArg (Except.map (fun x : Expr × TypeChecker.State => x.1))
      outerRun

theorem cvmValidationPDomainCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationRootContextTest, cvmValidationPDomainTest,
        .sort (mkLevelIMaxCpp (.succ (.param `u)) (.succ .zero))⟩ := by
  rw [cvmValidationPDomainShapeTest]
  exact cvmValidationAlphaToPropCheckTest cvmValidationIndexNameTest

theorem cvmValidationFamilyGetTest :
    cvmConstructorContext.env.get
        constructorValidityMatrixKernelType.name =
      .ok cvmDeclaredInfo := by
  unfold Kernel.Environment.get
  rw [cvmCtorFamilyLookup]
  rfl

@[simp] theorem cvmValidationCheckLevelParamTest
    (context : AddInductive.Context)
    (lparams : context.lparams = [`u]) :
    TypeChecker.Inner.checkLevel context.toTypeChecker (.param `u) =
      .ok () := by
  simp [TypeChecker.Inner.checkLevel, AddInductive.Context.toTypeChecker,
    lparams, Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] theorem cvmInferConstantFamilyFullTest
    (context : AddInductive.Context)
    (envEq : context.env = cvmConstructorContext.env)
    (lparams : context.lparams = [`u])
    (safety : context.safety = .safe) :
    TypeChecker.Inner.inferConstant context.toTypeChecker
        constructorValidityMatrixKernelType.name [.param `u] false =
      .ok constructorValidityMatrixKernelType.type := by
  unfold TypeChecker.Inner.inferConstant
  simp only [AddInductive.Context.toTypeChecker]
  rw [envEq, cvmValidationFamilyGetTest]
  have terminalLparams :
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext.lparams =
        [`u] := cvmTerminalLparams_eq
  unfold cvmDeclaredInfo AddInductive.singletonDeclaredInfo
  rw [terminalLparams]
  have levelCheck : TypeChecker.Inner.checkLevel
      ({ env := cvmConstructorContext.env
         lctx := context.lctx
         safety := .safe
         lparams := [`u]
         fuel := context.fuel } : TypeChecker.Context)
      (.param `u) = .ok () := by
    simp [TypeChecker.Inner.checkLevel,
      Level.getUndefParam, Level.forEach,
      Level.hasParam_eq, Level.hasParam']
    rfl
  simp [constructorValidityMatrixKernelType, constructorValidityMatrixInfo,
    ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParamsCpp,
    ConstantInfo.type, ConstantInfo.toConstantVal,
    Expr.instantiateLevelParamsCpp_eq, safety, lparams, levelCheck,
    Bind.bind, Except.bind, Pure.pure,
    Except.pure]
  simp [Expr.instantiateLevelParamsCoreCpp', Level.substParamsCpp', ConstantInfo.type,
    ConstantInfo.toConstantVal]

def cvmValidationFamilyConstStateTest
    (state : TypeChecker.State) : TypeChecker.State :=
  prbReplayInsert state
    (.const constructorValidityMatrixKernelType.name [.param `u])
    constructorValidityMatrixKernelType.type

theorem cvmValidationInferTypeFamilyCoreTest
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State)
    (cacheMiss : state.inferTypeC[
      (.const constructorValidityMatrixKernelType.name
        [.param `u] : Expr)]? = none)
    (envEq : context.env = cvmConstructorContext.env)
    (lparams : context.lparams = [`u])
    (safety : context.safety = .safe) :
    TypeChecker.Inner.inferType'
        (.const constructorValidityMatrixKernelType.name [.param `u]) false
        (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
      .ok (constructorValidityMatrixKernelType.type,
        cvmValidationFamilyConstStateTest state) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange', cacheMiss,
    cvmValidationFamilyConstStateTest, prbReplayInsert,
    cvmInferConstantFamilyFullTest context envEq lparams safety,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

def cvmValidationFamilyTailFullTest (alpha : Expr) : Expr :=
  .forallE `P
    (.forallE cvmValidationIndexNameTest alpha (.sort .zero) .default)
    (.sort (.succ (.param `u))) .default

def cvmValidationFirstAppFullTest (alpha : Expr) : Expr :=
  .app (.const constructorValidityMatrixKernelType.name [.param `u]) alpha

def cvmValidationFamilyAlphaStateTest
    (state : TypeChecker.State) (alphaId : FVarId) : TypeChecker.State :=
  prbReplayInsert (cvmValidationFamilyConstStateTest state)
    (.fvar alphaId) (.sort (.succ (.param `u)))

def cvmValidationFamilyFirstAppStateTest
    (state : TypeChecker.State) (alphaId : FVarId) : TypeChecker.State :=
  prbReplayInsert (cvmValidationFamilyAlphaStateTest state alphaId)
    (cvmValidationFirstAppFullTest (.fvar alphaId))
    (cvmValidationFamilyTailFullTest (.fvar alphaId))

def cvmValidationFamilyPredicateStateTest
    (state : TypeChecker.State) (alphaId predicateId : FVarId) :
    TypeChecker.State :=
  prbReplayInsert (cvmValidationFamilyFirstAppStateTest state alphaId)
    (.fvar predicateId)
    (.forallE cvmValidationIndexNameTest (.fvar alphaId)
      (.sort .zero) .default)

def cvmValidationFamilyFullAppStateTest
    (state : TypeChecker.State) (alphaId predicateId : FVarId) :
    TypeChecker.State :=
  prbReplayInsert
    (cvmValidationFamilyPredicateStateTest state alphaId predicateId)
    (cvmValidationFamilyApplicationTest
      (.fvar alphaId) (.fvar predicateId))
    (.sort (.succ (.param `u)))

theorem cvmValidationFamilyApplicationCheckTest
    (context : AddInductive.Context) (alphaId predicateId : FVarId)
    (alphaEq : alphaId = cvmValidationAlphaIdTest)
    (idsNe : alphaId ≠ predicateId)
    (alphaFind : context.lctx.find? alphaId =
      some (.cdecl alphaIndex alphaId alphaName
        (.sort (.succ (.param `u))) alphaBi alphaKind))
    (predicateFind : context.lctx.find? predicateId =
      some (.cdecl predicateIndex predicateId predicateName
        cvmValidationPDomainTest predicateBi predicateKind))
    (envEq : context.env = cvmConstructorContext.env)
    (lparams : context.lparams = [`u])
    (safety : context.safety = .safe)
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, cvmValidationFamilyApplicationTest
        (.fvar alphaId) (.fvar predicateId),
        .sort (.succ (.param `u))⟩ := by
  let initial := ({} : TypeChecker.State)
  have familyRun : TypeChecker.Inner.inferType'
      (.const constructorValidityMatrixKernelType.name [.param `u]) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker initial =
        .ok (constructorValidityMatrixKernelType.type,
          cvmValidationFamilyConstStateTest initial) := by
    apply cvmValidationInferTypeFamilyCoreTest
    · simp [initial]
    · exact envEq
    · exact lparams
    · exact safety
  have alphaMiss :
      (cvmValidationFamilyConstStateTest initial).inferTypeC[
        (.fvar alphaId : Expr)]? = none := by
    simp [cvmValidationFamilyConstStateTest, prbReplayInsert, initial]
  have alphaRun : TypeChecker.Inner.inferType' (.fvar alphaId) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      (cvmValidationFamilyConstStateTest initial) =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFamilyAlphaStateTest initial alphaId) := by
    simpa [cvmValidationFamilyAlphaStateTest] using
      prbValidationInferTypeFVarCore 9999 context
        (cvmValidationFamilyConstStateTest initial) alphaId
        (.sort (.succ (.param `u))) alphaMiss alphaFind
  have firstRun := prbInferAppCoreOf 9999 context.toTypeChecker initial
    (cvmValidationFamilyConstStateTest initial)
    (cvmValidationFamilyAlphaStateTest initial alphaId)
    (.const constructorValidityMatrixKernelType.name [.param `u])
    (.fvar alphaId) (.sort (.succ (.param `u)))
    (.forallE `P
      (.forallE cvmValidationIndexNameTest (.bvar 0)
        (.sort .zero) .default)
      (.sort (.succ (.param `u))) .default)
    `α .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [Expr.looseBVarRange'])
    (by simp [initial])
    (by simpa [cvmKernelFamilyTypeShapeTest] using familyRun)
    alphaRun (by rfl)
  have firstRun' : TypeChecker.Inner.inferType'
      (cvmValidationFirstAppFullTest (.fvar alphaId)) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker initial =
        .ok (cvmValidationFamilyTailFullTest (.fvar alphaId),
          cvmValidationFamilyFirstAppStateTest initial alphaId) := by
    simpa [cvmValidationFirstAppFullTest,
      cvmValidationFamilyTailFullTest,
      cvmValidationFamilyFirstAppStateTest,
      cvmValidationFamilyAlphaStateTest, prbReplayInsert,
      Expr.instantiate1_eq, Expr.instantiate1'] using firstRun
  have predicateMiss :
      (cvmValidationFamilyFirstAppStateTest initial alphaId).inferTypeC[
        (.fvar predicateId : Expr)]? = none := by
    have idsBeq : ((.fvar alphaId : Expr) == .fvar predicateId) = false := by
      change Expr.eqv (.fvar alphaId) (.fvar predicateId) = false
      rw [Expr.eqv_eq]
      simp [Expr.eqv', idsNe]
    simp [cvmValidationFamilyFirstAppStateTest,
      cvmValidationFamilyAlphaStateTest,
      cvmValidationFamilyConstStateTest,
      cvmValidationFirstAppFullTest, prbReplayInsert, initial, idsBeq]
  have predicateRun : TypeChecker.Inner.inferType' (.fvar predicateId) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker
      (cvmValidationFamilyFirstAppStateTest initial alphaId) =
        .ok (.forallE cvmValidationIndexNameTest (.fvar alphaId)
            (.sort .zero) .default,
          cvmValidationFamilyPredicateStateTest initial alphaId predicateId) := by
    simpa [cvmValidationFamilyPredicateStateTest,
      cvmValidationPDomainShapeTest, alphaEq] using
      prbValidationInferTypeFVarCore 9999 context
        (cvmValidationFamilyFirstAppStateTest initial alphaId)
        predicateId cvmValidationPDomainTest predicateMiss predicateFind
  have fullRun := prbInferAppCoreOf 9999 context.toTypeChecker initial
    (cvmValidationFamilyFirstAppStateTest initial alphaId)
    (cvmValidationFamilyPredicateStateTest initial alphaId predicateId)
    (cvmValidationFirstAppFullTest (.fvar alphaId))
    (.fvar predicateId)
    (.forallE cvmValidationIndexNameTest (.fvar alphaId)
      (.sort .zero) .default)
    (.sort (.succ (.param `u))) `P .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [cvmValidationFirstAppFullTest, Expr.looseBVarRange'])
    (by simp [initial])
    firstRun' predicateRun (by rfl)
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel
      (TypeChecker.checkType (cvmValidationFamilyApplicationTest
        (.fvar alphaId) (.fvar predicateId))) =
      .ok (.sort (.succ (.param `u)))
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [depth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (cvmValidationFamilyApplicationTest
        (.fvar alphaId) (.fvar predicateId)) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker initial) = _
  simpa [cvmValidationFamilyApplicationTest,
    cvmValidationFirstAppFullTest,
    cvmValidationFamilyFullAppStateTest,
    cvmValidationFamilyPredicateStateTest, prbReplayInsert,
    Expr.instantiate1_eq, Expr.instantiate1', Functor.map, Except.map] using
    congrArg (Except.map (fun x : Expr × TypeChecker.State => x.1))
      fullRun

def cvmValidationPredicateFullStateTest
    (state : TypeChecker.State) (predicateId : FVarId) :
    TypeChecker.State :=
  prbReplayInsert state (.fvar predicateId) cvmValidationPDomainTest

def cvmValidationPredicateArgumentStateTest
    (state : TypeChecker.State) (predicateId argumentId : FVarId) :
    TypeChecker.State :=
  prbReplayInsert (cvmValidationPredicateFullStateTest state predicateId)
    (.fvar argumentId) (.fvar cvmValidationAlphaIdTest)

def cvmValidationPredicateFullAppStateTest
    (state : TypeChecker.State) (predicateId argumentId : FVarId) :
    TypeChecker.State :=
  prbReplayInsert
    (cvmValidationPredicateArgumentStateTest state predicateId argumentId)
    (cvmValidationPredicateApplicationTest predicateId (.fvar argumentId))
    (.sort .zero)

theorem cvmValidationPredicateApplicationCheckTest
    (context : AddInductive.Context) (predicateId argumentId : FVarId)
    (idsNe : predicateId ≠ argumentId)
    (predicateFind : context.lctx.find? predicateId =
      some (.cdecl predicateIndex predicateId predicateName
        cvmValidationPDomainTest predicateBi predicateKind))
    (argumentFind : context.lctx.find? argumentId =
      some (.cdecl argumentIndex argumentId argumentName
        (.fvar cvmValidationAlphaIdTest) argumentBi argumentKind))
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨context,
        cvmValidationPredicateApplicationTest predicateId (.fvar argumentId),
        .sort .zero⟩ := by
  let initial := ({} : TypeChecker.State)
  have predicateRun : TypeChecker.Inner.inferType'
      (.fvar predicateId) false (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker initial =
        .ok (.forallE cvmValidationIndexNameTest
            (.fvar cvmValidationAlphaIdTest) (.sort .zero) .default,
          cvmValidationPredicateFullStateTest initial predicateId) := by
    simpa [cvmValidationPredicateFullStateTest,
      cvmValidationPDomainShapeTest] using
      prbValidationInferTypeFVarCore 9999 context initial predicateId
        cvmValidationPDomainTest (by simp [initial]) predicateFind
  have argumentMiss :
      (cvmValidationPredicateFullStateTest initial predicateId).inferTypeC[
        (.fvar argumentId : Expr)]? = none := by
    have idsBeq : ((.fvar predicateId : Expr) == .fvar argumentId) = false := by
      change Expr.eqv (.fvar predicateId) (.fvar argumentId) = false
      rw [Expr.eqv_eq]
      simp [Expr.eqv', idsNe]
    simp [cvmValidationPredicateFullStateTest, prbReplayInsert,
      initial, idsBeq]
  have argumentRun : TypeChecker.Inner.inferType'
      (.fvar argumentId) false (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker
      (cvmValidationPredicateFullStateTest initial predicateId) =
        .ok (.fvar cvmValidationAlphaIdTest,
          cvmValidationPredicateArgumentStateTest
            initial predicateId argumentId) := by
    simpa [cvmValidationPredicateArgumentStateTest] using
      prbValidationInferTypeFVarCore 9999 context
        (cvmValidationPredicateFullStateTest initial predicateId)
        argumentId (.fvar cvmValidationAlphaIdTest)
        argumentMiss argumentFind
  have appRun := prbInferAppCoreOf 9999 context.toTypeChecker initial
    (cvmValidationPredicateFullStateTest initial predicateId)
    (cvmValidationPredicateArgumentStateTest initial predicateId argumentId)
    (.fvar predicateId) (.fvar argumentId)
    (.fvar cvmValidationAlphaIdTest) (.sort .zero)
    cvmValidationIndexNameTest .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [Expr.looseBVarRange'])
    (by simp [initial])
    predicateRun argumentRun (by rfl)
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel
      (TypeChecker.checkType
        (cvmValidationPredicateApplicationTest predicateId
          (.fvar argumentId))) = .ok (.sort .zero)
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [depth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (cvmValidationPredicateApplicationTest predicateId
        (.fvar argumentId)) false
      (TypeChecker.Methods.withFuel 9999) context.toTypeChecker initial) = _
  simpa [cvmValidationPredicateApplicationTest,
    cvmValidationPredicateFullAppStateTest,
    cvmValidationPredicateArgumentStateTest, prbReplayInsert,
    Expr.instantiate1_eq, Expr.instantiate1', Functor.map, Except.map] using
    congrArg (Except.map (fun x : Expr × TypeChecker.State => x.1))
      appRun

theorem cvmValidationRootFreshTest :
    cvmValidationRootContextTest.lctx.find?
      cvmValidationRootContextTest.freshFVarId = none :=
  cvmValidationRootLocalRunTest.fresh

theorem cvmValidationFunctionFreshTest :
    cvmValidationFunctionContextTest.lctx.find?
      cvmValidationFunctionContextTest.freshFVarId = none :=
  cvmValidationFunctionLocalRunTest.fresh

theorem cvmValidationAlphaFindInAlphaTest :
    cvmValidationAlphaContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) := by
  simpa [cvmValidationAlphaIdTest, cvmValidationAlphaContextTest,
    cvmFamilyContext] using
    (TypeChecker.CandidateLocalContextRun.empty cvmFamilyContext rfl
      |>.push_findNew `α .default (.sort (.succ (.param `u))))

theorem cvmValidationAlphaNePTest :
    cvmValidationAlphaIdTest ≠ cvmValidationPIdTest := by
  intro equal
  have fresh := cvmValidationAlphaLocalRunTest.fresh
  change cvmValidationAlphaContextTest.lctx.find?
    cvmValidationPIdTest = none at fresh
  rw [← equal, cvmValidationAlphaFindInAlphaTest] at fresh
  contradiction

theorem cvmValidationXFindTest :
    cvmValidationXContextTest.lctx.find? cvmValidationXIdTest =
      some (.cdecl cvmValidationRootContextTest.lctx.decls.size
        cvmValidationXIdTest `x (.fvar cvmValidationAlphaIdTest)
        .default .default) := by
  have found := cvmValidationRootLocalRunTest.push_findNew `x .default
    (AddInductive.consumeTypeAnnotations cvmCtorXDomain)
  simpa [cvmValidationXContextTest, cvmValidationXIdTest,
    cvmCtorXDomainValidationShapeTest,
    AddInductive.consumeTypeAnnotations] using found

theorem cvmValidationPNeXTest :
    cvmValidationPIdTest ≠ cvmValidationXIdTest := by
  intro equal
  have fresh := cvmValidationRootFreshTest
  change cvmValidationRootContextTest.lctx.find?
    cvmValidationXIdTest = none at fresh
  rw [← equal, cvmValidationPFindTest] at fresh
  contradiction

theorem cvmValidationLaterFindTest :
    cvmValidationLaterContextTest.lctx.find? cvmValidationLaterIdTest =
      some (.cdecl cvmValidationFunctionContextTest.lctx.decls.size
        cvmValidationLaterIdTest `later (.fvar cvmValidationAlphaIdTest)
        .default .default) := by
  have found := cvmValidationFunctionLocalRunTest.push_findNew `later .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain)
  simpa [cvmValidationLaterContextTest, cvmValidationLaterIdTest,
    cvmCtorLaterDomainValidationShapeTest,
    AddInductive.consumeTypeAnnotations] using found

theorem cvmValidationPNeLaterTest :
    cvmValidationPIdTest ≠ cvmValidationLaterIdTest := by
  intro equal
  have fresh := cvmValidationFunctionFreshTest
  change cvmValidationFunctionContextTest.lctx.find?
    cvmValidationLaterIdTest = none at fresh
  rw [← equal, cvmValidationPFindInFunctionTest] at fresh
  contradiction

theorem cvmValidationProofCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationXContextTest, cvmCtorProofDomain, .sort .zero⟩ := by
  rw [cvmCtorProofDomainValidationShapeTest]
  exact cvmValidationPredicateApplicationCheckTest
    cvmValidationXContextTest cvmValidationPIdTest
    cvmValidationXIdTest cvmValidationPNeXTest
    cvmValidationPFindInXTest cvmValidationXFindTest (by rfl)

theorem cvmValidationLaterProofCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationLaterContextTest, cvmCtorLaterProofDomain,
        .sort .zero⟩ := by
  rw [cvmCtorLaterProofDomainValidationShapeTest]
  exact cvmValidationPredicateApplicationCheckTest
    cvmValidationLaterContextTest cvmValidationPIdTest
    cvmValidationLaterIdTest cvmValidationPNeLaterTest
    cvmValidationPFindInLaterTest cvmValidationLaterFindTest (by rfl)

theorem cvmValidationDirectCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationProofContextTest, cvmCtorDirectDomain,
        .sort (.succ (.param `u))⟩ := by
  rw [cvmCtorDirectDomainValidationShapeTest]
  exact cvmValidationFamilyApplicationCheckTest
    cvmValidationProofContextTest cvmValidationAlphaIdTest
    cvmValidationPIdTest rfl cvmValidationAlphaNePTest
    cvmValidationAlphaFindInProofTest cvmValidationPFindInProofTest
    (by rfl) (by rfl) (by rfl) (by rfl)

theorem cvmValidationLaterProofLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmValidationLaterProofContextTest :=
  cvmValidationLaterLocalRunTest.push `laterProof .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain)

theorem cvmValidationAlphaFindInLaterTest :
    cvmValidationLaterContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmValidationFunctionLocalRunTest.push_findOld `later .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain)
    cvmValidationAlphaFindInFunctionTest

theorem cvmValidationAlphaFindInLaterProofTest :
    cvmValidationLaterProofContextTest.lctx.find?
        cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmValidationLaterLocalRunTest.push_findOld `laterProof .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain)
    cvmValidationAlphaFindInLaterTest

theorem cvmValidationPFindInLaterProofTest :
    cvmValidationLaterProofContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmValidationLaterLocalRunTest.push_findOld `laterProof .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain)
    cvmValidationPFindInLaterTest

theorem cvmValidationTerminalCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationLaterProofContextTest, cvmCtorTerminal,
        .sort (.succ (.param `u))⟩ := by
  rw [cvmCtorTerminalValidationShapeTest]
  exact cvmValidationFamilyApplicationCheckTest
    cvmValidationLaterProofContextTest cvmValidationAlphaIdTest
    cvmValidationPIdTest rfl cvmValidationAlphaNePTest
    cvmValidationAlphaFindInLaterProofTest
    cvmValidationPFindInLaterProofTest
    (by rfl) (by rfl) (by rfl) (by rfl)

def cvmValidationFamilyCachedFirstAppStateTest
    (state : TypeChecker.State) (alphaId : FVarId) : TypeChecker.State :=
  prbReplayInsert (cvmValidationFamilyConstStateTest state)
    (cvmValidationFirstAppFullTest (.fvar alphaId))
    (cvmValidationFamilyTailFullTest (.fvar alphaId))

def cvmValidationFamilyCachedPredicateStateTest
    (state : TypeChecker.State) (alphaId predicateId : FVarId) :
    TypeChecker.State :=
  prbReplayInsert (cvmValidationFamilyCachedFirstAppStateTest state alphaId)
    (.fvar predicateId)
    (.forallE cvmValidationIndexNameTest (.fvar alphaId)
      (.sort .zero) .default)

def cvmValidationFamilyCachedFullAppStateTest
    (state : TypeChecker.State) (alphaId predicateId : FVarId) :
    TypeChecker.State :=
  prbReplayInsert
    (cvmValidationFamilyCachedPredicateStateTest state alphaId predicateId)
    (cvmValidationFamilyApplicationTest
      (.fvar alphaId) (.fvar predicateId))
    (.sort (.succ (.param `u)))

theorem cvmValidationInferFirstAppAlphaCachedCoreTest
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (alphaId : FVarId)
    (alphaCache : state.inferTypeC[(.fvar alphaId : Expr)]? =
      some (.sort (.succ (.param `u))))
    (constMiss : state.inferTypeC[
      (.const constructorValidityMatrixKernelType.name
        [.param `u] : Expr)]? = none)
    (firstMiss : state.inferTypeC[
      cvmValidationFirstAppFullTest (.fvar alphaId)]? = none)
    (envEq : context.env = cvmConstructorContext.env)
    (lparams : context.lparams = [`u])
    (safety : context.safety = .safe) :
    TypeChecker.Inner.inferType'
      (cvmValidationFirstAppFullTest (.fvar alphaId)) false
      (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
        .ok (cvmValidationFamilyTailFullTest (.fvar alphaId),
          cvmValidationFamilyCachedFirstAppStateTest state alphaId) := by
  have familyRun := cvmValidationInferTypeFamilyCoreTest fuel context state
    constMiss envEq lparams safety
  have alphaCache' :
      (cvmValidationFamilyConstStateTest state).inferTypeC[
        (.fvar alphaId : Expr)]? =
          some (.sort (.succ (.param `u))) := by
    simp only [cvmValidationFamilyConstStateTest, prbReplayInsert,
      Std.HashMap.getElem?_insert]
    rw [prbConstBeqFVar]
    exact alphaCache
  have alphaRun := prbValidationInferTypeCachedCore fuel context
    (cvmValidationFamilyConstStateTest state) (.fvar alphaId)
    (.sort (.succ (.param `u)))
    (by simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq, Expr.looseBVarRange']) alphaCache'
  have appRun := prbInferAppCoreOf fuel context.toTypeChecker state
    (cvmValidationFamilyConstStateTest state)
    (cvmValidationFamilyConstStateTest state)
    (.const constructorValidityMatrixKernelType.name [.param `u])
    (.fvar alphaId) (.sort (.succ (.param `u)))
    (.forallE `P
      (.forallE cvmValidationIndexNameTest (.bvar 0)
        (.sort .zero) .default)
      (.sort (.succ (.param `u))) .default)
    `α .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [Expr.looseBVarRange'])
    firstMiss
    (by simpa [cvmKernelFamilyTypeShapeTest] using familyRun)
    alphaRun (by rfl)
  simpa [cvmValidationFirstAppFullTest,
    cvmValidationFamilyTailFullTest,
    cvmValidationFamilyCachedFirstAppStateTest, prbReplayInsert,
    Expr.instantiate1_eq, Expr.instantiate1'] using appRun

theorem cvmValidationFamilyApplicationAlphaCachedCoreTest
    (fuel : Nat) (context : AddInductive.Context)
    (state : TypeChecker.State) (alphaId predicateId : FVarId)
    (alphaEq : alphaId = cvmValidationAlphaIdTest)
    (alphaCache : state.inferTypeC[(.fvar alphaId : Expr)]? =
      some (.sort (.succ (.param `u))))
    (constMiss : state.inferTypeC[
      (.const constructorValidityMatrixKernelType.name
        [.param `u] : Expr)]? = none)
    (firstMiss : state.inferTypeC[
      cvmValidationFirstAppFullTest (.fvar alphaId)]? = none)
    (predicateMiss :
      (cvmValidationFamilyCachedFirstAppStateTest state alphaId).inferTypeC[
        (.fvar predicateId : Expr)]? = none)
    (applicationMiss : state.inferTypeC[
      cvmValidationFamilyApplicationTest
        (.fvar alphaId) (.fvar predicateId)]? = none)
    (predicateFind : context.lctx.find? predicateId =
      some (.cdecl predicateIndex predicateId predicateName
        cvmValidationPDomainTest predicateBi predicateKind))
    (envEq : context.env = cvmConstructorContext.env)
    (lparams : context.lparams = [`u])
    (safety : context.safety = .safe) :
    TypeChecker.Inner.inferType'
      (cvmValidationFamilyApplicationTest
        (.fvar alphaId) (.fvar predicateId)) false
      (TypeChecker.Methods.withFuel fuel) context.toTypeChecker state =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFamilyCachedFullAppStateTest
            state alphaId predicateId) := by
  have firstRun := cvmValidationInferFirstAppAlphaCachedCoreTest
    fuel context state alphaId alphaCache constMiss firstMiss
    envEq lparams safety
  have predicateRun : TypeChecker.Inner.inferType' (.fvar predicateId) false
      (TypeChecker.Methods.withFuel fuel) context.toTypeChecker
      (cvmValidationFamilyCachedFirstAppStateTest state alphaId) =
        .ok (.forallE cvmValidationIndexNameTest (.fvar alphaId)
            (.sort .zero) .default,
          cvmValidationFamilyCachedPredicateStateTest
            state alphaId predicateId) := by
    simpa [cvmValidationFamilyCachedPredicateStateTest,
      cvmValidationPDomainShapeTest, alphaEq] using
      prbValidationInferTypeFVarCore fuel context
        (cvmValidationFamilyCachedFirstAppStateTest state alphaId)
        predicateId cvmValidationPDomainTest predicateMiss predicateFind
  have appRun := prbInferAppCoreOf fuel context.toTypeChecker state
    (cvmValidationFamilyCachedFirstAppStateTest state alphaId)
    (cvmValidationFamilyCachedPredicateStateTest state alphaId predicateId)
    (cvmValidationFirstAppFullTest (.fvar alphaId))
    (.fvar predicateId)
    (.forallE cvmValidationIndexNameTest (.fvar alphaId)
      (.sort .zero) .default)
    (.sort (.succ (.param `u))) `P .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [cvmValidationFirstAppFullTest, Expr.looseBVarRange'])
    applicationMiss firstRun predicateRun (by rfl)
  simpa [cvmValidationFamilyApplicationTest,
    cvmValidationFirstAppFullTest,
    cvmValidationFamilyCachedFullAppStateTest,
    cvmValidationFamilyCachedPredicateStateTest, prbReplayInsert,
    Expr.instantiate1_eq, Expr.instantiate1'] using appRun

def cvmValidationFunctionFullAlphaStateTest : TypeChecker.State :=
  prbReplayInsert ({} : TypeChecker.State)
    (.fvar cvmValidationAlphaIdTest) (.sort (.succ (.param `u)))

def cvmValidationFunctionFullInternalIdTest : FVarId :=
  ⟨cvmValidationFunctionFullAlphaStateTest.ngen.curr⟩

def cvmValidationFunctionFullInternalStateTest : TypeChecker.State :=
  { cvmValidationFunctionFullAlphaStateTest with
    ngen := cvmValidationFunctionFullAlphaStateTest.ngen.next }

def cvmValidationFunctionFullInternalContextTest : AddInductive.Context :=
  { cvmValidationDirectContextTest with
    lctx := cvmValidationDirectContextTest.lctx.mkLocalDecl
      cvmValidationFunctionFullInternalIdTest `y
      (.fvar cvmValidationAlphaIdTest) .default }

def cvmValidationFunctionFullBodyStateTest : TypeChecker.State :=
  cvmValidationFamilyCachedFullAppStateTest
    cvmValidationFunctionFullInternalStateTest
    cvmValidationAlphaIdTest cvmValidationPIdTest

def cvmValidationFunctionFullFinalStateTest : TypeChecker.State :=
  prbReplayInsert cvmValidationFunctionFullBodyStateTest
    (.forallE `y (.fvar cvmValidationAlphaIdTest)
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
      .default)
    (.sort (.succ (.param `u)))

theorem cvmValidationFunctionFullInternalFreshTest :
    cvmValidationDirectContextTest.lctx.find?
      cvmValidationFunctionFullInternalIdTest = none := by
  rw [cvmValidationDirectLocalRunTest.wf.find?_eq_find?_toList,
    List.find?_eq_none]
  intro decl membership equal
  simp only [cvmValidationDirectContextTest,
    AddInductive.Context.pushLocalDecl] at membership
  rw [LocalContext.mkLocalDecl_toList
    cvmValidationProofLocalRunTest.wf.decls_wf] at membership
  simp only [List.mem_cons] at membership
  simp only [cvmValidationProofContextTest,
    AddInductive.Context.pushLocalDecl] at membership
  rw [LocalContext.mkLocalDecl_toList
    cvmValidationXLocalRunTest.wf.decls_wf] at membership
  simp only [List.mem_cons] at membership
  simp only [cvmValidationXContextTest,
    AddInductive.Context.pushLocalDecl] at membership
  rw [LocalContext.mkLocalDecl_toList
    cvmValidationRootLocalRunTest.wf.decls_wf] at membership
  simp only [List.mem_cons] at membership
  simp only [cvmValidationRootContextTest,
    cvmValidationFamilyContextTest,
    AddInductive.Context.pushLocalDecl] at membership
  rw [LocalContext.mkLocalDecl_toList
    cvmValidationAlphaLocalRunTest.wf.decls_wf] at membership
  simp only [List.mem_cons] at membership
  simp only [cvmValidationAlphaContextTest,
    AddInductive.Context.pushLocalDecl] at membership
  rw [LocalContext.mkLocalDecl_toList
    (TypeChecker.CandidateLocalContextRun.empty
      cvmFamilyContext rfl).wf.decls_wf] at membership
  simp only [List.mem_cons] at membership
  rw [show cvmFamilyContext.lctx.toList = [] by rfl] at membership
  simp only [List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [LocalDecl.fvarId, cvmValidationFunctionFullInternalIdTest,
      cvmValidationFunctionFullAlphaStateTest, prbReplayInsert, cvmValidationAlphaIdTest,
      cvmFamilyContext, constructorValidityMatrixContext, AddInductive.Context.freshFVarId]
      at equal
  all_goals injection equal
  all_goals simp [NameGenerator.next] at *

@[simp] theorem cvmValidationAlphaPBeqFalseTest :
    ((.fvar cvmValidationAlphaIdTest : Expr) ==
      .fvar cvmValidationPIdTest) = false := by
  change Expr.eqv (.fvar cvmValidationAlphaIdTest)
    (.fvar cvmValidationPIdTest) = false
  rw [Expr.eqv_eq]
  simp [Expr.eqv', cvmValidationAlphaNePTest]

theorem cvmValidationPFindInFunctionFullInternalTest :
    cvmValidationFunctionFullInternalContextTest.lctx.find?
        cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) := by
  exact TypeChecker.localContextFindOld
    cvmValidationDirectContextTest.lctx cvmValidationPIdTest
    cvmValidationFunctionFullInternalIdTest `y
    (.fvar cvmValidationAlphaIdTest) .default .default _
    cvmValidationDirectLocalRunTest.wf
    cvmValidationFunctionFullInternalFreshTest
    cvmValidationPFindInDirectTest

theorem cvmValidationFunctionCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationDirectContextTest, cvmCtorFunctionDomain,
        .sort (.succ (.param `u))⟩ := by
  have domainRun : TypeChecker.Inner.inferType'
      (.fvar cvmValidationAlphaIdTest) false
      (TypeChecker.Methods.withFuel 9998)
      cvmValidationDirectContextTest.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFunctionFullAlphaStateTest) := by
    simpa [cvmValidationFunctionFullAlphaStateTest] using
      prbValidationInferTypeFVarCore 9998 cvmValidationDirectContextTest
        ({} : TypeChecker.State) cvmValidationAlphaIdTest
        (.sort (.succ (.param `u))) Std.HashMap.getElem?_empty
        cvmValidationAlphaFindInDirectTest
  have bodyRun : TypeChecker.Inner.inferType'
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest)) false
      (TypeChecker.Methods.withFuel 9998)
      cvmValidationFunctionFullInternalContextTest.toTypeChecker
      cvmValidationFunctionFullInternalStateTest =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFunctionFullBodyStateTest) := by
    apply cvmValidationFamilyApplicationAlphaCachedCoreTest
    · rfl
    · simp [cvmValidationFunctionFullInternalStateTest,
        cvmValidationFunctionFullAlphaStateTest, prbReplayInsert]
    · simp [cvmValidationFunctionFullInternalStateTest,
        cvmValidationFunctionFullAlphaStateTest, prbReplayInsert]
    · simp [cvmValidationFunctionFullInternalStateTest,
        cvmValidationFunctionFullAlphaStateTest,
        cvmValidationFirstAppFullTest, prbReplayInsert]
    · simp [cvmValidationFamilyCachedFirstAppStateTest, cvmValidationFamilyConstStateTest,
        cvmValidationFunctionFullInternalStateTest, cvmValidationFunctionFullAlphaStateTest,
        cvmValidationFirstAppFullTest, prbReplayInsert]
    · simp [cvmValidationFunctionFullInternalStateTest,
        cvmValidationFunctionFullAlphaStateTest,
        cvmValidationFamilyApplicationTest, prbReplayInsert]
    · exact cvmValidationPFindInFunctionFullInternalTest
    · rfl
    · rfl
    · rfl
  have forallRun : TypeChecker.Inner.inferForall
      (.forallE `y (.fvar cvmValidationAlphaIdTest)
        (cvmValidationFamilyApplicationTest
          (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
        .default) false
      (TypeChecker.Methods.withFuel 9999)
      cvmValidationDirectContextTest.toTypeChecker
      ({} : TypeChecker.State) =
        .ok (.sort (.succ (.param `u)),
          cvmValidationFunctionFullBodyStateTest) := by
    unfold TypeChecker.Inner.inferForall
    simp only [cvmValidationFamilyApplicationTest,
      TypeChecker.Inner.inferForall.loop]
    rw [show (.fvar cvmValidationAlphaIdTest : Expr).instantiateRev #[] =
        .fvar cvmValidationAlphaIdTest by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    rw [show TypeChecker.Inner.inferType
        (.fvar cvmValidationAlphaIdTest) false
        (TypeChecker.Methods.withFuel 9999)
        cvmValidationDirectContextTest.toTypeChecker
        ({} : TypeChecker.State) =
          TypeChecker.Inner.inferType'
            (.fvar cvmValidationAlphaIdTest) false
            (TypeChecker.Methods.withFuel 9998)
            cvmValidationDirectContextTest.toTypeChecker
            ({} : TypeChecker.State) by rfl]
    rw [domainRun]
    simp only [prbEnsureSortExact]
    rw [prbWithLocalDeclEq]
    change TypeChecker.Inner.inferForall.loop false
      #[Expr.fvar cvmValidationFunctionFullInternalIdTest]
      #[Level.succ (.param `u)]
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
      (TypeChecker.Methods.withFuel 9999)
      cvmValidationFunctionFullInternalContextTest.toTypeChecker
      cvmValidationFunctionFullInternalStateTest = _
    simp only [cvmValidationFamilyApplicationTest,
      TypeChecker.Inner.inferForall.loop]
    rw [show (((.const constructorValidityMatrixKernelType.name
          [.param `u] : Expr).app (.fvar cvmValidationAlphaIdTest)).app
          (.fvar cvmValidationPIdTest)).instantiateRev
          #[Expr.fvar cvmValidationFunctionFullInternalIdTest] =
        ((.const constructorValidityMatrixKernelType.name
          [.param `u] : Expr).app (.fvar cvmValidationAlphaIdTest)).app
          (.fvar cvmValidationPIdTest) by
      simp only [Expr.instantiateRev_eq]
      exact Expr.instantiate_eq_self (by
        simp [Expr.looseBVarRange'])]
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
    have bodyRunExplicit : TypeChecker.Inner.inferType'
        (((.const constructorValidityMatrixKernelType.name
          [.param `u] : Expr).app (.fvar cvmValidationAlphaIdTest)).app
          (.fvar cvmValidationPIdTest)) false
        (TypeChecker.Methods.withFuel 9998)
        cvmValidationFunctionFullInternalContextTest.toTypeChecker
        cvmValidationFunctionFullInternalStateTest =
          .ok (.sort (.succ (.param `u)),
            cvmValidationFunctionFullBodyStateTest) := by
      simpa [cvmValidationFamilyApplicationTest] using bodyRun
    rw [show TypeChecker.Inner.inferType
        (((.const constructorValidityMatrixKernelType.name
          [.param `u] : Expr).app (.fvar cvmValidationAlphaIdTest)).app
          (.fvar cvmValidationPIdTest)) false
        (TypeChecker.Methods.withFuel 9999)
        cvmValidationFunctionFullInternalContextTest.toTypeChecker
        cvmValidationFunctionFullInternalStateTest =
          TypeChecker.Inner.inferType'
            (((.const constructorValidityMatrixKernelType.name
              [.param `u] : Expr).app
              (.fvar cvmValidationAlphaIdTest)).app
              (.fvar cvmValidationPIdTest)) false
            (TypeChecker.Methods.withFuel 9998)
            cvmValidationFunctionFullInternalContextTest.toTypeChecker
            cvmValidationFunctionFullInternalStateTest by rfl]
    rw [bodyRunExplicit]
    simp [Expr.sortLevel!, Pure.pure, ReaderT.pure,
      StateT.pure, Except.pure]
  have outerRun := prbInferTypeForallCore 9999
    cvmValidationDirectContextTest.toTypeChecker
    ({} : TypeChecker.State) cvmValidationFunctionFullBodyStateTest
    `y (.fvar cvmValidationAlphaIdTest)
    (cvmValidationFamilyApplicationTest
      (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
    (.sort (.succ (.param `u))) .default
    (by
      apply Expr.hasLooseBVars_eq_false_of_bounded <;>
        simp [cvmValidationFamilyApplicationTest,
          Expr.looseBVarRange'])
    Std.HashMap.getElem?_empty forallRun
  rw [cvmCtorFunctionDomainValidationShapeTest]
  unfold AddInductive.CandidateCheckTypeStep.Valid
  change TypeChecker.M.run cvmValidationDirectContextTest.env
    cvmValidationDirectContextTest.safety cvmValidationDirectContextTest.lctx
    cvmValidationDirectContextTest.lparams cvmValidationDirectContextTest.fuel
      (TypeChecker.checkType (.forallE `y
        (.fvar cvmValidationAlphaIdTest)
        (cvmValidationFamilyApplicationTest
          (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
        .default)) = .ok (.sort (.succ (.param `u)))
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType'
      (.forallE `y (.fvar cvmValidationAlphaIdTest)
        (cvmValidationFamilyApplicationTest
          (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
        .default) false
      (TypeChecker.Methods.withFuel 9999)
      cvmValidationDirectContextTest.toTypeChecker
      ({} : TypeChecker.State)) = _
  simpa [cvmValidationFunctionFullFinalStateTest,
    prbReplayInsert, Functor.map, Except.map] using
    congrArg (Except.map (fun x : Expr × TypeChecker.State => x.1))
      outerRun

theorem cvmValidationAlphaRootCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationRootContextTest, .fvar cvmValidationAlphaIdTest,
        .sort (.succ (.param `u))⟩ :=
  prbCandidateCheckTypeFVar cvmValidationRootContextTest
    cvmValidationAlphaIdTest (.sort (.succ (.param `u)))
    cvmValidationRootDepthTest cvmValidationAlphaFindTest

theorem cvmValidationAlphaFunctionCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationFunctionContextTest, .fvar cvmValidationAlphaIdTest,
        .sort (.succ (.param `u))⟩ :=
  prbCandidateCheckTypeFVar cvmValidationFunctionContextTest
    cvmValidationAlphaIdTest (.sort (.succ (.param `u)))
    cvmValidationFunctionDepthTest cvmValidationAlphaFindInFunctionTest

def cvmCheckedOfValidTest
    (context : AddInductive.Context) (source inferred : Expr)
    (fvars : source.FVarsIn
      (fun fv => (context.lctx.find? fv).isSome = true))
    (noMVar : source.hasMVar = false)
    (valid : AddInductive.CandidateCheckTypeStep.Valid
      ⟨context, source, inferred⟩) :
    AddInductive.ConstructorCheckedExpr context source :=
  .ofRun fvars noMVar valid

def cvmValidationSortCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationRootContextTest
      (.sort (.succ (.param `u))) :=
  cvmCheckedOfValidTest _ _ _
    (by simp [FVarsIn, Level.hasMVar'])
    (by simp [Expr.hasMVar_eq_cache, Level.hasMVar_eq, Level.hasMVar'])
    cvmValidationRootSortCheckTest

def cvmValidationPDomainCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationRootContextTest
      cvmValidationPDomainTest :=
  cvmCheckedOfValidTest _ _ _ (by
    rw [cvmValidationPDomainShapeTest]
    simp [FVarsIn, Level.hasMVar']
    change (cvmValidationRootContextTest.lctx.find?
      cvmValidationAlphaIdTest).isSome = true
    rw [cvmValidationAlphaFindTest]
    rfl)
    (by
      rw [cvmValidationPDomainShapeTest]
      simp [Expr.hasMVar_eq_cache, Level.hasMVar_eq, Level.hasMVar'])
    cvmValidationPDomainCheckTest

def cvmValidationAlphaRootCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationRootContextTest
      (.fvar cvmValidationAlphaIdTest) :=
  cvmCheckedOfValidTest _ _ _ (by
    change (cvmValidationRootContextTest.lctx.find?
      cvmValidationAlphaIdTest).isSome = true
    rw [cvmValidationAlphaFindTest]
    rfl)
    (by simp [Expr.hasMVar_eq_cache])
    cvmValidationAlphaRootCheckTest

def cvmValidationProofCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationXContextTest
      cvmCtorProofDomain :=
  cvmCheckedOfValidTest _ _ _ (by
    rw [cvmCtorProofDomainValidationShapeTest]
    simp [FVarsIn]
    constructor
    · change (cvmValidationXContextTest.lctx.find?
        cvmValidationPIdTest).isSome = true
      rw [cvmValidationPFindInXTest]
      rfl
    · change (cvmValidationXContextTest.lctx.find?
      cvmValidationXIdTest).isSome = true
      rw [cvmValidationXFindTest]
      rfl)
    (by
      rw [cvmCtorProofDomainValidationShapeTest]
      simp [Expr.hasMVar_eq_cache])
    cvmValidationProofCheckTest

def cvmValidationDirectCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationProofContextTest
      cvmCtorDirectDomain :=
  cvmCheckedOfValidTest _ _ _ (by
    rw [cvmCtorDirectDomainValidationShapeTest]
    simp [cvmValidationFamilyApplicationTest, FVarsIn, Level.hasMVar']
    constructor
    · change (cvmValidationProofContextTest.lctx.find?
        cvmValidationAlphaIdTest).isSome = true
      rw [cvmValidationAlphaFindInProofTest]
      rfl
    · change (cvmValidationProofContextTest.lctx.find?
      cvmValidationPIdTest).isSome = true
      rw [cvmValidationPFindInProofTest]
      rfl)
    (by
      rw [cvmCtorDirectDomainValidationShapeTest]
      simp [cvmValidationFamilyApplicationTest, Expr.hasMVar_eq_cache,
        Level.hasMVar_eq, Level.hasMVar'])
    cvmValidationDirectCheckTest

def cvmValidationFunctionCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationDirectContextTest
      cvmCtorFunctionDomain :=
  cvmCheckedOfValidTest _ _ _ (by
    rw [cvmCtorFunctionDomainValidationShapeTest]
    simp [cvmValidationFamilyApplicationTest, FVarsIn, Level.hasMVar']
    constructor
    · change (cvmValidationDirectContextTest.lctx.find?
        cvmValidationAlphaIdTest).isSome = true
      rw [cvmValidationAlphaFindInDirectTest]
      rfl
    · change (cvmValidationDirectContextTest.lctx.find?
      cvmValidationPIdTest).isSome = true
      rw [cvmValidationPFindInDirectTest]
      rfl)
    (by
      rw [cvmCtorFunctionDomainValidationShapeTest]
      simp [cvmValidationFamilyApplicationTest, Expr.hasMVar_eq_cache,
        Level.hasMVar_eq, Level.hasMVar'])
    cvmValidationFunctionCheckTest

def cvmValidationAlphaFunctionCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationFunctionContextTest
      (.fvar cvmValidationAlphaIdTest) :=
  cvmCheckedOfValidTest _ _ _ (by
    change (cvmValidationFunctionContextTest.lctx.find?
      cvmValidationAlphaIdTest).isSome = true
    rw [cvmValidationAlphaFindInFunctionTest]
    rfl)
    (by simp [Expr.hasMVar_eq_cache])
    cvmValidationAlphaFunctionCheckTest

def cvmValidationLaterProofCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationLaterContextTest
      cvmCtorLaterProofDomain :=
  cvmCheckedOfValidTest _ _ _ (by
    rw [cvmCtorLaterProofDomainValidationShapeTest]
    simp [cvmValidationPredicateApplicationTest, FVarsIn]
    constructor
    · change (cvmValidationLaterContextTest.lctx.find?
        cvmValidationPIdTest).isSome = true
      rw [cvmValidationPFindInLaterTest]
      rfl
    · change (cvmValidationLaterContextTest.lctx.find?
      cvmValidationLaterIdTest).isSome = true
      rw [cvmValidationLaterFindTest]
      rfl)
    (by
      rw [cvmCtorLaterProofDomainValidationShapeTest]
      simp [cvmValidationPredicateApplicationTest, Expr.hasMVar_eq_cache])
    cvmValidationLaterProofCheckTest

def cvmValidationTerminalCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationLaterProofContextTest
      cvmCtorTerminal :=
  cvmCheckedOfValidTest _ _ _ (by
    rw [cvmCtorTerminalValidationShapeTest]
    simp [cvmValidationFamilyApplicationTest, FVarsIn, Level.hasMVar']
    constructor
    · change (cvmValidationLaterProofContextTest.lctx.find?
        cvmValidationAlphaIdTest).isSome = true
      rw [cvmValidationAlphaFindInLaterProofTest]
      rfl
    · change (cvmValidationLaterProofContextTest.lctx.find?
      cvmValidationPIdTest).isSome = true
      rw [cvmValidationPFindInLaterProofTest]
      rfl)
    (by
      rw [cvmCtorTerminalValidationShapeTest]
      simp [cvmValidationFamilyApplicationTest, Expr.hasMVar_eq_cache,
        Level.hasMVar_eq, Level.hasMVar'])
    cvmValidationTerminalCheckTest

@[simp] theorem cvmValidationConsumeXTest :
    AddInductive.consumeTypeAnnotations cvmCtorXDomain =
      cvmCtorXDomain := by
  rw [cvmCtorXDomainValidationShapeTest]
  simp [AddInductive.consumeTypeAnnotations]

@[simp] theorem cvmValidationConsumeProofTest :
    AddInductive.consumeTypeAnnotations cvmCtorProofDomain =
      cvmCtorProofDomain := by
  rw [cvmCtorProofDomainValidationShapeTest]
  simp [AddInductive.consumeTypeAnnotations]

@[simp] theorem cvmValidationConsumeDirectTest :
    AddInductive.consumeTypeAnnotations cvmCtorDirectDomain =
      cvmCtorDirectDomain := by
  rw [cvmCtorDirectDomainValidationShapeTest]
  simp [cvmValidationFamilyApplicationTest,
    AddInductive.consumeTypeAnnotations,
    constructorValidityMatrixKernelType,
    constructorValidityMatrixInfo, ConstantInfo.name,
    ConstantInfo.toConstantVal]

@[simp] theorem cvmValidationConsumeFunctionTest :
    AddInductive.consumeTypeAnnotations cvmCtorFunctionDomain =
      cvmCtorFunctionDomain := by
  rw [cvmCtorFunctionDomainValidationShapeTest]
  simp [AddInductive.consumeTypeAnnotations]

@[simp] theorem cvmValidationConsumeLaterTest :
    AddInductive.consumeTypeAnnotations cvmCtorLaterDomain =
      cvmCtorLaterDomain := by
  rw [cvmCtorLaterDomainValidationShapeTest]
  simp [AddInductive.consumeTypeAnnotations]

@[simp] theorem cvmValidationConsumeLaterProofTest :
    AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain =
      cvmCtorLaterProofDomain := by
  rw [cvmCtorLaterProofDomainValidationShapeTest]
  simp [cvmValidationPredicateApplicationTest,
    AddInductive.consumeTypeAnnotations]

theorem cvmCtorPDomainValidationShapeTest :
    cvmCtorPDomain = .forallE cvmCtorPDomain.bindingName!
      (.fvar cvmValidationAlphaIdTest) (.sort .zero) .default := by
  simp_cvm_ctor_expr
  simp [cvmValidationAlphaIdTest, cvmFamilyContext, constructorValidityMatrixContext,
    AddInductive.Context.freshFVarId]

theorem cvmValidationCtorPDomainCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationRootContextTest, cvmCtorPDomain,
        .sort (mkLevelIMaxCpp (.succ (.param `u)) (.succ .zero))⟩ := by
  rw [cvmCtorPDomainValidationShapeTest]
  exact cvmValidationAlphaToPropCheckTest cvmCtorPDomain.bindingName!

def cvmValidationXCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationRootContextTest
      cvmCtorXDomain := by
  rw [cvmCtorXDomainValidationShapeTest]
  exact cvmValidationAlphaRootCheckedTest

def cvmValidationXConsumedCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationRootContextTest
      (AddInductive.consumeTypeAnnotations cvmCtorXDomain) := by
  rw [cvmValidationConsumeXTest]
  exact cvmValidationXCheckedTest

def cvmValidationProofConsumedCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationXContextTest
      (AddInductive.consumeTypeAnnotations cvmCtorProofDomain) := by
  rw [cvmValidationConsumeProofTest]
  exact cvmValidationProofCheckedTest

def cvmValidationDirectConsumedCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationProofContextTest
      (AddInductive.consumeTypeAnnotations cvmCtorDirectDomain) := by
  rw [cvmValidationConsumeDirectTest]
  exact cvmValidationDirectCheckedTest

def cvmValidationFunctionConsumedCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationDirectContextTest
      (AddInductive.consumeTypeAnnotations cvmCtorFunctionDomain) := by
  rw [cvmValidationConsumeFunctionTest]
  exact cvmValidationFunctionCheckedTest

def cvmValidationLaterCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationFunctionContextTest
      cvmCtorLaterDomain := by
  rw [cvmCtorLaterDomainValidationShapeTest]
  exact cvmValidationAlphaFunctionCheckedTest

def cvmValidationLaterConsumedCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationFunctionContextTest
      (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain) := by
  rw [cvmValidationConsumeLaterTest]
  exact cvmValidationLaterCheckedTest

def cvmValidationLaterProofConsumedCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationLaterContextTest
      (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain) := by
  rw [cvmValidationConsumeLaterProofTest]
  exact cvmValidationLaterProofCheckedTest

def cvmValidationReflObservationTest
    (context : AddInductive.Context) (source : Expr) :
    AddInductive.CandidateIsDefEqObservation context source source :=
  ⟨AddInductive.candidateIsDefEqRefl context source⟩

def cvmValidationXAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation cvmValidationRootContextTest
      cvmCtorXDomain
      (AddInductive.consumeTypeAnnotations cvmCtorXDomain) := by
  rw [cvmValidationConsumeXTest]
  exact cvmValidationReflObservationTest _ _

def cvmValidationProofAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation cvmValidationXContextTest
      cvmCtorProofDomain
      (AddInductive.consumeTypeAnnotations cvmCtorProofDomain) := by
  rw [cvmValidationConsumeProofTest]
  exact cvmValidationReflObservationTest _ _

def cvmValidationDirectAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation cvmValidationProofContextTest
      cvmCtorDirectDomain
      (AddInductive.consumeTypeAnnotations cvmCtorDirectDomain) := by
  rw [cvmValidationConsumeDirectTest]
  exact cvmValidationReflObservationTest _ _

def cvmValidationFunctionAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation cvmValidationDirectContextTest
      cvmCtorFunctionDomain
      (AddInductive.consumeTypeAnnotations cvmCtorFunctionDomain) := by
  rw [cvmValidationConsumeFunctionTest]
  exact cvmValidationReflObservationTest _ _

def cvmValidationLaterAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation cvmValidationFunctionContextTest
      cvmCtorLaterDomain
      (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain) := by
  rw [cvmValidationConsumeLaterTest]
  exact cvmValidationReflObservationTest _ _

def cvmValidationLaterProofAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation cvmValidationLaterContextTest
      cvmCtorLaterProofDomain
      (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain) := by
  rw [cvmValidationConsumeLaterProofTest]
  exact cvmValidationReflObservationTest _ _

theorem cvmValidationXFreshTest :
    cvmValidationXContextTest.lctx.find?
      cvmValidationXContextTest.freshFVarId = none :=
  cvmValidationXLocalRunTest.fresh

theorem cvmValidationProofFreshTest :
    cvmValidationProofContextTest.lctx.find?
      cvmValidationProofContextTest.freshFVarId = none :=
  cvmValidationProofLocalRunTest.fresh

theorem cvmValidationDirectFreshTest :
    cvmValidationDirectContextTest.lctx.find?
      cvmValidationDirectContextTest.freshFVarId = none :=
  cvmValidationDirectLocalRunTest.fresh

theorem cvmValidationLaterFreshTest :
    cvmValidationLaterContextTest.lctx.find?
      cvmValidationLaterContextTest.freshFVarId = none :=
  cvmValidationLaterLocalRunTest.fresh

def cvmValidationFunctionPosContextTest : AddInductive.Context :=
  cvmValidationDirectContextTest.pushLocalDecl `y .default
    (.fvar cvmValidationAlphaIdTest)

theorem cvmValidationFunctionPosLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmValidationFunctionPosContextTest :=
  cvmValidationDirectLocalRunTest.push `y .default
    (.fvar cvmValidationAlphaIdTest)

theorem cvmValidationAlphaFindInFunctionPosTest :
    cvmValidationFunctionPosContextTest.lctx.find?
        cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmValidationDirectLocalRunTest.push_findOld `y .default
    (.fvar cvmValidationAlphaIdTest) cvmValidationAlphaFindInDirectTest

theorem cvmValidationPFindInFunctionPosTest :
    cvmValidationFunctionPosContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmValidationDirectLocalRunTest.push_findOld `y .default
    (.fvar cvmValidationAlphaIdTest) cvmValidationPFindInDirectTest

theorem cvmValidationFunctionPosBodyCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationFunctionPosContextTest,
        cvmValidationFamilyApplicationTest
          (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest),
        .sort (.succ (.param `u))⟩ :=
  cvmValidationFamilyApplicationCheckTest
    cvmValidationFunctionPosContextTest cvmValidationAlphaIdTest
    cvmValidationPIdTest rfl cvmValidationAlphaNePTest
    cvmValidationAlphaFindInFunctionPosTest
    cvmValidationPFindInFunctionPosTest
    (by rfl) (by rfl) (by rfl) (by rfl)

def cvmValidationFunctionPosBodyCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationFunctionPosContextTest
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest)) :=
  cvmCheckedOfValidTest _ _ _ (by
    simp [cvmValidationFamilyApplicationTest, FVarsIn, Level.hasMVar']
    constructor
    · change (cvmValidationFunctionPosContextTest.lctx.find?
        cvmValidationAlphaIdTest).isSome = true
      rw [cvmValidationAlphaFindInFunctionPosTest]
      rfl
    · change (cvmValidationFunctionPosContextTest.lctx.find?
      cvmValidationPIdTest).isSome = true
      rw [cvmValidationPFindInFunctionPosTest]
      rfl)
    (by
      simp [cvmValidationFamilyApplicationTest, Expr.hasMVar_eq_cache,
        Level.hasMVar_eq, Level.hasMVar'])
    cvmValidationFunctionPosBodyCheckTest

def cvmStagedUniverseInputTest :
    VInductDecl.StagedNormalizationCandidateUniverseInput
      cvmFamilyContext cvmConstructorContext VEnv.empty [`u]
      cvmCandidate constructorValidityMatrixDecl where
  staged := {
    raw := constructorValidityMatrixType
    raw_types_eq := rfl
    declaration_uvars_eq := rfl
    preFamily := cvmPreFamilyStage
    family := cvmFamilyStage
    validation_nparams_eq := rfl
    constructorValidation := by
      simpa [cvmFamilyStage, cvmConstructorValidationContextTest,
        cvmValidationRootContextTest, cvmFamilyTerminalContextTest_eq] using
        cvmConstructorValidationTest
    constructors := cvmConstructorsStage
    familyTypesProduced := cvmFamilyTypesProduced
    familiesProduced := cvmFamiliesProduced }
  universeRun := by
    simpa [cvmFamilyStage, cvmConstructorValidationContextTest,
      cvmValidationRootContextTest, cvmFamilyTerminalContextTest_eq] using
      cvmUniverseRunTest

theorem cvmStagedStatsTest_eq :
    cvmStagedUniverseInputTest.staged.family.validation.stats =
      cvmFamilyValidationRun.stats := by
  rfl

theorem cvmStagedIndConstsTest_eq :
    cvmStagedUniverseInputTest.staged.family.validation.stats.indConsts =
      #[.const constructorValidityMatrixKernelType.name [.param `u]] := by
  rw [cvmStagedStatsTest_eq, cvmFamilyValidationRun.stats_eq]
  simp only [cvmFamilyValidationRun,
    AddInductive.CandidateExprTrace.singletonCandidateInductiveStats]
  rw [show
    cvmCandidate.families.singleton.familyType.type.context.lparams = [`u] by
      rw [cvmFamilyCandidateContext_eq]
      rfl]
  rfl

theorem cvmValidationAlphaHasNoIndOccTest :
    AddInductive.hasIndOcc
      cvmStagedUniverseInputTest.staged.family.validation.stats.indConsts
      (.fvar cvmValidationAlphaIdTest) = false := by
  rw [cvmStagedIndConstsTest_eq]
  simp [AddInductive.hasIndOcc]

theorem cvmValidationProofHasNoIndOccTest :
    AddInductive.hasIndOcc
      cvmStagedUniverseInputTest.staged.family.validation.stats.indConsts
      cvmCtorProofDomain = false := by
  rw [cvmStagedIndConstsTest_eq,
    cvmCtorProofDomainValidationShapeTest]
  simp [AddInductive.hasIndOcc]

theorem cvmValidationDirectHasIndOccTest :
    AddInductive.hasIndOcc
      cvmStagedUniverseInputTest.staged.family.validation.stats.indConsts
      cvmCtorDirectDomain = true := by
  rw [cvmStagedIndConstsTest_eq,
    cvmCtorDirectDomainValidationShapeTest]
  simp [AddInductive.hasIndOcc,
    cvmValidationFamilyApplicationTest, Expr.constName!]

theorem cvmValidationFunctionHasIndOccTest :
    AddInductive.hasIndOcc
      cvmStagedUniverseInputTest.staged.family.validation.stats.indConsts
      cvmCtorFunctionDomain = true := by
  rw [cvmStagedIndConstsTest_eq,
    cvmCtorFunctionDomainValidationShapeTest]
  simp [AddInductive.hasIndOcc,
    cvmValidationFamilyApplicationTest, Expr.constName!]

theorem cvmValidationLaterProofHasNoIndOccTest :
    AddInductive.hasIndOcc
      cvmStagedUniverseInputTest.staged.family.validation.stats.indConsts
      cvmCtorLaterProofDomain = false := by
  rw [cvmStagedIndConstsTest_eq,
    cvmCtorLaterProofDomainValidationShapeTest]
  simp [AddInductive.hasIndOcc,
    cvmValidationPredicateApplicationTest]

theorem cvmValidationFunctionPosBodyHasIndOccTest :
    AddInductive.hasIndOcc
      cvmStagedUniverseInputTest.staged.family.validation.stats.indConsts
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest)) =
      true := by
  rw [cvmStagedIndConstsTest_eq]
  simp [AddInductive.hasIndOcc,
    cvmValidationFamilyApplicationTest, Expr.constName!]

theorem cvmCandidateWhnfResultEqTest
    (self : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (other : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, result⟩) :
    result = source := by
  unfold AddInductive.CandidateWhnfStep.Valid at self other
  rw [self] at other
  exact (Except.ok.inj other).symm

theorem cvmValidationAlphaRootWhnfSelfTest :
    AddInductive.CandidateWhnfStep.Valid
      ⟨cvmValidationRootContextTest, .fvar cvmValidationAlphaIdTest,
        .fvar cvmValidationAlphaIdTest⟩ := by
  apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
  · rfl
  · unfold TypeChecker.Inner.isLetFVar
    rw [cvmValidationAlphaFindTest]

theorem cvmValidationProofWhnfSelfTest :
    AddInductive.CandidateWhnfStep.Valid
      ⟨cvmValidationXContextTest, cvmCtorProofDomain,
        cvmCtorProofDomain⟩ := by
  rw [cvmCtorProofDomainValidationShapeTest]
  apply TypeChecker.candidateWhnfFVarAppFVar_refl
    cvmValidationXContextTest cvmValidationPIdTest cvmValidationXIdTest
  · rfl
  · rfl
  · rw [show cvmValidationXContextTest.env =
        cvmConstructorContext.env by rfl]
    exact cvmCtorQuotInit
  · unfold TypeChecker.Inner.isLetFVar
    rw [cvmValidationPFindInXTest]

theorem cvmValidationDirectWhnfSelfTest :
    AddInductive.CandidateWhnfStep.Valid
      ⟨cvmValidationProofContextTest, cvmCtorDirectDomain,
        cvmCtorDirectDomain⟩ := by
  rw [cvmCtorDirectDomainValidationShapeTest]
  unfold cvmValidationFamilyApplicationTest
  apply cvmCtorFamilyWhnf cvmValidationProofContextTest
    cvmValidationAlphaIdTest cvmValidationPIdTest
    (by rfl) (by rfl) (by rfl)
  rw [show cvmValidationProofContextTest.env =
    cvmConstructorContext.env by rfl]
  exact cvmCtorQuotInit

theorem cvmValidationFunctionWhnfSelfTest :
    AddInductive.CandidateWhnfStep.Valid
      ⟨cvmValidationDirectContextTest, cvmCtorFunctionDomain,
        cvmCtorFunctionDomain⟩ := by
  apply TypeChecker.CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
    _ _ 9999
  · rfl
  · rw [cvmCtorFunctionDomainValidationShapeTest]
    rfl

theorem cvmValidationAlphaFunctionWhnfSelfTest :
    AddInductive.CandidateWhnfStep.Valid
      ⟨cvmValidationFunctionContextTest,
        .fvar cvmValidationAlphaIdTest,
        .fvar cvmValidationAlphaIdTest⟩ := by
  apply TypeChecker.candidateWhnfFVar_refl _ _ 9999
  · rfl
  · unfold TypeChecker.Inner.isLetFVar
    rw [cvmValidationAlphaFindInFunctionTest]

theorem cvmValidationLaterProofWhnfSelfTest :
    AddInductive.CandidateWhnfStep.Valid
      ⟨cvmValidationLaterContextTest, cvmCtorLaterProofDomain,
        cvmCtorLaterProofDomain⟩ := by
  rw [cvmCtorLaterProofDomainValidationShapeTest]
  unfold cvmValidationPredicateApplicationTest
  apply TypeChecker.candidateWhnfFVarAppFVar_refl
    cvmValidationLaterContextTest cvmValidationPIdTest
    cvmValidationLaterIdTest
  · rfl
  · rfl
  · rw [show cvmValidationLaterContextTest.env =
        cvmConstructorContext.env by rfl]
    exact cvmCtorQuotInit
  · unfold TypeChecker.Inner.isLetFVar
    rw [cvmValidationPFindInLaterTest]

theorem cvmValidationFunctionPosBodyWhnfSelfTest :
    AddInductive.CandidateWhnfStep.Valid
      ⟨cvmValidationFunctionPosContextTest,
        cvmValidationFamilyApplicationTest
          (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest),
        cvmValidationFamilyApplicationTest
          (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest)⟩ := by
  unfold cvmValidationFamilyApplicationTest
  apply cvmCtorFamilyWhnf cvmValidationFunctionPosContextTest
    cvmValidationAlphaIdTest cvmValidationPIdTest
    (by rfl) (by rfl) (by rfl)
  rw [show cvmValidationFunctionPosContextTest.env =
    cvmConstructorContext.env by rfl]
  exact cvmCtorQuotInit

theorem cvmValidationAlphaDirectCheckTest :
    AddInductive.CandidateCheckTypeStep.Valid
      ⟨cvmValidationDirectContextTest, .fvar cvmValidationAlphaIdTest,
        .sort (.succ (.param `u))⟩ :=
  prbCandidateCheckTypeFVar cvmValidationDirectContextTest
    cvmValidationAlphaIdTest (.sort (.succ (.param `u)))
    (by rfl) cvmValidationAlphaFindInDirectTest

def cvmValidationAlphaDirectCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationDirectContextTest
      (.fvar cvmValidationAlphaIdTest) :=
  cvmCheckedOfValidTest _ _ _ (by
    change (cvmValidationDirectContextTest.lctx.find?
      cvmValidationAlphaIdTest).isSome = true
    rw [cvmValidationAlphaFindInDirectTest]
    rfl)
    (by simp [Expr.hasMVar_eq_cache])
    cvmValidationAlphaDirectCheckTest

def cvmValidationAlphaDirectConsumedCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationDirectContextTest
      (AddInductive.consumeTypeAnnotations
        (.fvar cvmValidationAlphaIdTest)) := by
  simp [AddInductive.consumeTypeAnnotations]
  exact cvmValidationAlphaDirectCheckedTest

def cvmValidationAlphaDirectAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation cvmValidationDirectContextTest
      (.fvar cvmValidationAlphaIdTest)
      (AddInductive.consumeTypeAnnotations
        (.fvar cvmValidationAlphaIdTest)) := by
  simp [AddInductive.consumeTypeAnnotations]
  exact cvmValidationReflObservationTest _ _

theorem cvmValidationXWhnfSelfTest :
    AddInductive.CandidateWhnfStep.Valid
      ⟨cvmValidationRootContextTest, cvmCtorXDomain,
        cvmCtorXDomain⟩ := by
  simpa [cvmCtorXDomainValidationShapeTest] using
    cvmValidationAlphaRootWhnfSelfTest

theorem cvmValidationLaterWhnfSelfTest :
    AddInductive.CandidateWhnfStep.Valid
      ⟨cvmValidationFunctionContextTest, cvmCtorLaterDomain,
        cvmCtorLaterDomain⟩ := by
  simpa [cvmCtorLaterDomainValidationShapeTest] using
    cvmValidationAlphaFunctionWhnfSelfTest

theorem cvmValidationXHasNoIndOccTest :
    AddInductive.hasIndOcc
      cvmStagedUniverseInputTest.staged.family.validation.stats.indConsts
      cvmCtorXDomain = false := by
  rw [cvmCtorXDomainValidationShapeTest]
  exact cvmValidationAlphaHasNoIndOccTest

theorem cvmValidationLaterHasNoIndOccTest :
    AddInductive.hasIndOcc
      cvmStagedUniverseInputTest.staged.family.validation.stats.indConsts
      cvmCtorLaterDomain = false := by
  rw [cvmCtorLaterDomainValidationShapeTest]
  exact cvmValidationAlphaHasNoIndOccTest

def cvmTransportPositivityFuelTraceTest
    {fuel fuel' : Nat} (fuelEq : fuel = fuel')
    (trace : AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source fuel) :
    AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source fuel' := by
  subst fuel'
  exact trace

def cvmTransportPositivityFuelAlignmentTest
    {fuel fuel' : Nat} (fuelEq : fuel = fuel')
    (trace : AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source fuel)
    (alignment : AddInductive.ConstructorPositivityAlignmentTrace
      (cvmTransportPositivityFuelTraceTest fuelEq trace)) :
    AddInductive.ConstructorPositivityAlignmentTrace trace := by
  subst fuel'
  exact alignment

def cvmAbsentPositivityAlignmentCoreTest
    (self : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (notForall : source.isForall = false)
    (noOccurrence : AddInductive.hasIndOcc stats.indConsts source = false)
    (checked : AddInductive.ConstructorCheckedExpr context source)
    (trace : AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source 1000) :
    AddInductive.ConstructorPositivityAlignmentTrace trace := by
  cases trace with
  | absent context source result fuel whnf occurs =>
      have resultEq := cvmCandidateWhnfResultEqTest self whnf
      subst result
      exact .absent checked
  | forallE context source fuel name domain body binderInfo whnf occurs
      domainFree tail =>
      have resultEq := cvmCandidateWhnfResultEqTest self whnf
      have impossible := congrArg Expr.isForall resultEq
      have forallEq : true = source.isForall := by
        simpa only [Expr.isForall] using impossible
      have : true = false := forallEq.trans notForall
      contradiction
  | target context source result fuel targetIdx whnf occurs terminal valid =>
      have resultEq := cvmCandidateWhnfResultEqTest self whnf
      subst result
      rw [noOccurrence] at occurs
      contradiction

def cvmTargetPositivityAlignmentCoreTest
    (self : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (notForall : source.isForall = false)
    (hasOccurrence : AddInductive.hasIndOcc stats.indConsts source = true)
    (checked : AddInductive.ConstructorCheckedExpr context source)
    (trace : AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source 1000) :
    AddInductive.ConstructorPositivityAlignmentTrace trace := by
  cases trace with
  | absent context source result fuel whnf occurs =>
      have resultEq := cvmCandidateWhnfResultEqTest self whnf
      subst result
      rw [hasOccurrence] at occurs
      contradiction
  | forallE context source fuel name domain body binderInfo whnf occurs
      domainFree tail =>
      have resultEq := cvmCandidateWhnfResultEqTest self whnf
      have impossible := congrArg Expr.isForall resultEq
      have forallEq : true = source.isForall := by
        simpa only [Expr.isForall] using impossible
      have : true = false := forallEq.trans notForall
      contradiction
  | target context source result fuel targetIdx whnf occurs terminal valid =>
      have resultEq := cvmCandidateWhnfResultEqTest self whnf
      subst result
      exact .target checked

def cvmAbsentPositivityModeAlignmentTest
    (self : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (notForall : source.isForall = false)
    (noOccurrence : AddInductive.hasIndOcc stats.indConsts source = false)
    (checked : AddInductive.ConstructorCheckedExpr context source)
    (inductiveFuel : context.fuel.inductiveFuel = 1000)
    (trace : AddInductive.ConstructorPositivityModeTrace stats false ctor
      argIdx context source) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      let normalized := cvmTransportPositivityFuelTraceTest
        inductiveFuel positivityTrace
      have normalizedAlignment := cvmAbsentPositivityAlignmentCoreTest
        self notForall noOccurrence checked normalized
      exact cvmTransportPositivityFuelAlignmentTest
        inductiveFuel positivityTrace normalizedAlignment

def cvmTargetPositivityModeAlignmentTest
    (self : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (notForall : source.isForall = false)
    (hasOccurrence : AddInductive.hasIndOcc stats.indConsts source = true)
    (checked : AddInductive.ConstructorCheckedExpr context source)
    (inductiveFuel : context.fuel.inductiveFuel = 1000)
    (trace : AddInductive.ConstructorPositivityModeTrace stats false ctor
      argIdx context source) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      let normalized := cvmTransportPositivityFuelTraceTest
        inductiveFuel positivityTrace
      have normalizedAlignment := cvmTargetPositivityAlignmentCoreTest
        self notForall hasOccurrence checked normalized
      exact cvmTransportPositivityFuelAlignmentTest
        inductiveFuel positivityTrace normalizedAlignment

def cvmValidationXPositivityAlignmentTest
    (trace : AddInductive.ConstructorPositivityModeTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats false
      constructorValidityMatrixKernelCtor.name 2
      cvmValidationRootContextTest cvmCtorXDomain) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace :=
  cvmAbsentPositivityModeAlignmentTest cvmValidationXWhnfSelfTest
    (by rw [cvmCtorXDomainValidationShapeTest]; rfl)
    cvmValidationXHasNoIndOccTest cvmValidationXCheckedTest (by rfl) trace

def cvmValidationProofPositivityAlignmentTest
    (trace : AddInductive.ConstructorPositivityModeTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats false
      constructorValidityMatrixKernelCtor.name 3
      cvmValidationXContextTest cvmCtorProofDomain) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace :=
  cvmAbsentPositivityModeAlignmentTest cvmValidationProofWhnfSelfTest
    (by rw [cvmCtorProofDomainValidationShapeTest]; rfl)
    cvmValidationProofHasNoIndOccTest cvmValidationProofCheckedTest
    (by rfl) trace

def cvmValidationDirectPositivityAlignmentTest
    (trace : AddInductive.ConstructorPositivityModeTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats false
      constructorValidityMatrixKernelCtor.name 4
      cvmValidationProofContextTest cvmCtorDirectDomain) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace :=
  cvmTargetPositivityModeAlignmentTest cvmValidationDirectWhnfSelfTest
    (by rw [cvmCtorDirectDomainValidationShapeTest]; rfl)
    cvmValidationDirectHasIndOccTest cvmValidationDirectCheckedTest
    (by rfl) trace

def cvmValidationLaterPositivityAlignmentTest
    (trace : AddInductive.ConstructorPositivityModeTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats false
      constructorValidityMatrixKernelCtor.name 6
      cvmValidationFunctionContextTest cvmCtorLaterDomain) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace :=
  cvmAbsentPositivityModeAlignmentTest cvmValidationLaterWhnfSelfTest
    (by rw [cvmCtorLaterDomainValidationShapeTest]; rfl)
    cvmValidationLaterHasNoIndOccTest cvmValidationLaterCheckedTest
    (by rfl) trace

def cvmValidationLaterProofPositivityAlignmentTest
    (trace : AddInductive.ConstructorPositivityModeTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats false
      constructorValidityMatrixKernelCtor.name 7
      cvmValidationLaterContextTest cvmCtorLaterProofDomain) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace :=
  cvmAbsentPositivityModeAlignmentTest cvmValidationLaterProofWhnfSelfTest
    (by rw [cvmCtorLaterProofDomainValidationShapeTest]; rfl)
    cvmValidationLaterProofHasNoIndOccTest
    cvmValidationLaterProofCheckedTest (by rfl) trace

def cvmTransportPositivityTraceTest
    {context context' : AddInductive.Context}
    (contextEq : context = context')
    {source source' : Expr} (sourceEq : source = source')
    (trace : AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source fuel) :
    AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context' source' fuel := by
  subst context'
  subst source'
  exact trace

def cvmTransportPositivityAlignmentTest
    {context context' : AddInductive.Context}
    (contextEq : context = context')
    {source source' : Expr} (sourceEq : source = source')
    (trace : AddInductive.ConstructorPositivityTrace stats ctor argIdx
      context source fuel)
    (alignment : AddInductive.ConstructorPositivityAlignmentTrace
      (cvmTransportPositivityTraceTest contextEq sourceEq trace)) :
    AddInductive.ConstructorPositivityAlignmentTrace trace := by
  subst context'
  subst source'
  exact alignment

def cvmValidationFunctionPositivityAlignmentTest
    (trace : AddInductive.ConstructorPositivityModeTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats false
      constructorValidityMatrixKernelCtor.name 5
      cvmValidationDirectContextTest cvmCtorFunctionDomain) :
    AddInductive.ConstructorPositivityModeAlignmentTrace trace := by
  cases trace with
  | skipped unsafeEq => contradiction
  | safe unsafeEq positivityTrace =>
      apply AddInductive.ConstructorPositivityModeAlignmentTrace.safe
      cases positivityTrace with
      | absent context source result fuel whnf occurs =>
          have resultEq := cvmCandidateWhnfResultEqTest
            cvmValidationFunctionWhnfSelfTest whnf
          subst result
          rw [cvmValidationFunctionHasIndOccTest] at occurs
          contradiction
      | forallE context source fuel name domain body binderInfo whnf occurs
          domainFree tail =>
          have resultEq := cvmCandidateWhnfResultEqTest
            cvmValidationFunctionWhnfSelfTest whnf
          rw [cvmCtorFunctionDomainValidationShapeTest] at resultEq
          injection resultEq with nameEq domainEq bodyEq binderInfoEq
          subst name
          subst domain
          subst body
          subst binderInfo
          have tailContextEq :
              cvmValidationDirectContextTest.pushLocalDecl `y .default
                  (AddInductive.consumeTypeAnnotations
                    (.fvar cvmValidationAlphaIdTest)) =
                cvmValidationFunctionPosContextTest := by
            simp [cvmValidationFunctionPosContextTest,
              AddInductive.consumeTypeAnnotations]
          have tailSourceEq :
              (cvmValidationFamilyApplicationTest
                (.fvar cvmValidationAlphaIdTest)
                (.fvar cvmValidationPIdTest)).instantiate1
                  cvmValidationDirectContextTest.freshExpr =
                cvmValidationFamilyApplicationTest
                  (.fvar cvmValidationAlphaIdTest)
                  (.fvar cvmValidationPIdTest) := by
            simp [cvmValidationFamilyApplicationTest,
              Expr.instantiate1_eq, Expr.instantiate1']
          let tailNormalized := cvmTransportPositivityTraceTest
            tailContextEq tailSourceEq tail
          have tailNormalizedAlignment :
              AddInductive.ConstructorPositivityAlignmentTrace
                tailNormalized := by
            cases htail : tailNormalized with
            | absent context source result fuel whnf occurs =>
                have resultEq := cvmCandidateWhnfResultEqTest
                  cvmValidationFunctionPosBodyWhnfSelfTest whnf
                subst result
                rw [cvmValidationFunctionPosBodyHasIndOccTest] at occurs
                contradiction
            | forallE context source fuel name domain body binderInfo whnf
                occurs domainFree tail =>
                have resultEq := cvmCandidateWhnfResultEqTest
                  cvmValidationFunctionPosBodyWhnfSelfTest whnf
                have impossible := congrArg Expr.isForall resultEq
                simp [cvmValidationFamilyApplicationTest,
                  Expr.isForall] at impossible
            | target context source result fuel targetIdx whnf occurs
                terminal valid =>
                have resultEq := cvmCandidateWhnfResultEqTest
                  cvmValidationFunctionPosBodyWhnfSelfTest whnf
                subst result
                exact .target cvmValidationFunctionPosBodyCheckedTest
          have tailAlignment := cvmTransportPositivityAlignmentTest
            tailContextEq tailSourceEq tail tailNormalizedAlignment
          exact .forallE cvmValidationFunctionCheckedTest
            cvmValidationAlphaDirectCheckedTest
            cvmValidationAlphaDirectConsumedCheckedTest
            (.succ (.param `u))
            (cvmValidationAlphaDirectConsumedCheckedTest.inferred_eq_of_run
              (by
                simpa [AddInductive.consumeTypeAnnotations] using
                  cvmValidationAlphaDirectCheckTest))
            cvmValidationDirectFreshTest
            cvmValidationAlphaDirectAnnotationsTest tail tailAlignment
      | target context source result fuel targetIdx whnf occurs terminal valid =>
          have resultEq := cvmCandidateWhnfResultEqTest
            cvmValidationFunctionWhnfSelfTest whnf
          subst result
          rw [cvmCtorFunctionDomainValidationShapeTest] at terminal
          simp [Expr.isForall] at terminal

def cvmValidationCtorPDomainCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationRootContextTest
      cvmCtorPDomain :=
  cvmCheckedOfValidTest _ _ _ (by
    rw [cvmCtorPDomainValidationShapeTest]
    simp [FVarsIn, Level.hasMVar']
    change (cvmValidationRootContextTest.lctx.find?
      cvmValidationAlphaIdTest).isSome = true
    rw [cvmValidationAlphaFindTest]
    rfl)
    (by
      rw [cvmCtorPDomainValidationShapeTest]
      simp [Expr.hasMVar_eq_cache, Level.hasMVar_eq, Level.hasMVar'])
    cvmValidationCtorPDomainCheckTest

def cvmValidationTerminalShapeCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmValidationLaterProofContextTest
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest)) := by
  rw [← cvmCtorTerminalValidationShapeTest]
  exact cvmValidationTerminalCheckedTest

theorem cvmCtorViewTest_eq :
    cvmCandidate.families.singleton.constructors.singleton.type.view =
      constructorValidityMatrixKernelCtor.type := by
  apply cvmCtorIdentityEvidence.identity.view_eq_source
  · apply TypeChecker.CandidateLocalContextRun.empty
    rw [cvmConstructorCandidateContext_eq]
    rfl
  · rw [cvmConstructorCandidateContext_eq]
    simp [constructorValidityMatrixKernelCtor,
      constructorValidityMatrixMkInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, FVarsIn, Level.hasMVar',
      Expr.looseBVarRange']
  · rfl

def cvmTransportValidationTraceTest
    {context context' : AddInductive.Context}
    (contextEq : context = context')
    {source source' : Expr} (sourceEq : source = source')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    AddInductive.ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context' source' argIdx fuel := by
  subst context'
  subst source'
  exact trace

def cvmTransportViewAlignmentTest
    {context context' : AddInductive.Context}
    (contextEq : context = context')
    {source source' view view' : Expr}
    (sourceEq : source = source') (viewEq : view = view')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel)
    (alignment : AddInductive.ConstructorViewAlignmentTrace
      (cvmTransportValidationTraceTest contextEq sourceEq trace) view') :
    AddInductive.ConstructorViewAlignmentTrace trace view := by
  subst context'
  subst source'
  subst view'
  exact alignment

@[simp] theorem cvmTransportValidationTraceSpineLengthTest
    {context context' : AddInductive.Context}
    (contextEq : context = context')
    {source source' : Expr} (sourceEq : source = source')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    (cvmTransportValidationTraceTest contextEq sourceEq trace).spineLength =
      trace.spineLength := by
  subst context'
  subst source'
  rfl

def cvmTransportValidationTraceIndexedTest
    {context context' : AddInductive.Context}
    (contextEq : context = context')
    {source source' : Expr} (sourceEq : source = source')
    {argIdx argIdx' : Nat} (argIdxEq : argIdx = argIdx')
    {fuel fuel' : Nat} (fuelEq : fuel = fuel')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    AddInductive.ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context' source' argIdx' fuel' := by
  subst context'
  subst source'
  subst argIdx'
  subst fuel'
  exact trace

def cvmTransportViewAlignmentIndexedTest
    {context context' : AddInductive.Context}
    (contextEq : context = context')
    {source source' view view' : Expr}
    (sourceEq : source = source') (viewEq : view = view')
    {argIdx argIdx' : Nat} (argIdxEq : argIdx = argIdx')
    {fuel fuel' : Nat} (fuelEq : fuel = fuel')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel)
    (alignment : AddInductive.ConstructorViewAlignmentTrace
      (cvmTransportValidationTraceIndexedTest contextEq sourceEq argIdxEq
        fuelEq trace) view') :
    AddInductive.ConstructorViewAlignmentTrace trace view := by
  subst context'
  subst source'
  subst view'
  subst argIdx'
  subst fuel'
  exact alignment

@[simp] theorem cvmTransportValidationTraceIndexedSpineLengthTest
    {context context' : AddInductive.Context}
    (contextEq : context = context')
    {source source' : Expr} (sourceEq : source = source')
    {argIdx argIdx' : Nat} (argIdxEq : argIdx = argIdx')
    {fuel fuel' : Nat} (fuelEq : fuel = fuel')
    (trace : AddInductive.ConstructorTypeValidationTrace stats isUnsafe
      familyIdx ctor context source argIdx fuel) :
    (cvmTransportValidationTraceIndexedTest contextEq sourceEq argIdxEq
      fuelEq trace).spineLength = trace.spineLength := by
  subst context'
  subst source'
  subst argIdx'
  subst fuel'
  rfl

set_option pp.universes false in
set_option pp.all false in
def cvmStagedPostFamilyInputTest :
    VInductDecl.StagedNormalizationCandidatePostFamilyInput
      cvmFamilyContext cvmConstructorContext VEnv.empty [`u]
      cvmCandidate constructorValidityMatrixDecl where
  universeInput := cvmStagedUniverseInputTest
  alignment := by
    rw [AddInductive.CandidateList.singleton_eta
      cvmCandidate.families.singleton.constructors]
    change AddInductive.ConstructorCandidateAlignmentTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats false 0
      { cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
        env := cvmConstructorContext.env }
      cvmStagedUniverseInputTest.staged.constructorValidation.trace
      (.cons cvmCandidate.families.singleton.constructors.singleton .nil)
    generalize htrace :
      cvmStagedUniverseInputTest.staged.constructorValidation.trace = trace
    cases trace with
    | cons seen head constructors fresh closed rootCheck typeTrace tailTrace =>
      clear htrace
      have rootContextEq :
          { cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
              env := cvmConstructorContext.env } =
            cvmValidationRootContextTest := by
        rw [cvmFamilyTerminalContextTest_eq]
        rfl
      have rootFuelEq :
          { cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
              env := cvmConstructorContext.env }.fuel.inductiveFuel = 1000 := by
        rw [cvmFamilyTerminalContextTest_eq]
        rfl
      let rootNormalized := cvmTransportValidationTraceIndexedTest
        rootContextEq (by rfl) (by rfl) rootFuelEq typeTrace
      let rootNormalizedTrace := rootNormalized
      have rootSpine : typeTrace.spineLength =
          rootNormalizedTrace.spineLength :=
        (cvmTransportValidationTraceIndexedSpineLengthTest rootContextEq
          (by rfl) (by rfl) rootFuelEq typeTrace).symm
      cases hroot : rootNormalizedTrace with
      | parameter context fuel argIdx name domain body binderInfo parameter
          parameterType parameterAt parameterTypeRun defeq afterAlphaTrace =>
        simp [hroot,
          AddInductive.ConstructorTypeValidationTrace.spineLength] at rootSpine
        rw [cvmStagedStatsTest_eq, cvmStatsParamsTest] at parameterAt
        simp at parameterAt
        subst parameter
        change AddInductive.getType (.fvar cvmValidationAlphaIdTest)
          cvmValidationRootContextTest = .ok parameterType at parameterTypeRun
        rw [cvmValidationGetTypeAlphaTest] at parameterTypeRun
        injection parameterTypeRun with parameterTypeEq
        subst parameterType
        let afterAlphaSourceEq := cvmFirstParameterSourceTest.trans
          cvmCtorAfterAlphaForallTest
        let afterAlphaNormalized := cvmTransportValidationTraceTest (by rfl)
          afterAlphaSourceEq afterAlphaTrace
        let afterAlphaNormalizedTrace := afterAlphaNormalized
        have afterAlphaSpine : afterAlphaTrace.spineLength =
            afterAlphaNormalizedTrace.spineLength :=
          (cvmTransportValidationTraceSpineLengthTest (by rfl)
            afterAlphaSourceEq afterAlphaTrace).symm
        cases hafterAlpha : afterAlphaNormalizedTrace with
        | parameter context fuel argIdx name domain body binderInfo parameter
            parameterType parameterAt parameterTypeRun defeq afterPTrace =>
          simp [hafterAlpha,
            AddInductive.ConstructorTypeValidationTrace.spineLength]
            at afterAlphaSpine
          rw [cvmStagedStatsTest_eq, cvmStatsParamsTest] at parameterAt
          simp at parameterAt
          subst parameter
          change AddInductive.getType (.fvar cvmValidationPIdTest)
            cvmValidationRootContextTest = .ok parameterType at parameterTypeRun
          rw [cvmValidationGetTypePTest] at parameterTypeRun
          injection parameterTypeRun with parameterTypeEq
          subst parameterType
          let afterPSourceEq := cvmSecondParameterSourceTest.trans
            cvmCtorAfterPForallTest
          let afterPNormalized := cvmTransportValidationTraceTest (by rfl)
            afterPSourceEq afterPTrace
          let afterPNormalizedTrace := afterPNormalized
          have afterPSpine : afterPTrace.spineLength =
              afterPNormalizedTrace.spineLength :=
            (cvmTransportValidationTraceSpineLengthTest (by rfl)
              afterPSourceEq afterPTrace).symm
          cases hafterP : afterPNormalizedTrace with
          | parameter context fuel argIdx name domain body binderInfo parameter
              parameterType parameterAt parameterTypeRun defeq tail =>
            rw [cvmStagedStatsTest_eq, cvmStatsParamsTest] at parameterAt
            simp at parameterAt
          | ordinary context fuel argIdx name domain body binderInfo sortResult
              noParameter ensureType universeTrace xPositivity afterXTrace =>
            simp [hafterP,
              AddInductive.ConstructorTypeValidationTrace.spineLength]
              at afterPSpine
            have xContextEq :
                cvmValidationRootContextTest.pushLocalDecl `x .default
                    (AddInductive.consumeTypeAnnotations cvmCtorXDomain) =
                  cvmValidationXContextTest := by rfl
            let afterXSourceEq := cvmFirstFieldSourceTest.trans
              cvmCtorAfterXForallTest
            let afterXNormalized := cvmTransportValidationTraceTest xContextEq
              afterXSourceEq afterXTrace
            let afterXNormalizedTrace := afterXNormalized
            have afterXSpine : afterXTrace.spineLength =
                afterXNormalizedTrace.spineLength :=
              (cvmTransportValidationTraceSpineLengthTest xContextEq
                afterXSourceEq afterXTrace).symm
            cases hafterX : afterXNormalizedTrace with
            | parameter context fuel argIdx name domain body binderInfo parameter
                parameterType parameterAt parameterTypeRun defeq tail =>
              rw [cvmStagedStatsTest_eq, cvmStatsParamsTest] at parameterAt
              simp at parameterAt
            | ordinary context fuel argIdx name domain body binderInfo sortResult
                noParameter ensureType universeTrace proofPositivity
                afterProofTrace =>
              simp [hafterX,
                AddInductive.ConstructorTypeValidationTrace.spineLength]
                at afterXSpine
              have proofContextEq :
                  cvmValidationXContextTest.pushLocalDecl `proof .default
                      (AddInductive.consumeTypeAnnotations cvmCtorProofDomain) =
                    cvmValidationProofContextTest := by rfl
              let afterProofSourceEq := cvmSecondFieldSourceTest.trans
                cvmCtorAfterProofForallTest
              let afterProofNormalized := cvmTransportValidationTraceTest
                proofContextEq afterProofSourceEq afterProofTrace
              let afterProofNormalizedTrace := afterProofNormalized
              have afterProofSpine : afterProofTrace.spineLength =
                  afterProofNormalizedTrace.spineLength :=
                (cvmTransportValidationTraceSpineLengthTest proofContextEq
                  afterProofSourceEq afterProofTrace).symm
              cases hafterProof : afterProofNormalizedTrace with
              | parameter context fuel argIdx name domain body binderInfo parameter
                  parameterType parameterAt parameterTypeRun defeq tail =>
                rw [cvmStagedStatsTest_eq, cvmStatsParamsTest] at parameterAt
                simp at parameterAt
              | ordinary context fuel argIdx name domain body binderInfo sortResult
                  noParameter ensureType universeTrace directPositivity
                  afterDirectTrace =>
                simp [hafterProof,
                  AddInductive.ConstructorTypeValidationTrace.spineLength]
                  at afterProofSpine
                have directContextEq :
                    cvmValidationProofContextTest.pushLocalDecl `direct .default
                        (AddInductive.consumeTypeAnnotations cvmCtorDirectDomain) =
                      cvmValidationDirectContextTest := by rfl
                let afterDirectSourceEq := cvmThirdFieldSourceTest.trans
                  cvmCtorAfterDirectForallTest
                let afterDirectNormalized := cvmTransportValidationTraceTest
                  directContextEq afterDirectSourceEq afterDirectTrace
                let afterDirectNormalizedTrace := afterDirectNormalized
                have afterDirectSpine : afterDirectTrace.spineLength =
                    afterDirectNormalizedTrace.spineLength :=
                  (cvmTransportValidationTraceSpineLengthTest directContextEq
                    afterDirectSourceEq afterDirectTrace).symm
                cases hafterDirect : afterDirectNormalizedTrace with
                | parameter context fuel argIdx name domain body binderInfo
                    parameter parameterType parameterAt parameterTypeRun defeq tail =>
                  rw [cvmStagedStatsTest_eq, cvmStatsParamsTest] at parameterAt
                  simp at parameterAt
                | ordinary context fuel argIdx name domain body binderInfo sortResult
                    noParameter ensureType universeTrace functionPositivity
                    afterFunctionTrace =>
                  simp [hafterDirect,
                    AddInductive.ConstructorTypeValidationTrace.spineLength]
                    at afterDirectSpine
                  have functionContextEq :
                      cvmValidationDirectContextTest.pushLocalDecl `function .default
                          (AddInductive.consumeTypeAnnotations
                            cvmCtorFunctionDomain) =
                        cvmValidationFunctionContextTest := by rfl
                  let afterFunctionSourceEq := cvmFourthFieldSourceTest.trans
                    cvmCtorAfterFunctionForallTest
                  let afterFunctionNormalized := cvmTransportValidationTraceTest
                    functionContextEq afterFunctionSourceEq afterFunctionTrace
                  let afterFunctionNormalizedTrace := afterFunctionNormalized
                  have afterFunctionSpine : afterFunctionTrace.spineLength =
                      afterFunctionNormalizedTrace.spineLength :=
                    (cvmTransportValidationTraceSpineLengthTest
                      functionContextEq afterFunctionSourceEq
                      afterFunctionTrace).symm
                  cases hafterFunction : afterFunctionNormalizedTrace with
                  | parameter context fuel argIdx name domain body binderInfo
                      parameter parameterType parameterAt parameterTypeRun defeq tail =>
                    rw [cvmStagedStatsTest_eq, cvmStatsParamsTest] at parameterAt
                    simp at parameterAt
                  | ordinary context fuel argIdx name domain body binderInfo sortResult
                      noParameter ensureType universeTrace laterPositivity
                      afterLaterTrace =>
                    simp [hafterFunction,
                      AddInductive.ConstructorTypeValidationTrace.spineLength]
                      at afterFunctionSpine
                    have laterContextEq :
                        cvmValidationFunctionContextTest.pushLocalDecl `later .default
                            (AddInductive.consumeTypeAnnotations
                              cvmCtorLaterDomain) =
                          cvmValidationLaterContextTest := by rfl
                    let afterLaterSourceEq := cvmFifthFieldSourceTest.trans
                      cvmCtorAfterLaterForallTest
                    let afterLaterNormalized := cvmTransportValidationTraceTest
                      laterContextEq afterLaterSourceEq afterLaterTrace
                    let afterLaterNormalizedTrace := afterLaterNormalized
                    have afterLaterSpine : afterLaterTrace.spineLength =
                        afterLaterNormalizedTrace.spineLength :=
                      (cvmTransportValidationTraceSpineLengthTest laterContextEq
                        afterLaterSourceEq afterLaterTrace).symm
                    cases hafterLater : afterLaterNormalizedTrace with
                    | parameter context fuel argIdx name domain body binderInfo
                        parameter parameterType parameterAt parameterTypeRun defeq tail =>
                      rw [cvmStagedStatsTest_eq, cvmStatsParamsTest] at parameterAt
                      simp at parameterAt
                    | ordinary context fuel argIdx name domain body binderInfo sortResult
                        noParameter ensureType universeTrace laterProofPositivity
                        terminalTrace =>
                      simp [hafterLater,
                        AddInductive.ConstructorTypeValidationTrace.spineLength]
                        at afterLaterSpine
                      have laterProofContextEq :
                          cvmValidationLaterContextTest.pushLocalDecl
                              `laterProof .default
                              (AddInductive.consumeTypeAnnotations
                                cvmCtorLaterProofDomain) =
                            cvmValidationLaterProofContextTest := by rfl
                      let terminalSourceEq := cvmSixthFieldSourceTest.trans
                        cvmCtorTerminalValidationShapeTest
                      let terminalNormalized := cvmTransportValidationTraceTest
                        laterProofContextEq terminalSourceEq terminalTrace
                      let terminalNormalizedTrace := terminalNormalized
                      have terminalSpine : terminalTrace.spineLength =
                          terminalNormalizedTrace.spineLength :=
                        (cvmTransportValidationTraceSpineLengthTest
                          laterProofContextEq terminalSourceEq
                          terminalTrace).symm
                      cases hterminal : terminalNormalizedTrace with
                      | terminal context source fuel argIdx terminal valid =>
                        simp [hterminal,
                          AddInductive.ConstructorTypeValidationTrace.spineLength]
                          at terminalSpine
                        have terminalNormalizedAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              terminalNormalizedTrace
                              (cvmValidationFamilyApplicationTest
                                (.fvar cvmValidationAlphaIdTest)
                                (.fvar cvmValidationPIdTest)) := by
                          rw [hterminal]
                          exact .terminal cvmValidationTerminalShapeCheckedTest
                            cvmValidationTerminalShapeCheckedTest terminal valid
                        have terminalAlignment := cvmTransportViewAlignmentTest
                          laterProofContextEq terminalSourceEq terminalSourceEq
                          terminalTrace terminalNormalizedAlignment
                        have afterLaterNormalizedAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              afterLaterNormalizedTrace
                              (.forallE `laterProof cvmCtorLaterProofDomain
                                cvmCtorAfterLater.bindingBody! .default) := by
                          rw [hafterLater]
                          exact .ordinary cvmValidationLaterProofCheckedTest
                            cvmValidationLaterProofCheckedTest
                            (cvmValidationReflObservationTest _ _)
                            cvmValidationLaterProofConsumedCheckedTest
                            laterProofPositivity
                            (cvmValidationLaterProofPositivityAlignmentTest
                              laterProofPositivity)
                            cvmValidationLaterFreshTest
                            cvmValidationLaterProofAnnotationsTest
                            terminalTrace terminalAlignment
                        have afterLaterAlignment := cvmTransportViewAlignmentTest
                          laterContextEq afterLaterSourceEq afterLaterSourceEq
                          afterLaterTrace afterLaterNormalizedAlignment
                        have afterFunctionNormalizedAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              afterFunctionNormalizedTrace
                              (.forallE `later cvmCtorLaterDomain
                                cvmCtorAfterFunction.bindingBody! .default) := by
                          rw [hafterFunction]
                          exact .ordinary cvmValidationLaterCheckedTest
                            cvmValidationLaterCheckedTest
                            (cvmValidationReflObservationTest _ _)
                            cvmValidationLaterConsumedCheckedTest laterPositivity
                            (cvmValidationLaterPositivityAlignmentTest
                              laterPositivity)
                            cvmValidationFunctionFreshTest
                            cvmValidationLaterAnnotationsTest
                            afterLaterTrace afterLaterAlignment
                        have afterFunctionAlignment :=
                          cvmTransportViewAlignmentTest functionContextEq
                            afterFunctionSourceEq afterFunctionSourceEq
                            afterFunctionTrace afterFunctionNormalizedAlignment
                        have afterDirectNormalizedAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              afterDirectNormalizedTrace
                              (.forallE `function cvmCtorFunctionDomain
                                cvmCtorAfterDirect.bindingBody! .default) := by
                          rw [hafterDirect]
                          exact .ordinary cvmValidationFunctionCheckedTest
                            cvmValidationFunctionCheckedTest
                            (cvmValidationReflObservationTest _ _)
                            cvmValidationFunctionConsumedCheckedTest
                            functionPositivity
                            (cvmValidationFunctionPositivityAlignmentTest
                              functionPositivity)
                            cvmValidationDirectFreshTest
                            cvmValidationFunctionAnnotationsTest
                            afterFunctionTrace afterFunctionAlignment
                        have afterDirectAlignment :=
                          cvmTransportViewAlignmentTest directContextEq
                            afterDirectSourceEq afterDirectSourceEq
                            afterDirectTrace afterDirectNormalizedAlignment
                        have afterProofNormalizedAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              afterProofNormalizedTrace
                              (.forallE `direct cvmCtorDirectDomain
                                cvmCtorAfterProof.bindingBody! .default) := by
                          rw [hafterProof]
                          exact .ordinary cvmValidationDirectCheckedTest
                            cvmValidationDirectCheckedTest
                            (cvmValidationReflObservationTest _ _)
                            cvmValidationDirectConsumedCheckedTest
                            directPositivity
                            (cvmValidationDirectPositivityAlignmentTest
                              directPositivity)
                            cvmValidationProofFreshTest
                            cvmValidationDirectAnnotationsTest
                            afterDirectTrace afterDirectAlignment
                        have afterProofAlignment :=
                          cvmTransportViewAlignmentTest proofContextEq
                            afterProofSourceEq afterProofSourceEq
                            afterProofTrace afterProofNormalizedAlignment
                        have afterXNormalizedAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              afterXNormalizedTrace
                              (.forallE `proof cvmCtorProofDomain
                                cvmCtorAfterX.bindingBody! .default) := by
                          rw [hafterX]
                          exact .ordinary cvmValidationProofCheckedTest
                            cvmValidationProofCheckedTest
                            (cvmValidationReflObservationTest _ _)
                            cvmValidationProofConsumedCheckedTest
                            proofPositivity
                            (cvmValidationProofPositivityAlignmentTest
                              proofPositivity)
                            cvmValidationXFreshTest
                            cvmValidationProofAnnotationsTest
                            afterProofTrace afterProofAlignment
                        have afterXAlignment := cvmTransportViewAlignmentTest
                          xContextEq afterXSourceEq afterXSourceEq
                          afterXTrace afterXNormalizedAlignment
                        have afterPNormalizedAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              afterPNormalizedTrace
                              (.forallE `x cvmCtorXDomain
                                cvmCtorAfterP.bindingBody! .default) := by
                          rw [hafterP]
                          exact .ordinary cvmValidationXCheckedTest
                            cvmValidationXCheckedTest
                            (cvmValidationReflObservationTest _ _)
                            cvmValidationXConsumedCheckedTest xPositivity
                            (cvmValidationXPositivityAlignmentTest xPositivity)
                            cvmValidationRootFreshTest
                            cvmValidationXAnnotationsTest
                            afterXTrace afterXAlignment
                        have afterPAlignment := cvmTransportViewAlignmentTest
                          (by rfl) afterPSourceEq afterPSourceEq afterPTrace
                          afterPNormalizedAlignment
                        have afterAlphaNormalizedAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              afterAlphaNormalizedTrace
                              (.forallE `P cvmCtorPDomain
                                cvmCtorAfterAlpha.bindingBody! .implicit) := by
                          rw [hafterAlpha]
                          exact .parameter cvmValidationCtorPDomainCheckedTest
                            cvmValidationCtorPDomainCheckedTest
                            cvmValidationPDomainCheckedTest rfl
                            (by
                              change (cvmValidationRootContextTest.lctx.find?
                                cvmValidationPIdTest).isSome = true
                              rw [cvmValidationPFindTest]
                              rfl)
                            afterPTrace afterPAlignment
                        have afterAlphaAlignment :=
                          cvmTransportViewAlignmentTest (by rfl)
                            afterAlphaSourceEq afterAlphaSourceEq
                            afterAlphaTrace afterAlphaNormalizedAlignment
                        have rootNormalizedAlignment :
                            AddInductive.ConstructorViewAlignmentTrace
                              rootNormalizedTrace
                              constructorValidityMatrixKernelCtor.type := by
                          rw [hroot]
                          exact .parameter cvmValidationSortCheckedTest
                            cvmValidationSortCheckedTest
                            cvmValidationSortCheckedTest rfl
                            (by
                              change (cvmValidationRootContextTest.lctx.find?
                                cvmValidationAlphaIdTest).isSome = true
                              rw [cvmValidationAlphaFindTest]
                              rfl)
                            afterAlphaTrace afterAlphaAlignment
                        have headAlignment :=
                          cvmTransportViewAlignmentIndexedTest rootContextEq
                            (by rfl) cvmCtorViewTest_eq (by rfl) rootFuelEq
                            typeTrace rootNormalizedAlignment
                        let rootScope : AddInductive.ConstructorCheckedExpr
                            ({ cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
                              env := cvmConstructorContext.env }).withEmptyLocalContext
                            constructorValidityMatrixKernelCtor.type :=
                          AddInductive.ConstructorCheckedExpr.ofClosedRoot
                            closed rootCheck
                        cases tailTrace with
                        | nil finalSeen =>
                          exact AddInductive.ConstructorCandidateAlignmentTrace.cons
                            rootScope
                            (by
                              change
                                cvmCandidate.families.singleton.constructors.singleton.type.trace.storedSpine =
                                  true
                              exact cvmCtorIdentityEvidence.identity.storedSpine)
                            (by
                              change
                                cvmCandidate.families.singleton.constructors.singleton.type.trace.spineLength =
                                  typeTrace.spineLength
                              have candidateSpine :=
                                cvmCtorIdentityEvidence.spineLength_eq.trans
                                  cvmCtorIdentityReplay_shape.1
                              omega)
                            (by
                              rw [cvmCtorWhnfDepth, rootContextEq]
                              rfl)
                            headAlignment
                            (AddInductive.ConstructorCandidateAlignmentTrace.nil
                              ((∅ : NameSet).insert
                                constructorValidityMatrixKernelCtor.name))
                    | terminal context source fuel argIdx terminal valid =>
                      simp [Expr.isForall] at terminal
                  | terminal context source fuel argIdx terminal valid =>
                    simp [Expr.isForall] at terminal
                | terminal context source fuel argIdx terminal valid =>
                  simp [Expr.isForall] at terminal
              | terminal context source fuel argIdx terminal valid =>
                simp [Expr.isForall] at terminal
            | terminal context source fuel argIdx terminal valid =>
              simp [Expr.isForall] at terminal
          | terminal context source fuel argIdx terminal valid =>
            simp [Expr.isForall] at terminal
        | ordinary context fuel argIdx name domain body binderInfo sortResult
            noParameter ensureType universeTrace positivity tail =>
          rw [cvmStagedStatsTest_eq, cvmStatsParamsTest] at noParameter
          simp at noParameter
        | terminal context source fuel argIdx terminal valid =>
          simp [Expr.isForall] at terminal
      | ordinary context fuel argIdx name domain body binderInfo sortResult
          noParameter ensureType universeTrace positivity tail =>
        rw [cvmStagedStatsTest_eq, cvmStatsParamsTest] at noParameter
        simp at noParameter
      | terminal context source fuel argIdx terminal valid =>
        simp [constructorValidityMatrixKernelCtor,
          constructorValidityMatrixMkInfo, ConstantInfo.type,
          ConstantInfo.toConstantVal, Expr.isForall] at terminal

def cvmPreFamilyContextTest : AddInductive.Context :=
  cvmValidationFamilyContextTest

def cvmPreFamilyXContextTest : AddInductive.Context :=
  cvmPreFamilyContextTest.pushLocalDecl `x .default
    (AddInductive.consumeTypeAnnotations cvmCtorXDomain)

def cvmPreFamilyProofContextTest : AddInductive.Context :=
  cvmPreFamilyXContextTest.pushLocalDecl `proof .default
    (AddInductive.consumeTypeAnnotations cvmCtorProofDomain)

def cvmPreFamilyAfterDirectContextTest : AddInductive.Context :=
  cvmPreFamilyProofContextTest.advanceFresh

def cvmPreFamilyAfterFunctionContextTest : AddInductive.Context :=
  cvmPreFamilyAfterDirectContextTest.advanceFresh

def cvmPreFamilyLaterContextTest : AddInductive.Context :=
  cvmPreFamilyAfterFunctionContextTest.pushLocalDecl `later .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain)

def cvmPreFamilyLaterProofContextTest : AddInductive.Context :=
  cvmPreFamilyLaterContextTest.pushLocalDecl `laterProof .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain)

def cvmPreFamilyFunctionInnerContextTest : AddInductive.Context :=
  cvmPreFamilyAfterDirectContextTest.pushLocalDecl `y .default
    (.fvar cvmValidationAlphaIdTest)

theorem cvmAdvanceLocalRunTest
    (run : TypeChecker.CandidateLocalContextRun context) :
    TypeChecker.CandidateLocalContextRun context.advanceFresh where
  wf := run.wf
  reserves := by
    intro decl membership
    exact NameGenerator.Reserves.mono NameGenerator.LE.next
      (run.reserves decl membership)

theorem cvmPreFamilyRootLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmPreFamilyContextTest :=
  cvmValidationFamilyLocalRunTest

theorem cvmPreFamilyXLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmPreFamilyXContextTest :=
  cvmPreFamilyRootLocalRunTest.push `x .default
    (AddInductive.consumeTypeAnnotations cvmCtorXDomain)

theorem cvmPreFamilyProofLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmPreFamilyProofContextTest :=
  cvmPreFamilyXLocalRunTest.push `proof .default
    (AddInductive.consumeTypeAnnotations cvmCtorProofDomain)

theorem cvmPreFamilyAfterDirectLocalRunTest :
    TypeChecker.CandidateLocalContextRun
      cvmPreFamilyAfterDirectContextTest :=
  cvmAdvanceLocalRunTest cvmPreFamilyProofLocalRunTest

theorem cvmPreFamilyAfterFunctionLocalRunTest :
    TypeChecker.CandidateLocalContextRun
      cvmPreFamilyAfterFunctionContextTest :=
  cvmAdvanceLocalRunTest cvmPreFamilyAfterDirectLocalRunTest

theorem cvmPreFamilyLaterLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmPreFamilyLaterContextTest :=
  cvmPreFamilyAfterFunctionLocalRunTest.push `later .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain)

theorem cvmPreFamilyLaterProofLocalRunTest :
    TypeChecker.CandidateLocalContextRun cvmPreFamilyLaterProofContextTest :=
  cvmPreFamilyLaterLocalRunTest.push `laterProof .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain)

theorem cvmPreFamilyFunctionInnerLocalRunTest :
    TypeChecker.CandidateLocalContextRun
      cvmPreFamilyFunctionInnerContextTest :=
  cvmPreFamilyAfterDirectLocalRunTest.push `y .default
    (.fvar cvmValidationAlphaIdTest)

theorem cvmPreFamilyAlphaFindRootTest :
    cvmPreFamilyContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) := by
  simpa [cvmPreFamilyContextTest, cvmValidationRootContextTest] using
    cvmValidationAlphaFindTest

theorem cvmPreFamilyPFindRootTest :
    cvmPreFamilyContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) := by
  simpa [cvmPreFamilyContextTest, cvmValidationRootContextTest] using
    cvmValidationPFindTest

theorem cvmPreFamilyAlphaFindXTest :
    cvmPreFamilyXContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmPreFamilyRootLocalRunTest.push_findOld `x .default
    (AddInductive.consumeTypeAnnotations cvmCtorXDomain)
    cvmPreFamilyAlphaFindRootTest

theorem cvmPreFamilyPFindXTest :
    cvmPreFamilyXContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmPreFamilyRootLocalRunTest.push_findOld `x .default
    (AddInductive.consumeTypeAnnotations cvmCtorXDomain)
    cvmPreFamilyPFindRootTest

theorem cvmPreFamilyRootFreshIdTest :
    cvmPreFamilyContextTest.freshFVarId = cvmValidationXIdTest := by
  rfl

theorem cvmPreFamilyXFindTest :
    cvmPreFamilyXContextTest.lctx.find? cvmValidationXIdTest =
      some (.cdecl cvmPreFamilyContextTest.lctx.decls.size
        cvmValidationXIdTest `x (.fvar cvmValidationAlphaIdTest)
        .default .default) := by
  have found := cvmPreFamilyRootLocalRunTest.push_findNew `x .default
    (AddInductive.consumeTypeAnnotations cvmCtorXDomain)
  rw [← cvmPreFamilyRootFreshIdTest]
  simpa [cvmPreFamilyXContextTest, cvmValidationXIdTest,
    cvmPreFamilyContextTest,
    cvmValidationRootContextTest, cvmCtorXDomainValidationShapeTest,
    AddInductive.consumeTypeAnnotations] using found

theorem cvmPreFamilyAlphaFindProofTest :
    cvmPreFamilyProofContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmPreFamilyXLocalRunTest.push_findOld `proof .default
    (AddInductive.consumeTypeAnnotations cvmCtorProofDomain)
    cvmPreFamilyAlphaFindXTest

theorem cvmPreFamilyPFindProofTest :
    cvmPreFamilyProofContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmPreFamilyXLocalRunTest.push_findOld `proof .default
    (AddInductive.consumeTypeAnnotations cvmCtorProofDomain)
    cvmPreFamilyPFindXTest

theorem cvmPreFamilyAlphaFindAfterDirectTest :
    cvmPreFamilyAfterDirectContextTest.lctx.find?
        cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) := by
  simpa [cvmPreFamilyAfterDirectContextTest,
    AddInductive.Context.advanceFresh] using cvmPreFamilyAlphaFindProofTest

theorem cvmPreFamilyPFindAfterDirectTest :
    cvmPreFamilyAfterDirectContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) := by
  simpa [cvmPreFamilyAfterDirectContextTest,
    AddInductive.Context.advanceFresh] using cvmPreFamilyPFindProofTest

theorem cvmPreFamilyAlphaFindAfterFunctionTest :
    cvmPreFamilyAfterFunctionContextTest.lctx.find?
        cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) := by
  simpa [cvmPreFamilyAfterFunctionContextTest,
    AddInductive.Context.advanceFresh] using
    cvmPreFamilyAlphaFindAfterDirectTest

theorem cvmPreFamilyPFindAfterFunctionTest :
    cvmPreFamilyAfterFunctionContextTest.lctx.find?
        cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) := by
  simpa [cvmPreFamilyAfterFunctionContextTest,
    AddInductive.Context.advanceFresh] using cvmPreFamilyPFindAfterDirectTest

theorem cvmPreFamilyAlphaFindLaterTest :
    cvmPreFamilyLaterContextTest.lctx.find? cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmPreFamilyAfterFunctionLocalRunTest.push_findOld `later .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain)
    cvmPreFamilyAlphaFindAfterFunctionTest

theorem cvmPreFamilyPFindLaterTest :
    cvmPreFamilyLaterContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmPreFamilyAfterFunctionLocalRunTest.push_findOld `later .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain)
    cvmPreFamilyPFindAfterFunctionTest

theorem cvmPreFamilyAfterFunctionFreshIdTest :
    cvmPreFamilyAfterFunctionContextTest.freshFVarId =
      cvmValidationLaterIdTest := by
  rfl

theorem cvmPreFamilyLaterFindTest :
    cvmPreFamilyLaterContextTest.lctx.find? cvmValidationLaterIdTest =
      some (.cdecl cvmPreFamilyAfterFunctionContextTest.lctx.decls.size
        cvmValidationLaterIdTest `later (.fvar cvmValidationAlphaIdTest)
        .default .default) := by
  have found := cvmPreFamilyAfterFunctionLocalRunTest.push_findNew
    `later .default (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain)
  rw [← cvmPreFamilyAfterFunctionFreshIdTest]
  simpa [cvmPreFamilyLaterContextTest, cvmValidationLaterIdTest,
    cvmPreFamilyAfterFunctionContextTest, cvmPreFamilyAfterDirectContextTest,
    cvmPreFamilyProofContextTest, cvmPreFamilyXContextTest,
    cvmPreFamilyContextTest, cvmValidationFunctionContextTest,
    cvmValidationDirectContextTest, cvmValidationProofContextTest,
    cvmValidationXContextTest, cvmValidationRootContextTest,
    cvmCtorLaterDomainValidationShapeTest,
    AddInductive.Context.advanceFresh,
    AddInductive.consumeTypeAnnotations] using found

theorem cvmPreFamilyAlphaFindLaterProofTest :
    cvmPreFamilyLaterProofContextTest.lctx.find?
        cvmValidationAlphaIdTest =
      some (.cdecl 0 cvmValidationAlphaIdTest `α
        (.sort (.succ (.param `u))) .default .default) :=
  cvmPreFamilyLaterLocalRunTest.push_findOld `laterProof .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain)
    cvmPreFamilyAlphaFindLaterTest

theorem cvmPreFamilyPFindLaterProofTest :
    cvmPreFamilyLaterProofContextTest.lctx.find? cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmPreFamilyLaterLocalRunTest.push_findOld `laterProof .default
    (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain)
    cvmPreFamilyPFindLaterTest

theorem cvmPreFamilyPFindFunctionInnerTest :
    cvmPreFamilyFunctionInnerContextTest.lctx.find?
        cvmValidationPIdTest =
      some (.cdecl cvmValidationAlphaContextTest.lctx.decls.size
        cvmValidationPIdTest `P cvmValidationPDomainTest
        .default .default) :=
  cvmPreFamilyAfterDirectLocalRunTest.push_findOld `y .default
    (.fvar cvmValidationAlphaIdTest) cvmPreFamilyPFindAfterDirectTest

theorem cvmPreFamilyRootFreshTest :
    cvmPreFamilyContextTest.lctx.find?
      cvmPreFamilyContextTest.freshFVarId = none :=
  cvmPreFamilyRootLocalRunTest.fresh

theorem cvmPreFamilyXFreshTest :
    cvmPreFamilyXContextTest.lctx.find?
      cvmPreFamilyXContextTest.freshFVarId = none :=
  cvmPreFamilyXLocalRunTest.fresh

theorem cvmPreFamilyProofFreshTest :
    cvmPreFamilyProofContextTest.lctx.find?
      cvmPreFamilyProofContextTest.freshFVarId = none :=
  cvmPreFamilyProofLocalRunTest.fresh

theorem cvmPreFamilyAfterDirectFreshTest :
    cvmPreFamilyAfterDirectContextTest.lctx.find?
      cvmPreFamilyAfterDirectContextTest.freshFVarId = none :=
  cvmPreFamilyAfterDirectLocalRunTest.fresh

theorem cvmPreFamilyAfterFunctionFreshTest :
    cvmPreFamilyAfterFunctionContextTest.lctx.find?
      cvmPreFamilyAfterFunctionContextTest.freshFVarId = none :=
  cvmPreFamilyAfterFunctionLocalRunTest.fresh

theorem cvmPreFamilyLaterFreshTest :
    cvmPreFamilyLaterContextTest.lctx.find?
      cvmPreFamilyLaterContextTest.freshFVarId = none :=
  cvmPreFamilyLaterLocalRunTest.fresh

theorem cvmPreFamilyFunctionInnerFreshTest :
    cvmPreFamilyFunctionInnerContextTest.lctx.find?
      cvmPreFamilyFunctionInnerContextTest.freshFVarId = none :=
  cvmPreFamilyFunctionInnerLocalRunTest.fresh

theorem cvmPreFamilyDepthTest (context : AddInductive.Context)
    (contextEq : context = cvmPreFamilyContextTest ∨
      context = cvmPreFamilyXContextTest ∨
      context = cvmPreFamilyProofContextTest ∨
      context = cvmPreFamilyAfterDirectContextTest ∨
      context = cvmPreFamilyAfterFunctionContextTest ∨
      context = cvmPreFamilyLaterContextTest ∨
      context = cvmPreFamilyLaterProofContextTest ∨
      context = cvmPreFamilyFunctionInnerContextTest) :
    context.fuel.recDepth = 10000 := by
  rcases contextEq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem cvmPreFamilyInductiveFuelTest (context : AddInductive.Context)
    (contextEq : context = cvmPreFamilyContextTest ∨
      context = cvmPreFamilyProofContextTest ∨
      context = cvmPreFamilyAfterDirectContextTest) :
    context.fuel.inductiveFuel = 1000 := by
  rcases contextEq with rfl | rfl | rfl <;> rfl

theorem cvmFamilyViewPreFamilyTest_eq :
    cvmCandidate.families.singleton.familyType.type.view =
      constructorValidityMatrixKernelType.type := by
  apply cvmFamilyIdentityEvidence.identity.view_eq_source
  · apply TypeChecker.CandidateLocalContextRun.empty
    rw [cvmFamilyCandidateContext_eq]
    rfl
  · rw [cvmFamilyCandidateContext_eq]
    simp [constructorValidityMatrixKernelType,
      constructorValidityMatrixInfo, ConstantInfo.type,
      ConstantInfo.toConstantVal, FVarsIn, Level.hasMVar',
      Expr.looseBVarRange']
  · rfl

theorem cvmStagedParamsPreFamilyTest_eq :
    cvmStagedUniverseInputTest.staged.family.validation.stats.params =
      #[.fvar cvmValidationAlphaIdTest, .fvar cvmValidationPIdTest] := by
  rw [cvmStagedStatsTest_eq, cvmStatsParamsTest]
  rfl

theorem cvmStagedNindicesPreFamilyTest_eq :
    cvmStagedUniverseInputTest.staged.family.validation.stats.nindices =
      #[0] := by
  rw [cvmStagedStatsTest_eq, cvmStatsNindices_eq]

def cvmPreFamilyIndicesTest : Expr :=
  .sort (.succ (.param `u))

theorem cvmPreFamilyParametersRunTest :
    AddInductive.instantiateFamilyParameters
      constructorValidityMatrixKernelType.type
      cvmStagedUniverseInputTest.staged.family.validation.stats.params.toList =
        .ok cvmPreFamilyIndicesTest := by
  rw [cvmStagedParamsPreFamilyTest_eq]
  simp [constructorValidityMatrixKernelType,
    constructorValidityMatrixInfo, ConstantInfo.type,
    ConstantInfo.toConstantVal,
    AddInductive.instantiateFamilyParameters,
    cvmPreFamilyIndicesTest, cvmValidationAlphaIdTest,
    cvmValidationPIdTest, cvmValidationAlphaContextTest,
    cvmFamilyContext, Expr.instantiate1_eq, Expr.instantiate1',
    Pure.pure, Except.pure]

@[simp] theorem cvmPreFamilyFamilyAppGetAppFnTest
    (alpha predicate : Expr) :
    (cvmValidationFamilyApplicationTest alpha predicate).getAppFn =
      .const constructorValidityMatrixKernelType.name [.param `u] := by
  rfl

@[simp] theorem cvmPreFamilyFamilyAppGetAppArgsTest
    (alpha predicate : Expr) :
    (cvmValidationFamilyApplicationTest alpha predicate).getAppArgs =
      #[alpha, predicate] := by
  rfl

theorem cvmPreFamilyFamilyAppValidTest :
    AddInductive.isValidIndAppIdx
      cvmStagedUniverseInputTest.staged.family.validation.stats
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest)) 0 =
      true := by
  simp +decide [AddInductive.isValidIndAppIdx,
    cvmStagedParamsPreFamilyTest_eq,
    cvmStagedNindicesPreFamilyTest_eq,
    cvmStagedIndConstsTest_eq,
    cvmPreFamilyFamilyAppGetAppFnTest,
    cvmPreFamilyFamilyAppGetAppArgsTest,
    prbExprBneSelfReplay]

def cvmPreFamilyIndicesCheckedTest
    (context : AddInductive.Context)
    (lparams : context.lparams = [`u])
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.ConstructorCheckedExpr context cvmPreFamilyIndicesTest :=
  .ofRun (by simp [cvmPreFamilyIndicesTest, FVarsIn, Level.hasMVar'])
    (by
      simp [cvmPreFamilyIndicesTest, Expr.hasMVar_eq_cache,
        Level.hasMVar_eq, Level.hasMVar'])
    (by
      unfold cvmPreFamilyIndicesTest
      exact prbPreFamilySortCheckValidReplay context lparams depth)

def cvmPreFamilyNilSpineTest
    (context : AddInductive.Context)
    (lparams : context.lparams = [`u])
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.ConstructorPreFamilyIndexSpineTrace context
      cvmPreFamilyIndicesTest [] :=
  .nil context cvmPreFamilyIndicesTest
    (cvmPreFamilyIndicesCheckedTest context lparams depth) rfl

def cvmPreFamilyFVarCheckedTest
    (context : AddInductive.Context) (id : FVarId) (type : Expr)
    (find : context.lctx.find? id =
      some (.cdecl index id name type bi kind))
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.ConstructorCheckedExpr context (.fvar id) :=
  .ofRun (by
      change (context.lctx.find? id).isSome = true
      rw [find]
      rfl)
    (by simp [Expr.hasMVar_eq_cache])
    (prbCandidateCheckTypeFVar context id type depth find)

def cvmPreFamilyFVarEnsureTest
    (context : AddInductive.Context) (id : FVarId) (level : Level)
    (find : context.lctx.find? id =
      some (.cdecl index id name (.sort level) bi kind))
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.ConstructorEnsureTypeObservation context (.fvar id) :=
  ⟨.sort level,
    prbPreFamilyFVarEnsureValidReplay context id level find depth⟩

def cvmPreFamilyPredicateCheckedTest
    (context : AddInductive.Context) (argumentId : FVarId)
    (idsNe : cvmValidationPIdTest ≠ argumentId)
    (predicateFind : context.lctx.find? cvmValidationPIdTest =
      some (.cdecl predicateIndex cvmValidationPIdTest predicateName
        cvmValidationPDomainTest predicateBi predicateKind))
    (argumentFind : context.lctx.find? argumentId =
      some (.cdecl argumentIndex argumentId argumentName
        (.fvar cvmValidationAlphaIdTest) argumentBi argumentKind))
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.ConstructorCheckedExpr context
      (cvmValidationPredicateApplicationTest cvmValidationPIdTest
        (.fvar argumentId)) :=
  .ofRun (by
      simp [cvmValidationPredicateApplicationTest, FVarsIn]
      constructor
      · change (context.lctx.find? cvmValidationPIdTest).isSome = true
        rw [predicateFind]
        rfl
      · change (context.lctx.find? argumentId).isSome = true
        rw [argumentFind]
        rfl)
    (by
      simp [cvmValidationPredicateApplicationTest, Expr.hasMVar_eq_cache])
    (cvmValidationPredicateApplicationCheckTest context
      cvmValidationPIdTest argumentId idsNe predicateFind argumentFind depth)

def cvmPreFamilyPredicateEnsureTest
    (context : AddInductive.Context) (argumentId : FVarId)
    (predicateFind : context.lctx.find? cvmValidationPIdTest =
      some (.cdecl predicateIndex cvmValidationPIdTest predicateName
        cvmValidationPDomainTest predicateBi predicateKind))
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.ConstructorEnsureTypeObservation context
      (cvmValidationPredicateApplicationTest cvmValidationPIdTest
        (.fvar argumentId)) :=
  ⟨.sort .zero,
    cvmEnsureTypeOfInferOnlyTest context
      (cvmValidationPredicateApplicationTest cvmValidationPIdTest
        (.fvar argumentId)) .zero
      (cvmValidationPredicateApplicationStateTest cvmValidationPIdTest
        (.fvar argumentId))
      (cvmInferTypePredicateApplicationOnlyTest context
        cvmValidationPIdTest (.fvar argumentId) predicateFind depth
        (by
          apply Expr.hasLooseBVars_eq_false_of_bounded <;>
            simp [cvmValidationPredicateApplicationTest,
              Expr.looseBVarRange']))⟩

def cvmPreFamilyReflAnnotationsTest
    (context : AddInductive.Context) (source : Expr) :
    AddInductive.CandidateIsDefEqObservation context source source :=
  ⟨AddInductive.candidateIsDefEqRefl context source⟩

def cvmPreFamilyXCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmPreFamilyContextTest
      cvmCtorXDomain := by
  rw [cvmCtorXDomainValidationShapeTest]
  exact cvmPreFamilyFVarCheckedTest _ _ _ cvmPreFamilyAlphaFindRootTest
    (cvmPreFamilyDepthTest _ (Or.inl rfl))

def cvmPreFamilyXEnsureTest :
    AddInductive.ConstructorEnsureTypeObservation cvmPreFamilyContextTest
      cvmCtorXDomain := by
  rw [cvmCtorXDomainValidationShapeTest]
  exact cvmPreFamilyFVarEnsureTest _ _ _ cvmPreFamilyAlphaFindRootTest
    (cvmPreFamilyDepthTest _ (Or.inl rfl))

def cvmPreFamilyXConsumedTest :
    AddInductive.ConstructorCheckedExpr cvmPreFamilyContextTest
      (AddInductive.consumeTypeAnnotations cvmCtorXDomain) := by
  rw [cvmValidationConsumeXTest]
  exact cvmPreFamilyXCheckedTest

def cvmPreFamilyXAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation cvmPreFamilyContextTest
      cvmCtorXDomain (AddInductive.consumeTypeAnnotations cvmCtorXDomain) := by
  rw [cvmValidationConsumeXTest]
  exact cvmPreFamilyReflAnnotationsTest _ _

def cvmPreFamilyProofCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmPreFamilyXContextTest
      cvmCtorProofDomain := by
  rw [cvmCtorProofDomainValidationShapeTest]
  exact cvmPreFamilyPredicateCheckedTest _ cvmValidationXIdTest
    cvmValidationPNeXTest cvmPreFamilyPFindXTest cvmPreFamilyXFindTest
    (cvmPreFamilyDepthTest _ (Or.inr (Or.inl rfl)))

def cvmPreFamilyProofEnsureTest :
    AddInductive.ConstructorEnsureTypeObservation cvmPreFamilyXContextTest
      cvmCtorProofDomain := by
  rw [cvmCtorProofDomainValidationShapeTest]
  exact cvmPreFamilyPredicateEnsureTest _ cvmValidationXIdTest
    cvmPreFamilyPFindXTest
    (cvmPreFamilyDepthTest _ (Or.inr (Or.inl rfl)))

def cvmPreFamilyProofConsumedTest :
    AddInductive.ConstructorCheckedExpr cvmPreFamilyXContextTest
      (AddInductive.consumeTypeAnnotations cvmCtorProofDomain) := by
  rw [cvmValidationConsumeProofTest]
  exact cvmPreFamilyProofCheckedTest

def cvmPreFamilyProofAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation cvmPreFamilyXContextTest
      cvmCtorProofDomain
      (AddInductive.consumeTypeAnnotations cvmCtorProofDomain) := by
  rw [cvmValidationConsumeProofTest]
  exact cvmPreFamilyReflAnnotationsTest _ _

def cvmPreFamilyFunctionAlphaCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmPreFamilyAfterDirectContextTest
      (.fvar cvmValidationAlphaIdTest) :=
  cvmPreFamilyFVarCheckedTest _ _ _ cvmPreFamilyAlphaFindAfterDirectTest
    (cvmPreFamilyDepthTest _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

def cvmPreFamilyFunctionAlphaEnsureTest :
    AddInductive.ConstructorEnsureTypeObservation
      cvmPreFamilyAfterDirectContextTest
      (.fvar cvmValidationAlphaIdTest) :=
  cvmPreFamilyFVarEnsureTest _ _ _ cvmPreFamilyAlphaFindAfterDirectTest
    (cvmPreFamilyDepthTest _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

def cvmPreFamilyFunctionAlphaConsumedTest :
    AddInductive.ConstructorCheckedExpr cvmPreFamilyAfterDirectContextTest
      (AddInductive.consumeTypeAnnotations
        (.fvar cvmValidationAlphaIdTest)) := by
  simp [AddInductive.consumeTypeAnnotations]
  exact cvmPreFamilyFunctionAlphaCheckedTest

def cvmPreFamilyFunctionAlphaAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation
      cvmPreFamilyAfterDirectContextTest (.fvar cvmValidationAlphaIdTest)
      (AddInductive.consumeTypeAnnotations
        (.fvar cvmValidationAlphaIdTest)) := by
  simp [AddInductive.consumeTypeAnnotations]
  exact cvmPreFamilyReflAnnotationsTest _ _

def cvmPreFamilyLaterCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmPreFamilyAfterFunctionContextTest
      cvmCtorLaterDomain := by
  rw [cvmCtorLaterDomainValidationShapeTest]
  exact cvmPreFamilyFVarCheckedTest _ _ _
    cvmPreFamilyAlphaFindAfterFunctionTest
    (cvmPreFamilyDepthTest _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

def cvmPreFamilyLaterEnsureTest :
    AddInductive.ConstructorEnsureTypeObservation
      cvmPreFamilyAfterFunctionContextTest cvmCtorLaterDomain := by
  rw [cvmCtorLaterDomainValidationShapeTest]
  exact cvmPreFamilyFVarEnsureTest _ _ _
    cvmPreFamilyAlphaFindAfterFunctionTest
    (cvmPreFamilyDepthTest _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))

def cvmPreFamilyLaterConsumedTest :
    AddInductive.ConstructorCheckedExpr cvmPreFamilyAfterFunctionContextTest
      (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain) := by
  rw [cvmValidationConsumeLaterTest]
  exact cvmPreFamilyLaterCheckedTest

def cvmPreFamilyLaterAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation
      cvmPreFamilyAfterFunctionContextTest cvmCtorLaterDomain
      (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain) := by
  rw [cvmValidationConsumeLaterTest]
  exact cvmPreFamilyReflAnnotationsTest _ _

def cvmPreFamilyLaterProofCheckedTest :
    AddInductive.ConstructorCheckedExpr cvmPreFamilyLaterContextTest
      cvmCtorLaterProofDomain := by
  rw [cvmCtorLaterProofDomainValidationShapeTest]
  exact cvmPreFamilyPredicateCheckedTest _ cvmValidationLaterIdTest
    cvmValidationPNeLaterTest cvmPreFamilyPFindLaterTest
    cvmPreFamilyLaterFindTest
    (cvmPreFamilyDepthTest _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))

def cvmPreFamilyLaterProofEnsureTest :
    AddInductive.ConstructorEnsureTypeObservation cvmPreFamilyLaterContextTest
      cvmCtorLaterProofDomain := by
  rw [cvmCtorLaterProofDomainValidationShapeTest]
  exact cvmPreFamilyPredicateEnsureTest _ cvmValidationLaterIdTest
    cvmPreFamilyPFindLaterTest
    (cvmPreFamilyDepthTest _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))

def cvmPreFamilyLaterProofConsumedTest :
    AddInductive.ConstructorCheckedExpr cvmPreFamilyLaterContextTest
      (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain) := by
  rw [cvmValidationConsumeLaterProofTest]
  exact cvmPreFamilyLaterProofCheckedTest

def cvmPreFamilyLaterProofAnnotationsTest :
    AddInductive.CandidateIsDefEqObservation cvmPreFamilyLaterContextTest
      cvmCtorLaterProofDomain
      (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain) := by
  rw [cvmValidationConsumeLaterProofTest]
  exact cvmPreFamilyReflAnnotationsTest _ _

theorem cvmPreFamilyFamilyArgsTest :
    (cvmValidationFamilyApplicationTest
      (.fvar cvmValidationAlphaIdTest)
      (.fvar cvmValidationPIdTest)).getAppArgs.toList.drop
        cvmStagedUniverseInputTest.staged.family.validation.stats.params.size =
      [] := by
  rw [cvmStagedParamsPreFamilyTest_eq]
  simp [cvmPreFamilyFamilyAppGetAppArgsTest]

def cvmPreFamilyFamilySpineTest
    (context : AddInductive.Context)
    (lparams : context.lparams = [`u])
    (depth : context.fuel.recDepth = 10000) :
    AddInductive.ConstructorPreFamilyIndexSpineTrace context
      cvmPreFamilyIndicesTest
      ((cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest)
        (.fvar cvmValidationPIdTest)).getAppArgs.toList.drop
          cvmStagedUniverseInputTest.staged.family.validation.stats.params.size) := by
  rw [cvmPreFamilyFamilyArgsTest]
  exact cvmPreFamilyNilSpineTest context lparams depth

def cvmPreFamilyTargetTraceTest
    (context : AddInductive.Context)
    (lparams : context.lparams = [`u])
    (depth : context.fuel.recDepth = 10000)
    (fuel : Nat) :
    AddInductive.ConstructorPreFamilyRecursiveTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest context
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
      (fuel + 1) :=
  .target context _ cvmPreFamilyFamilyAppValidTest
    (cvmPreFamilyFamilySpineTest context lparams depth)

theorem cvmPreFamilyTargetRunTest
    (context : AddInductive.Context)
    (lparams : context.lparams = [`u])
    (depth : context.fuel.recDepth = 10000)
    (fuel : Nat) :
    AddInductive.ConstructorPreFamilyRecursiveTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest context
      (cvmValidationFamilyApplicationTest
        (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
      (fuel + 1) =
        .ok (cvmPreFamilyTargetTraceTest context lparams depth fuel) :=
  AddInductive.ConstructorPreFamilyRecursiveTrace.target_build_eq
    rfl cvmPreFamilyFamilyAppValidTest
      (cvmPreFamilyFamilySpineTest context lparams depth)

theorem cvmPreFamilyRecursiveTraceBuildEqTest
    (trace : AddInductive.ConstructorPreFamilyRecursiveTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest context source fuel) :
    AddInductive.ConstructorPreFamilyRecursiveTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest context source fuel = .ok trace := by
  induction trace with
  | forallE context name domain body binderInfo domainCheck ensureType
      consumedCheck annotations fresh tail ih =>
    exact AddInductive.ConstructorPreFamilyRecursiveTrace.forallE_build_eq
      domainCheck ensureType consumedCheck annotations fresh tail ih
  | target context source valid spine =>
    cases source <;> try
      { exact AddInductive.ConstructorPreFamilyRecursiveTrace.target_build_eq
          rfl valid spine }
    rename_i binderName binderType body binderInfo
    unfold AddInductive.isValidIndAppIdx at valid
    rw [cvmStagedIndConstsTest_eq] at valid
    have mismatch :
        (((.forallE binderName binderType body binderInfo : Expr).getAppFn ==
          .const constructorValidityMatrixKernelType.name [.param `u])) =
          false := by
      change Expr.eqv (.forallE binderName binderType body binderInfo)
        (.const constructorValidityMatrixKernelType.name [.param `u]) = false
      rw [Expr.eqv_eq]
      rfl
    simp [mismatch] at valid

def cvmPreFamilyDirectFieldTraceTest :
    AddInductive.ConstructorPreFamilyRecursiveTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyProofContextTest
      cvmCtorDirectDomain 1000 := by
  rw [cvmCtorDirectDomainValidationShapeTest]
  exact cvmPreFamilyTargetTraceTest cvmPreFamilyProofContextTest rfl
    (cvmPreFamilyDepthTest _
      (Or.inr (Or.inr (Or.inl rfl)))) 999

theorem cvmPreFamilyDirectFieldRunTest :
    AddInductive.ConstructorPreFamilyRecursiveTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyProofContextTest
      cvmCtorDirectDomain 1000 =
        .ok cvmPreFamilyDirectFieldTraceTest := by
  exact cvmPreFamilyRecursiveTraceBuildEqTest
    cvmPreFamilyDirectFieldTraceTest

def cvmPreFamilyDirectFieldTraceAtFuelTest :
    AddInductive.ConstructorPreFamilyRecursiveTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyProofContextTest
      cvmCtorDirectDomain
      cvmPreFamilyProofContextTest.fuel.inductiveFuel := by
  rw [cvmPreFamilyInductiveFuelTest _ (Or.inr (Or.inl rfl))]
  exact cvmPreFamilyDirectFieldTraceTest

theorem cvmPreFamilyDirectFieldRunAtFuelTest :
    AddInductive.ConstructorPreFamilyRecursiveTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyProofContextTest
      cvmCtorDirectDomain
      cvmPreFamilyProofContextTest.fuel.inductiveFuel =
        .ok cvmPreFamilyDirectFieldTraceAtFuelTest := by
  exact cvmPreFamilyRecursiveTraceBuildEqTest
    cvmPreFamilyDirectFieldTraceAtFuelTest

def cvmPreFamilyFunctionFieldTraceTest :
    AddInductive.ConstructorPreFamilyRecursiveTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyAfterDirectContextTest
      cvmCtorFunctionDomain 1000 := by
  rw [cvmCtorFunctionDomainValidationShapeTest]
  exact .forallE cvmPreFamilyAfterDirectContextTest `y
    (.fvar cvmValidationAlphaIdTest)
    (cvmValidationFamilyApplicationTest
      (.fvar cvmValidationAlphaIdTest) (.fvar cvmValidationPIdTest))
    .default cvmPreFamilyFunctionAlphaCheckedTest
    cvmPreFamilyFunctionAlphaEnsureTest
    cvmPreFamilyFunctionAlphaConsumedTest
    cvmPreFamilyFunctionAlphaAnnotationsTest
    cvmPreFamilyAfterDirectFreshTest
    (by
      simpa [cvmPreFamilyFunctionInnerContextTest,
        AddInductive.consumeTypeAnnotations,
        cvmValidationFamilyApplicationTest,
        Expr.instantiate1_eq, Expr.instantiate1'] using
        (cvmPreFamilyTargetTraceTest cvmPreFamilyFunctionInnerContextTest rfl
          (cvmPreFamilyDepthTest _
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr rfl)))))))) 998))

theorem cvmPreFamilyFunctionFieldRunTest :
    AddInductive.ConstructorPreFamilyRecursiveTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyAfterDirectContextTest
      cvmCtorFunctionDomain 1000 =
        .ok cvmPreFamilyFunctionFieldTraceTest := by
  exact cvmPreFamilyRecursiveTraceBuildEqTest
    cvmPreFamilyFunctionFieldTraceTest

def cvmPreFamilyFunctionFieldTraceAtFuelTest :
    AddInductive.ConstructorPreFamilyRecursiveTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyAfterDirectContextTest
      cvmCtorFunctionDomain
      cvmPreFamilyAfterDirectContextTest.fuel.inductiveFuel := by
  rw [cvmPreFamilyInductiveFuelTest _
    (Or.inr (Or.inr rfl))]
  exact cvmPreFamilyFunctionFieldTraceTest

theorem cvmPreFamilyFunctionFieldRunAtFuelTest :
    AddInductive.ConstructorPreFamilyRecursiveTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyAfterDirectContextTest
      cvmCtorFunctionDomain
      cvmPreFamilyAfterDirectContextTest.fuel.inductiveFuel =
        .ok cvmPreFamilyFunctionFieldTraceAtFuelTest := by
  exact cvmPreFamilyRecursiveTraceBuildEqTest
    cvmPreFamilyFunctionFieldTraceAtFuelTest

theorem cvmPreFamilyParameterBuildEqTest
    (parameterAt : stats.params[argIdx]? = some parameter)
    (tail : AddInductive.ConstructorPreFamilyViewTrace stats familyIdx
      familyIndices context (body.instantiate1 parameter) (argIdx + 1)
      removed recursiveStarted)
    (tailRun : AddInductive.ConstructorPreFamilyViewTrace.build stats
      familyIdx familyIndices context (body.instantiate1 parameter)
      (argIdx + 1) removed recursiveStarted fuel = .ok tail) :
    AddInductive.ConstructorPreFamilyViewTrace.build stats familyIdx
      familyIndices context (.forallE name domain body binderInfo) argIdx
      removed recursiveStarted (fuel + 1) =
        .ok (.parameter context argIdx removed recursiveStarted name domain
          body binderInfo parameter parameterAt tail) := by
  simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
  split
  · rename_i observed observedAt
    rw [parameterAt] at observedAt
    cases observedAt
    rw [tailRun]
    rfl
  · rename_i noParameter
    rw [parameterAt] at noParameter
    contradiction

theorem cvmPreFamilyOrdinaryBuildEqTest
    (noParameter : stats.params[argIdx]? = none)
    (nonrecursive : AddInductive.hasIndOcc stats.indConsts domain = false)
    (independent : AddInductive.constructorIndependentOf domain removed = true)
    (domainCheck : AddInductive.ConstructorCheckedExpr context domain)
    (ensureType : AddInductive.ConstructorEnsureTypeObservation context domain)
    (consumedCheck : AddInductive.ConstructorCheckedExpr context
      (AddInductive.consumeTypeAnnotations domain))
    (annotations : AddInductive.CandidateIsDefEqObservation context domain
      (AddInductive.consumeTypeAnnotations domain))
    (fresh : context.lctx.find? context.freshFVarId = none)
    (tail : AddInductive.ConstructorPreFamilyViewTrace stats familyIdx
      familyIndices
      (context.pushLocalDecl name binderInfo
        (AddInductive.consumeTypeAnnotations domain))
      (body.instantiate1 context.freshExpr) (argIdx + 1) removed
      recursiveStarted)
    (tailRun : AddInductive.ConstructorPreFamilyViewTrace.build stats
      familyIdx familyIndices
      (context.pushLocalDecl name binderInfo
        (AddInductive.consumeTypeAnnotations domain))
      (body.instantiate1 context.freshExpr) (argIdx + 1) removed
      recursiveStarted fuel = .ok tail) :
    AddInductive.ConstructorPreFamilyViewTrace.build stats familyIdx
      familyIndices context (.forallE name domain body binderInfo) argIdx
      removed recursiveStarted (fuel + 1) =
        .ok (.ordinary context argIdx removed recursiveStarted name domain
          body binderInfo noParameter nonrecursive independent domainCheck
          ensureType consumedCheck annotations fresh tail) := by
  simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
  split
  · rename_i parameter parameterAt
    rw [noParameter] at parameterAt
    contradiction
  · split
    · rw [dif_pos independent]
      rw [domainCheck.check_eq, ensureType.observe_eq,
        consumedCheck.check_eq]
      simp only [Bind.bind, Except.bind]
      rw [annotations.observe_eq]
      simp only []
      rw [dif_pos fresh, tailRun]
      rfl
    · rename_i recursive
      rw [nonrecursive] at recursive
      contradiction

theorem cvmPreFamilyRecursiveBuildEqTest
    (noParameter : stats.params[argIdx]? = none)
    (isRecursive : AddInductive.hasIndOcc stats.indConsts domain = true)
    (independent : AddInductive.constructorIndependentOf domain removed = true)
    (field : AddInductive.ConstructorPreFamilyRecursiveTrace stats familyIdx
      familyIndices context domain context.fuel.inductiveFuel)
    (fieldRun : AddInductive.ConstructorPreFamilyRecursiveTrace.build stats
      familyIdx familyIndices context domain context.fuel.inductiveFuel =
        .ok field)
    (fresh : context.lctx.find? context.freshFVarId = none)
    (tail : AddInductive.ConstructorPreFamilyViewTrace stats familyIdx
      familyIndices context.advanceFresh
      (body.instantiate1 context.freshExpr) (argIdx + 1)
      (context.freshFVarId :: removed) true)
    (tailRun : AddInductive.ConstructorPreFamilyViewTrace.build stats
      familyIdx familyIndices context.advanceFresh
      (body.instantiate1 context.freshExpr) (argIdx + 1)
      (context.freshFVarId :: removed) true fuel = .ok tail) :
    AddInductive.ConstructorPreFamilyViewTrace.build stats familyIdx
      familyIndices context (.forallE name domain body binderInfo) argIdx
      removed recursiveStarted (fuel + 1) =
        .ok (.recursive context argIdx removed recursiveStarted name domain
          body binderInfo noParameter isRecursive independent field fresh
          tail) := by
  simp only [AddInductive.ConstructorPreFamilyViewTrace.build]
  split
  · rename_i parameter parameterAt
    rw [noParameter] at parameterAt
    contradiction
  · split
    · rename_i nonrecursive
      rw [isRecursive] at nonrecursive
      contradiction
    · rw [dif_pos independent, fieldRun]
      simp only [Bind.bind, Except.bind]
      rw [dif_pos fresh, tailRun]
      rfl

theorem cvmPreFamilyParameterAtZeroTest :
    cvmStagedUniverseInputTest.staged.family.validation.stats.params[0]? =
      some (.fvar cvmValidationAlphaIdTest) := by
  rw [cvmStagedParamsPreFamilyTest_eq]
  rfl

theorem cvmPreFamilyParameterAtOneTest :
    cvmStagedUniverseInputTest.staged.family.validation.stats.params[1]? =
      some (.fvar cvmValidationPIdTest) := by
  rw [cvmStagedParamsPreFamilyTest_eq]
  rfl

theorem cvmPreFamilyNoParameterTwoTest :
    cvmStagedUniverseInputTest.staged.family.validation.stats.params[2]? =
      none := by
  rw [cvmStagedParamsPreFamilyTest_eq]
  rfl

theorem cvmPreFamilyNoParameterThreeTest :
    cvmStagedUniverseInputTest.staged.family.validation.stats.params[3]? =
      none := by
  rw [cvmStagedParamsPreFamilyTest_eq]
  rfl

theorem cvmPreFamilyNoParameterFourTest :
    cvmStagedUniverseInputTest.staged.family.validation.stats.params[4]? =
      none := by
  rw [cvmStagedParamsPreFamilyTest_eq]
  rfl

theorem cvmPreFamilyNoParameterFiveTest :
    cvmStagedUniverseInputTest.staged.family.validation.stats.params[5]? =
      none := by
  rw [cvmStagedParamsPreFamilyTest_eq]
  rfl

theorem cvmPreFamilyNoParameterSixTest :
    cvmStagedUniverseInputTest.staged.family.validation.stats.params[6]? =
      none := by
  rw [cvmStagedParamsPreFamilyTest_eq]
  rfl

theorem cvmPreFamilyNoParameterSevenTest :
    cvmStagedUniverseInputTest.staged.family.validation.stats.params[7]? =
      none := by
  rw [cvmStagedParamsPreFamilyTest_eq]
  rfl

theorem cvmPreFamilyLaterHasNoIndOccTest :
    AddInductive.hasIndOcc
      cvmStagedUniverseInputTest.staged.family.validation.stats.indConsts
      cvmCtorLaterDomain = false := by
  rw [cvmCtorLaterDomainValidationShapeTest]
  exact cvmValidationAlphaHasNoIndOccTest

theorem cvmPreFamilyNeFreshOfFindTest
    {context : AddInductive.Context} {id : FVarId} {decl : LocalDecl}
    (fresh : context.lctx.find? context.freshFVarId = none)
    (find : context.lctx.find? id = some decl) :
    id ≠ context.freshFVarId := by
  intro equality
  rw [← equality, find] at fresh
  contradiction

theorem cvmPreFamilyAlphaNeDirectRemovedTest :
    cvmValidationAlphaIdTest ≠
      cvmPreFamilyProofContextTest.freshFVarId :=
  cvmPreFamilyNeFreshOfFindTest cvmPreFamilyProofFreshTest
    cvmPreFamilyAlphaFindProofTest

theorem cvmPreFamilyPNeDirectRemovedTest :
    cvmValidationPIdTest ≠
      cvmPreFamilyProofContextTest.freshFVarId :=
  cvmPreFamilyNeFreshOfFindTest cvmPreFamilyProofFreshTest
    cvmPreFamilyPFindProofTest

theorem cvmPreFamilyAlphaNeFunctionRemovedTest :
    cvmValidationAlphaIdTest ≠
      cvmPreFamilyAfterDirectContextTest.freshFVarId :=
  cvmPreFamilyNeFreshOfFindTest cvmPreFamilyAfterDirectFreshTest
    cvmPreFamilyAlphaFindAfterDirectTest

theorem cvmPreFamilyPNeFunctionRemovedTest :
    cvmValidationPIdTest ≠
      cvmPreFamilyAfterDirectContextTest.freshFVarId :=
  cvmPreFamilyNeFreshOfFindTest cvmPreFamilyAfterDirectFreshTest
    cvmPreFamilyPFindAfterDirectTest

theorem cvmPreFamilyNeFreshOfReservesTest
    {context : AddInductive.Context} {id : FVarId}
    (reserved : context.ngen.Reserves id) :
    id ≠ context.freshFVarId := by
  intro equality
  apply NameGenerator.not_reserves_self (ngen := context.ngen)
  change context.ngen.Reserves context.freshFVarId
  rw [← equality]
  exact reserved

theorem cvmPreFamilyDirectReservedAfterFunctionTest :
    cvmPreFamilyAfterFunctionContextTest.ngen.Reserves
      cvmPreFamilyProofContextTest.freshFVarId := by
  have first : cvmPreFamilyAfterDirectContextTest.ngen.Reserves
      cvmPreFamilyProofContextTest.freshFVarId := by
    simpa [cvmPreFamilyAfterDirectContextTest,
      AddInductive.Context.advanceFresh,
      AddInductive.Context.freshFVarId] using
      (NameGenerator.next_reserves_self
        (ngen := cvmPreFamilyProofContextTest.ngen))
  have second := NameGenerator.Reserves.mono NameGenerator.LE.next first
  simpa [cvmPreFamilyAfterFunctionContextTest,
    AddInductive.Context.advanceFresh] using second

theorem cvmPreFamilyFunctionReservedAfterFunctionTest :
    cvmPreFamilyAfterFunctionContextTest.ngen.Reserves
      cvmPreFamilyAfterDirectContextTest.freshFVarId := by
  simpa [cvmPreFamilyAfterFunctionContextTest,
    AddInductive.Context.advanceFresh,
    AddInductive.Context.freshFVarId] using
    (NameGenerator.next_reserves_self
      (ngen := cvmPreFamilyAfterDirectContextTest.ngen))

theorem cvmPreFamilyLaterNeDirectRemovedTest :
    cvmValidationLaterIdTest ≠
      cvmPreFamilyProofContextTest.freshFVarId := by
  apply Ne.symm
  rw [← cvmPreFamilyAfterFunctionFreshIdTest]
  exact cvmPreFamilyNeFreshOfReservesTest
    cvmPreFamilyDirectReservedAfterFunctionTest

theorem cvmPreFamilyLaterNeFunctionRemovedTest :
    cvmValidationLaterIdTest ≠
      cvmPreFamilyAfterDirectContextTest.freshFVarId := by
  apply Ne.symm
  rw [← cvmPreFamilyAfterFunctionFreshIdTest]
  exact cvmPreFamilyNeFreshOfReservesTest
    cvmPreFamilyFunctionReservedAfterFunctionTest

theorem cvmPreFamilyFunctionIndependentTest :
    AddInductive.constructorIndependentOf cvmCtorFunctionDomain
      [cvmPreFamilyProofContextTest.freshFVarId] = true := by
  rw [cvmCtorFunctionDomainValidationShapeTest]
  simp [AddInductive.constructorIndependentOf,
    cvmValidationFamilyApplicationTest, Expr.fvarsList,
    cvmPreFamilyAlphaNeDirectRemovedTest,
    cvmPreFamilyPNeDirectRemovedTest]

theorem cvmPreFamilyLaterIndependentTest :
    AddInductive.constructorIndependentOf cvmCtorLaterDomain
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] = true := by
  rw [cvmCtorLaterDomainValidationShapeTest]
  simp [AddInductive.constructorIndependentOf, Expr.fvarsList,
    cvmPreFamilyAlphaNeFunctionRemovedTest,
    cvmPreFamilyAlphaNeDirectRemovedTest]

theorem cvmPreFamilyLaterProofIndependentTest :
    AddInductive.constructorIndependentOf cvmCtorLaterProofDomain
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] = true := by
  rw [cvmCtorLaterProofDomainValidationShapeTest]
  simp [AddInductive.constructorIndependentOf,
    cvmValidationPredicateApplicationTest, Expr.fvarsList,
    cvmPreFamilyPNeFunctionRemovedTest,
    cvmPreFamilyPNeDirectRemovedTest,
    cvmPreFamilyLaterNeFunctionRemovedTest,
    cvmPreFamilyLaterNeDirectRemovedTest]

theorem cvmPreFamilyTerminalIndependentTest :
    AddInductive.constructorIndependentOf cvmCtorTerminal
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] = true := by
  rw [cvmCtorTerminalValidationShapeTest]
  simp [AddInductive.constructorIndependentOf,
    cvmValidationFamilyApplicationTest, Expr.fvarsList,
    cvmPreFamilyAlphaNeFunctionRemovedTest,
    cvmPreFamilyAlphaNeDirectRemovedTest,
    cvmPreFamilyPNeFunctionRemovedTest,
    cvmPreFamilyPNeDirectRemovedTest]

theorem cvmPreFamilyTerminalValidTest :
    AddInductive.isValidIndAppIdx
      cvmStagedUniverseInputTest.staged.family.validation.stats
      cvmCtorTerminal 0 = true := by
  rw [cvmCtorTerminalValidationShapeTest]
  exact cvmPreFamilyFamilyAppValidTest

def cvmPreFamilyTerminalSpineTest :
    AddInductive.ConstructorPreFamilyIndexSpineTrace
      cvmPreFamilyLaterProofContextTest cvmPreFamilyIndicesTest
      (cvmCtorTerminal.getAppArgs.toList.drop
        cvmStagedUniverseInputTest.staged.family.validation.stats.params.size) := by
  rw [cvmCtorTerminalValidationShapeTest]
  exact cvmPreFamilyFamilySpineTest cvmPreFamilyLaterProofContextTest rfl
    (cvmPreFamilyDepthTest _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl rfl))))))))

def cvmPreFamilyTerminalTraceTest :
    AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyLaterProofContextTest
      cvmCtorTerminal 8
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] true :=
  .terminal cvmPreFamilyLaterProofContextTest cvmCtorTerminal 8
    [cvmPreFamilyAfterDirectContextTest.freshFVarId,
      cvmPreFamilyProofContextTest.freshFVarId] true
    cvmPreFamilyTerminalValidTest cvmPreFamilyTerminalIndependentTest
    cvmPreFamilyTerminalSpineTest

theorem cvmPreFamilyTerminalRunTest :
    AddInductive.ConstructorPreFamilyViewTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyLaterProofContextTest
      cvmCtorTerminal 8
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] true 992 =
        .ok cvmPreFamilyTerminalTraceTest := by
  exact AddInductive.ConstructorPreFamilyViewTrace.terminal_build_eq
    (fuel := 991) (by rw [cvmCtorTerminalValidationShapeTest]; rfl)
    cvmPreFamilyTerminalValidTest cvmPreFamilyTerminalIndependentTest
    cvmPreFamilyTerminalSpineTest

theorem cvmPreFamilyLaterFreshExprValidationTest :
    cvmPreFamilyLaterContextTest.freshExpr =
      cvmValidationLaterContextTest.freshExpr := by
  rfl

theorem cvmPreFamilyLaterProofTailSourceTest :
    cvmCtorAfterLater.bindingBody!.instantiate1
      cvmPreFamilyLaterContextTest.freshExpr = cvmCtorTerminal := by
  rw [cvmPreFamilyLaterFreshExprValidationTest]
  exact cvmSixthFieldSourceTest

theorem cvmPreFamilyLaterProofTraceRunTest :
    ∃ trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyLaterContextTest
      cvmCtorAfterLater 7
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] true,
    AddInductive.ConstructorPreFamilyViewTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyLaterContextTest
      cvmCtorAfterLater 7
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] true 993 = .ok trace := by
  have tailContext : cvmPreFamilyLaterContextTest.pushLocalDecl
      `laterProof .default
        (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain) =
      cvmPreFamilyLaterProofContextTest := by
    rfl
  obtain ⟨tailTrace, tailRun⟩ :
      ∃ tailTrace : AddInductive.ConstructorPreFamilyViewTrace
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest
        (cvmPreFamilyLaterContextTest.pushLocalDecl `laterProof .default
          (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain))
        (cvmCtorAfterLater.bindingBody!.instantiate1
          cvmPreFamilyLaterContextTest.freshExpr) 8
        [cvmPreFamilyAfterDirectContextTest.freshFVarId,
          cvmPreFamilyProofContextTest.freshFVarId] true,
      AddInductive.ConstructorPreFamilyViewTrace.build
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest
        (cvmPreFamilyLaterContextTest.pushLocalDecl `laterProof .default
          (AddInductive.consumeTypeAnnotations cvmCtorLaterProofDomain))
        (cvmCtorAfterLater.bindingBody!.instantiate1
          cvmPreFamilyLaterContextTest.freshExpr) 8
        [cvmPreFamilyAfterDirectContextTest.freshFVarId,
          cvmPreFamilyProofContextTest.freshFVarId] true 992 =
        .ok tailTrace := by
    rw [tailContext, cvmPreFamilyLaterProofTailSourceTest]
    exact ⟨cvmPreFamilyTerminalTraceTest, cvmPreFamilyTerminalRunTest⟩
  rw [cvmCtorAfterLaterForallTest]
  let trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyLaterContextTest
      (.forallE `laterProof cvmCtorLaterProofDomain
        cvmCtorAfterLater.bindingBody! .default) 7
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] true :=
    .ordinary cvmPreFamilyLaterContextTest 7
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] true
      `laterProof cvmCtorLaterProofDomain cvmCtorAfterLater.bindingBody!
      .default cvmPreFamilyNoParameterSevenTest
      cvmValidationLaterProofHasNoIndOccTest
      cvmPreFamilyLaterProofIndependentTest
      cvmPreFamilyLaterProofCheckedTest cvmPreFamilyLaterProofEnsureTest
      cvmPreFamilyLaterProofConsumedTest
      cvmPreFamilyLaterProofAnnotationsTest cvmPreFamilyLaterFreshTest
      tailTrace
  refine ⟨trace, ?_⟩
  exact cvmPreFamilyOrdinaryBuildEqTest
    cvmPreFamilyNoParameterSevenTest
    cvmValidationLaterProofHasNoIndOccTest
    cvmPreFamilyLaterProofIndependentTest
    cvmPreFamilyLaterProofCheckedTest cvmPreFamilyLaterProofEnsureTest
    cvmPreFamilyLaterProofConsumedTest
    cvmPreFamilyLaterProofAnnotationsTest cvmPreFamilyLaterFreshTest
    tailTrace tailRun

theorem cvmPreFamilyAfterFunctionFreshExprValidationTest :
    cvmPreFamilyAfterFunctionContextTest.freshExpr =
      cvmValidationFunctionContextTest.freshExpr := by
  rfl

theorem cvmPreFamilyLaterTailSourceTest :
    cvmCtorAfterFunction.bindingBody!.instantiate1
      cvmPreFamilyAfterFunctionContextTest.freshExpr =
      cvmCtorAfterLater := by
  rw [cvmPreFamilyAfterFunctionFreshExprValidationTest]
  exact cvmFifthFieldSourceTest

theorem cvmPreFamilyLaterTraceRunTest :
    ∃ trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyAfterFunctionContextTest
      cvmCtorAfterFunction 6
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] true,
    AddInductive.ConstructorPreFamilyViewTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyAfterFunctionContextTest
      cvmCtorAfterFunction 6
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] true 994 = .ok trace := by
  obtain ⟨laterProofTrace, laterProofRun⟩ :=
    cvmPreFamilyLaterProofTraceRunTest
  have tailContext : cvmPreFamilyAfterFunctionContextTest.pushLocalDecl
      `later .default
        (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain) =
      cvmPreFamilyLaterContextTest := by
    rfl
  obtain ⟨tailTrace, tailRun⟩ :
      ∃ tailTrace : AddInductive.ConstructorPreFamilyViewTrace
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest
        (cvmPreFamilyAfterFunctionContextTest.pushLocalDecl `later .default
          (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain))
        (cvmCtorAfterFunction.bindingBody!.instantiate1
          cvmPreFamilyAfterFunctionContextTest.freshExpr) 7
        [cvmPreFamilyAfterDirectContextTest.freshFVarId,
          cvmPreFamilyProofContextTest.freshFVarId] true,
      AddInductive.ConstructorPreFamilyViewTrace.build
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest
        (cvmPreFamilyAfterFunctionContextTest.pushLocalDecl `later .default
          (AddInductive.consumeTypeAnnotations cvmCtorLaterDomain))
        (cvmCtorAfterFunction.bindingBody!.instantiate1
          cvmPreFamilyAfterFunctionContextTest.freshExpr) 7
        [cvmPreFamilyAfterDirectContextTest.freshFVarId,
          cvmPreFamilyProofContextTest.freshFVarId] true 993 =
        .ok tailTrace := by
    rw [tailContext, cvmPreFamilyLaterTailSourceTest]
    exact ⟨laterProofTrace, laterProofRun⟩
  rw [cvmCtorAfterFunctionForallTest]
  let trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyAfterFunctionContextTest
      (.forallE `later cvmCtorLaterDomain
        cvmCtorAfterFunction.bindingBody! .default) 6
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] true :=
    .ordinary cvmPreFamilyAfterFunctionContextTest 6
      [cvmPreFamilyAfterDirectContextTest.freshFVarId,
        cvmPreFamilyProofContextTest.freshFVarId] true
      `later cvmCtorLaterDomain cvmCtorAfterFunction.bindingBody!
      .default cvmPreFamilyNoParameterSixTest
      cvmPreFamilyLaterHasNoIndOccTest cvmPreFamilyLaterIndependentTest
      cvmPreFamilyLaterCheckedTest cvmPreFamilyLaterEnsureTest
      cvmPreFamilyLaterConsumedTest cvmPreFamilyLaterAnnotationsTest
      cvmPreFamilyAfterFunctionFreshTest tailTrace
  refine ⟨trace, ?_⟩
  exact cvmPreFamilyOrdinaryBuildEqTest cvmPreFamilyNoParameterSixTest
    cvmPreFamilyLaterHasNoIndOccTest cvmPreFamilyLaterIndependentTest
    cvmPreFamilyLaterCheckedTest cvmPreFamilyLaterEnsureTest
    cvmPreFamilyLaterConsumedTest cvmPreFamilyLaterAnnotationsTest
    cvmPreFamilyAfterFunctionFreshTest tailTrace tailRun

theorem cvmPreFamilyAfterDirectFreshExprValidationTest :
    cvmPreFamilyAfterDirectContextTest.freshExpr =
      cvmValidationDirectContextTest.freshExpr := by
  rfl

theorem cvmPreFamilyFunctionTailSourceTest :
    cvmCtorAfterDirect.bindingBody!.instantiate1
      cvmPreFamilyAfterDirectContextTest.freshExpr =
      cvmCtorAfterFunction := by
  rw [cvmPreFamilyAfterDirectFreshExprValidationTest]
  exact cvmFourthFieldSourceTest

theorem cvmPreFamilyFunctionTraceRunTest :
    ∃ trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyAfterDirectContextTest
      cvmCtorAfterDirect 5
      [cvmPreFamilyProofContextTest.freshFVarId] true,
    AddInductive.ConstructorPreFamilyViewTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyAfterDirectContextTest
      cvmCtorAfterDirect 5
      [cvmPreFamilyProofContextTest.freshFVarId] true 995 = .ok trace := by
  obtain ⟨laterTrace, laterRun⟩ := cvmPreFamilyLaterTraceRunTest
  obtain ⟨tailTrace, tailRun⟩ :
      ∃ tailTrace : AddInductive.ConstructorPreFamilyViewTrace
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest
        cvmPreFamilyAfterDirectContextTest.advanceFresh
        (cvmCtorAfterDirect.bindingBody!.instantiate1
          cvmPreFamilyAfterDirectContextTest.freshExpr) 6
        (cvmPreFamilyAfterDirectContextTest.freshFVarId ::
          [cvmPreFamilyProofContextTest.freshFVarId]) true,
      AddInductive.ConstructorPreFamilyViewTrace.build
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest
        cvmPreFamilyAfterDirectContextTest.advanceFresh
        (cvmCtorAfterDirect.bindingBody!.instantiate1
          cvmPreFamilyAfterDirectContextTest.freshExpr) 6
        (cvmPreFamilyAfterDirectContextTest.freshFVarId ::
          [cvmPreFamilyProofContextTest.freshFVarId]) true 994 =
        .ok tailTrace := by
    rw [show cvmPreFamilyAfterDirectContextTest.advanceFresh =
      cvmPreFamilyAfterFunctionContextTest by rfl]
    rw [cvmPreFamilyFunctionTailSourceTest]
    exact ⟨laterTrace, laterRun⟩
  rw [cvmCtorAfterDirectForallTest]
  let trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyAfterDirectContextTest
      (.forallE `function cvmCtorFunctionDomain
        cvmCtorAfterDirect.bindingBody! .default) 5
      [cvmPreFamilyProofContextTest.freshFVarId] true :=
    .recursive cvmPreFamilyAfterDirectContextTest 5
      [cvmPreFamilyProofContextTest.freshFVarId] true
      `function cvmCtorFunctionDomain cvmCtorAfterDirect.bindingBody!
      .default cvmPreFamilyNoParameterFiveTest
      cvmValidationFunctionHasIndOccTest
      cvmPreFamilyFunctionIndependentTest
      cvmPreFamilyFunctionFieldTraceAtFuelTest
      cvmPreFamilyAfterDirectFreshTest tailTrace
  refine ⟨trace, ?_⟩
  exact cvmPreFamilyRecursiveBuildEqTest cvmPreFamilyNoParameterFiveTest
    cvmValidationFunctionHasIndOccTest cvmPreFamilyFunctionIndependentTest
    cvmPreFamilyFunctionFieldTraceAtFuelTest
    cvmPreFamilyFunctionFieldRunAtFuelTest
    cvmPreFamilyAfterDirectFreshTest tailTrace tailRun

theorem cvmPreFamilyProofFreshExprValidationTest :
    cvmPreFamilyProofContextTest.freshExpr =
      cvmValidationProofContextTest.freshExpr := by
  rfl

theorem cvmPreFamilyDirectTailSourceTest :
    cvmCtorAfterProof.bindingBody!.instantiate1
      cvmPreFamilyProofContextTest.freshExpr = cvmCtorAfterDirect := by
  rw [cvmPreFamilyProofFreshExprValidationTest]
  exact cvmThirdFieldSourceTest

theorem cvmPreFamilyDirectIndependentTest :
    AddInductive.constructorIndependentOf cvmCtorDirectDomain [] = true := by
  simp [AddInductive.constructorIndependentOf]

theorem cvmPreFamilyDirectTraceRunTest :
    ∃ trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyProofContextTest
      cvmCtorAfterProof 4 [] false,
    AddInductive.ConstructorPreFamilyViewTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyProofContextTest
      cvmCtorAfterProof 4 [] false 996 = .ok trace := by
  obtain ⟨functionTrace, functionRun⟩ := cvmPreFamilyFunctionTraceRunTest
  obtain ⟨tailTrace, tailRun⟩ :
      ∃ tailTrace : AddInductive.ConstructorPreFamilyViewTrace
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest cvmPreFamilyProofContextTest.advanceFresh
        (cvmCtorAfterProof.bindingBody!.instantiate1
          cvmPreFamilyProofContextTest.freshExpr) 5
        [cvmPreFamilyProofContextTest.freshFVarId] true,
      AddInductive.ConstructorPreFamilyViewTrace.build
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest cvmPreFamilyProofContextTest.advanceFresh
        (cvmCtorAfterProof.bindingBody!.instantiate1
          cvmPreFamilyProofContextTest.freshExpr) 5
        [cvmPreFamilyProofContextTest.freshFVarId] true 995 =
        .ok tailTrace := by
    rw [show cvmPreFamilyProofContextTest.advanceFresh =
      cvmPreFamilyAfterDirectContextTest by rfl]
    rw [cvmPreFamilyDirectTailSourceTest]
    exact ⟨functionTrace, functionRun⟩
  rw [cvmCtorAfterProofForallTest]
  let trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyProofContextTest
      (.forallE `direct cvmCtorDirectDomain
        cvmCtorAfterProof.bindingBody! .default) 4 [] false :=
    .recursive cvmPreFamilyProofContextTest 4 [] false
      `direct cvmCtorDirectDomain cvmCtorAfterProof.bindingBody!
      .default cvmPreFamilyNoParameterFourTest
      cvmValidationDirectHasIndOccTest cvmPreFamilyDirectIndependentTest
      cvmPreFamilyDirectFieldTraceAtFuelTest
      cvmPreFamilyProofFreshTest tailTrace
  refine ⟨trace, ?_⟩
  exact cvmPreFamilyRecursiveBuildEqTest cvmPreFamilyNoParameterFourTest
    cvmValidationDirectHasIndOccTest cvmPreFamilyDirectIndependentTest
    cvmPreFamilyDirectFieldTraceAtFuelTest
    cvmPreFamilyDirectFieldRunAtFuelTest cvmPreFamilyProofFreshTest
    tailTrace tailRun

theorem cvmPreFamilyXFreshExprValidationTest :
    cvmPreFamilyXContextTest.freshExpr =
      cvmValidationXContextTest.freshExpr := by
  rfl

theorem cvmPreFamilyProofTailSourceTest :
    cvmCtorAfterX.bindingBody!.instantiate1
      cvmPreFamilyXContextTest.freshExpr = cvmCtorAfterProof := by
  rw [cvmPreFamilyXFreshExprValidationTest]
  exact cvmSecondFieldSourceTest

theorem cvmPreFamilyProofIndependentTest :
    AddInductive.constructorIndependentOf cvmCtorProofDomain [] = true := by
  simp [AddInductive.constructorIndependentOf]

theorem cvmPreFamilyProofTraceRunTest :
    ∃ trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyXContextTest
      cvmCtorAfterX 3 [] false,
    AddInductive.ConstructorPreFamilyViewTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyXContextTest
      cvmCtorAfterX 3 [] false 997 = .ok trace := by
  obtain ⟨directTrace, directRun⟩ := cvmPreFamilyDirectTraceRunTest
  obtain ⟨tailTrace, tailRun⟩ :
      ∃ tailTrace : AddInductive.ConstructorPreFamilyViewTrace
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest
        (cvmPreFamilyXContextTest.pushLocalDecl `proof .default
          (AddInductive.consumeTypeAnnotations cvmCtorProofDomain))
        (cvmCtorAfterX.bindingBody!.instantiate1
          cvmPreFamilyXContextTest.freshExpr) 4 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest
        (cvmPreFamilyXContextTest.pushLocalDecl `proof .default
          (AddInductive.consumeTypeAnnotations cvmCtorProofDomain))
        (cvmCtorAfterX.bindingBody!.instantiate1
          cvmPreFamilyXContextTest.freshExpr) 4 [] false 996 =
        .ok tailTrace := by
    rw [show cvmPreFamilyXContextTest.pushLocalDecl `proof .default
      (AddInductive.consumeTypeAnnotations cvmCtorProofDomain) =
      cvmPreFamilyProofContextTest by rfl]
    rw [cvmPreFamilyProofTailSourceTest]
    exact ⟨directTrace, directRun⟩
  rw [cvmCtorAfterXForallTest]
  let trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyXContextTest
      (.forallE `proof cvmCtorProofDomain
        cvmCtorAfterX.bindingBody! .default) 3 [] false :=
    .ordinary cvmPreFamilyXContextTest 3 [] false
      `proof cvmCtorProofDomain cvmCtorAfterX.bindingBody! .default
      cvmPreFamilyNoParameterThreeTest
      cvmValidationProofHasNoIndOccTest cvmPreFamilyProofIndependentTest
      cvmPreFamilyProofCheckedTest cvmPreFamilyProofEnsureTest
      cvmPreFamilyProofConsumedTest cvmPreFamilyProofAnnotationsTest
      cvmPreFamilyXFreshTest tailTrace
  refine ⟨trace, ?_⟩
  exact cvmPreFamilyOrdinaryBuildEqTest cvmPreFamilyNoParameterThreeTest
    cvmValidationProofHasNoIndOccTest cvmPreFamilyProofIndependentTest
    cvmPreFamilyProofCheckedTest cvmPreFamilyProofEnsureTest
    cvmPreFamilyProofConsumedTest cvmPreFamilyProofAnnotationsTest
    cvmPreFamilyXFreshTest tailTrace tailRun

theorem cvmPreFamilyRootFreshExprValidationTest :
    cvmPreFamilyContextTest.freshExpr =
      cvmValidationRootContextTest.freshExpr := by
  rfl

theorem cvmPreFamilyXTailSourceTest :
    cvmCtorAfterP.bindingBody!.instantiate1
      cvmPreFamilyContextTest.freshExpr = cvmCtorAfterX := by
  rw [cvmPreFamilyRootFreshExprValidationTest]
  exact cvmFirstFieldSourceTest

theorem cvmPreFamilyXIndependentTest :
    AddInductive.constructorIndependentOf cvmCtorXDomain [] = true := by
  simp [AddInductive.constructorIndependentOf]

theorem cvmPreFamilyXTraceRunTest :
    ∃ trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      cvmCtorAfterP 2 [] false,
    AddInductive.ConstructorPreFamilyViewTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      cvmCtorAfterP 2 [] false 998 = .ok trace := by
  obtain ⟨proofTrace, proofRun⟩ := cvmPreFamilyProofTraceRunTest
  obtain ⟨tailTrace, tailRun⟩ :
      ∃ tailTrace : AddInductive.ConstructorPreFamilyViewTrace
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest
        (cvmPreFamilyContextTest.pushLocalDecl `x .default
          (AddInductive.consumeTypeAnnotations cvmCtorXDomain))
        (cvmCtorAfterP.bindingBody!.instantiate1
          cvmPreFamilyContextTest.freshExpr) 3 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest
        (cvmPreFamilyContextTest.pushLocalDecl `x .default
          (AddInductive.consumeTypeAnnotations cvmCtorXDomain))
        (cvmCtorAfterP.bindingBody!.instantiate1
          cvmPreFamilyContextTest.freshExpr) 3 [] false 997 =
        .ok tailTrace := by
    rw [show cvmPreFamilyContextTest.pushLocalDecl `x .default
      (AddInductive.consumeTypeAnnotations cvmCtorXDomain) =
      cvmPreFamilyXContextTest by rfl]
    rw [cvmPreFamilyXTailSourceTest]
    exact ⟨proofTrace, proofRun⟩
  rw [cvmCtorAfterPForallTest]
  let trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      (.forallE `x cvmCtorXDomain cvmCtorAfterP.bindingBody! .default)
      2 [] false :=
    .ordinary cvmPreFamilyContextTest 2 [] false `x cvmCtorXDomain
      cvmCtorAfterP.bindingBody! .default cvmPreFamilyNoParameterTwoTest
      (by
        rw [cvmCtorXDomainValidationShapeTest]
        exact cvmValidationAlphaHasNoIndOccTest)
      cvmPreFamilyXIndependentTest cvmPreFamilyXCheckedTest
      cvmPreFamilyXEnsureTest cvmPreFamilyXConsumedTest
      cvmPreFamilyXAnnotationsTest cvmPreFamilyRootFreshTest tailTrace
  refine ⟨trace, ?_⟩
  exact cvmPreFamilyOrdinaryBuildEqTest cvmPreFamilyNoParameterTwoTest
    (by
      rw [cvmCtorXDomainValidationShapeTest]
      exact cvmValidationAlphaHasNoIndOccTest)
    cvmPreFamilyXIndependentTest cvmPreFamilyXCheckedTest
    cvmPreFamilyXEnsureTest cvmPreFamilyXConsumedTest
    cvmPreFamilyXAnnotationsTest cvmPreFamilyRootFreshTest tailTrace tailRun

theorem cvmPreFamilyPTailSourceTest :
    cvmCtorAfterAlpha.bindingBody!.instantiate1
      (.fvar cvmValidationPIdTest) = cvmCtorAfterP := by
  exact cvmSecondParameterSourceTest

theorem cvmPreFamilyPTraceRunTest :
    ∃ trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      cvmCtorAfterAlpha 1 [] false,
    AddInductive.ConstructorPreFamilyViewTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      cvmCtorAfterAlpha 1 [] false 999 = .ok trace := by
  obtain ⟨xTrace, xRun⟩ := cvmPreFamilyXTraceRunTest
  obtain ⟨tailTrace, tailRun⟩ :
      ∃ tailTrace : AddInductive.ConstructorPreFamilyViewTrace
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest cvmPreFamilyContextTest
        (cvmCtorAfterAlpha.bindingBody!.instantiate1
          (.fvar cvmValidationPIdTest)) 2 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest cvmPreFamilyContextTest
        (cvmCtorAfterAlpha.bindingBody!.instantiate1
          (.fvar cvmValidationPIdTest)) 2 [] false 998 =
        .ok tailTrace := by
    rw [cvmPreFamilyPTailSourceTest]
    exact ⟨xTrace, xRun⟩
  rw [cvmCtorAfterAlphaForallTest]
  let trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      (.forallE `P cvmCtorPDomain cvmCtorAfterAlpha.bindingBody! .implicit)
      1 [] false :=
    .parameter cvmPreFamilyContextTest 1 [] false `P cvmCtorPDomain
      cvmCtorAfterAlpha.bindingBody! .implicit
      (.fvar cvmValidationPIdTest) cvmPreFamilyParameterAtOneTest tailTrace
  refine ⟨trace, ?_⟩
  exact cvmPreFamilyParameterBuildEqTest
    cvmPreFamilyParameterAtOneTest tailTrace tailRun

theorem cvmPreFamilyAlphaTailSourceTest :
    constructorValidityMatrixKernelCtor.type.bindingBody!.instantiate1
      (.fvar cvmValidationAlphaIdTest) = cvmCtorAfterAlpha := by
  exact cvmFirstParameterSourceTest

theorem cvmCtorRootForallTest :
    constructorValidityMatrixKernelCtor.type =
      .forallE `α (.sort (.succ (.param `u)))
        constructorValidityMatrixKernelCtor.type.bindingBody! .implicit := by
  simp_cvm_ctor_expr

theorem cvmPreFamilyRawTraceRunTest :
    ∃ trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      constructorValidityMatrixKernelCtor.type 0 [] false,
    AddInductive.ConstructorPreFamilyViewTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      constructorValidityMatrixKernelCtor.type 0 [] false 1000 =
        .ok trace := by
  obtain ⟨pTrace, pRun⟩ := cvmPreFamilyPTraceRunTest
  obtain ⟨tailTrace, tailRun⟩ :
      ∃ tailTrace : AddInductive.ConstructorPreFamilyViewTrace
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest cvmPreFamilyContextTest
        (constructorValidityMatrixKernelCtor.type.bindingBody!.instantiate1
          (.fvar cvmValidationAlphaIdTest)) 1 [] false,
      AddInductive.ConstructorPreFamilyViewTrace.build
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest cvmPreFamilyContextTest
        (constructorValidityMatrixKernelCtor.type.bindingBody!.instantiate1
          (.fvar cvmValidationAlphaIdTest)) 1 [] false 999 =
        .ok tailTrace := by
    rw [cvmPreFamilyAlphaTailSourceTest]
    exact ⟨pTrace, pRun⟩
  rw [cvmCtorRootForallTest]
  let trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      (.forallE `α (.sort (.succ (.param `u)))
        constructorValidityMatrixKernelCtor.type.bindingBody! .implicit)
      0 [] false :=
    .parameter cvmPreFamilyContextTest 0 [] false `α
      (.sort (.succ (.param `u)))
      constructorValidityMatrixKernelCtor.type.bindingBody! .implicit
      (.fvar cvmValidationAlphaIdTest) cvmPreFamilyParameterAtZeroTest
      tailTrace
  refine ⟨trace, ?_⟩
  exact cvmPreFamilyParameterBuildEqTest
    cvmPreFamilyParameterAtZeroTest tailTrace tailRun

theorem cvmPreFamilyCandidateTraceRunTest :
    ∃ trace : AddInductive.ConstructorPreFamilyViewTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      cvmCandidate.families.singleton.constructors.singleton.type.view
      0 [] false,
    AddInductive.ConstructorPreFamilyViewTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      cvmCandidate.families.singleton.constructors.singleton.type.view
      0 [] false 1000 = .ok trace := by
  rw [cvmCtorViewTest_eq]
  exact cvmPreFamilyRawTraceRunTest

theorem cvmSafetyRunDirectTest :
    AddInductive.checkConstructorPreFamilySafety
      cvmStagedUniverseInputTest.staged.family.validation.stats
      cvmCandidate.families.singleton.familyType.type.view
      cvmCandidate.families.singleton.constructors
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext =
        .ok () := by
  rw [cvmFamilyViewPreFamilyTest_eq]
  rw [AddInductive.CandidateList.singleton_eta
    cvmCandidate.families.singleton.constructors]
  rw [cvmFamilyTerminalContextTest_eq]
  change AddInductive.checkConstructorPreFamilySafety
    cvmStagedUniverseInputTest.staged.family.validation.stats
    constructorValidityMatrixKernelType.type
    (.cons cvmCandidate.families.singleton.constructors.singleton .nil)
    cvmPreFamilyContextTest = .ok ()
  obtain ⟨headTrace, headRun⟩ := cvmPreFamilyCandidateTraceRunTest
  let listTrace : AddInductive.ConstructorPreFamilyListTrace
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      (.cons cvmCandidate.families.singleton.constructors.singleton .nil) :=
    .cons headTrace .nil
  have headRunAtFuel :
      AddInductive.ConstructorPreFamilyViewTrace.build
        cvmStagedUniverseInputTest.staged.family.validation.stats 0
        cvmPreFamilyIndicesTest cvmPreFamilyContextTest
        cvmCandidate.families.singleton.constructors.singleton.type.view
        0 [] false cvmPreFamilyContextTest.fuel.inductiveFuel =
          .ok headTrace := by
    rw [cvmPreFamilyInductiveFuelTest _ (Or.inl rfl)]
    exact headRun
  have listRun : AddInductive.ConstructorPreFamilyListTrace.build
      cvmStagedUniverseInputTest.staged.family.validation.stats 0
      cvmPreFamilyIndicesTest cvmPreFamilyContextTest
      (.cons cvmCandidate.families.singleton.constructors.singleton .nil) =
        .ok listTrace :=
    AddInductive.ConstructorPreFamilyListTrace.cons_build_eq headTrace
      headRunAtFuel .nil rfl
  have translationUnique :
      (AddInductive.theoryTranslationUnique
          constructorValidityMatrixKernelType.type &&
        (AddInductive.CandidateList.cons
          cvmCandidate.families.singleton.constructors.singleton
          (AddInductive.CandidateList.nil : AddInductive.CandidateList
            AddInductive.CandidateConstructor [])).viewTranslationUnique) =
        true := by
    change (AddInductive.theoryTranslationUnique
      constructorValidityMatrixKernelType.type &&
      (cvmCandidate.families.singleton.constructors.singleton.type.trace.viewTranslationUnique &&
        true)) = true
    rw [cvmCandidate.families.singleton.constructors.singleton.type.trace.viewTranslationUnique_eq]
    change (AddInductive.theoryTranslationUnique
      constructorValidityMatrixKernelType.type &&
      (AddInductive.theoryTranslationUnique
        cvmCandidate.families.singleton.constructors.singleton.type.view &&
        true)) = true
    rw [cvmCtorViewTest_eq]
    simp [AddInductive.theoryTranslationUnique,
      constructorValidityMatrixKernelType,
      constructorValidityMatrixKernelCtor,
      constructorValidityMatrixInfo, constructorValidityMatrixMkInfo,
      ConstantInfo.type, ConstantInfo.toConstantVal]
  unfold AddInductive.checkConstructorPreFamilySafety
  rw [if_pos translationUnique]
  rw [cvmPreFamilyParametersRunTest]
  simp only [Bind.bind, Except.bind]
  rw [listRun]
  rfl

theorem cvmSafetyRunTest :
    AddInductive.checkConstructorPreFamilySafety
      cvmStagedPostFamilyInputTest.universeInput.staged.family.validation.stats
      cvmCandidate.families.singleton.familyType.type.view
      cvmCandidate.families.singleton.constructors
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext =
        .ok () := by
  simpa [cvmStagedPostFamilyInputTest] using cvmSafetyRunDirectTest

def cvmStagedPreFamilyInputTest :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      cvmFamilyContext cvmConstructorContext VEnv.empty [`u]
      cvmCandidate constructorValidityMatrixDecl :=
  VInductDecl.StagedNormalizationCandidatePreFamilyInput.ofRun
    cvmStagedPostFamilyInputTest cvmSafetyRunTest

/- Public CVM stage names now expose the structural D2--D4 replay above. -/
theorem cvmUniverseRun :
    AddInductive.checkConstructorUniverseListSemantics
      cvmFamilyValidationRun.stats constructorValidityMatrixKernelType.ctors
      { cvmCandidate.families.singleton.familyType.type.trace.terminalContext with
        env := cvmConstructorContext.env } = .ok () :=
  by
    change AddInductive.checkConstructorUniverseListSemantics
      cvmFamilyValidationRun.stats constructorValidityMatrixKernelType.ctors
      cvmConstructorValidationContextTest = .ok ()
    rw [cvmConstructorValidationContextTest_root]
    exact cvmUniverseRunTest

def cvmConstructorValidation := cvmConstructorValidationTest

def cvmStagedUniverseInput := cvmStagedUniverseInputTest

def cvmStagedPostFamilyInput := cvmStagedPostFamilyInputTest

theorem cvmSafetyRunDirect :
    AddInductive.checkConstructorPreFamilySafety
      cvmStagedUniverseInput.staged.family.validation.stats
      cvmCandidate.families.singleton.familyType.type.view
      cvmCandidate.families.singleton.constructors
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext =
        .ok () :=
  cvmSafetyRunDirectTest

theorem cvmSafetyRun :
    AddInductive.checkConstructorPreFamilySafety
      cvmStagedPostFamilyInput.universeInput.staged.family.validation.stats
      cvmCandidate.families.singleton.familyType.type.view
      cvmCandidate.families.singleton.constructors
      cvmCandidate.families.singleton.familyType.type.trace.terminalContext =
        .ok () :=
  cvmSafetyRunTest

def cvmStagedPreFamilyInput := cvmStagedPreFamilyInputTest

/- The accepted CVM package may inherit the ordinary verified-checker
transition frontier and the one exact L4L-01E execution witness, but no
stage-local native decision may re-enter constructor validation, universe
checking, alignment, or pre-family safety. -/
/--
info: 'Lean4Lean.InductiveReplayFixtures.cvmStagedPreFamilyInput' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.abstract_fvars_shape,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert,
 cvmExecutionResult_isOk._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms cvmStagedPreFamilyInput

/-! ## Exact produced generation packages -/

def cvmCanonicalFamily :
    AddInductive.CandidateFamily constructorValidityMatrixKernelType where
  familyType := cvmCandidate.families.singleton.familyType
  constructors := .cons
    cvmCandidate.families.singleton.constructors.singleton .nil

def cvmCanonicalCandidate :
    AddInductive.NormalizationCandidate [constructorValidityMatrixKernelType] where
  families := .cons cvmCanonicalFamily .nil

theorem cvmOneCtorCandidate_eta
    (candidate : AddInductive.NormalizationCandidate
      [constructorValidityMatrixKernelType]) :
    candidate = {
      families := .cons {
        familyType := candidate.families.singleton.familyType
        constructors := .cons
          candidate.families.singleton.constructors.singleton .nil }
        .nil } := by
  cases candidate with
  | mk families =>
      cases families with
      | cons family tail =>
          cases tail
          cases family with
          | mk familyType constructors =>
              cases constructors with
              | cons constructor tail =>
                  cases tail
                  rfl

theorem cvmCandidate_eq_canonical : cvmCandidate = cvmCanonicalCandidate := by
  simpa [cvmCanonicalCandidate, cvmCanonicalFamily] using
    cvmOneCtorCandidate_eta cvmCandidate

theorem cvmCanonicalCandidate_produced :
    AddInductive.buildNormalizationCandidate 2
        [constructorValidityMatrixKernelType] 0 false
        constructorValidityMatrixContext = .ok cvmCanonicalCandidate := by
  rw [← cvmCandidate_eq_canonical]
  exact cvmCandidate_produced

abbrev cvmCanonicalStagedPreFamilyInput :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      cvmFamilyContext cvmConstructorContext VEnv.empty [`u]
      cvmCanonicalCandidate constructorValidityMatrixDecl :=
  cvmCandidate_eq_canonical ▸ cvmStagedPreFamilyInput

def cvmFamilySemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun VEnv.empty [`u]
      cvmCanonicalCandidate.families.singleton.familyType.type
      constructorValidityMatrixType.type :=
  cvmFamilyStage.type.rootInput.semanticOfIdentity
    cvmFamilyIdentityEvidence.identity

def cvmCtorSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun cvmTypeEnv [`u]
      cvmCanonicalCandidate.families.singleton.constructors.singleton.type
      constructorValidityMatrixType.ctors[0].type :=
  cvmCtorStagedInput.type.rootInput.semanticOfIdentity
    cvmCtorIdentityEvidence.identity

def cvmCtorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun cvmTypeEnv [`u]
      cvmCanonicalCandidate.families.singleton.constructors.singleton
      constructorValidityMatrixType.ctors[0] where
  name_eq := cvmCtorNames_eq
  uvars_eq := rfl
  type := cvmCtorSemanticRootRun

def cvmConstructorSemanticListRun :
    VInductDecl.CandidateConstructorSemanticListRun cvmTypeEnv [`u]
      cvmCanonicalCandidate.families.singleton.constructors
      constructorValidityMatrixType.ctors :=
  .cons cvmCtorSemanticRun .nil

def cvmFamilySemanticRun :
    VInductDecl.CandidateFamilySemanticRun VEnv.empty [`u]
      cvmCanonicalCandidate.families.singleton constructorValidityMatrixType where
  name_eq := cvmFamilyNames_eq
  uvars_eq := rfl
  type := cvmFamilySemanticRootRun
  typeEnv := cvmTypeEnv
  addType := cvmTypeEnv_add
  constructors := cvmConstructorSemanticListRun

def cvmReferenceNormalization :
    VInductDecl.NormalizationCandidateSemanticRun VEnv.empty [`u]
      cvmCanonicalCandidate constructorValidityMatrixDecl where
  raw := constructorValidityMatrixType
  raw_types_eq := rfl
  uvars_eq := rfl
  family := cvmFamilySemanticRun

theorem cvmCandidate_generationShape :
    VInductDecl.normalizationCandidateGenerationShape
      constructorValidityMatrixDecl constructorValidityMatrixType
      cvmCanonicalCandidate = true := by
  rw [← cvmCandidate_eq_canonical]
  unfold VInductDecl.normalizationCandidateGenerationShape
  rw [AddInductive.CandidateList.singleton_eta
    cvmCandidate.families.singleton.constructors]
  have familyStored := cvmFamilyIdentityEvidence.identity.storedSpine
  have familyLength := cvmFamilyIdentityEvidence.spineLength_eq.trans
    cvmFamilyIdentityReplay_shape.1
  have ctorStored := cvmCtorIdentityEvidence.identity.storedSpine
  have ctorLength := cvmCtorIdentityEvidence.spineLength_eq.trans
    cvmCtorIdentityReplay_shape.1
  simp [VInductDecl.candidateConstructorSemanticGenerationShape,
    constructorValidityMatrixDecl, constructorValidityMatrixType,
    VExpr.telN, VExpr.dropN, VInductDecl.ctorFields,
    familyStored, familyLength, ctorStored, ctorLength]

abbrev cvmProducedGenerationShapeCandidate :
    VInductDecl.ProducedGenerationShapeCandidate constructorValidityMatrixDecl
      constructorValidityMatrixType constructorValidityMatrixKernelType 0
      false constructorValidityMatrixContext where
  candidate := cvmCanonicalCandidate
  produced := cvmCanonicalCandidate_produced
  shape := cvmCandidate_generationShape

private theorem cvmCandidate_analysis
    (normalization : VInductDecl.NormalizationCandidateSemanticRun VEnv.empty
      [`u] cvmCanonicalCandidate constructorValidityMatrixDecl) :
    normalization.root.normalization.generation? =
      some constructorValidityMatrixGenerationChecked := by
  rw [cvmCanonicalStagedPreFamilyInput.normalization_eq normalization
    cvmReferenceNormalization]
  have hnorm : cvmReferenceNormalization.root.normalization =
      VInductDecl.Normalization.identity constructorValidityMatrixDecl := by
    apply normalization_eq_of_view_eq
    rfl
  rw [hnorm]
  rfl

theorem cvmExactProducedGenerationCandidatePackage_exists :
    Nonempty (VInductDecl.ExactProducedGenerationCandidatePackage
      VEnv.empty [`u] cvmProducedGenerationShapeCandidate
      constructorValidityMatrixGenerationChecked) :=
  cvmProducedGenerationShapeCandidate.exactProducedPackage_nonempty
    cvmCanonicalStagedPreFamilyInput
      (stagedPreFamily_transport_raw cvmCandidate_eq_canonical
        cvmStagedPreFamilyInput).symm
      constructorValidityMatrixGenerationChecked
    cvmCandidate_analysis

private def cvmExactProducedGenerationCandidatePackage :
    VInductDecl.ExactProducedGenerationCandidatePackage VEnv.empty [`u]
      cvmProducedGenerationShapeCandidate
      constructorValidityMatrixGenerationChecked :=
  cvmProducedGenerationShapeCandidate.exactProducedPackage
    cvmCanonicalStagedPreFamilyInput
      (stagedPreFamily_transport_raw cvmCandidate_eq_canonical
        cvmStagedPreFamilyInput).symm
      constructorValidityMatrixGenerationChecked
    cvmCandidate_analysis

def cvmGenerationCandidateSemanticRun :
    VInductDecl.GenerationCandidateSemanticRun
      cvmExactProducedGenerationCandidatePackage.normalization
      constructorValidityMatrixGenerationChecked :=
  cvmExactProducedGenerationCandidatePackage.semantic

def cvmProducedGenerationCandidatePackage :
    VInductDecl.ProducedGenerationCandidatePackage VEnv.empty [`u] :=
  cvmExactProducedGenerationCandidatePackage.package

def cvmGenerationCertificate :
    constructorValidityMatrixDecl.GenerationCertificate VEnv.empty where
  generation := constructorValidityMatrixGenerationChecked
  wf := cvmExactProducedGenerationCandidatePackage.semantic.run.wf

def cvmCertifiedFinalEnv : VEnv :=
  (VEnv.empty.addInductGeneration
    constructorValidityMatrixGenerationChecked).get!

theorem cvm_addInductGeneration :
    VEnv.empty.addInductGeneration
        constructorValidityMatrixGenerationChecked =
      some cvmCertifiedFinalEnv := by
  rfl

theorem cvm_addInductCertified :
    VEnv.empty.addInductCertified cvmGenerationCertificate =
      some cvmCertifiedFinalEnv :=
  cvm_addInductGeneration

theorem cvmGeneration_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty cvmCertifiedFinalEnv
      constructorValidityMatrixGenerationChecked) :=
  VEnv.addInductGeneration_trace cvm_addInductGeneration

theorem cvmCertified_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty cvmCertifiedFinalEnv
      constructorValidityMatrixGenerationChecked) :=
  cvmGeneration_trace

theorem cvmCertified_ordered : cvmCertifiedFinalEnv.Ordered :=
  VEnv.addInductCertified_WF .empty cvm_addInductCertified

def prbCanonicalFamily :
    AddInductive.CandidateFamily propRecursiveBoundaryKernelType where
  familyType := prbCandidate.families.singleton.familyType
  constructors := .cons
    prbCandidate.families.singleton.constructors.singleton .nil

def prbCanonicalCandidate :
    AddInductive.NormalizationCandidate [propRecursiveBoundaryKernelType] where
  families := .cons prbCanonicalFamily .nil

theorem prbOneCtorCandidate_eta
    (candidate : AddInductive.NormalizationCandidate
      [propRecursiveBoundaryKernelType]) :
    candidate = {
      families := .cons {
        familyType := candidate.families.singleton.familyType
        constructors := .cons
          candidate.families.singleton.constructors.singleton .nil }
        .nil } := by
  cases candidate with
  | mk families =>
      cases families with
      | cons family tail =>
          cases tail
          cases family with
          | mk familyType constructors =>
              cases constructors with
              | cons constructor tail =>
                  cases tail
                  rfl

theorem prbCandidate_eq_canonical : prbCandidate = prbCanonicalCandidate := by
  simpa [prbCanonicalCandidate, prbCanonicalFamily] using
    prbOneCtorCandidate_eta prbCandidate

theorem prbCanonicalCandidate_produced :
    AddInductive.buildNormalizationCandidate 1
        [propRecursiveBoundaryKernelType] 0 false
        propRecursiveBoundaryContext = .ok prbCanonicalCandidate := by
  rw [← prbCandidate_eq_canonical]
  exact prbCandidate_produced

abbrev prbCanonicalStagedPreFamilyInput :
    VInductDecl.StagedNormalizationCandidatePreFamilyInput
      prbFamilyContext prbConstructorContext VEnv.empty [`u]
      prbCanonicalCandidate propRecursiveBoundaryDecl :=
  prbCandidate_eq_canonical ▸ prbStagedPreFamilyInput

def prbFamilySemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun VEnv.empty [`u]
      prbCanonicalCandidate.families.singleton.familyType.type
      propRecursiveBoundaryType.type :=
  prbFamilyStage.type.rootInput.semanticOfIdentity
    prbFamilyIdentityEvidence.identity

def prbCtorSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun prbTypeEnv [`u]
      prbCanonicalCandidate.families.singleton.constructors.singleton.type
      propRecursiveBoundaryType.ctors[0].type :=
  prbCtorStagedInput.type.rootInput.semanticOfIdentity
    prbCtorIdentityEvidence.identity

def prbCtorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun prbTypeEnv [`u]
      prbCanonicalCandidate.families.singleton.constructors.singleton
      propRecursiveBoundaryType.ctors[0] where
  name_eq := prbCtorNames_eq
  uvars_eq := rfl
  type := prbCtorSemanticRootRun

def prbConstructorSemanticListRun :
    VInductDecl.CandidateConstructorSemanticListRun prbTypeEnv [`u]
      prbCanonicalCandidate.families.singleton.constructors
      propRecursiveBoundaryType.ctors :=
  .cons prbCtorSemanticRun .nil

def prbFamilySemanticRun :
    VInductDecl.CandidateFamilySemanticRun VEnv.empty [`u]
      prbCanonicalCandidate.families.singleton propRecursiveBoundaryType where
  name_eq := prbFamilyNames_eq
  uvars_eq := rfl
  type := prbFamilySemanticRootRun
  typeEnv := prbTypeEnv
  addType := prbTypeEnv_add
  constructors := prbConstructorSemanticListRun

def prbReferenceNormalization :
    VInductDecl.NormalizationCandidateSemanticRun VEnv.empty [`u]
      prbCanonicalCandidate propRecursiveBoundaryDecl where
  raw := propRecursiveBoundaryType
  raw_types_eq := rfl
  uvars_eq := rfl
  family := prbFamilySemanticRun

theorem prbCandidate_generationShape :
    VInductDecl.normalizationCandidateGenerationShape
      propRecursiveBoundaryDecl propRecursiveBoundaryType
        prbCanonicalCandidate =
        true := by
  rw [← prbCandidate_eq_canonical]
  unfold VInductDecl.normalizationCandidateGenerationShape
  rw [AddInductive.CandidateList.singleton_eta
    prbCandidate.families.singleton.constructors]
  have familyStored := prbFamilyIdentityEvidence.identity.storedSpine
  have familyLength := prbFamilyIdentityEvidence.spineLength_eq.trans
    prbFamilyIdentityReplay_shape.1
  have ctorStored := prbCtorIdentityEvidence.identity.storedSpine
  have ctorLength := prbCtorIdentityEvidence.spineLength_eq.trans
    prbCtorIdentityReplay_shape.1
  simp [VInductDecl.candidateConstructorSemanticGenerationShape,
    propRecursiveBoundaryDecl, propRecursiveBoundaryType,
    VExpr.telN, VExpr.dropN, VInductDecl.ctorFields,
    familyStored, familyLength, ctorStored, ctorLength]

abbrev prbProducedGenerationShapeCandidate :
    VInductDecl.ProducedGenerationShapeCandidate propRecursiveBoundaryDecl
      propRecursiveBoundaryType propRecursiveBoundaryKernelType 0 false
      propRecursiveBoundaryContext where
  candidate := prbCanonicalCandidate
  produced := prbCanonicalCandidate_produced
  shape := prbCandidate_generationShape

private theorem prbCandidate_analysis
    (normalization : VInductDecl.NormalizationCandidateSemanticRun VEnv.empty
      [`u] prbCanonicalCandidate propRecursiveBoundaryDecl) :
    normalization.root.normalization.generation? =
      some propRecursiveBoundaryGenerationChecked := by
  rw [prbCanonicalStagedPreFamilyInput.normalization_eq normalization
    prbReferenceNormalization]
  have hnorm : prbReferenceNormalization.root.normalization =
      VInductDecl.Normalization.identity propRecursiveBoundaryDecl := by
    apply normalization_eq_of_view_eq
    rfl
  rw [hnorm]
  rfl

theorem prbExactProducedGenerationCandidatePackage_exists :
    Nonempty (VInductDecl.ExactProducedGenerationCandidatePackage
      VEnv.empty [`u] prbProducedGenerationShapeCandidate
      propRecursiveBoundaryGenerationChecked) :=
  prbProducedGenerationShapeCandidate.exactProducedPackage_nonempty
    prbCanonicalStagedPreFamilyInput
    (stagedPreFamily_transport_raw prbCandidate_eq_canonical
      prbStagedPreFamilyInput).symm propRecursiveBoundaryGenerationChecked
    prbCandidate_analysis

private def prbExactProducedGenerationCandidatePackage :
    VInductDecl.ExactProducedGenerationCandidatePackage VEnv.empty [`u]
      prbProducedGenerationShapeCandidate
      propRecursiveBoundaryGenerationChecked :=
  prbProducedGenerationShapeCandidate.exactProducedPackage
    prbCanonicalStagedPreFamilyInput
    (stagedPreFamily_transport_raw prbCandidate_eq_canonical
      prbStagedPreFamilyInput).symm propRecursiveBoundaryGenerationChecked
    prbCandidate_analysis

def prbGenerationCandidateSemanticRun :
    VInductDecl.GenerationCandidateSemanticRun
      prbExactProducedGenerationCandidatePackage.normalization
      propRecursiveBoundaryGenerationChecked :=
  prbExactProducedGenerationCandidatePackage.semantic

def prbProducedGenerationCandidatePackage :
    VInductDecl.ProducedGenerationCandidatePackage VEnv.empty [`u] :=
  prbExactProducedGenerationCandidatePackage.package

def prbGenerationCertificate :
    propRecursiveBoundaryDecl.GenerationCertificate VEnv.empty where
  generation := propRecursiveBoundaryGenerationChecked
  wf := prbExactProducedGenerationCandidatePackage.semantic.run.wf

def prbCertifiedFinalEnv : VEnv :=
  (VEnv.empty.addInductGeneration propRecursiveBoundaryGenerationChecked).get!

theorem prb_addInductGeneration :
    VEnv.empty.addInductGeneration propRecursiveBoundaryGenerationChecked =
      some prbCertifiedFinalEnv := by
  rfl

theorem prb_addInductCertified :
    VEnv.empty.addInductCertified prbGenerationCertificate =
      some prbCertifiedFinalEnv :=
  prb_addInductGeneration

theorem prbGeneration_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty prbCertifiedFinalEnv
      propRecursiveBoundaryGenerationChecked) :=
  VEnv.addInductGeneration_trace prb_addInductGeneration

theorem prbCertified_trace :
    Nonempty (VEnv.AddInductGenerationTrace VEnv.empty prbCertifiedFinalEnv
      propRecursiveBoundaryGenerationChecked) :=
  prbGeneration_trace

theorem prbCertified_ordered : prbCertifiedFinalEnv.Ordered :=
  VEnv.addInductCertified_WF .empty prb_addInductCertified

/-! ## Actual kernel-metadata replay -/

def cvmReplayCtorEnv : VEnv :=
  (cvmTypeEnv.addConst constructorValidityMatrixType.ctors[0].name
    constructorValidityMatrixType.ctors[0].toVConstant).get!

def cvmReplayRecEnv : VEnv :=
  (cvmReplayCtorEnv.addConst ``ConstructorValidityMatrix.rec
    constructorValidityMatrixGenerationChecked.recursor).get!

theorem cvmRawCtor_wf :
    constructorValidityMatrixType.ctors[0].toVConstant.WF cvmTypeEnv :=
  cvmRawCtor_isType

theorem cvmReplayCtorEnv_ordered : cvmReplayCtorEnv.Ordered :=
  .const (n := constructorValidityMatrixType.ctors[0].name)
    (ci := constructorValidityMatrixType.ctors[0].toVConstant)
    cvmTypeEnv_ordered cvmRawCtor_wf rfl

theorem cvmGenerationEnv :
    VInductDecl.GenerationEnv constructorValidityMatrixGenerationChecked
      cvmReplayCtorEnv := by
  apply cvmGenerationCertificate.wf.toGenerationEnv (envT := cvmTypeEnv)
  · rfl
  · exact (VEnv.addConst_le cvmTypeEnv_add).trans
      (VEnv.addConst_le (show
        cvmTypeEnv.addConst constructorValidityMatrixType.ctors[0].name
          constructorValidityMatrixType.ctors[0].toVConstant =
            some cvmReplayCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      cvmTypeEnv.addConst constructorValidityMatrixType.ctors[0].name
        constructorValidityMatrixType.ctors[0].toVConstant =
          some cvmReplayCtorEnv from rfl)
  · exact cvmReplayCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈
      [⟨constructorValidityMatrixType.ctors[0],
        constructorValidityMatrixChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

theorem cvmInfo_tr :
    TrConstVal .safe VEnv.empty constructorValidityMatrixInfo
      constructorValidityMatrixType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr VEnv.empty
      constructorValidityMatrixInfo.levelParams []
      constructorValidityMatrixInfo.type
      constructorValidityMatrixType.type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := cvmRawFamily_isType
  exact hshape.to_trExprS .empty trivial ⟨.sort u, htype⟩

theorem cvmMkInfo_tr :
    TrConstVal .safe cvmTypeEnv constructorValidityMatrixMkInfo
      constructorValidityMatrixType.ctors[0] := by
  exact ⟨⟨by decide, rfl, cvmCtorSource_tr⟩, rfl⟩

theorem cvmRecInfo_tr :
    TrConstVal .safe cvmReplayCtorEnv constructorValidityMatrixRecInfo
      (inductGenerationRecVal constructorValidityMatrixGenerationChecked) := by
  have hfamily : cvmReplayCtorEnv.constants
      ``ConstructorValidityMatrix =
        some constructorValidityMatrixType.toVConstant := rfl
  have hmk : cvmReplayCtorEnv.constants
      ``ConstructorValidityMatrix.mk =
        some constructorValidityMatrixType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr cvmReplayCtorEnv
      constructorValidityMatrixRecInfo.levelParams []
      constructorValidityMatrixRecInfo.type
      (inductGenerationRecVal
        constructorValidityMatrixGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := cvmGenerationEnv.recursor_wf
  exact hshape.to_trExprS cvmReplayCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

def cvmReplayTypeMap : ConstMap :=
  ({} : ConstMap).insert constructorValidityMatrixType.name
    constructorValidityMatrixInfo

def cvmReplayCtorMap : ConstMap :=
  cvmReplayTypeMap.insert constructorValidityMatrixType.ctors[0].name
    constructorValidityMatrixMkInfo

def cvmReplayMap : ConstMap :=
  cvmReplayCtorMap.insert ``ConstructorValidityMatrix.rec
    constructorValidityMatrixRecInfo

theorem cvmReplayType_fresh :
    ({} : ConstMap).find? constructorValidityMatrixType.name = none := by
  simp [SMap.find?]

theorem cvmReplayTypeMap_wf : cvmReplayTypeMap.WF :=
  SMap.WF.empty.insert _ _ cvmReplayType_fresh

theorem cvmReplayMk_fresh :
    cvmReplayTypeMap.find? constructorValidityMatrixType.ctors[0].name =
      none := by
  rw [cvmReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [constructorValidityMatrixType, SMap.find?]

theorem cvmReplayCtorMap_wf : cvmReplayCtorMap.WF :=
  cvmReplayTypeMap_wf.insert _ _ cvmReplayMk_fresh

theorem cvmReplayRec_fresh :
    cvmReplayCtorMap.find? ``ConstructorValidityMatrix.rec = none := by
  rw [cvmReplayCtorMap, cvmReplayTypeMap_wf.find?_insert,
    cvmReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [constructorValidityMatrixType, SMap.find?]

def cvmAddInductTraceChecked :
    AddInductTrace ({} : ConstMap) VEnv.empty constructorValidityMatrixDecl
      cvmReplayMap cvmCertifiedFinalEnv := by
  refine cvmProducedGenerationCandidatePackage.package.addInductTrace
    cvmReplayTypeMap cvmTypeEnv cvmReplayCtorMap cvmReplayCtorEnv
    cvmReplayRecEnv ?_ ?_ ?_ ?_ ⟨rfl⟩
  · exact {
      info := constructorValidityMatrixInfo
      kind_eq := by
        simp [constructorValidityMatrixInfo, InductConstantKind.Matches]
      tr := cvmInfo_tr
      map_fresh := cvmReplayType_fresh
      env_add := cvmTypeEnv_add
      map_add := rfl }
  · exact .cons {
      info := constructorValidityMatrixMkInfo
      kind_eq := by
        simp [constructorValidityMatrixMkInfo, InductConstantKind.Matches]
      tr := cvmMkInfo_tr
      map_fresh := by
        simpa [constructorValidityMatrixType] using cvmReplayMk_fresh
      env_add := rfl
      map_add := rfl } .nil
  · exact {
      info := constructorValidityMatrixRecInfo
      kind_eq := by
        simp [constructorValidityMatrixRecInfo, InductConstantKind.Matches]
      tr := cvmRecInfo_tr
      map_fresh := by
        rw [show
          (inductGenerationRecVal
            cvmProducedGenerationCandidatePackage.package.generation).name =
              ``ConstructorValidityMatrix.rec by rfl]
        exact cvmReplayRec_fresh
      env_add := rfl
      map_add := rfl }
  · decide

theorem cvm_addInduct_checked :
    AddInduct ({} : ConstMap) VEnv.empty constructorValidityMatrixDecl
      cvmReplayMap cvmCertifiedFinalEnv :=
  ⟨cvmAddInductTraceChecked⟩

theorem cvm_trEnv'_checked :
    TrEnv' .safe cvmReplayMap false cvmCertifiedFinalEnv :=
  .induct cvm_addInduct_checked .empty

theorem cvm_env_wf_checked : cvmCertifiedFinalEnv.WF :=
  cvm_trEnv'_checked.wf

theorem cvm_aligned_checked :
    Aligned .safe cvmReplayMap cvmCertifiedFinalEnv :=
  cvm_trEnv'_checked.aligned

theorem cvmReplay_type_map_lookup :
    cvmReplayMap.find? constructorValidityMatrixType.name =
      some constructorValidityMatrixInfo := by
  rw [cvmReplayMap, cvmReplayCtorMap_wf.find?_insert,
    cvmReplayCtorMap, cvmReplayTypeMap_wf.find?_insert,
    cvmReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [constructorValidityMatrixType]

theorem cvmReplay_ctor_map_lookup :
    cvmReplayMap.find? constructorValidityMatrixType.ctors[0].name =
      some constructorValidityMatrixMkInfo := by
  rw [cvmReplayMap, cvmReplayCtorMap_wf.find?_insert,
    cvmReplayCtorMap, cvmReplayTypeMap_wf.find?_insert]
  simp [constructorValidityMatrixType]

theorem cvmReplay_rec_map_lookup :
    cvmReplayMap.find? ``ConstructorValidityMatrix.rec =
      some constructorValidityMatrixRecInfo := by
  rw [cvmReplayMap, cvmReplayCtorMap_wf.find?_insert]
  simp

theorem cvmFinalEnv_type_lookup :
    cvmCertifiedFinalEnv.constants constructorValidityMatrixType.name =
      some constructorValidityMatrixType.toVConstant := by
  rcases cvmCertified_trace with ⟨trace⟩
  exact trace.family_lookup

theorem cvmFinalEnv_ctor_lookup :
    cvmCertifiedFinalEnv.constants
        constructorValidityMatrixType.ctors[0].name =
      some constructorValidityMatrixType.ctors[0].toVConstant := by
  rcases cvmCertified_trace with ⟨trace⟩
  exact trace.ctor_lookup (.head _)

theorem cvmFinalEnv_rec_lookup :
    cvmCertifiedFinalEnv.constants ``ConstructorValidityMatrix.rec =
      some constructorValidityMatrixGenerationChecked.recursor := by
  rcases cvmCertified_trace with ⟨trace⟩
  exact trace.rec_lookup

theorem cvmReplay_type_lookup_unique :
    constructorValidityMatrixInfo.name =
        constructorValidityMatrixType.name ∧
      TrConstant .safe cvmCertifiedFinalEnv constructorValidityMatrixInfo
        constructorValidityMatrixType.toVConstant :=
  cvm_aligned_checked.find?_uniq cvmReplay_type_map_lookup
    cvmFinalEnv_type_lookup

theorem cvmReplay_ctor_lookup_unique :
    constructorValidityMatrixMkInfo.name =
        constructorValidityMatrixType.ctors[0].name ∧
      TrConstant .safe cvmCertifiedFinalEnv constructorValidityMatrixMkInfo
        constructorValidityMatrixType.ctors[0].toVConstant :=
  cvm_aligned_checked.find?_uniq cvmReplay_ctor_map_lookup
    cvmFinalEnv_ctor_lookup

theorem cvmReplay_rec_lookup_unique :
    constructorValidityMatrixRecInfo.name =
        ``ConstructorValidityMatrix.rec ∧
      TrConstant .safe cvmCertifiedFinalEnv constructorValidityMatrixRecInfo
        constructorValidityMatrixGenerationChecked.recursor :=
  cvm_aligned_checked.find?_uniq cvmReplay_rec_map_lookup
    cvmFinalEnv_rec_lookup

theorem cvmFinalEnv_rule_mem :
    ∀ df ∈ constructorValidityMatrixGenerationChecked.generatedRules,
      cvmCertifiedFinalEnv.defeqs df := by
  intro df hdf
  rcases cvmCertified_trace with ⟨trace⟩
  exact trace.rule_mem hdf

theorem cvmFinalEnv_iota_mem :
    cvmCertifiedFinalEnv.defeqs
      constructorValidityMatrixGenerationChecked.generatedRules[0] := by
  apply cvmFinalEnv_rule_mem
  exact .head _

def prbReplayCtorEnv : VEnv :=
  (prbTypeEnv.addConst propRecursiveBoundaryType.ctors[0].name
    propRecursiveBoundaryType.ctors[0].toVConstant).get!

def prbReplayRecEnv : VEnv :=
  (prbReplayCtorEnv.addConst ``PropRecursiveBoundary.rec
    propRecursiveBoundaryGenerationChecked.recursor).get!

theorem prbRawCtor_wf :
    propRecursiveBoundaryType.ctors[0].toVConstant.WF prbTypeEnv :=
  prbRawCtor_isType

theorem prbReplayCtorEnv_ordered : prbReplayCtorEnv.Ordered :=
  .const (n := propRecursiveBoundaryType.ctors[0].name)
    (ci := propRecursiveBoundaryType.ctors[0].toVConstant)
    prbTypeEnv_ordered prbRawCtor_wf rfl

theorem prbGenerationEnv :
    VInductDecl.GenerationEnv propRecursiveBoundaryGenerationChecked
      prbReplayCtorEnv := by
  apply prbGenerationCertificate.wf.toGenerationEnv (envT := prbTypeEnv)
  · rfl
  · exact (VEnv.addConst_le prbTypeEnv_add).trans
      (VEnv.addConst_le (show
        prbTypeEnv.addConst propRecursiveBoundaryType.ctors[0].name
          propRecursiveBoundaryType.ctors[0].toVConstant =
            some prbReplayCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      prbTypeEnv.addConst propRecursiveBoundaryType.ctors[0].name
        propRecursiveBoundaryType.ctors[0].toVConstant =
          some prbReplayCtorEnv from rfl)
  · exact prbReplayCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈
      [⟨propRecursiveBoundaryType.ctors[0],
        propRecursiveBoundaryChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

theorem prbInfo_tr :
    TrConstVal .safe VEnv.empty propRecursiveBoundaryInfo
      propRecursiveBoundaryType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr VEnv.empty
      propRecursiveBoundaryInfo.levelParams []
      propRecursiveBoundaryInfo.type propRecursiveBoundaryType.type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := prbRawFamily_isType
  exact hshape.to_trExprS .empty trivial ⟨.sort u, htype⟩

theorem prbMkInfo_tr :
    TrConstVal .safe prbTypeEnv propRecursiveBoundaryMkInfo
      propRecursiveBoundaryType.ctors[0] := by
  exact ⟨⟨by decide, rfl, prbCtorSource_tr⟩, rfl⟩

theorem prbRecInfo_tr :
    TrConstVal .safe prbReplayCtorEnv propRecursiveBoundaryRecInfo
      (inductGenerationRecVal propRecursiveBoundaryGenerationChecked) := by
  have hfamily : prbReplayCtorEnv.constants ``PropRecursiveBoundary =
      some propRecursiveBoundaryType.toVConstant := rfl
  have hmk : prbReplayCtorEnv.constants ``PropRecursiveBoundary.mk =
      some propRecursiveBoundaryType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr prbReplayCtorEnv
      propRecursiveBoundaryRecInfo.levelParams []
      propRecursiveBoundaryRecInfo.type
      (inductGenerationRecVal propRecursiveBoundaryGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := prbGenerationEnv.recursor_wf
  exact hshape.to_trExprS prbReplayCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

def prbReplayTypeMap : ConstMap :=
  ({} : ConstMap).insert propRecursiveBoundaryType.name
    propRecursiveBoundaryInfo

def prbReplayCtorMap : ConstMap :=
  prbReplayTypeMap.insert propRecursiveBoundaryType.ctors[0].name
    propRecursiveBoundaryMkInfo

def prbReplayMap : ConstMap :=
  prbReplayCtorMap.insert ``PropRecursiveBoundary.rec
    propRecursiveBoundaryRecInfo

theorem prbReplayType_fresh :
    ({} : ConstMap).find? propRecursiveBoundaryType.name = none := by
  simp [SMap.find?]

theorem prbReplayTypeMap_wf : prbReplayTypeMap.WF :=
  SMap.WF.empty.insert _ _ prbReplayType_fresh

theorem prbReplayMk_fresh :
    prbReplayTypeMap.find? propRecursiveBoundaryType.ctors[0].name =
      none := by
  rw [prbReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [propRecursiveBoundaryType, SMap.find?]

theorem prbReplayCtorMap_wf : prbReplayCtorMap.WF :=
  prbReplayTypeMap_wf.insert _ _ prbReplayMk_fresh

theorem prbReplayRec_fresh :
    prbReplayCtorMap.find? ``PropRecursiveBoundary.rec = none := by
  rw [prbReplayCtorMap, prbReplayTypeMap_wf.find?_insert,
    prbReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [propRecursiveBoundaryType, SMap.find?]

def prbAddInductTraceChecked :
    AddInductTrace ({} : ConstMap) VEnv.empty propRecursiveBoundaryDecl
      prbReplayMap prbCertifiedFinalEnv := by
  refine prbProducedGenerationCandidatePackage.package.addInductTrace
    prbReplayTypeMap prbTypeEnv prbReplayCtorMap prbReplayCtorEnv
    prbReplayRecEnv ?_ ?_ ?_ ?_ ⟨rfl⟩
  · exact {
      info := propRecursiveBoundaryInfo
      kind_eq := by
        simp [propRecursiveBoundaryInfo, InductConstantKind.Matches]
      tr := prbInfo_tr
      map_fresh := prbReplayType_fresh
      env_add := prbTypeEnv_add
      map_add := rfl }
  · exact .cons {
      info := propRecursiveBoundaryMkInfo
      kind_eq := by
        simp [propRecursiveBoundaryMkInfo, InductConstantKind.Matches]
      tr := prbMkInfo_tr
      map_fresh := by
        simpa [propRecursiveBoundaryType] using prbReplayMk_fresh
      env_add := rfl
      map_add := rfl } .nil
  · exact {
      info := propRecursiveBoundaryRecInfo
      kind_eq := by
        simp [propRecursiveBoundaryRecInfo, InductConstantKind.Matches]
      tr := prbRecInfo_tr
      map_fresh := by
        rw [show
          (inductGenerationRecVal
            prbProducedGenerationCandidatePackage.package.generation).name =
              ``PropRecursiveBoundary.rec by rfl]
        exact prbReplayRec_fresh
      env_add := rfl
      map_add := rfl }
  · decide

theorem prb_addInduct_checked :
    AddInduct ({} : ConstMap) VEnv.empty propRecursiveBoundaryDecl
      prbReplayMap prbCertifiedFinalEnv :=
  ⟨prbAddInductTraceChecked⟩

theorem prb_trEnv'_checked :
    TrEnv' .safe prbReplayMap false prbCertifiedFinalEnv :=
  .induct prb_addInduct_checked .empty

theorem prb_env_wf_checked : prbCertifiedFinalEnv.WF :=
  prb_trEnv'_checked.wf

theorem prb_aligned_checked :
    Aligned .safe prbReplayMap prbCertifiedFinalEnv :=
  prb_trEnv'_checked.aligned

theorem prbReplay_type_map_lookup :
    prbReplayMap.find? propRecursiveBoundaryType.name =
      some propRecursiveBoundaryInfo := by
  rw [prbReplayMap, prbReplayCtorMap_wf.find?_insert,
    prbReplayCtorMap, prbReplayTypeMap_wf.find?_insert,
    prbReplayTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [propRecursiveBoundaryType]

theorem prbReplay_ctor_map_lookup :
    prbReplayMap.find? propRecursiveBoundaryType.ctors[0].name =
      some propRecursiveBoundaryMkInfo := by
  rw [prbReplayMap, prbReplayCtorMap_wf.find?_insert,
    prbReplayCtorMap, prbReplayTypeMap_wf.find?_insert]
  simp [propRecursiveBoundaryType]

theorem prbReplay_rec_map_lookup :
    prbReplayMap.find? ``PropRecursiveBoundary.rec =
      some propRecursiveBoundaryRecInfo := by
  rw [prbReplayMap, prbReplayCtorMap_wf.find?_insert]
  simp

theorem prbFinalEnv_type_lookup :
    prbCertifiedFinalEnv.constants propRecursiveBoundaryType.name =
      some propRecursiveBoundaryType.toVConstant := by
  rcases prbCertified_trace with ⟨trace⟩
  exact trace.family_lookup

theorem prbFinalEnv_ctor_lookup :
    prbCertifiedFinalEnv.constants propRecursiveBoundaryType.ctors[0].name =
      some propRecursiveBoundaryType.ctors[0].toVConstant := by
  rcases prbCertified_trace with ⟨trace⟩
  exact trace.ctor_lookup (.head _)

theorem prbFinalEnv_rec_lookup :
    prbCertifiedFinalEnv.constants ``PropRecursiveBoundary.rec =
      some propRecursiveBoundaryGenerationChecked.recursor := by
  rcases prbCertified_trace with ⟨trace⟩
  exact trace.rec_lookup

theorem prbReplay_type_lookup_unique :
    propRecursiveBoundaryInfo.name = propRecursiveBoundaryType.name ∧
      TrConstant .safe prbCertifiedFinalEnv propRecursiveBoundaryInfo
        propRecursiveBoundaryType.toVConstant :=
  prb_aligned_checked.find?_uniq prbReplay_type_map_lookup
    prbFinalEnv_type_lookup

theorem prbReplay_ctor_lookup_unique :
    propRecursiveBoundaryMkInfo.name =
        propRecursiveBoundaryType.ctors[0].name ∧
      TrConstant .safe prbCertifiedFinalEnv propRecursiveBoundaryMkInfo
        propRecursiveBoundaryType.ctors[0].toVConstant :=
  prb_aligned_checked.find?_uniq prbReplay_ctor_map_lookup
    prbFinalEnv_ctor_lookup

theorem prbReplay_rec_lookup_unique :
    propRecursiveBoundaryRecInfo.name = ``PropRecursiveBoundary.rec ∧
      TrConstant .safe prbCertifiedFinalEnv propRecursiveBoundaryRecInfo
        propRecursiveBoundaryGenerationChecked.recursor :=
  prb_aligned_checked.find?_uniq prbReplay_rec_map_lookup
    prbFinalEnv_rec_lookup

theorem prbFinalEnv_rule_mem :
    ∀ df ∈ propRecursiveBoundaryGenerationChecked.generatedRules,
      prbCertifiedFinalEnv.defeqs df := by
  intro df hdf
  rcases prbCertified_trace with ⟨trace⟩
  exact trace.rule_mem hdf

theorem prbFinalEnv_iota_mem :
    prbCertifiedFinalEnv.defeqs
      propRecursiveBoundaryGenerationChecked.generatedRules[0] := by
  apply prbFinalEnv_rule_mem
  exact .head _

end Lean4Lean.InductiveReplayFixtures
