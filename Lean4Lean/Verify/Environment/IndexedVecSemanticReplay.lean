import Lean4Lean.Verify.Environment.IndexedVecOuterReplay

/-!
# Complete semantic replay of the IndexedVec normalization candidate

This module connects the exact executable family/`nil`/`cons` candidate
produced by `buildNormalizationCandidate` to its Theory generation
certificate and the E1 kernel-environment replay. Every retained candidate
node is interpreted in its exact pre-family or post-family verifier context;
the final transaction therefore consumes the certificate projected from the
same producer-selected package rather than an independently supplied
well-formedness proof.
-/

namespace Lean4Lean.InductiveReplayFixtures
open Lean Meta
open Lean4Lean.InductiveFixtures
open IndexedVecConsReplay

theorem indexedVecSemanticNatHasPrimitives : VEnv.HasPrimitives natFinalEnv := by
  have absent (n : Name) (hlookup : natFinalEnv.constants n = none) :
      ¬ natFinalEnv.contains n := by
    rintro ⟨ci, hci⟩
    rw [hlookup] at hci
    contradiction
  refine {
    bool := fun h => (absent ``Bool rfl h).elim
    boolFalse := fun h => by
      change none = some _ at h
      contradiction
    boolTrue := fun h => by
      change none = some _ at h
      contradiction
    nat := fun _ => ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    natZero := fun h => by
      change some natType.ctors[0].toVConstant = some _ at h
      exact (Option.some.inj h).symm
    natSucc := fun h => by
      change some natType.ctors[1].toVConstant = some _ at h
      exact (Option.some.inj h).symm
    natAdd := fun h => (absent ``Nat.add rfl h).elim
    natSub := fun h => (absent ``Nat.sub rfl h).elim
    natMul := fun h => (absent ``Nat.mul rfl h).elim
    natPow := fun h => (absent ``Nat.pow rfl h).elim
    natGcd := fun h => (absent ``Nat.gcd rfl h).elim
    natMod := fun h => (absent ``Nat.mod rfl h).elim
    natDiv := fun h => (absent ``Nat.div rfl h).elim
    natBEq := fun h => (absent ``Nat.beq rfl h).elim
    natBLE := fun h => (absent ``Nat.ble rfl h).elim
    natLAnd := fun h => (absent ``Nat.land rfl h).elim
    natLOr := fun h => (absent ``Nat.lor rfl h).elim
    natXor := fun h => (absent ``Nat.xor rfl h).elim
    natShiftLeft := fun h => (absent ``Nat.shiftLeft rfl h).elim
    natShiftRight := fun h => (absent ``Nat.shiftRight rfl h).elim
    charOfNat := fun h => by
      change none = some _ at h
      contradiction
    stringOfList := fun h => by
      change none = some _ at h
      contradiction }

theorem indexedVecSemanticNatSafePrimitives :
    indexedVecKernelEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  change natMap.find?' n = some ci at hfind
  rw [natMap_wf.find?'_eq_find?, natMap,
    natCtorMap_wf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    simp at heq
    subst n
    simp at hfind
    subst ci
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
    simp +decide [NameSet.contains] at hprim
  · rw [natCtorMap, natZeroMap_wf.find?_insert] at hfind
    split at hfind
    · rename_i heq
      simp at heq
      subst n
      simp at hfind
      subst ci
      exact ⟨rfl, rfl⟩
    · rw [natZeroMap, natTypeMap_wf.find?_insert] at hfind
      split at hfind
      · rename_i heq
        simp at heq
        subst n
        simp at hfind
        subst ci
        exact ⟨rfl, rfl⟩
      · rw [natTypeMap,
          SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
          at hfind
        split at hfind
        · rename_i heq
          simp at heq
          subst n
          simp at hfind
          subst ci
          exact ⟨rfl, rfl⟩
        · simp [SMap.find?] at hfind

def indexedVecSemanticNatVEnvs : VEnvs where
  venv _ := natFinalEnv

theorem indexedVecSemanticNatVEnvsWF : indexedVecSemanticNatVEnvs.WF indexedVecKernelEnv where
  tr := by
    intro safety
    change TrEnv' _ natMap false natFinalEnv
    exact nat_trEnv'.sf_mono DefinitionSafety.le_safe
  hasPrimitives := indexedVecSemanticNatHasPrimitives
  safePrimitives := indexedVecSemanticNatSafePrimitives
  mono := fun _ => .rfl

def indexedVecSemanticAddType :
    AddInductConstant .induct natMap natFinalEnv
      indexedVecType.toVConstVal indexedVecTypeMap indexedVecTypeEnv where
  info := indexedVecInfo
  kind_eq := by simp [indexedVecInfo, InductConstantKind.Matches]
  tr := indexedVecInfo_tr
  map_fresh := by simpa [indexedVecType] using indexedVecType_fresh
  env_add := rfl
  map_add := rfl

theorem indexedVecSemanticFamilyPrefixNe :
    indexedVecFamilyCandidateContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def indexedVecSemanticFamilyContextRun :
    TypeChecker.CandidateContextRun indexedVecFamilyCandidateContext :=
  TypeChecker.CandidateContextRun.root indexedVecSemanticNatVEnvsWF rfl
    indexedVecSemanticFamilyPrefixNe

theorem indexedVecSemanticFamilySourceTr :
    TrExprS natFinalEnv [`u] [] indexedVecInfo.type indexedVecType.type :=
  indexedVecInfo_tr.1.2.2

def indexedVecPreFamilyStage :
    TypeChecker.CandidateSemanticStage indexedVecFamilyCandidateContext
      natFinalEnv [`u] where
  contextRun := indexedVecSemanticFamilyContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

def indexedVecFamilyValidationRun :
    AddInductive.CandidateExprTrace.FamilyValidationRun
      indexedVecKernelType indexedVecFamilyCandidate.trace where
  nparams := 1
  resultLevel := .succ (.param `u)
  stats := indexedVecCandidateInductiveStats
  stats_eq := rfl
  terminal_eq := indexedVecFamilyCandidate_terminalResult
  run := indexedVec_checkInductiveTypes

def indexedVecFamilyStage :
    VInductDecl.CandidateFamilyStagedInput
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecFamilyListCandidate.familyType indexedVecType
      indexedVecPreFamilyStage where
  name_eq := rfl
  uvars_eq := rfl
  type := {
    context_eq := rfl
    source_tr := indexedVecSemanticFamilySourceTr
    whnfFuel := 9999
    whnfDepth := rfl }
  validation := indexedVecFamilyValidationRun
  typeEnv := indexedVecTypeEnv
  addInduct := indexedVecSemanticAddType
  family_lctx_eq := rfl
  constructorContext_eq := rfl
  quotInit_eq := rfl
  name_not_reflected := by decide
  name_not_primitive := by
    simp [indexedVecType, Kernel.Environment.primitives,
      NameSet.ofList]
    simp +decide [NameSet.contains]

def indexedVecSemanticCtorContextRun :
    TypeChecker.CandidateContextRun ctorContext :=
  indexedVecFamilyStage.postContextRun

theorem indexedVecSemanticNilSourceTr :
    TrExprS indexedVecTypeEnv [`u] [] indexedVecNilInfo.type
      indexedVecType.ctors[0].type :=
  indexedVecNilInfo_tr.1.2.2

theorem indexedVecSemanticConsIsType :
    indexedVecTypeEnv.IsType 1 [] indexedVecType.ctors[1].type := by
  have hwf :=
    (indexedVecChecked.wf_of_decl indexedVecDecl_wf).identityGeneration
      nat_env_wf.ordered
  have hctor := hwf.rawCtor_isType (envT := indexedVecTypeEnv) rfl
    (ctor := indexedVecChecked.identityGeneration.block.ctorPairs[1])
    (by simp)
  simpa only [
    show indexedVecDecl.uvars = 1 by rfl,
    show indexedVecChecked.identityGeneration.block.ctorPairs[1].raw.type =
      indexedVecType.ctors[1].type by rfl] using hctor

theorem indexedVecSemanticConsSourceTr :
    TrExprS indexedVecTypeEnv [`u] [] indexedVecConsInfo.type
      indexedVecType.ctors[1].type := by
  have hshape : TrTypeExpr indexedVecTypeEnv [`u] []
      indexedVecConsInfo.type indexedVecType.ctors[1].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := indexedVecSemanticConsIsType
  exact hshape.to_trExprS indexedVecTypeEnv_ordered trivial
    ⟨.sort u, htype⟩

noncomputable def indexedVecStagedSemanticInput :
    VInductDecl.StagedNormalizationCandidateSemanticInput
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl where
  raw := indexedVecType
  raw_types_eq := rfl
  declaration_uvars_eq := rfl
  preFamily := indexedVecPreFamilyStage
  family := indexedVecFamilyStage
  constructorValidation :=
    AddInductive.ConstructorValidationRun.of_run
      indexedVecValidationCheckConstructors
  constructors := .cons {
    name_eq := rfl
    uvars_eq := rfl
    type := {
      context_eq := rfl
      source_tr := indexedVecSemanticNilSourceTr
      whnfFuel := 9999
      whnfDepth := rfl } } (.cons {
    name_eq := rfl
    uvars_eq := rfl
    type := {
      context_eq := rfl
      source_tr := indexedVecSemanticConsSourceTr
      whnfFuel := 9999
      whnfDepth := rfl } } .nil)
  familyTypesProduced := indexedVecFamilyTypeListProduced
  familiesProduced := indexedVecFamilyListProduced

/-- Generic automatic assembly joins the arbitrary-length operational list
witnesses to the complete retained semantic hierarchy for the two-constructor
fixture.  No expected normalized view is an input to this theorem. -/
theorem indexedVecProducedSemanticHierarchy_exists :
    Nonempty (VInductDecl.ProducedNormalizationCandidateSemanticRun
      indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl) :=
  indexedVecStagedSemanticInput.exists

/-- The automatically assembled hierarchy retains both constructor headers in
the producer's `nil`/`cons` source order.  This inspects the semantic result,
not the separately constructed concrete replay below. -/
theorem indexedVecProducedSemanticHierarchy_constructorHeaders :
    ∃ run : VInductDecl.ProducedNormalizationCandidateSemanticRun
        indexedVecFamilyCandidateContext ctorContext natFinalEnv [`u]
        indexedVecNormalizationCandidate indexedVecDecl,
      VInductDecl.sameCtorHeaders indexedVecType.ctors
        run.semantic.family.root.constructors.views = true := by
  obtain ⟨run⟩ := indexedVecProducedSemanticHierarchy_exists
  have hraw : run.semantic.raw = indexedVecType := by
    have htypes : [indexedVecType] = [run.semantic.raw] := by
      simpa [indexedVecDecl] using run.semantic.raw_types_eq
    injection htypes with h
    exact h.symm
  exact ⟨run, by
    simpa only [hraw] using
      run.semantic.family.root.constructors.sameHeaders⟩

private def indexedVecReorderedViewType : VInductiveType :=
  { indexedVecType with
    ctors := [indexedVecType.ctors[1], indexedVecType.ctors[0]] }

private def indexedVecReorderedViewDecl : VInductDecl :=
  { indexedVecDecl with types := [indexedVecReorderedViewType] }

/-- Swapping the two otherwise unchanged constructor payloads fails the
computational normalization-shape gate before semantic or generation evidence
can be attached. -/
theorem indexedVecReorderedView_rejected :
    VInductDecl.normalization? indexedVecDecl
      indexedVecReorderedViewDecl = none := rfl

theorem indexedVecSemanticFamilyViewTr :
    TrExpr natFinalEnv [`u] [] indexedVecFamilyCandidate.view
      indexedVecType.type := by
  rw [indexedVecFamilyCandidate_view_eq]
  obtain ⟨u, htype⟩ := indexedVecType_wf
  exact ⟨_, indexedVecSemanticFamilySourceTr, ⟨_, htype⟩⟩

theorem indexedVecSemanticNilViewTr :
    TrExpr indexedVecTypeEnv [`u] [] nilCandidate.view
      indexedVecType.ctors[0].type := by
  rw [nilCandidate_view_eq]
  obtain ⟨u, htype⟩ := indexedVecNil_wf
  exact ⟨_, indexedVecSemanticNilSourceTr, ⟨_, htype⟩⟩

theorem indexedVecSemanticConsViewTr :
    TrExpr indexedVecTypeEnv [`u] [] consCandidate.view
      indexedVecType.ctors[1].type := by
  rw [consCandidate_view_eq]
  obtain ⟨u, htype⟩ := indexedVecSemanticConsIsType
  exact ⟨_, indexedVecSemanticConsSourceTr, ⟨_, htype⟩⟩

def indexedVecSemanticFamilyRootRun :
    TypeChecker.CandidateExprRootRun natFinalEnv [`u]
      indexedVecFamilyCandidate indexedVecType.type indexedVecType.type where
  contextRun := indexedVecSemanticFamilyContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := indexedVecSemanticFamilySourceTr
  view_tr := indexedVecSemanticFamilyViewTr
  whnfFuel := 9999
  whnfDepth := rfl

def indexedVecSemanticNilRootRun :
    TypeChecker.CandidateExprRootRun indexedVecTypeEnv [`u]
      nilCandidate indexedVecType.ctors[0].type
      indexedVecType.ctors[0].type where
  contextRun := by
    simpa [nilCandidate, nilCandidateContext] using indexedVecSemanticCtorContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := indexedVecSemanticNilSourceTr
  view_tr := indexedVecSemanticNilViewTr
  whnfFuel := 9999
  whnfDepth := rfl

def indexedVecSemanticConsRootRun :
    TypeChecker.CandidateExprRootRun indexedVecTypeEnv [`u]
      consCandidate indexedVecType.ctors[1].type
      indexedVecType.ctors[1].type where
  contextRun := by
    simpa [consCandidate, consRootContext] using indexedVecSemanticCtorContextRun
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  source_tr := indexedVecSemanticConsSourceTr
  view_tr := indexedVecSemanticConsViewTr
  whnfFuel := 9999
  whnfDepth := rfl

def indexedVecSemanticFamilySemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun natFinalEnv [`u]
      indexedVecFamilyCandidate indexedVecType.type :=
  indexedVecSemanticFamilyRootRun.semanticOfIdentity
    indexedVecFamilyCandidate_identity

def indexedVecSemanticNilSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun indexedVecTypeEnv [`u]
      nilCandidate indexedVecType.ctors[0].type :=
  indexedVecSemanticNilRootRun.semanticOfIdentity nilCandidate_identity

def indexedVecSemanticConsSemanticRootRun :
    TypeChecker.CandidateExprSemanticRootRun indexedVecTypeEnv [`u]
      consCandidate indexedVecType.ctors[1].type :=
  indexedVecSemanticConsRootRun.semanticOfIdentity consCandidate_identity

def indexedVecSemanticNilConstructorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun indexedVecTypeEnv [`u]
      indexedVecNilConstructorCandidate indexedVecType.ctors[0] where
  name_eq := rfl
  uvars_eq := rfl
  type := indexedVecSemanticNilSemanticRootRun

def indexedVecSemanticConsConstructorSemanticRun :
    VInductDecl.CandidateConstructorSemanticRun indexedVecTypeEnv [`u]
      indexedVecConsConstructorCandidate indexedVecType.ctors[1] where
  name_eq := rfl
  uvars_eq := rfl
  type := indexedVecSemanticConsSemanticRootRun

def indexedVecSemanticNilConstructorRun :
    VInductDecl.CandidateConstructorRun indexedVecTypeEnv [`u]
      indexedVecNilConstructorCandidate indexedVecType.ctors[0] :=
  indexedVecSemanticNilConstructorSemanticRun.root

def indexedVecSemanticConsConstructorRun :
    VInductDecl.CandidateConstructorRun indexedVecTypeEnv [`u]
      indexedVecConsConstructorCandidate indexedVecType.ctors[1] :=
  indexedVecSemanticConsConstructorSemanticRun.root

def indexedVecSemanticConstructorSemanticListRun :
    VInductDecl.CandidateConstructorSemanticListRun indexedVecTypeEnv [`u]
      indexedVecFamilyListCandidate.constructors indexedVecType.ctors := by
  exact .cons indexedVecSemanticNilConstructorSemanticRun
    (.cons indexedVecSemanticConsConstructorSemanticRun .nil)

def indexedVecSemanticConstructorListRun :
    VInductDecl.CandidateConstructorListRun indexedVecTypeEnv [`u]
      indexedVecFamilyListCandidate.constructors indexedVecType.ctors :=
  indexedVecSemanticConstructorSemanticListRun.roots

def indexedVecSemanticFamilySemanticRun :
    VInductDecl.CandidateFamilySemanticRun natFinalEnv [`u]
      indexedVecFamilyListCandidate indexedVecType where
  name_eq := rfl
  uvars_eq := rfl
  type := indexedVecSemanticFamilySemanticRootRun
  typeEnv := indexedVecTypeEnv
  addType := rfl
  constructors := indexedVecSemanticConstructorSemanticListRun

def indexedVecSemanticFamilyRun :
    VInductDecl.CandidateFamilyRun natFinalEnv [`u]
      indexedVecFamilyListCandidate indexedVecType :=
  indexedVecSemanticFamilySemanticRun.root

/-- Temporary L4L-01A compatibility witness. The two-stage owner proves a
semantic run exists without choosing this concrete identity value; L4L-01E
removes the explicit downstream witness. -/
def indexedVecSemanticNormalizationCandidateSemanticRun :
    VInductDecl.NormalizationCandidateSemanticRun natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl where
  raw := indexedVecType
  raw_types_eq := rfl
  uvars_eq := rfl
  family := indexedVecSemanticFamilySemanticRun

def indexedVecSemanticNormalizationCandidateRun :
    VInductDecl.NormalizationCandidateRun natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl :=
  indexedVecSemanticNormalizationCandidateSemanticRun.root

/-- Reconstructing every family and constructor payload leaves the identity
IndexedVec declaration unchanged. -/
theorem indexedVecSemantic_viewDecl_eq :
    indexedVecSemanticNormalizationCandidateRun.viewDecl =
      indexedVecDecl := rfl

/-- The candidate-derived normalization is exactly the analyzer's canonical
identity normalization, not merely propositionally interchangeable with it. -/
theorem indexedVecSemantic_normalization_eq :
    indexedVecSemanticNormalizationCandidateRun.normalization =
      indexedVecChecked.identityGeneration.block.normalization := rfl

def indexedVecSemanticFamilySpineRun :
    TypeChecker.CandidateExprSpineRun natFinalEnv [`u]
      indexedVecFamilyCandidate indexedVecType.type
      indexedVecType.type :=
  indexedVecSemanticFamilySemanticRootRun.spine
    indexedVecFamilyCandidate_identity.storedSpine

def indexedVecSemanticNilSpineRun :
    TypeChecker.CandidateExprSpineRun indexedVecTypeEnv [`u]
      nilCandidate indexedVecType.ctors[0].type
      indexedVecType.ctors[0].type :=
  indexedVecSemanticNilSemanticRootRun.spine
    nilCandidate_identity.storedSpine

def indexedVecSemanticConsSpineRun :
    TypeChecker.CandidateExprSpineRun indexedVecTypeEnv [`u]
      consCandidate indexedVecType.ctors[1].type
      indexedVecType.ctors[1].type :=
  indexedVecSemanticConsSemanticRootRun.spine
    consCandidate_identity.storedSpine

theorem indexedVecSemanticCandidate_generationShape :
    indexedVecSemanticNormalizationCandidateSemanticRun.generationShape =
      true := by
  change ((indexedVecFamilyCandidate.trace.storedSpine && true) &&
    ((nilCandidate.trace.storedSpine && true) &&
      ((consCandidate.trace.storedSpine && true) && true))) = true
  rw [indexedVecFamilyCandidate_identity.storedSpine,
    nilCandidate_identity.storedSpine,
    consCandidate_identity.storedSpine]
  rfl

/-- The consolidated constructor gate rejects truncation in either direction
before dependent semantic generation is assembled. -/
theorem indexedVecSemanticCandidate_missingRawShape_rejected :
    VInductDecl.candidateConstructorSemanticGenerationShape indexedVecDecl
      (.cons indexedVecNilConstructorCandidate .nil) [] = false :=
  rfl

theorem indexedVecSemanticCandidate_extraRawShape_rejected :
    VInductDecl.candidateConstructorSemanticGenerationShape indexedVecDecl
      .nil [indexedVecType.ctors[0]] = false :=
  rfl

/-- Temporary L4L-01A view-WF compatibility premise. L4L-01D derives this
from retained validation and L4L-01E removes it from package construction. -/
theorem indexedVecSemanticCandidate_viewDecl_wf :
    indexedVecSemanticNormalizationCandidateRun.viewDecl.WF natFinalEnv := by
  change indexedVecDecl.WF natFinalEnv
  exact indexedVecDecl_wf

def indexedVecSemanticProducedGenerationShapeCandidate :
    VInductDecl.ProducedGenerationShapeCandidate indexedVecDecl indexedVecType
      indexedVecKernelType 0 false indexedVecFamilyCandidateContext where
  candidate := indexedVecNormalizationCandidate
  produced := indexedVecNormalizationCandidateProduced
  shape := indexedVecSemanticCandidate_generationShape

/-- The strengthened outer gate retains the complete parameter/index and
ordered `nil`/`cons` generation layout in the same produced result. -/
theorem indexedVecSemanticGenerationShapeCandidate_produced :
    VInductDecl.produceGenerationShapeCandidate indexedVecDecl indexedVecType
      indexedVecKernelType 0 false indexedVecFamilyCandidateContext =
        .ok indexedVecSemanticProducedGenerationShapeCandidate := by
  have produced :
      AddInductive.buildNormalizationCandidate indexedVecDecl.nparams
          [indexedVecKernelType] 0 false indexedVecFamilyCandidateContext =
        .ok indexedVecNormalizationCandidate :=
    indexedVecNormalizationCandidateProduced
  simpa only [indexedVecSemanticProducedGenerationShapeCandidate] using
    VInductDecl.produceGenerationShapeCandidate_eq_ok
      (source := indexedVecDecl) (raw := indexedVecType)
      produced indexedVecSemanticCandidate_generationShape

def indexedVecSemanticGenerationCandidateSemanticRun :
    VInductDecl.GenerationCandidateSemanticRun
      indexedVecSemanticNormalizationCandidateSemanticRun
      indexedVecChecked.identityGeneration :=
  VInductDecl.GenerationCandidateSemanticRun.ofGenerationShape
    indexedVecSemanticNormalizationCandidateSemanticRun
    indexedVecChecked.identityGeneration rfl
    indexedVecSemanticCandidate_viewDecl_wf
    indexedVecSemanticCandidate_generationShape

def indexedVecSemanticGenerationCandidateRun :
    VInductDecl.GenerationCandidateRun
      indexedVecSemanticNormalizationCandidateRun
      indexedVecChecked.identityGeneration :=
  indexedVecSemanticGenerationCandidateSemanticRun.run

def indexedVecSemanticGenerationCandidatePackage :
    VInductDecl.GenerationCandidatePackage natFinalEnv [`u] :=
  indexedVecSemanticGenerationCandidateSemanticRun.package

def indexedVecSemanticProducedGenerationCandidatePackage :
    VInductDecl.ProducedGenerationCandidatePackage natFinalEnv [`u] :=
  indexedVecSemanticProducedGenerationShapeCandidate.producedPackage
    indexedVecSemanticNormalizationCandidateSemanticRun rfl
    indexedVecChecked.identityGeneration rfl
    indexedVecSemanticCandidate_viewDecl_wf

def indexedVecSemanticGenerationCertificate :
    indexedVecDecl.GenerationCertificate natFinalEnv :=
  indexedVecSemanticProducedGenerationCandidatePackage.package.certificate

theorem indexedVecSemantic_addInductCertified :
    natFinalEnv.addInductCertified indexedVecSemanticGenerationCertificate =
      some indexedVecFinalEnv := by
  rfl

theorem indexedVecSemanticCertified_trace :
    Nonempty (VEnv.AddInductGenerationTrace natFinalEnv
      indexedVecFinalEnv indexedVecChecked.identityGeneration) :=
  VEnv.addInductCertified_trace indexedVecSemantic_addInductCertified

theorem indexedVecSemanticCertified_ordered :
    indexedVecFinalEnv.Ordered :=
  VEnv.addInductCertified_WF nat_env_wf.ordered
    indexedVecSemantic_addInductCertified

def indexedVecSemanticAddInductTraceChecked :
    AddInductTrace natMap natFinalEnv indexedVecDecl indexedVecMap
      indexedVecFinalEnv := by
  refine indexedVecSemanticProducedGenerationCandidatePackage.package.addInductTrace
    indexedVecTypeMap indexedVecTypeEnv indexedVecCtorMap
    indexedVecCtorEnv indexedVecRecEnv ?_ ?_ ?_ ⟨rfl⟩
  · exact {
      info := indexedVecInfo
      kind_eq := by simp [indexedVecInfo, InductConstantKind.Matches]
      tr := indexedVecInfo_tr
      map_fresh := by
        rw [show
          indexedVecSemanticProducedGenerationCandidatePackage.package.generation.block.sourceType.name =
            ``IndexedVec by rfl]
        exact indexedVecType_fresh
      env_add := rfl
      map_add := rfl }
  · refine .cons (m₂ := indexedVecNilMap)
      (env₂ := indexedVecNilEnv) ?_ ?_
    · exact {
        info := indexedVecNilInfo
        kind_eq := by simp [indexedVecNilInfo, InductConstantKind.Matches]
        tr := indexedVecNilInfo_tr
        map_fresh := by simpa [indexedVecType] using indexedVecNil_fresh
        env_add := rfl
        map_add := rfl }
    · refine .cons ?_ .nil
      exact {
        info := indexedVecConsInfo
        kind_eq := by simp [indexedVecConsInfo, InductConstantKind.Matches]
        tr := indexedVecConsInfo_tr
        map_fresh := by simpa [indexedVecType] using indexedVecCons_fresh
        env_add := rfl
        map_add := rfl }
  · exact {
      info := indexedVecRecInfo
      kind_eq := by simp [indexedVecRecInfo, InductConstantKind.Matches]
      tr := indexedVecRecInfo_tr
      map_fresh := by
        rw [show
          (inductGenerationRecVal
            indexedVecSemanticProducedGenerationCandidatePackage.package.generation).name =
              ``IndexedVec.rec by rfl]
        exact indexedVecRec_fresh
      env_add := rfl
      map_add := rfl }

theorem indexedVecSemantic_addInduct_checked :
    AddInduct natMap natFinalEnv indexedVecDecl indexedVecMap
      indexedVecFinalEnv :=
  ⟨indexedVecSemanticAddInductTraceChecked⟩

theorem indexedVecSemantic_trEnv'_checked :
    TrEnv' .safe indexedVecMap false indexedVecFinalEnv :=
  .induct indexedVecSemantic_addInduct_checked nat_trEnv'

theorem indexedVecSemantic_env_wf_checked : indexedVecFinalEnv.WF :=
  indexedVecSemantic_trEnv'_checked.wf

theorem indexedVecSemantic_aligned_checked :
    Aligned .safe indexedVecMap indexedVecFinalEnv :=
  indexedVecSemantic_trEnv'_checked.aligned

/-
The semantic assembly, executable producer, and final E1 replay intentionally
inherit the existing transitional verifier closure. These guards make
additions to that closure visible at the public roots of this module.
-/
/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecProducedSemanticHierarchy_exists' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
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
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecProducedSemanticHierarchy_exists

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecProducedSemanticHierarchy_constructorHeaders' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
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
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecProducedSemanticHierarchy_constructorHeaders

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecReorderedView_rejected' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms indexedVecReorderedView_rejected

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemanticCandidate_missingRawShape_rejected' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemanticCandidate_missingRawShape_rejected

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemanticCandidate_extraRawShape_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms indexedVecSemanticCandidate_extraRawShape_rejected

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemanticGenerationShapeCandidate_produced' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
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
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemanticGenerationShapeCandidate_produced

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemanticGenerationCandidateSemanticRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
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
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemanticGenerationCandidateSemanticRun

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemanticProducedGenerationCandidatePackage' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
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
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemanticProducedGenerationCandidatePackage

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecSemantic_trEnv'_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
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
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemantic_trEnv'_checked

end Lean4Lean.InductiveReplayFixtures
