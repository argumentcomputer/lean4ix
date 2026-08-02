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

theorem indexedVecSemanticTypeTrEnv' :
    TrEnv' .safe indexedVecTypeMap false indexedVecTypeEnv :=
  .inductStaging indexedVecSemanticAddType indexedVecType_wf nat_trEnv'

theorem indexedVecSemanticTypeHasPrimitives :
    VEnv.HasPrimitives indexedVecTypeEnv := by
  have absent (n : Name) (hlookup : indexedVecTypeEnv.constants n = none) :
      ¬ indexedVecTypeEnv.contains n := by
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

theorem indexedVecSemanticTypeSafePrimitives :
    ctorEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  change indexedVecTypeMap.find?' n = some ci at hfind
  rw [indexedVecTypeMap_wf.find?'_eq_find?, indexedVecTypeMap,
    natMap_wf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    simp at heq
    subst n
    simp at hfind
    subst ci
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
    simp +decide [NameSet.contains] at hprim
  · apply indexedVecSemanticNatSafePrimitives (n := n) (ci := ci)
    · change natMap.find?' n = some ci
      rw [natMap_wf.find?'_eq_find?]
      exact hfind
    · exact hprim

def indexedVecSemanticTypeVEnvs : VEnvs where
  venv _ := indexedVecTypeEnv

theorem indexedVecSemanticTypeVEnvsWF :
    indexedVecSemanticTypeVEnvs.WF ctorEnv where
  tr := by
    intro safety
    change TrEnv' _ indexedVecTypeMap false indexedVecTypeEnv
    exact indexedVecSemanticTypeTrEnv'.sf_mono DefinitionSafety.le_safe
  hasPrimitives := indexedVecSemanticTypeHasPrimitives
  safePrimitives := indexedVecSemanticTypeSafePrimitives
  mono := fun _ => .rfl

theorem indexedVecSemanticFamilyPrefixNe :
    indexedVecFamilyCandidateContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def indexedVecSemanticFamilyContextRun :
    TypeChecker.CandidateContextRun indexedVecFamilyCandidateContext :=
  TypeChecker.CandidateContextRun.root indexedVecSemanticNatVEnvsWF rfl
    indexedVecSemanticFamilyPrefixNe

theorem indexedVecSemanticCtorPrefixNe :
    ctorContext.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix := by
  decide

def indexedVecSemanticCtorContextRun :
    TypeChecker.CandidateContextRun ctorContext :=
  TypeChecker.CandidateContextRun.root indexedVecSemanticTypeVEnvsWF rfl
    indexedVecSemanticCtorPrefixNe

theorem indexedVecSemanticFamilySourceTr :
    TrExprS natFinalEnv [`u] [] indexedVecInfo.type indexedVecType.type :=
  indexedVecInfo_tr.1.2.2

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
  simpa using hctor

theorem indexedVecSemanticConsSourceTr :
    TrExprS indexedVecTypeEnv [`u] [] indexedVecConsInfo.type
      indexedVecType.ctors[1].type := by
  have hshape : TrTypeExpr indexedVecTypeEnv [`u] []
      indexedVecConsInfo.type indexedVecType.ctors[1].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := indexedVecSemanticConsIsType
  exact hshape.to_trExprS indexedVecTypeEnv_ordered trivial
    ⟨.sort u, htype⟩

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

def indexedVecSemanticNilConstructorRun :
    VInductDecl.CandidateConstructorRun indexedVecTypeEnv [`u]
      indexedVecNilConstructorCandidate indexedVecType.ctors[0] where
  name_eq := rfl
  uvars_eq := rfl
  viewType := indexedVecType.ctors[0].type
  typeRun := indexedVecSemanticNilRootRun

def indexedVecSemanticConsConstructorRun :
    VInductDecl.CandidateConstructorRun indexedVecTypeEnv [`u]
      indexedVecConsConstructorCandidate indexedVecType.ctors[1] where
  name_eq := rfl
  uvars_eq := rfl
  viewType := indexedVecType.ctors[1].type
  typeRun := indexedVecSemanticConsRootRun

def indexedVecSemanticConstructorListRun :
    VInductDecl.CandidateConstructorListRun indexedVecTypeEnv [`u]
      indexedVecFamilyListCandidate.constructors indexedVecType.ctors := by
  exact .cons indexedVecSemanticNilConstructorRun
    (.cons indexedVecSemanticConsConstructorRun .nil)

def indexedVecSemanticFamilyRun :
    VInductDecl.CandidateFamilyRun natFinalEnv [`u]
      indexedVecFamilyListCandidate indexedVecType where
  name_eq := rfl
  uvars_eq := rfl
  viewType := indexedVecType.type
  typeRun := indexedVecSemanticFamilyRootRun
  typeEnv := indexedVecTypeEnv
  addType := rfl
  constructors := indexedVecSemanticConstructorListRun

def indexedVecSemanticNormalizationCandidateRun :
    VInductDecl.NormalizationCandidateRun natFinalEnv [`u]
      indexedVecNormalizationCandidate indexedVecDecl where
  raw := indexedVecType
  raw_types_eq := rfl
  uvars_eq := rfl
  family := indexedVecSemanticFamilyRun

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
  indexedVecSemanticFamilyRootRun.spineOfIdentity
    indexedVecFamilyCandidate_identity

def indexedVecSemanticNilSpineRun :
    TypeChecker.CandidateExprSpineRun indexedVecTypeEnv [`u]
      nilCandidate indexedVecType.ctors[0].type
      indexedVecType.ctors[0].type :=
  indexedVecSemanticNilRootRun.spineOfIdentity nilCandidate_identity

def indexedVecSemanticConsSpineRun :
    TypeChecker.CandidateExprSpineRun indexedVecTypeEnv [`u]
      consCandidate indexedVecType.ctors[1].type
      indexedVecType.ctors[1].type :=
  indexedVecSemanticConsRootRun.spineOfIdentity consCandidate_identity

def indexedVecSemanticFamilyGenerationRun :
    VInductDecl.CandidateFamilyGenerationRun
      indexedVecSemanticNormalizationCandidateRun
      indexedVecChecked.identityGeneration where
  spine := indexedVecSemanticFamilySpineRun
  rawTel := rfl
  viewTel := rfl
  rawResult := rfl
  viewResult := rfl
  rightType := VEnv.HasType.sort (by decide)

def indexedVecSemanticNilNormalizedCtor : VInductDecl.NormalizedCtor :=
  indexedVecChecked.identityGeneration.block.ctorPairs[0]

def indexedVecSemanticConsNormalizedCtor : VInductDecl.NormalizedCtor :=
  indexedVecChecked.identityGeneration.block.ctorPairs[1]

theorem indexedVecSemanticNilRightType :
    indexedVecTypeEnv.HasType 1
      (indexedVecSemanticNilNormalizedCtor.declaredBinders indexedVecDecl.nparams).reverse
      (indexedVecSemanticNilNormalizedCtor.resultTarget
        indexedVecChecked.identityGeneration.block)
      (.sort indexedVecChecked.resultLevel) := by
  have hwf :=
    (indexedVecChecked.wf_of_decl indexedVecDecl_wf).identityGeneration
      nat_env_wf.ordered
  have hctor := hwf.ctors indexedVecTypeEnv rfl
    (ctor := indexedVecSemanticNilNormalizedCtor) (by
      simp [indexedVecSemanticNilNormalizedCtor])
  simpa [indexedVecSemanticNilNormalizedCtor] using hctor.declaredResult.hasType.2

theorem indexedVecSemanticConsRightType :
    indexedVecTypeEnv.HasType 1
      (indexedVecSemanticConsNormalizedCtor.declaredBinders indexedVecDecl.nparams).reverse
      (indexedVecSemanticConsNormalizedCtor.resultTarget
        indexedVecChecked.identityGeneration.block)
      (.sort indexedVecChecked.resultLevel) := by
  have hwf :=
    (indexedVecChecked.wf_of_decl indexedVecDecl_wf).identityGeneration
      nat_env_wf.ordered
  have hctor := hwf.ctors indexedVecTypeEnv rfl
    (ctor := indexedVecSemanticConsNormalizedCtor) (by
      simp [indexedVecSemanticConsNormalizedCtor])
  simpa [indexedVecSemanticConsNormalizedCtor] using hctor.declaredResult.hasType.2

def indexedVecSemanticNilGenerationRun :
    VInductDecl.CandidateNormalizedCtorRun
      indexedVecChecked.identityGeneration.block indexedVecTypeEnv [`u]
      indexedVecSemanticNilConstructorRun indexedVecSemanticNilNormalizedCtor where
  raw_eq := rfl
  view_eq := rfl
  spine := indexedVecSemanticNilSpineRun
  rawTel := rfl
  viewTel := rfl
  rawResult := rfl
  viewResult := rfl
  rightType := indexedVecSemanticNilRightType

def indexedVecSemanticConsGenerationRun :
    VInductDecl.CandidateNormalizedCtorRun
      indexedVecChecked.identityGeneration.block indexedVecTypeEnv [`u]
      indexedVecSemanticConsConstructorRun indexedVecSemanticConsNormalizedCtor where
  raw_eq := rfl
  view_eq := rfl
  spine := indexedVecSemanticConsSpineRun
  rawTel := rfl
  viewTel := rfl
  rawResult := rfl
  viewResult := rfl
  rightType := indexedVecSemanticConsRightType

def indexedVecSemanticConstructorGenerationListRun :
    VInductDecl.CandidateNormalizedCtorListRun
      indexedVecChecked.identityGeneration.block indexedVecTypeEnv [`u]
      indexedVecSemanticConstructorListRun
      indexedVecChecked.identityGeneration.block.ctorPairs := by
  exact .cons indexedVecSemanticNilGenerationRun
    (.cons indexedVecSemanticConsGenerationRun .nil)

def indexedVecSemanticGenerationCandidateRun :
    VInductDecl.GenerationCandidateRun
      indexedVecSemanticNormalizationCandidateRun
      indexedVecChecked.identityGeneration where
  normalization_eq := rfl
  checked := indexedVecChecked.wf_of_decl indexedVecDecl_wf
  family := indexedVecSemanticFamilyGenerationRun
  typeEnv_wf := by
    simpa using indexedVecSemanticCtorContextRun.context.Ewf
  constructors := indexedVecSemanticConstructorGenerationListRun

def indexedVecSemanticGenerationCandidatePackage :
    VInductDecl.GenerationCandidatePackage natFinalEnv [`u] :=
  indexedVecSemanticGenerationCandidateRun.package

def indexedVecSemanticProducedGenerationCandidatePackage :
    VInductDecl.ProducedGenerationCandidatePackage natFinalEnv [`u] :=
  indexedVecSemanticGenerationCandidateRun.producedPackage
    indexedVecFamilyCandidateContext 1 0 false
    indexedVecNormalizationCandidateProduced

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
      map_fresh := by simpa [indexedVecType] using indexedVecType_fresh
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
        simpa [inductGenerationRecVal, indexedVecDecl,
          indexedVecType] using indexedVecRec_fresh
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
The executable producer and final E1 replay intentionally inherit the
existing transitional verifier closure. These guards make additions to that
closure visible at the two public roots of this module.
-/
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
 Expr.hasExprMVar_eq,
 Expr.hasFVar_eq,
 Expr.hasLevelMVar_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
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
 Expr.hasExprMVar_eq,
 Expr.hasFVar_eq,
 Expr.hasLevelMVar_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVecSemantic_trEnv'_checked

end Lean4Lean.InductiveReplayFixtures
