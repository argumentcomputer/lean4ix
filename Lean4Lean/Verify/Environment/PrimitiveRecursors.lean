import Lean4Lean.Verify.Environment.CandidateIdentityReplay
import Lean4Lean.Verify.Environment.ConstructorValidation
import Lean4Lean.Verify.Environment.NormalizationElimination
import Lean4Lean.Verify.Environment.Extension

/-!
# Primitive recursor replay

Structural reconstruction of the host recursor records generated for the
closed Bool/Nat primitive sources.  The proofs follow the retained producer
execution and expose only translation-visible headers; generated rule
payloads remain owned by `mkRecRules`.
-/

-- These executable replay proofs intentionally retain explicit reduction
-- inventories; narrowed trust contracts can make individual entries redundant.
set_option linter.unusedSimpArgs false

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace AddInductive.PrimitiveRecursorReplay

/-- Reconstruct the semantic generation environment from the exact family
and constructor insertion folds. -/
theorem generationEnv_of_insertion
    {source : VInductDecl} {generation : source.BlockGenerationChecked}
    {input blockEnv ctorEnv : VEnv}
    (inputOrdered : input.Ordered)
    (generationWF : generation.WF input blockEnv)
    (addTypes : AddInductConstants .induct inputMap input
      source.blockTypeConstants typeMap blockEnv)
    (addCtors : AddInductConstants .ctor typeMap blockEnv
      source.blockConstructorConstants ctorMap ctorEnv) :
    VInductDecl.BlockGenerationEnv generation ctorEnv := by
  have blockOrdered : blockEnv.Ordered := by
    apply VInductDecl.constFold_ordered source.blockTypeConstants inputOrdered
      ?_ addTypes.to_foldlM
    intro raw member
    simp only [VInductDecl.blockTypeConstants, List.mem_map] at member
    obtain ⟨family, familyMember, rfl⟩ := member
    have normalizedMember : family ∈ generation.families.map (·.raw) := by
      rw [generation.families_map_raw]
      exact familyMember
    obtain ⟨normalized, hnormalized, rawEq⟩ :=
      List.mem_map.1 normalizedMember
    subst family
    show input.IsType normalized.raw.uvars [] normalized.raw.type
    rw [generation.family_uvars hnormalized]
    exact generationWF.rawFamily_isType hnormalized
  have ctorOrdered : ctorEnv.Ordered := by
    apply VInductDecl.constFold_ordered source.blockConstructorConstants
      blockOrdered ?_ addCtors.to_foldlM
    intro raw member
    have normalizedMember : raw ∈ generation.flatCtors.map (·.ctor.raw) := by
      rw [generation.flatCtors_map_raw]
      exact member
    obtain ⟨constructor, constructorMember, rfl⟩ :=
      List.mem_map.1 normalizedMember
    show blockEnv.IsType constructor.ctor.raw.uvars []
      constructor.ctor.raw.type
    rw [generation.flatCtor_uvars constructorMember]
    exact generationWF.rawCtor_isType constructorMember
  apply generationWF.toBlockGenerationEnv
    (addTypes.le.trans addCtors.le) addCtors.le ctorOrdered
  · intro family familyMember
    apply addCtors.le.constants
    apply addTypes.lookup family.raw.toVConstVal
    simp only [VInductDecl.blockTypeConstants, List.mem_map]
    refine ⟨family.raw, ?_, rfl⟩
    rw [← generation.families_map_raw]
    exact List.mem_map.2 ⟨family, familyMember, rfl⟩
  · intro constructor constructorMember
    apply addCtors.lookup constructor.ctor.raw
    rw [← generation.flatCtors_map_raw]
    exact List.mem_map.2 ⟨constructor, constructorMember, rfl⟩

private theorem sortOne_data_hasExprMVar_false :
    (Expr.sort (.succ .zero)).data.hasExprMVar = false := by
  change (Expr.sort (.succ .zero)).hasExprMVar = false
  exact Expr.sort_hasExprMVar _

private theorem sortOne_data_hasLevelMVar_false :
    (Expr.sort (.succ .zero)).data.hasLevelMVar = false := by
  change (Expr.sort (.succ .zero)).hasLevelMVar = false
  rw [Expr.sort_hasLevelMVar, Level.hasMVar_eq]
  rfl

private theorem sortOne_data_hasFVar_false :
    (Expr.sort (.succ .zero)).data.hasFVar = false := by
  change (Expr.sort (.succ .zero)).hasFVar = false
  exact Expr.sort_hasFVar _

/-- Full checking of the canonical primitive family sort at every positive
recursive depth. -/
theorem checkTypeSortOne (context : AddInductive.Context) (n : Nat)
    (hdepth : context.fuel.recDepth = n + 1) :
    TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel
      (TypeChecker.checkType (.sort (.succ .zero))) =
        .ok (.sort (.succ (.succ .zero))) := by
  have hlevel : TypeChecker.Inner.checkLevel context.toTypeChecker
      (.succ .zero) = .ok () := by
    simp [TypeChecker.Inner.checkLevel, Level.getUndefParam,
      Level.forEach, Level.hasParam_eq, Level.hasParam']
    rfl
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType (.sort (.succ .zero)) false
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      context.toTypeChecker ({} : TypeChecker.State)) = _
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.sort (.succ .zero)) false
      (TypeChecker.Methods.withFuel n)
      context.toTypeChecker ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq,
    Expr.looseBVarRange', hlevel,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, ReaderT.pure, StateT.pure, Except.pure,
    StateT.run', Functor.map, Except.map,
    get, getThe, MonadStateOf.get, StateT.get,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    liftM, monadLift, MonadLift.monadLift, StateT.lift,
    readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read]

/-- WHNF of the canonical primitive family sort at every positive recursion depth. -/
theorem whnfSortOne (context : AddInductive.Context) (n : Nat)
    (hdepth : context.fuel.recDepth = n + 1) :
    TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel
      (TypeChecker.whnf (.sort (.succ .zero))) =
        .ok (.sort (.succ .zero)) := by
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.whnf (.sort (.succ .zero))
      (TypeChecker.Methods.withFuel context.fuel.recDepth)
      context.toTypeChecker ({} : TypeChecker.State)) = _
  rw [hdepth]
  rfl

/-- A successful canonical singleton family-validation observer already fixes
its statistics, terminal reader context, and the two fuel witnesses needed by
the recursive candidate pass.  No successful candidate execution is needed
to recover these facts. -/
theorem canonicalSingletonValidationStatsAndFuel
    {context : AddInductive.Context} {indType : InductiveType}
    {validation : AddInductive.FamilyValidationBlockResult}
    (validationRun : AddInductive.observeFamilyValidationBlock 0 [indType]
      context = .ok validation)
    (type_eq : indType.type = .sort (.succ .zero)) :
    validation.stats =
        AddInductive.singletonInductiveStats context indType (.succ .zero) ∧
      validation.validationContext = context ∧
      ∃ depth inductiveFuel,
        context.fuel.recDepth = depth + 1 ∧
          context.fuel.inductiveFuel = inductiveFuel + 1 := by
  let capture : AddInductive.InductiveStats →
      AddInductive.M (AddInductive.InductiveStats × AddInductive.Context) :=
    fun stats => fun selectedContext => .ok (stats, selectedContext)
  have actual :
      AddInductive.checkInductiveTypes 0 #[indType] capture context =
        .ok (validation.stats, validation.validationContext) := by
    rw [AddInductive.checkInductiveTypes_factor, validationRun]
    rfl
  cases depth_eq : context.fuel.recDepth with
  | zero =>
      simp [capture, AddInductive.checkInductiveTypes,
        AddInductive.checkInductiveTypes.loopInd, type_eq,
        TypeChecker.M.run, TypeChecker.checkType, TypeChecker.RecM.run,
        TypeChecker.Inner.inferType, TypeChecker.Methods.withFuel,
        readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, StateT.bind, Except.bind,
        Pure.pure, ReaderT.pure, StateT.pure, Except.pure,
        StateT.run', Functor.map, Except.map, depth_eq,
        throw, throwThe, MonadExceptOf.throw,
        liftM, monadLift, MonadLift.monadLift, StateT.lift] at actual
      split at actual <;> contradiction
  | succ depth =>
      cases inductive_eq : context.fuel.inductiveFuel with
      | zero =>
          have hclosed : context.env.checkNoMVarNoFVar indType.name
              indType.type = .ok () := by
            rw [type_eq]
            simp [Kernel.Environment.checkNoMVarNoFVar,
              Kernel.Environment.checkNoMVar, Kernel.Environment.checkNoFVar,
              Expr.hasMVar, Expr.hasFVar,
              sortOne_data_hasExprMVar_false,
              sortOne_data_hasLevelMVar_false, sortOne_data_hasFVar_false,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          have hcheck : TypeChecker.M.run context.env context.safety
              context.lctx context.lparams context.fuel
              (TypeChecker.checkType indType.type) =
                .ok (.sort (.succ (.succ .zero))) := by
            rw [type_eq]
            apply show TypeChecker.M.run context.env context.safety
                context.lctx context.lparams context.fuel
                (TypeChecker.checkType (.sort (.succ .zero))) =
                  .ok (.sort (.succ (.succ .zero))) from ?_
            exact checkTypeSortOne context depth depth_eq
          have hwhnf : TypeChecker.M.run context.env context.safety
              context.lctx context.lparams context.fuel
              (TypeChecker.whnf indType.type) =
                .ok (.sort (.succ .zero)) := by
            rw [type_eq]
            apply show TypeChecker.M.run context.env context.safety
                context.lctx context.lparams context.fuel
                (TypeChecker.whnf (.sort (.succ .zero))) =
                  .ok (.sort (.succ .zero)) from ?_
            exact whnfSortOne context depth depth_eq
          rw [type_eq] at hclosed hcheck hwhnf
          simp [capture, AddInductive.checkInductiveTypes,
            AddInductive.checkInductiveTypes.loopInd, type_eq,
            hclosed, hcheck, hwhnf, inductive_eq,
            readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
            ReaderT.bind, Bind.bind, Except.bind,
            Pure.pure, ReaderT.pure, Except.pure,
            AddInductive.liftTypeChecker_apply] at actual
          rw [AddInductive.checkInductiveTypes.loopInd.loop.eq_1] at actual
          simp [throw, throwThe, MonadExceptOf.throw] at actual
      | succ inductiveFuel =>
          have hclosed : context.env.checkNoMVarNoFVar indType.name
              indType.type = .ok () := by
            rw [type_eq]
            simp [Kernel.Environment.checkNoMVarNoFVar,
              Kernel.Environment.checkNoMVar, Kernel.Environment.checkNoFVar,
              Expr.hasMVar, Expr.hasFVar,
              sortOne_data_hasExprMVar_false,
              sortOne_data_hasLevelMVar_false, sortOne_data_hasFVar_false,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          have hcheck : TypeChecker.M.run context.env context.safety
              context.lctx context.lparams context.fuel
              (TypeChecker.checkType indType.type) =
                .ok (.sort (.succ (.succ .zero))) := by
            rw [type_eq]
            exact checkTypeSortOne context depth depth_eq
          have hwhnf : TypeChecker.M.run context.env context.safety
              context.lctx context.lparams context.fuel
              (TypeChecker.whnf indType.type) =
                .ok (.sort (.succ .zero)) := by
            rw [type_eq]
            exact whnfSortOne context depth depth_eq
          have canonical :=
            AddInductive.checkInductiveTypes_singleton_zero_of_whnf_sort
              context indType (.sort (.succ (.succ .zero))) (.succ .zero)
              capture (by omega) hclosed hcheck hwhnf rfl
          rw [canonical] at actual
          have pairEq := Except.ok.inj actual.symm
          exact ⟨congrArg Prod.fst pairEq, congrArg Prod.snd pairEq,
            ⟨depth, inductiveFuel, rfl, rfl⟩⟩

/-- A successful canonical singleton normalization run specializes the
validation-only result above. -/
theorem canonicalSingletonStatsAndFuel
    {context : AddInductive.Context} {indType : InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {execution : AddInductive.NormalizationCandidateExecution 0 [indType]
      numNested isUnsafe context}
    (produced : AddInductive.buildNormalizationCandidateExecution 0 [indType]
      numNested isUnsafe context = .ok execution)
    (type_eq : indType.type = .sort (.succ .zero)) :
    execution.stats =
        AddInductive.singletonInductiveStats context indType (.succ .zero) ∧
      execution.validationContext = context ∧
      ∃ depth inductiveFuel,
        context.fuel.recDepth = depth + 1 ∧
          context.fuel.inductiveFuel = inductiveFuel + 1 := by
  simpa only [AddInductive.NormalizationCandidateExecution.familyValidationResult]
    using canonicalSingletonValidationStatsAndFuel
      (execution.familyValidationResult_run produced) type_eq

/-- The recursive candidate observer for the canonical family sort succeeds
at every positive family-validation fuel pair. -/
theorem sortOneCandidateObservable
    (context : AddInductive.Context) (depth inductiveFuel : Nat)
    (hdepth : context.fuel.recDepth = depth + 1)
    (_hinductive : context.fuel.inductiveFuel = inductiveFuel + 1) :
    AddInductive.CandidateExpr.Observable context
      (.sort (.succ .zero)) := by
  have hcheck : TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel
      (TypeChecker.checkType (.sort (.succ .zero))) =
        .ok (.sort (.succ (.succ .zero))) :=
    checkTypeSortOne context depth hdepth
  have hwhnf : TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel
      (TypeChecker.whnf (.sort (.succ .zero))) =
        .ok (.sort (.succ .zero)) :=
    whnfSortOne context depth hdepth
  refine ⟨_, AddInductive.buildCandidateExpr_of_whnf_nonForall
    context (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
      (.sort (.succ .zero)) ?_ hcheck hwhnf rfl⟩
  omega

/-- Canonical singleton validation discharges its previously external family
candidate observer directly from the retained validation equation. -/
theorem canonicalFamilyTypeObservable
    {context : AddInductive.Context} {indType : InductiveType}
    {validation : AddInductive.FamilyValidationBlockResult}
    (validationRun : AddInductive.observeFamilyValidationBlock 0 [indType]
      context = .ok validation)
    (type_eq : indType.type = .sort (.succ .zero)) :
    AddInductive.CandidateFamilyType.Observable
      { context with lctx := {} } indType := by
  cases indType with
  | mk name type ctors =>
    simp only at type_eq
    subst type
    obtain ⟨_stats, _validationContext, depth, inductiveFuel,
        hdepth, hinductive⟩ :=
      canonicalSingletonValidationStatsAndFuel validationRun rfl
    let observerContext : AddInductive.Context := { context with lctx := {} }
    have observerDepth : observerContext.fuel.recDepth = depth + 1 := by
      simpa [observerContext] using hdepth
    have hcheck : TypeChecker.M.run observerContext.env
        observerContext.safety observerContext.lctx observerContext.lparams
        observerContext.fuel
        (TypeChecker.checkType (.sort (.succ .zero))) =
          .ok (.sort (.succ (.succ .zero))) :=
      checkTypeSortOne observerContext depth observerDepth
    have hwhnf : TypeChecker.M.run observerContext.env
        observerContext.safety observerContext.lctx observerContext.lparams
        observerContext.fuel
        (TypeChecker.whnf (.sort (.succ .zero))) =
          .ok (.sort (.succ .zero)) :=
      whnfSortOne observerContext depth observerDepth
    let candidate : AddInductive.CandidateExpr (.sort (.succ .zero)) :=
      ⟨observerContext,
        .terminal observerContext (.sort (.succ .zero))
          (.sort (.succ (.succ .zero))) (.sort (.succ .zero)) hcheck hwhnf⟩
    have candidateRun : AddInductive.buildCandidateExpr
        (.sort (.succ .zero)) observerContext = .ok candidate := by
      simpa [candidate] using
        AddInductive.buildCandidateExpr_of_whnf_nonForall observerContext
          (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
          (.sort (.succ .zero)) (by omega) hcheck hwhnf rfl
    refine ⟨⟨candidate⟩, .succ .zero, ?_, ?_⟩
    · change AddInductive.normalizeCandidateFamilyType
        { name := name, type := .sort (.succ .zero), ctors := ctors }
          observerContext = .ok ⟨candidate⟩
      unfold AddInductive.normalizeCandidateFamilyType
      simp only [ReaderT.bind, Bind.bind, candidateRun, Except.bind,
        ReaderT.pure, Pure.pure, Except.pure]
    · rfl

/-- Canonical host source selected by primitive recognition for `Bool`. -/
def boolSource : InductiveType where
  name := ``Bool
  type := .sort (.succ .zero)
  ctors := [
    ⟨``Bool.false, .const ``Bool []⟩,
    ⟨``Bool.true, .const ``Bool []⟩]

/-- Exact singleton statistics produced while validating canonical `Bool`. -/
def boolStats : AddInductive.InductiveStats where
  levels := []
  resultLevel := .succ .zero
  nindices := #[0]
  indConsts := #[.const ``Bool []]
  params := #[]
  isNotZero := true

private def boolMajorType : Expr :=
  AddInductive.consumeTypeAnnotations <|
    mkAppN (mkAppN boolStats.indConsts[0]! boolStats.params) #[]

private def boolMajorContext (root : AddInductive.Context) :
    AddInductive.Context :=
  root.pushLocalDecl `t .default boolMajorType

private def boolMotiveType (root : AddInductive.Context) : Expr :=
  let majorContext := boolMajorContext root
  majorContext.lctx.mkForall #[] <|
    majorContext.lctx.mkForall #[root.freshExpr] <|
      .sort (.param `u)

private def boolMotiveContext (root : AddInductive.Context) :
    AddInductive.Context :=
  (boolMajorContext root).pushLocalDecl
    (if #[boolSource].size > 1 then (`motive).appendIndexAfter (0 + 1)
      else `motive)
    .default (AddInductive.consumeTypeAnnotations (boolMotiveType root))

private def boolInitialRecInfos (root : AddInductive.Context) :
    Array AddInductive.RecInfo :=
  #[{ motive := (boolMajorContext root).freshExpr
      minors := #[]
      indices := #[]
      major := root.freshExpr }]

private def boolMinorType (_root : AddInductive.Context)
    (context : AddInductive.Context) (recInfos : Array AddInductive.RecInfo)
    (ctorName : Name) : Expr :=
  let t := Expr.const ``Bool []
  let (itIdx, itIndices) := AddInductive.getIIndices boolStats t
  let introApp := mkAppN
    (mkAppN (.const ctorName boolStats.levels) boolStats.params) #[]
  let motiveApp := Expr.app
    (mkAppN recInfos[itIdx]!.motive itIndices) introApp
  context.lctx.mkForall #[] <| context.lctx.mkForall #[] motiveApp

private def boolFalseContext (root : AddInductive.Context) :
    AddInductive.Context :=
  let context := boolMotiveContext root
  context.pushLocalDecl
    ((``Bool.false).replacePrefix ``Bool .anonymous) .default
    (AddInductive.consumeTypeAnnotations <|
      boolMinorType root context (boolInitialRecInfos root) ``Bool.false)

private def boolAfterFalseRecInfos (root : AddInductive.Context) :
    Array AddInductive.RecInfo :=
  (boolInitialRecInfos root).modify 0 fun info =>
    { info with minors := info.minors.push (boolMotiveContext root).freshExpr }

private def boolTrueContext (root : AddInductive.Context) :
    AddInductive.Context :=
  let context := boolFalseContext root
  context.pushLocalDecl
    ((``Bool.true).replacePrefix ``Bool .anonymous) .default
    (AddInductive.consumeTypeAnnotations <|
      boolMinorType root context (boolAfterFalseRecInfos root) ``Bool.true)

private def boolFinalRecInfos (root : AddInductive.Context) :
    Array AddInductive.RecInfo :=
  (boolAfterFalseRecInfos root).modify 0 fun info =>
    { info with minors := info.minors.push (boolFalseContext root).freshExpr }

private theorem mkRecInfos_bool
    (root : AddInductive.Context)
    (hwhnf : TypeChecker.M.run root.env root.safety root.lctx root.lparams
      root.fuel (TypeChecker.whnf boolSource.type) =
        .ok (.sort (.succ .zero)))
    (hinductive : root.fuel.inductiveFuel = inductiveFuel + 1)
    (k : Array AddInductive.RecInfo → AddInductive.M α) :
    AddInductive.mkRecInfos boolStats #[boolSource] (.param `u) k root =
      k (boolFinalRecInfos root) (boolTrueContext root) := by
  unfold AddInductive.mkRecInfos
  rw [AddInductive.mkRecInfos.loopInd1.eq_1]
  have hsize : 0 < #[boolSource].size := by decide
  rw [dif_pos hsize]
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind]
  rw [show #[boolSource][0].type = boolSource.type by rfl]
  simp only [AddInductive.liftTypeChecker_apply]
  rw [hwhnf]
  simp only [hinductive, AddInductive.mkRecInfos.loopArgs1,
    AddInductive.withLocalDecl_apply, AddInductive.getLCtx_apply,
    ReaderT.bind, Bind.bind, Except.bind, Pure.pure, ReaderT.pure,
    Except.pure]
  rw [AddInductive.mkRecInfos.loopInd1.eq_1]
  have hdone : ¬ 1 < #[boolSource].size := by decide
  rw [dif_neg hdone]
  rw [AddInductive.mkRecInfos.loopInd2.eq_1]
  rw [dif_pos hsize]
  rw [show #[boolSource][0] = boolSource by rfl]
  rw [show boolSource.name = ``Bool by rfl]
  rw [show boolSource.ctors =
    [⟨``Bool.false, .const ``Bool []⟩,
     ⟨``Bool.true, .const ``Bool []⟩] by rfl]
  simp only [AddInductive.mkRecInfos.loopCtors,
    AddInductive.mkRecInfos.loopCtorArgs,
    readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
    Except.bind, AddInductive.Context.pushLocalDecl]
  rw [hinductive]
  simp only [AddInductive.mkRecInfos.loopCtorArgs.loop]
  rw [AddInductive.mkRecInfos.loopU.eq_1]
  have huempty : ¬ 0 < (#[] : Array Expr).size := by decide
  rw [dif_neg huempty]
  simp only [AddInductive.getLCtx_apply,
    AddInductive.withLocalDecl_apply, ReaderT.bind, Bind.bind, Except.bind,
    Pure.pure, ReaderT.pure, Except.pure]
  simp only [AddInductive.Context.pushLocalDecl]
  rw [hinductive]
  simp only [AddInductive.mkRecInfos.loopCtorArgs.loop]
  rw [AddInductive.mkRecInfos.loopU.eq_1]
  rw [dif_neg huempty]
  simp only [AddInductive.getLCtx_apply,
    AddInductive.withLocalDecl_apply, ReaderT.bind, Bind.bind, Except.bind,
    Pure.pure, ReaderT.pure, Except.pure]
  rw [AddInductive.mkRecInfos.loopInd2.eq_1]
  rw [dif_neg hdone]
  change k (boolFinalRecInfos root) (boolTrueContext root) = _
  rfl

private def boolRoot (kernelEnv : Environment) (allowPrimitive : Bool)
    (fuel : FuelConfig) : AddInductive.Context where
  env := kernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := allowPrimitive
  fuel := fuel

/-- Translation-facing canonical host type of the generated `Bool.rec`. -/
def boolExpectedRecursorType : Expr :=
  Expr.forallE .anonymous
    (Expr.forallE .anonymous (.const ``Bool []) (.sort (.param `u)) .default)
    (Expr.forallE .anonymous
      (.app (.bvar 0) (.const ``Bool.false []))
      (Expr.forallE .anonymous
        (.app (.bvar 1) (.const ``Bool.true []))
        (Expr.forallE .anonymous (.const ``Bool [])
          (.app (.bvar 3) (.bvar 0)) .default)
        .default)
      .default)
    .default

private def boolGeneratedRecursorType (root : AddInductive.Context) : Expr :=
  let recInfos := boolFinalRecInfos root
  AddInductive.declareRecursors.generatedRecursorType boolStats
    (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
    (boolTrueContext root).lctx recInfos[0]!

private def boolClosedRoot : AddInductive.Context :=
  boolRoot (Environment.empty `_boolRecursorProof) false default

private theorem localContextMkForall_empty (lctx : LocalContext) (e : Expr) :
    lctx.mkForall #[] e = e := by
  unfold LocalContext.mkForall LocalContext.mkBinding
  change e.abstract #[] = e
  simpa using (Expr.abstract_eq e [] (.inl rfl) .nil)

private theorem inferImplicit_eqv (e : Expr) (numParams : Nat)
    (considerRange : Bool) :
    e.inferImplicit numParams considerRange == e := by
  induction numParams generalizing e with
  | zero =>
      cases e <;> exact Expr.eqv_refl _
  | succ numParams ih =>
      cases e <;> try exact Expr.eqv_refl _
      rename_i name domain body binderInfo
      unfold Expr.inferImplicit
      have bodyEqv := ih body
      have domainEqv := Expr.eqv_refl domain
      cases condition :
          (binderInfo.isExplicit &&
            Expr.hasLooseBVarInExplicitDomain
              (body.inferImplicit numParams considerRange) 0 considerRange) <;>
        simpa [condition, (· == ·), Expr.eqv_eq, Expr.eqv'] using
          And.intro domainEqv bodyEqv

private theorem forallE_eqv
    {leftName rightName : Name} {leftDomain rightDomain : Expr}
    {leftBody rightBody : Expr} {leftInfo rightInfo : BinderInfo}
    (domain : leftDomain == rightDomain)
    (body : leftBody == rightBody) :
    Expr.forallE leftName leftDomain leftBody leftInfo ==
      Expr.forallE rightName rightDomain rightBody rightInfo := by
  simpa [(· == ·), Expr.eqv_eq, Expr.eqv'] using
    And.intro domain body

private theorem exprAbstractList_empty (e : Expr) :
    e.abstractList [] = e := by
  have abstractArray : e.abstract #[] = e := by
    simpa using (Expr.abstract_eq e [] (.inl rfl) .nil)
  exact (Expr.abstract_eq e [] (.inl rfl) .nil).symm.trans abstractArray

private theorem localContextMkForall_singleton
    {lctx : LocalContext} {id : FVarId} {index : Nat} {name : Name}
    {type body : Expr} {binderInfo : BinderInfo} {kind : LocalDeclKind}
    (find : lctx.find? id = some (.cdecl index id name type binderInfo kind))
    (bodyClosed : body.looseBVarRange' = 0)
    (typeClosed : type.looseBVarRange' = 0) :
    lctx.mkForall #[.fvar id] body =
      .forallE name type (body.abstract1 id) binderInfo := by
  rw [LocalContext.mkForall]
  change LocalContext.mkBinding false lctx
    ⟨[id].map Expr.fvar⟩ body = _
  rw [LocalContext.mkBinding_eq bodyClosed (by simp) (by
      intro x member d found
      simp only [List.mem_singleton] at member
      subst x
      rw [find] at found
      cases found
      exact ⟨typeClosed, by
        intro value present
        simp [LocalDecl.value?] at present⟩),
    LocalContext.mkBindingList_eq_fold (by
      intro x member
      simp only [List.mem_singleton] at member
      subst x
      exact ⟨_, find⟩) (by simp)]
  simp only [List.foldr, LocalContext.mkBindingList1]
  rw [find]
  simp [exprAbstractList_empty]

private theorem localContextMkForall_pair
    {lctx : LocalContext} {first second : FVarId}
    {firstIndex secondIndex : Nat} {firstName secondName : Name}
    {firstType secondType body : Expr}
    {firstBinderInfo secondBinderInfo : BinderInfo}
    {firstKind secondKind : LocalDeclKind}
    (first_ne_second : first ≠ second)
    (firstFind : lctx.find? first = some
      (.cdecl firstIndex first firstName firstType firstBinderInfo firstKind))
    (secondFind : lctx.find? second = some
      (.cdecl secondIndex second secondName secondType secondBinderInfo
        secondKind))
    (bodyClosed : body.looseBVarRange' = 0)
    (firstTypeClosed : firstType.looseBVarRange' = 0)
    (secondTypeClosed : secondType.looseBVarRange' = 0) :
    lctx.mkForall #[.fvar first, .fvar second] body =
      Expr.forallE firstName firstType
        ((Expr.forallE secondName secondType (body.abstract1 second)
          secondBinderInfo).abstract1 first)
        firstBinderInfo := by
  rw [LocalContext.mkForall]
  change LocalContext.mkBinding false lctx
    ⟨[first, second].map Expr.fvar⟩ body = _
  rw [LocalContext.mkBinding_eq bodyClosed (by simp [first_ne_second]) (by
      intro x member d found
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rw [firstFind] at found
        cases found
        exact ⟨firstTypeClosed, by
          intro value present
          simp [LocalDecl.value?] at present⟩
      · rw [secondFind] at found
        cases found
        exact ⟨secondTypeClosed, by
          intro value present
          simp [LocalDecl.value?] at present⟩),
    LocalContext.mkBindingList_eq_fold (by
      intro x member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨_, firstFind⟩
      · exact ⟨_, secondFind⟩) (by simp [first_ne_second])]
  simp only [List.foldr, LocalContext.mkBindingList1]
  simp [secondFind, firstFind, exprAbstractList_empty]

private theorem boolMotiveType_eq
    (root : AddInductive.Context)
    (rootRun : TypeChecker.CandidateLocalContextRun root) :
    boolMotiveType root =
      .forallE `t boolMajorType (.sort (.param `u)) .default := by
  have majorFind := rootRun.push_findNew `t .default boolMajorType
  have majorFind' : (boolMajorContext root).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t boolMajorType .default .default) := by
    simpa [boolMajorContext] using majorFind
  unfold boolMotiveType
  simp only [AddInductive.Context.freshExpr]
  rw [localContextMkForall_empty,
    localContextMkForall_singleton majorFind'
      (by simp [Expr.looseBVarRange'])
      (by simp [boolMajorType, boolStats, mkAppN,
        AddInductive.consumeTypeAnnotations, Expr.looseBVarRange'])]
  rfl

private theorem boolFinalRecInfos_eq (root : AddInductive.Context) :
    boolFinalRecInfos root =
      #[{ motive := (boolMajorContext root).freshExpr
          minors := #[(boolMotiveContext root).freshExpr,
            (boolFalseContext root).freshExpr]
          indices := #[]
          major := root.freshExpr }] := by
  rfl

private theorem boolGetIIndices :
    AddInductive.getIIndices boolStats (.const ``Bool []) = (0, #[]) := by
  have valid : AddInductive.isValidIndAppIdx boolStats
      (.const ``Bool []) 0 = true := by
    simp +decide [AddInductive.isValidIndAppIdx, boolStats,
      Expr.getAppFn, Expr.getAppArgs, Expr.getAppNumArgs]
  have found := AddInductive.isValidIndApp?_singleton_zero boolStats
    (.const ``Bool []) (by decide) valid
  have args : (Expr.const ``Bool []).getAppArgs = #[] := by
    rw [Expr.getAppArgs_eq]
    rfl
  rw [AddInductive.getIIndices, found, args]
  rw [show boolStats.params.size = 0 by rfl]
  apply Prod.ext
  · rfl
  · apply Array.eq_empty_of_size_eq_zero
    change ((#[] : Array Expr).toSubarray 0 0).copy.size = 0
    rw [Subarray.copy_eq_toArray, Subarray.size_toArray,
      Subarray.size_eq]
    rfl

private theorem boolFalseMinorType_eq
    (root : AddInductive.Context) :
    boolMinorType root (boolMotiveContext root) (boolInitialRecInfos root)
        ``Bool.false =
      .app (boolMajorContext root).freshExpr (.const ``Bool.false []) := by
  unfold boolMinorType
  simp only [boolGetIIndices]
  simp [boolInitialRecInfos, boolStats, mkAppN,
    localContextMkForall_empty]

private theorem boolTrueMinorType_eq
    (root : AddInductive.Context) :
    boolMinorType root (boolFalseContext root)
        (boolAfterFalseRecInfos root) ``Bool.true =
      .app (boolMajorContext root).freshExpr (.const ``Bool.true []) := by
  unfold boolMinorType
  simp only [boolGetIIndices]
  simp [boolAfterFalseRecInfos, boolStats, mkAppN,
    boolInitialRecInfos, localContextMkForall_empty]

private def boolRawExpectedRecursorType : Expr :=
  Expr.forallE `motive
    (Expr.forallE `t (.const ``Bool []) (.sort (.param `u)) .default)
    (Expr.forallE `false
      (.app (.bvar 0) (.const ``Bool.false []))
      (Expr.forallE `true
        (.app (.bvar 1) (.const ``Bool.true []))
        (Expr.forallE `t (.const ``Bool [])
          (.app (.bvar 3) (.bvar 0)) .default)
        .default)
      .default)
    .default

private theorem boolGeneratedRecursorRaw_eq
    (root : AddInductive.Context)
    (rootRun : TypeChecker.CandidateLocalContextRun root) :
    let recInfos := boolFinalRecInfos root
    ((boolTrueContext root).lctx.mkForall boolStats.params <|
      (boolTrueContext root).lctx.mkForall (recInfos.map (·.motive)) <|
      (boolTrueContext root).lctx.mkForall (recInfos.flatMap (·.minors)) <|
      (boolTrueContext root).lctx.mkForall recInfos[0]!.indices <|
      (boolTrueContext root).lctx.mkForall #[recInfos[0]!.major]
        (.app (mkAppN recInfos[0]!.motive recInfos[0]!.indices)
          recInfos[0]!.major)) = boolRawExpectedRecursorType := by
  have majorRun : TypeChecker.CandidateLocalContextRun
      (boolMajorContext root) := by
    simpa [boolMajorContext] using
      rootRun.push `t .default boolMajorType
  have motiveRun : TypeChecker.CandidateLocalContextRun
      (boolMotiveContext root) := by
    simpa [boolMotiveContext] using
      majorRun.push `motive .default
        (AddInductive.consumeTypeAnnotations (boolMotiveType root))
  have falseRun : TypeChecker.CandidateLocalContextRun
      (boolFalseContext root) := by
    simpa [boolFalseContext] using
      motiveRun.push
        ((``Bool.false).replacePrefix ``Bool .anonymous) .default
        (AddInductive.consumeTypeAnnotations <|
          boolMinorType root (boolMotiveContext root)
            (boolInitialRecInfos root) ``Bool.false)
  have trueRun : TypeChecker.CandidateLocalContextRun
      (boolTrueContext root) := by
    simpa [boolTrueContext] using
      falseRun.push
        ((``Bool.true).replacePrefix ``Bool .anonymous) .default
        (AddInductive.consumeTypeAnnotations <|
          boolMinorType root (boolFalseContext root)
            (boolAfterFalseRecInfos root) ``Bool.true)

  have tFindMajor := rootRun.push_findNew `t .default boolMajorType
  have tFindMajor' : (boolMajorContext root).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t boolMajorType .default .default) := by
    simpa [boolMajorContext] using tFindMajor
  have tFindMotive : (boolMotiveContext root).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t boolMajorType .default .default) := by
    simpa [boolMotiveContext] using
      majorRun.push_findOld `motive .default
        (AddInductive.consumeTypeAnnotations (boolMotiveType root))
        tFindMajor
  have tFindFalse : (boolFalseContext root).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t boolMajorType .default .default) := by
    simpa [boolFalseContext] using
      motiveRun.push_findOld
        ((``Bool.false).replacePrefix ``Bool .anonymous) .default
        (AddInductive.consumeTypeAnnotations <|
          boolMinorType root (boolMotiveContext root)
            (boolInitialRecInfos root) ``Bool.false) tFindMotive
  have tFind : (boolTrueContext root).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t boolMajorType .default .default) := by
    simpa [boolTrueContext] using
      falseRun.push_findOld
        ((``Bool.true).replacePrefix ``Bool .anonymous) .default
        (AddInductive.consumeTypeAnnotations <|
          boolMinorType root (boolFalseContext root)
            (boolAfterFalseRecInfos root) ``Bool.true) tFindFalse

  have motiveFindMotive := majorRun.push_findNew `motive .default
    (AddInductive.consumeTypeAnnotations (boolMotiveType root))
  have motiveFindMotive' : (boolMotiveContext root).lctx.find?
      (boolMajorContext root).freshFVarId = some (.cdecl
        (boolMajorContext root).lctx.decls.size
        (boolMajorContext root).freshFVarId `motive
        (AddInductive.consumeTypeAnnotations (boolMotiveType root))
        .default .default) := by
    simpa [boolMotiveContext] using motiveFindMotive
  have motiveFindFalse : (boolFalseContext root).lctx.find?
      (boolMajorContext root).freshFVarId = some (.cdecl
        (boolMajorContext root).lctx.decls.size
        (boolMajorContext root).freshFVarId `motive
        (AddInductive.consumeTypeAnnotations (boolMotiveType root))
        .default .default) := by
    simpa [boolFalseContext] using
      motiveRun.push_findOld
        ((``Bool.false).replacePrefix ``Bool .anonymous) .default
        (AddInductive.consumeTypeAnnotations <|
          boolMinorType root (boolMotiveContext root)
            (boolInitialRecInfos root) ``Bool.false) motiveFindMotive
  have motiveFind : (boolTrueContext root).lctx.find?
      (boolMajorContext root).freshFVarId = some (.cdecl
        (boolMajorContext root).lctx.decls.size
        (boolMajorContext root).freshFVarId `motive
        (AddInductive.consumeTypeAnnotations (boolMotiveType root))
        .default .default) := by
    simpa [boolTrueContext] using
      falseRun.push_findOld
        ((``Bool.true).replacePrefix ``Bool .anonymous) .default
        (AddInductive.consumeTypeAnnotations <|
          boolMinorType root (boolFalseContext root)
            (boolAfterFalseRecInfos root) ``Bool.true) motiveFindFalse

  have falseFindFalse := motiveRun.push_findNew
    ((``Bool.false).replacePrefix ``Bool .anonymous) .default
    (AddInductive.consumeTypeAnnotations <|
      boolMinorType root (boolMotiveContext root)
        (boolInitialRecInfos root) ``Bool.false)
  have falseFindFalse' : (boolFalseContext root).lctx.find?
      (boolMotiveContext root).freshFVarId = some (.cdecl
        (boolMotiveContext root).lctx.decls.size
        (boolMotiveContext root).freshFVarId
        ((``Bool.false).replacePrefix ``Bool .anonymous)
        (AddInductive.consumeTypeAnnotations <|
          boolMinorType root (boolMotiveContext root)
            (boolInitialRecInfos root) ``Bool.false) .default .default) := by
    simpa [boolFalseContext] using falseFindFalse
  have falseFind : (boolTrueContext root).lctx.find?
      (boolMotiveContext root).freshFVarId = some (.cdecl
        (boolMotiveContext root).lctx.decls.size
        (boolMotiveContext root).freshFVarId
        ((``Bool.false).replacePrefix ``Bool .anonymous)
        (AddInductive.consumeTypeAnnotations <|
          boolMinorType root (boolMotiveContext root)
            (boolInitialRecInfos root) ``Bool.false) .default .default) := by
    simpa [boolTrueContext] using
      falseRun.push_findOld
        ((``Bool.true).replacePrefix ``Bool .anonymous) .default
        (AddInductive.consumeTypeAnnotations <|
          boolMinorType root (boolFalseContext root)
            (boolAfterFalseRecInfos root) ``Bool.true) falseFindFalse
  have trueFind := falseRun.push_findNew
    ((``Bool.true).replacePrefix ``Bool .anonymous) .default
    (AddInductive.consumeTypeAnnotations <|
      boolMinorType root (boolFalseContext root)
        (boolAfterFalseRecInfos root) ``Bool.true)
  have trueFind' : (boolTrueContext root).lctx.find?
      (boolFalseContext root).freshFVarId = some (.cdecl
        (boolFalseContext root).lctx.decls.size
        (boolFalseContext root).freshFVarId
        ((``Bool.true).replacePrefix ``Bool .anonymous)
        (AddInductive.consumeTypeAnnotations <|
          boolMinorType root (boolFalseContext root)
            (boolAfterFalseRecInfos root) ``Bool.true) .default .default) := by
    simpa [boolTrueContext] using trueFind
  have false_ne_true : (boolMotiveContext root).freshFVarId ≠
      (boolFalseContext root).freshFVarId := by
    intro equal
    have fresh := falseRun.fresh
    rw [← equal, falseFindFalse'] at fresh
    contradiction
  have t_ne_motive : root.freshFVarId ≠
      (boolMajorContext root).freshFVarId := by
    intro equal
    have fresh := majorRun.fresh
    rw [← equal, tFindMajor'] at fresh
    contradiction
  have motive_ne_false : (boolMajorContext root).freshFVarId ≠
      (boolMotiveContext root).freshFVarId := by
    intro equal
    have fresh := motiveRun.fresh
    rw [← equal, motiveFindMotive'] at fresh
    contradiction
  have motive_ne_true : (boolMajorContext root).freshFVarId ≠
      (boolFalseContext root).freshFVarId := by
    intro equal
    have fresh := falseRun.fresh
    rw [← equal, motiveFindFalse] at fresh
    contradiction
  have false_bne_motive :
      ((boolMotiveContext root).freshFVarId ==
        (boolMajorContext root).freshFVarId) = false :=
    beq_eq_false_iff_ne.mpr motive_ne_false.symm
  have true_bne_motive :
      ((boolFalseContext root).freshFVarId ==
        (boolMajorContext root).freshFVarId) = false :=
    beq_eq_false_iff_ne.mpr motive_ne_true.symm

  dsimp only
  rw [show boolStats.params = #[] by rfl,
    show (boolFinalRecInfos root).map (·.motive) =
      #[(boolMajorContext root).freshExpr] by
        rw [boolFinalRecInfos_eq]
        simp,
    show (boolFinalRecInfos root).flatMap (·.minors) =
      #[(boolMotiveContext root).freshExpr,
        (boolFalseContext root).freshExpr] by
        rw [boolFinalRecInfos_eq]
        simp,
    show (boolFinalRecInfos root)[0]!.indices = #[] by
      rw [boolFinalRecInfos_eq]
      rfl,
    show (boolFinalRecInfos root)[0]!.major = root.freshExpr by
      rw [boolFinalRecInfos_eq]
      rfl,
    show (boolFinalRecInfos root)[0]!.motive =
      (boolMajorContext root).freshExpr by
        rw [boolFinalRecInfos_eq]
        rfl]
  simp only [AddInductive.Context.freshExpr]
  simp only [localContextMkForall_empty]
  rw [localContextMkForall_singleton tFind
      (by simp [boolMajorType, boolStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.looseBVarRange'])
      (by simp [boolMajorType, boolStats, mkAppN,
        AddInductive.consumeTypeAnnotations, Expr.looseBVarRange']),
    localContextMkForall_pair false_ne_true falseFind trueFind'
      (by simp [boolMajorType, boolStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.abstract1,
        t_ne_motive, false_bne_motive, true_bne_motive,
        false_ne_true, Expr.looseBVarRange'])
      (by simp [boolFalseMinorType_eq root,
        boolMajorType, boolStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.looseBVarRange'])
      (by simp [boolTrueMinorType_eq root,
        boolMajorType, boolStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.looseBVarRange']),
    localContextMkForall_singleton motiveFind
      (by simp [boolFalseMinorType_eq root, boolTrueMinorType_eq root,
        boolMajorType, boolStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.abstract1,
        t_ne_motive, false_bne_motive, true_bne_motive,
        false_ne_true, Expr.looseBVarRange'])
      (by simp [boolMotiveType_eq root rootRun,
        boolMajorType, boolStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.looseBVarRange'])]
  rw [boolMotiveType_eq root rootRun, boolFalseMinorType_eq root,
    boolTrueMinorType_eq root]
  simp [boolRawExpectedRecursorType, boolMajorType, boolStats, mkAppN,
    AddInductive.consumeTypeAnnotations, AddInductive.Context.freshExpr,
    Expr.abstract1, Expr.abstract_eq, Name.replacePrefix, t_ne_motive,
    false_bne_motive, true_bne_motive, false_ne_true]

private theorem boolGeneratedRecursorType_eqv
    (root : AddInductive.Context)
    (rootRun : TypeChecker.CandidateLocalContextRun root) :
    boolGeneratedRecursorType root == boolExpectedRecursorType := by
  unfold boolGeneratedRecursorType
  unfold AddInductive.declareRecursors.generatedRecursorType
  let raw : Expr := let recInfos := boolFinalRecInfos root
    (boolTrueContext root).lctx.mkForall boolStats.params <|
      (boolTrueContext root).lctx.mkForall (recInfos.map (·.motive)) <|
      (boolTrueContext root).lctx.mkForall (recInfos.flatMap (·.minors)) <|
      (boolTrueContext root).lctx.mkForall recInfos[0]!.indices <|
      (boolTrueContext root).lctx.mkForall #[recInfos[0]!.major]
        (.app (mkAppN recInfos[0]!.motive recInfos[0]!.indices)
          recInfos[0]!.major)
  change raw.inferImplicit 1000 false == boolExpectedRecursorType
  have inferred : raw.inferImplicit 1000 false == raw :=
    inferImplicit_eqv raw 1000 false
  have raw_eq : raw = boolRawExpectedRecursorType := by
    dsimp only [raw]
    exact boolGeneratedRecursorRaw_eq root rootRun
  have assembled : raw == boolRawExpectedRecursorType := by
    rw [raw_eq]
    exact Expr.eqv_refl _
  have expected : boolRawExpectedRecursorType ==
      boolExpectedRecursorType := by
    unfold boolRawExpectedRecursorType boolExpectedRecursorType
    apply forallE_eqv
    · apply forallE_eqv <;> exact Expr.eqv_refl _
    · apply forallE_eqv
      · exact Expr.eqv_refl _
      · apply forallE_eqv
        · exact Expr.eqv_refl _
        · apply forallE_eqv <;> exact Expr.eqv_refl _
  exact BEq.trans inferred (BEq.trans assembled expected)

def boolExpectedRecursorVal : RecursorVal where
  name := ``Bool.rec
  levelParams := [`u]
  type := boolExpectedRecursorType
  all := [``Bool]
  numParams := 0
  numIndices := 0
  numMotives := 1
  numMinors := 2
  rules := []
  k := false
  isUnsafe := false

/-- A successful canonical Bool recursor phase contains exactly the record
assembled by the producer; its rule payload remains producer-owned. -/
theorem declareRecursors_bool_infos (root : AddInductive.Context)
    (hwhnf : TypeChecker.M.run root.env root.safety root.lctx root.lparams
      root.fuel (TypeChecker.whnf boolSource.type) =
        .ok (.sort (.succ .zero)))
    (hinductive : root.fuel.inductiveFuel = inductiveFuel + 1)
    {result : AddInductive.RecursorDeclarationResult}
    (run : AddInductive.declareRecursors boolStats #[boolSource]
      (.param `u) false root = .ok result) :
    ∃ rules, result.infos =
      [AddInductive.declareRecursors.generatedRecursorVal boolStats
        #[boolSource] (.param `u) false
        ((boolFinalRecInfos root).map (·.motive))
        ((boolFinalRecInfos root).flatMap (·.minors))
        (boolTrueContext root).lctx root.lparams
        (root.safety != .safe) 0 boolSource
        (boolFinalRecInfos root)[0]! rules] := by
  unfold AddInductive.declareRecursors at run
  unfold AddInductive.declareRecursorsAt at run
  rw [mkRecInfos_bool root hwhnf hinductive] at run
  simp only [AddInductive.getLCtx_apply, ReaderT.bind, Bind.bind] at run
  simp only [Except.bind] at run
  cases hloop : StateT.run'
      (AddInductive.declareRecursors.loop boolStats #[boolSource]
        (.param `u) false (boolFinalRecInfos root)
        ((boolFinalRecInfos root).map (·.motive))
        ((boolFinalRecInfos root).flatMap (·.minors))
        (boolTrueContext root).lctx root.lparams
        (root.safety != .safe) root.allowPrimitive 0 root.env)
      0 (boolTrueContext root) with
  | error error =>
      rw [hloop] at run
      contradiction
  | ok tail =>
      rw [hloop] at run
      simp only [Except.bind, Pure.pure, Except.pure] at run
      have result_eq := Except.ok.inj run
      subst result
      exact AddInductive.declareRecursors.loop_singleton_infos_eq
        (by simp) (by simp) hloop

/-- Transport the canonical Bool recursor translation to the exact record
retained by a successful producer execution. -/
theorem declareRecursors_bool_evidence (root : AddInductive.Context)
    (rootRun : TypeChecker.CandidateLocalContextRun root)
    (lparams_eq : root.lparams = [])
    (safety_eq : root.safety = .safe)
    (hwhnf : TypeChecker.M.run root.env root.safety root.lctx root.lparams
      root.fuel (TypeChecker.whnf boolSource.type) =
        .ok (.sort (.succ .zero)))
    (hinductive : root.fuel.inductiveFuel = inductiveFuel + 1)
    {result : AddInductive.RecursorDeclarationResult}
    (run : AddInductive.declareRecursors boolStats #[boolSource]
      (.param `u) false root = .ok result)
    {ctorEnv : VEnv} {raw : VConstVal}
    (tr : TrConstVal .safe ctorEnv (.recInfo boolExpectedRecursorVal) raw) :
    List.Forall₂
      (fun info raw => TrConstVal .safe ctorEnv (.recInfo info) raw)
      result.infos [raw] := by
  obtain ⟨rules, infos_eq⟩ := show ∃ rules, result.infos =
      [AddInductive.declareRecursors.generatedRecursorVal boolStats
        #[boolSource] (.param `u) false
        ((boolFinalRecInfos root).map (·.motive))
        ((boolFinalRecInfos root).flatMap (·.minors))
        (boolTrueContext root).lctx root.lparams
        (root.safety != .safe) 0 boolSource
        (boolFinalRecInfos root)[0]! rules] from by
    unfold AddInductive.declareRecursors at run
    unfold AddInductive.declareRecursorsAt at run
    rw [mkRecInfos_bool root hwhnf hinductive] at run
    simp only [AddInductive.getLCtx_apply, ReaderT.bind, Bind.bind,
      Except.bind] at run
    cases hloop : StateT.run'
        (AddInductive.declareRecursors.loop boolStats #[boolSource]
          (.param `u) false (boolFinalRecInfos root)
          ((boolFinalRecInfos root).map (·.motive))
          ((boolFinalRecInfos root).flatMap (·.minors))
          (boolTrueContext root).lctx root.lparams
          (root.safety != .safe) root.allowPrimitive 0 root.env)
        0 (boolTrueContext root) with
    | error error =>
        rw [hloop] at run
        contradiction
    | ok tail =>
        rw [hloop] at run
        simp only [Pure.pure, Except.pure] at run
        have result_eq := Except.ok.inj run
        subst result
        exact AddInductive.declareRecursors.loop_singleton_infos_eq
          (by decide) (by decide) hloop
  rw [infos_eq]
  apply List.Forall₂.cons
  · apply VInductDecl.trConstVal_of_translation_header (tr := tr)
    · simp [AddInductive.declareRecursors.generatedRecursorVal,
        boolExpectedRecursorVal, safety_eq, ConstantInfo.safety,
        ConstantInfo.isUnsafe, ConstantInfo.isPartial]
    · simp [AddInductive.declareRecursors.generatedRecursorVal,
        boolExpectedRecursorVal, lparams_eq, AddInductive.getRecLevelParams,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal]
    · simpa [AddInductive.declareRecursors.generatedRecursorVal,
        boolExpectedRecursorVal, boolGeneratedRecursorType,
        ConstantInfo.type, ConstantInfo.toConstantVal, (· == ·)] using
        boolGeneratedRecursorType_eqv root rootRun
    · rfl
  · exact .nil
/-- The translation-facing Bool header denotes the canonical Theory
recursor in every semantically reconstructed post-constructor environment. -/
theorem boolExpectedRecursorTranslation {ctorEnv : VEnv}
    (generationEnv : VInductDecl.BlockGenerationEnv
      VPrimitiveInductive.boolGeneration ctorEnv) :
    TrConstVal .safe ctorEnv (.recInfo boolExpectedRecursorVal)
      VPrimitiveInductive.boolGeneration.recursors[0] := by
  have familyLookup := generationEnv.familyConst
    VPrimitiveInductive.boolGeneration.families[0]
    (List.getElem_mem (l := VPrimitiveInductive.boolGeneration.families)
      (n := 0) (by decide))
  have falseLookup := generationEnv.ctorConst
    VPrimitiveInductive.boolGeneration.flatCtors[0]
    (List.getElem_mem (l := VPrimitiveInductive.boolGeneration.flatCtors)
      (n := 0) (by decide))
  have trueLookup := generationEnv.ctorConst
    VPrimitiveInductive.boolGeneration.flatCtors[1]
    (List.getElem_mem (l := VPrimitiveInductive.boolGeneration.flatCtors)
      (n := 1) (by decide))
  change ctorEnv.constants ``Bool =
    some VPrimitiveInductive.boolType.toVConstant at familyLookup
  change ctorEnv.constants ``Bool.false = some
    VPrimitiveInductive.boolConstructors[0].toVConstant at falseLookup
  change ctorEnv.constants ``Bool.true = some
    VPrimitiveInductive.boolConstructors[1].toVConstant at trueLookup
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr ctorEnv [`u] [] boolExpectedRecursorType
      VPrimitiveInductive.boolGeneration.recursors[0].type := by
    apply TrTypeExpr.forallE
    · apply TrTypeExpr.forallE
      · exact .const familyLookup rfl rfl
      · apply TrTypeExpr.sort
        rfl
    · apply TrTypeExpr.forallE
      · apply TrTypeExpr.app
        · apply TrTypeExpr.bvar
          rfl
        · exact .const falseLookup rfl rfl
      · apply TrTypeExpr.forallE
        · apply TrTypeExpr.app
          · apply TrTypeExpr.bvar
            rfl
          · exact .const trueLookup rfl rfl
        · apply TrTypeExpr.forallE
          · exact .const familyLookup rfl rfl
          · apply TrTypeExpr.app
            · apply TrTypeExpr.bvar
              rfl
            · apply TrTypeExpr.bvar
              rfl
  obtain ⟨sort, recursorType⟩ := generationEnv.recursor_wf
    (List.getElem_mem (l := VPrimitiveInductive.boolGeneration.families)
      (n := 0) (by decide))
  rw [show (VPrimitiveInductive.boolGeneration.recursor
      VPrimitiveInductive.boolGeneration.families[0]).uvars = 1 by rfl]
    at recursorType
  have rawWF : VPrimitiveInductive.boolGeneration.recursors[0].type.WF
      ctorEnv 1 [] := by
    refine ⟨.sort sort, ?_⟩
    change ctorEnv.HasType 1 []
      VPrimitiveInductive.boolGeneration.recursors[0].type (.sort sort)
    simpa [VInductDecl.BlockGenerationChecked.recursors] using recursorType
  exact shape.to_trExprS generationEnv.ord trivial rawWF


def natSource (binderName : Name) (binderInfo : BinderInfo) : InductiveType where
  name := ``Nat
  type := .sort (.succ .zero)
  ctors := [
    ⟨``Nat.zero, .const ``Nat []⟩,
    ⟨``Nat.succ,
      .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩]

def natStats : AddInductive.InductiveStats where
  levels := []
  resultLevel := .succ .zero
  nindices := #[0]
  indConsts := #[.const ``Nat []]
  params := #[]
  isNotZero := true

private theorem unfoldInductiveConst_none
    (context : AddInductive.Context) (constName : Name)
    (info : InductiveVal) (methods : TypeChecker.Methods)
    (state : TypeChecker.State)
    (hfind : context.env.find? constName = some (.inductInfo info)) :
    TypeChecker.Inner.unfoldDefinition (.const constName []) methods
      context.toTypeChecker state = .ok (none, state) := by
  change TypeChecker.Inner.unfoldDefinitionCore (.const constName []) methods
    context.toTypeChecker state = .ok (none, state)
  unfold TypeChecker.Inner.unfoldDefinitionCore
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM TypeChecker.getEnv : TypeChecker.RecM Environment)
      methods context.toTypeChecker state = .ok (context.env, state) by rfl]
  simp only []
  unfold TypeChecker.Inner.isDelta
  simp [Expr.getAppFn, hfind, ConstantInfo.deltaValue?,
    ReaderT.pure, StateT.pure, Except.pure, Pure.pure]

private theorem whnfLoopInductiveConst
    (context : AddInductive.Context) (constName : Name)
    (info : InductiveVal) (methods : TypeChecker.Methods)
    (state : TypeChecker.State) (whnfFuel : Nat)
    (hfind : context.env.find? constName = some (.inductInfo info)) :
    TypeChecker.Inner.whnf'.loop (.const constName []) (whnfFuel + 1)
      methods context.toTypeChecker state =
        .ok (.const constName [], state) := by
  unfold TypeChecker.Inner.whnf'.loop
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM TypeChecker.getEnv : TypeChecker.RecM Environment)
      methods context.toTypeChecker state = .ok (context.env, state) by rfl]
  simp only [Except.bind]
  rw [show TypeChecker.Inner.whnfCore' (.const constName []) false methods
      context.toTypeChecker state = .ok (.const constName [], state) by rfl]
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM (TypeChecker.Inner.reduceNative context.env
      (.const constName [])) : TypeChecker.RecM (Option Expr))
      methods context.toTypeChecker state = .ok (none, state) by rfl]
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show TypeChecker.Inner.reduceNat (.const constName []) methods
      context.toTypeChecker state = .ok (none, state) by rfl]
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [unfoldInductiveConst_none context constName info methods state hfind]
  rfl

private theorem inferTypeFVarCore
    (context : AddInductive.Context) (id : FVarId) (type : Expr)
    (methods : TypeChecker.Methods) (state : TypeChecker.State)
    (hcache : state.inferTypeI[(.fvar id : Expr)]? = none)
    (hfind : context.lctx.find? id =
      some (.cdecl index id name type bi kind)) :
    TypeChecker.Inner.inferType' (.fvar id) true methods
      context.toTypeChecker state =
        .ok (type, { state with inferTypeI :=
          state.inferTypeI.insert (.fvar id) type }) := by
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq,
    Expr.looseBVarRange']
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (get : TypeChecker.RecM TypeChecker.State)
      methods context.toTypeChecker state = .ok (state, state) by rfl]
  simp only [Except.bind, hcache]
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (readThe TypeChecker.Context : TypeChecker.RecM TypeChecker.Context)
      methods context.toTypeChecker state =
        .ok (context.toTypeChecker, state) by rfl]
  simp [hcache, TypeChecker.Inner.inferFVar,
    AddInductive.Context.toTypeChecker, hfind, LocalDecl.type,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    get, getThe, MonadStateOf.get, StateT.get,
    readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    liftM, monadLift, MonadLift.monadLift, StateT.lift,
    Functor.map, StateT.map, Except.map,
    ReaderT.pure, StateT.pure, Except.pure, Pure.pure]

theorem whnfInductiveConst
    (context : AddInductive.Context) (constName : Name)
    (info : InductiveVal) (recursionFuel whnfFuel : Nat)
    (hdepth : context.fuel.recDepth = recursionFuel + 1)
    (hwhnfFuel : context.fuel.whnf = whnfFuel + 1)
    (hfind : context.env.find? constName = some (.inductInfo info)) :
    TypeChecker.M.run context.env context.safety context.lctx context.lparams
      context.fuel (TypeChecker.whnf (.const constName [])) =
        .ok (.const constName []) := by
  unfold TypeChecker.M.run TypeChecker.whnf TypeChecker.RecM.run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.whnf' (.const constName [])
      (TypeChecker.Methods.withFuel recursionFuel)
      context.toTypeChecker ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.whnf'
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind, Pure.pure]
  rw [show (get : TypeChecker.RecM TypeChecker.State)
      (TypeChecker.Methods.withFuel recursionFuel)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (({} : TypeChecker.State), ({} : TypeChecker.State)) by rfl]
  simp only [Std.HashMap.getElem?_empty]
  simp only [readThe, MonadReaderOf.read, ReaderT.bind, StateT.bind,
    Except.bind, Bind.bind, ReaderT.pure, StateT.pure, Except.pure,
    Pure.pure]
  rw [show (liftM read : TypeChecker.RecM TypeChecker.Context)
      (TypeChecker.Methods.withFuel recursionFuel)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (context.toTypeChecker, ({} : TypeChecker.State)) by rfl]
  simp only []
  rw [show context.toTypeChecker.eagerReduce = false by rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show context.toTypeChecker.fuel.whnf = whnfFuel + 1 by
    simpa [AddInductive.Context.toTypeChecker] using hwhnfFuel]
  rw [whnfLoopInductiveConst context constName info
    (TypeChecker.Methods.withFuel recursionFuel) ({} : TypeChecker.State)
    whnfFuel hfind]
  rfl

/-- Full type checking of a closed, universe-monomorphic inductive constant
is determined by its exact post-declaration lookup. -/
theorem checkTypeInductiveConst
    (context : AddInductive.Context) (constName : Name)
    (info : InductiveVal) (result : Expr) (depth : Nat)
    (hdepth : context.fuel.recDepth = depth + 1)
    (hfind : context.env.find? constName = some (.inductInfo info))
    (hlevels : info.levelParams = [])
    (hunsafe : info.isUnsafe = false)
    (htype : info.type = result) :
    TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel
      (TypeChecker.checkType (.const constName [])) = .ok result := by
  have hinfer : TypeChecker.Inner.inferConstant context.toTypeChecker
      constName [] false = .ok result := by
    unfold TypeChecker.Inner.inferConstant
    rw [show context.toTypeChecker.env.get constName =
        .ok (.inductInfo info) by
      unfold Kernel.Environment.get
      simp only [AddInductive.Context.toTypeChecker, hfind]
      rfl]
    simp [AddInductive.Context.toTypeChecker, hlevels, hunsafe, htype,
      ConstantInfo.levelParams, ConstantInfo.isUnsafe,
      ConstantInfo.instantiateTypeLevelParamsCpp,
      ConstantInfo.type, ConstantInfo.toConstantVal,
      Expr.instantiateLevelParamsCpp,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  unfold TypeChecker.M.run TypeChecker.checkType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.const constName []) false
      (TypeChecker.Methods.withFuel depth) context.toTypeChecker
      ({} : TypeChecker.State)) = .ok result
  unfold TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange_eq,
    Expr.looseBVarRange']
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (get : TypeChecker.RecM TypeChecker.State)
      (TypeChecker.Methods.withFuel depth) context.toTypeChecker
        ({} : TypeChecker.State) =
      .ok (({} : TypeChecker.State), ({} : TypeChecker.State)) by rfl]
  simp only [Std.HashMap.getElem?_empty]
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (readThe TypeChecker.Context : TypeChecker.RecM
      TypeChecker.Context) (TypeChecker.Methods.withFuel depth)
        context.toTypeChecker ({} : TypeChecker.State) =
      .ok (context.toTypeChecker, ({} : TypeChecker.State)) by rfl]
  simp only
  rw [show TypeChecker.Inner.inferConstant context.toTypeChecker
      constName [] false = .ok result from hinfer]
  rfl

/-- The post-family lookup, together with positive checker and candidate
fuel, supplies the complete observer for a primitive family constant. -/
theorem inductiveConstCandidateObservable
    (context : AddInductive.Context) (constName : Name)
    (info : InductiveVal) (result : Expr)
    (depth whnfFuel inductiveFuel : Nat)
    (hdepth : context.fuel.recDepth = depth + 1)
    (hwhnfFuel : context.fuel.whnf = whnfFuel + 1)
    (_hinductive : context.fuel.inductiveFuel = inductiveFuel + 1)
    (hfind : context.env.find? constName = some (.inductInfo info))
    (hlevels : info.levelParams = [])
    (hunsafe : info.isUnsafe = false)
    (htype : info.type = result) :
    AddInductive.CandidateExpr.Observable context (.const constName []) := by
  have hcheck := checkTypeInductiveConst context constName info result depth
    hdepth hfind hlevels hunsafe htype
  have hwhnf := whnfInductiveConst context constName info depth whnfFuel
    hdepth hwhnfFuel hfind
  refine ⟨_, AddInductive.buildCandidateExpr_of_whnf_nonForall
    context (.const constName []) result (.const constName []) ?_
      hcheck hwhnf rfl⟩
  omega

/-- Lift a successful type candidate to its one-constructor wrapper. -/
theorem candidateConstructorObservable_of_expr
    {context : AddInductive.Context} {source : Constructor}
    (observable : AddInductive.CandidateExpr.Observable context source.type) :
    AddInductive.CandidateConstructor.Observable context source := by
  obtain ⟨candidate, run⟩ := observable
  refine ⟨⟨candidate⟩, ?_⟩
  unfold AddInductive.normalizeCandidateConstructor
  simp only [ReaderT.bind, Bind.bind, run, Except.bind,
    ReaderT.pure, Pure.pure, Except.pure]

/-- Loop-level form of `inductiveConstCandidateObservable`, used by each
recursive child of the canonical `Nat.succ` Pi candidate. -/
theorem inductiveConstCandidateLoop
    (context : AddInductive.Context) (constName : Name)
    (info : InductiveVal) (result : Expr)
    (depth whnfFuel candidateFuel : Nat)
    (hdepth : context.fuel.recDepth = depth + 1)
    (hwhnfFuel : context.fuel.whnf = whnfFuel + 1)
    (hfind : context.env.find? constName = some (.inductInfo info))
    (hlevels : info.levelParams = [])
    (hunsafe : info.isUnsafe = false)
    (htype : info.type = result) :
    ∃ trace : AddInductive.CandidateExprTrace context (.const constName []),
      AddInductive.buildCandidateExpr.loop context (.const constName [])
        (candidateFuel + 1) = .ok trace := by
  have hcheck := checkTypeInductiveConst context constName info result depth
    hdepth hfind hlevels hunsafe htype
  have hwhnf := whnfInductiveConst context constName info depth whnfFuel
    hdepth hwhnfFuel hfind
  exact ⟨_, AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
    context (.const constName []) result (.const constName []) candidateFuel
      hcheck hwhnf rfl⟩

/-- Reconstruct the canonical recursive `Nat.succ` candidate from its real
constructor root check and the declared `Nat` family lookup. -/
theorem natSuccCandidateObservable
    (context : AddInductive.Context) (familyInfo : InductiveVal)
    (binderName : Name) (binderInfo : BinderInfo) (inferred : Expr)
    (familyLookup : context.env.find? ``Nat =
      some (.inductInfo familyInfo))
    (rootCheck : AddInductive.CandidateCheckTypeStep.Valid
      ⟨context,
        .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo,
        inferred⟩)
    (familyLevels : familyInfo.levelParams = [])
    (familySafe : familyInfo.isUnsafe = false)
    (familyType : familyInfo.type = .sort (.succ .zero))
    (depthEq : context.fuel.recDepth = 10000)
    (whnfEq : context.fuel.whnf = 100000)
    (_inductiveEq : context.fuel.inductiveFuel = 1000)
    (emptyLctx : context.lctx = {}) :
    AddInductive.CandidateExpr.Observable context
      (.forallE binderName (.const ``Nat []) (.const ``Nat [])
        binderInfo) := by
  have rootWhnf : AddInductive.CandidateWhnfStep.Valid
      ⟨context,
        .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo,
        .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩ := by
    apply TypeChecker.CandidateExprIdentityReplay.Shaped.candidateWhnfForallSource_refl
      context _ 9999
    · omega
    · rfl
  let annotations := AddInductive.builtCandidateTypeAnnotations
    (.const ``Nat [])
  have annotationsRun : AddInductive.buildCandidateTypeAnnotations
      (.const ``Nat []) = .ok annotations :=
    AddInductive.buildCandidateTypeAnnotations_built _
  have annotationsConsumed : annotations.consumed = .const ``Nat [] := by
    have hmatches := AddInductive.CandidateTypeAnnotations.matches_of_build
      annotations annotationsRun
    simpa [AddInductive.CandidateTypeAnnotations.Matches,
      AddInductive.consumeTypeAnnotations] using hmatches
  have annotationsEq : AddInductive.CandidateIsDefEqStep.Valid
      ⟨context, .const ``Nat [], annotations.consumed⟩ := by
    rw [annotationsConsumed]
    exact AddInductive.candidateIsDefEqRefl context (.const ``Nat [])
  obtain ⟨domainTrace, domainRun⟩ :=
    inductiveConstCandidateLoop context ``Nat familyInfo
      (.sort (.succ .zero)) 9999 99999 9998
      (by omega) (by omega) familyLookup familyLevels familySafe familyType
  let bodyContext := context.pushLocalDecl binderName binderInfo
    annotations.consumed
  have bodyLookup : bodyContext.env.find? ``Nat =
      some (.inductInfo familyInfo) := by
    simpa [bodyContext, AddInductive.Context.pushLocalDecl] using familyLookup
  obtain ⟨bodyTrace, bodyRun⟩ :=
    inductiveConstCandidateLoop bodyContext ``Nat familyInfo
      (.sort (.succ .zero)) 9999 99999 9998
      (by simpa [bodyContext, AddInductive.Context.pushLocalDecl] using depthEq)
      (by simpa [bodyContext, AddInductive.Context.pushLocalDecl] using whnfEq)
      bodyLookup familyLevels familySafe familyType
  have bodySourceEq :
      (Expr.const ``Nat []).instantiate1 context.freshExpr =
        Expr.const ``Nat [] := by
    simp [Expr.instantiate1_eq, Expr.instantiate1']
  obtain ⟨bodyTrace', bodyRun'⟩ :
      ∃ bodyTrace' : AddInductive.CandidateExprTrace
          (context.pushLocalDecl binderName binderInfo annotations.consumed)
          ((Expr.const ``Nat []).instantiate1 context.freshExpr),
        AddInductive.buildCandidateExpr.loop
            (context.pushLocalDecl binderName binderInfo annotations.consumed)
            ((Expr.const ``Nat []).instantiate1 context.freshExpr) (9998 + 1) =
          .ok bodyTrace' := by
    rw [bodySourceEq]
    exact ⟨bodyTrace, by simpa only [bodyContext] using bodyRun⟩
  have fresh : context.lctx.find? context.freshFVarId = none := by
    rw [emptyLctx]
    exact TypeChecker.emptyLocalContextFindNone _
  let outerTrace : AddInductive.CandidateExprTrace context
      (.forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo) :=
    .forallE context
      (.forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo)
      inferred binderName (.const ``Nat []) (.const ``Nat []) binderInfo
      fresh annotations annotationsEq rootCheck rootWhnf domainTrace bodyTrace'
  have outerRun : AddInductive.buildCandidateExpr.loop context
      (.forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo)
      (9999 + 1) = .ok outerTrace := by
    exact AddInductive.buildCandidateExpr_loop_of_whnf_forall
      context
      (.forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo)
      inferred 9999 binderName (.const ``Nat []) (.const ``Nat []) binderInfo
      fresh annotations annotationsRun annotationsEq rootCheck rootWhnf
      domainTrace bodyTrace' domainRun bodyRun'
  refine ⟨⟨context, outerTrace⟩, ?_⟩
  unfold AddInductive.buildCandidateExpr
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  rw [show context.fuel.recDepth = 9999 + 1 by omega]
  rw [outerRun]
  rfl

/-- The second root observation in a successful canonical `Nat` constructor
validation run is precisely the full check needed by `Nat.succ`. -/
theorem natSuccRootCheckOfConstructorRun
    (stats : AddInductive.InductiveStats) (context : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo)
    (run : AddInductive.checkConstructors
      #[natSource binderName binderInfo] stats false context = .ok ()) :
    ∃ inferred, AddInductive.CandidateCheckTypeStep.Valid
      ⟨context.withEmptyLocalContext,
        .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo,
        inferred⟩ := by
  let validation := AddInductive.ConstructorBlockValidationRun.of_run run
  cases validation.traces with
  | cons constructors families =>
    cases families
    cases constructors with
    | cons seen zero tail fresh closed zeroRoot zeroType rest =>
      cases rest with
      | cons seen succ tail fresh closed succRoot succType done =>
        cases done
        exact ⟨succRoot.inferred, succRoot.valid⟩

/-- Canonical `Bool` validation and declaration discharge every recursive
normalization observer needed to build the retained candidate execution. -/
theorem boolCandidateObserversComplete
    (env : Environment) (mapWF : env.constants.WF) :
    AddInductive.NormalizationCandidateExecution.CandidateObserversComplete
      0 [boolSource] 0 false
        (AddInductive.Context.forInductive env [] false true {}) := by
  let candidateContext :=
    AddInductive.Context.forInductive env [] false true ({} : FuelConfig)
  intro validation validationRun familyEnv declareRun _constructorRun
  have familyObservable : AddInductive.CandidateFamilyType.Observable
      { candidateContext with lctx := {} } boolSource :=
    canonicalFamilyTypeObservable validationRun rfl
  obtain ⟨statsEq, validationEq, _depth, _inductiveFuel,
      _hdepth, _hinductive⟩ :=
    canonicalSingletonValidationStatsAndFuel validationRun rfl
  have boolStatsEq :
      AddInductive.singletonInductiveStats candidateContext boolSource
        (.succ .zero) = boolStats := by
    rfl
  have statsEq' : validation.stats = boolStats :=
    statsEq.trans boolStatsEq
  have declareRun' : AddInductive.declareInductiveTypes boolStats 0
      #[boolSource] 0 false candidateContext = .ok familyEnv := by
    simpa only [statsEq', validationEq] using declareRun
  have declareTrace := AddInductive.DeclareInductiveInfoListRun.of_run (by
    simpa only [AddInductive.declareInductiveTypes] using declareRun')
  let familyInfo := AddInductive.singletonDeclaredInfo boolStats 0 0
    boolSource 0 false candidateContext
  have infosEq :
      (AddInductive.declaredInductiveInfos boolStats 0 #[boolSource] 0 false
        candidateContext).toList = [familyInfo] := by
    exact AddInductive.declaredInductiveInfos_singleton boolStats 0 0
      boolSource 0 false candidateContext rfl
  have familyMember : familyInfo ∈
      (AddInductive.declaredInductiveInfos boolStats 0 #[boolSource] 0 false
        candidateContext).toList := by
    rw [infosEq]
    simp
  have familyMapWF : familyEnv.constants.WF :=
    declareTrace.map_wf mapWF
  have familyLookupMap : familyEnv.constants.find? familyInfo.name =
      some (.inductInfo familyInfo) :=
    declareTrace.map_lookup mapWF familyMember
  have familyLookup : familyEnv.find? ``Bool =
      some (.inductInfo familyInfo) := by
    change familyEnv.constants.find?' ``Bool = _
    rw [familyMapWF.find?'_eq_find?]
    simpa [familyInfo, AddInductive.singletonDeclaredInfo, boolSource] using
      familyLookupMap
  let constructorContext : AddInductive.Context :=
    { candidateContext with env := familyEnv, lctx := {} }
  have constObservable : AddInductive.CandidateExpr.Observable
      constructorContext (.const ``Bool []) := by
    apply inductiveConstCandidateObservable constructorContext ``Bool
      familyInfo (.sort (.succ .zero)) 9999 99999 999
    · rfl
    · rfl
    · rfl
    · simpa [constructorContext] using familyLookup
    · rfl
    · rfl
    · rfl
  have falseObservable : AddInductive.CandidateConstructor.Observable
      constructorContext ⟨``Bool.false, .const ``Bool []⟩ :=
    candidateConstructorObservable_of_expr constObservable
  have trueObservable : AddInductive.CandidateConstructor.Observable
      constructorContext ⟨``Bool.true, .const ``Bool []⟩ :=
    candidateConstructorObservable_of_expr constObservable
  exact ⟨.cons familyObservable .nil,
    .cons (.cons falseObservable (.cons trueObservable .nil)) .nil⟩

/-- Canonical `Nat` validation and declaration discharge every recursive
normalization observer, including both children of the `Nat.succ` Pi. -/
theorem natCandidateObserversComplete
    (env : Environment) (mapWF : env.constants.WF)
    (binderName : Name) (binderInfo : BinderInfo) :
    AddInductive.NormalizationCandidateExecution.CandidateObserversComplete
      0 [natSource binderName binderInfo] 0 false
        (AddInductive.Context.forInductive env [] false true {}) := by
  let candidateContext :=
    AddInductive.Context.forInductive env [] false true ({} : FuelConfig)
  intro validation validationRun familyEnv declareRun constructorRun
  have familyObservable : AddInductive.CandidateFamilyType.Observable
      { candidateContext with lctx := {} }
        (natSource binderName binderInfo) :=
    canonicalFamilyTypeObservable validationRun rfl
  obtain ⟨statsEq, validationEq, _depth, _inductiveFuel,
      _hdepth, _hinductive⟩ :=
    canonicalSingletonValidationStatsAndFuel validationRun rfl
  have natStatsEq :
      AddInductive.singletonInductiveStats candidateContext
        (natSource binderName binderInfo) (.succ .zero) = natStats := by
    rfl
  have statsEq' : validation.stats = natStats :=
    statsEq.trans natStatsEq
  have declareRun' : AddInductive.declareInductiveTypes natStats 0
      #[natSource binderName binderInfo] 0 false candidateContext =
        .ok familyEnv := by
    simpa only [statsEq', validationEq] using declareRun
  have declareTrace := AddInductive.DeclareInductiveInfoListRun.of_run (by
    simpa only [AddInductive.declareInductiveTypes] using declareRun')
  let familyInfo := AddInductive.singletonDeclaredInfo natStats 0 0
    (natSource binderName binderInfo) 0 false candidateContext
  have infosEq :
      (AddInductive.declaredInductiveInfos natStats 0
        #[natSource binderName binderInfo] 0 false
          candidateContext).toList = [familyInfo] := by
    exact AddInductive.declaredInductiveInfos_singleton natStats 0 0
      (natSource binderName binderInfo) 0 false candidateContext rfl
  have familyMember : familyInfo ∈
      (AddInductive.declaredInductiveInfos natStats 0
        #[natSource binderName binderInfo] 0 false
          candidateContext).toList := by
    rw [infosEq]
    simp
  have familyMapWF : familyEnv.constants.WF :=
    declareTrace.map_wf mapWF
  have familyLookupMap : familyEnv.constants.find? familyInfo.name =
      some (.inductInfo familyInfo) :=
    declareTrace.map_lookup mapWF familyMember
  have familyLookup : familyEnv.find? ``Nat =
      some (.inductInfo familyInfo) := by
    change familyEnv.constants.find?' ``Nat = _
    rw [familyMapWF.find?'_eq_find?]
    simpa [familyInfo, AddInductive.singletonDeclaredInfo, natSource] using
      familyLookupMap
  let constructorBase : AddInductive.Context :=
    { candidateContext with env := familyEnv }
  let constructorContext : AddInductive.Context :=
    { candidateContext with env := familyEnv, lctx := {} }
  have constructorRun' : AddInductive.checkConstructors
      #[natSource binderName binderInfo] natStats false constructorBase =
        .ok () := by
    simpa only [statsEq', validationEq, constructorBase] using constructorRun
  obtain ⟨inferred, rootCheckBase⟩ :=
    natSuccRootCheckOfConstructorRun natStats constructorBase
      binderName binderInfo constructorRun'
  have rootCheck : AddInductive.CandidateCheckTypeStep.Valid
      ⟨constructorContext,
        .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo,
        inferred⟩ := by
    simpa [constructorBase, constructorContext,
      AddInductive.Context.withEmptyLocalContext] using rootCheckBase
  have constObservable : AddInductive.CandidateExpr.Observable
      constructorContext (.const ``Nat []) := by
    apply inductiveConstCandidateObservable constructorContext ``Nat
      familyInfo (.sort (.succ .zero)) 9999 99999 999
    · rfl
    · rfl
    · rfl
    · simpa [constructorContext] using familyLookup
    · rfl
    · rfl
    · rfl
  have zeroObservable : AddInductive.CandidateConstructor.Observable
      constructorContext ⟨``Nat.zero, .const ``Nat []⟩ :=
    candidateConstructorObservable_of_expr constObservable
  have succExprObservable : AddInductive.CandidateExpr.Observable
      constructorContext
        (.forallE binderName (.const ``Nat []) (.const ``Nat [])
          binderInfo) := by
    apply natSuccCandidateObservable constructorContext familyInfo
      binderName binderInfo inferred
    · simpa [constructorContext] using familyLookup
    · exact rootCheck
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have succObservable : AddInductive.CandidateConstructor.Observable
      constructorContext
        ⟨``Nat.succ,
          .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩ :=
    candidateConstructorObservable_of_expr succExprObservable
  exact ⟨.cons familyObservable .nil,
    .cons (.cons zeroObservable (.cons succObservable .nil)) .nil⟩

/-- A constant cannot be normalized with an exhausted non-eager WHNF
counter, even when the mutual checker recursion has positive depth. -/
private theorem whnfConst_zero
    {env : Environment} {safety : DefinitionSafety}
    {lctx : LocalContext} {lparams : List Name} {fuel : FuelConfig}
    (constName : Name) (recursionFuel : Nat)
    (hdepth : fuel.recDepth = recursionFuel + 1)
    (hzero : fuel.whnf = 0) :
    TypeChecker.M.run env safety lctx lparams fuel
      (TypeChecker.whnf (.const constName [])) =
        .error .deterministicTimeout := by
  let context : TypeChecker.Context := { env, lctx, safety, lparams, fuel }
  unfold TypeChecker.M.run TypeChecker.whnf TypeChecker.RecM.run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.whnf' (.const constName [])
      (TypeChecker.Methods.withFuel recursionFuel)
      context ({} : TypeChecker.State)) = _
  unfold TypeChecker.Inner.whnf'
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind, Pure.pure]
  rw [show (get : TypeChecker.RecM TypeChecker.State)
      (TypeChecker.Methods.withFuel recursionFuel)
      context ({} : TypeChecker.State) =
        .ok (({} : TypeChecker.State), ({} : TypeChecker.State)) by rfl]
  simp only [Std.HashMap.getElem?_empty]
  simp only [readThe, MonadReaderOf.read, ReaderT.bind, StateT.bind,
    Except.bind, Bind.bind, ReaderT.pure, StateT.pure, Except.pure,
    Pure.pure]
  rw [show (liftM read : TypeChecker.RecM TypeChecker.Context)
      (TypeChecker.Methods.withFuel recursionFuel)
      context ({} : TypeChecker.State) =
        .ok (context, ({} : TypeChecker.State)) by rfl]
  simp only []
  rw [show context.eagerReduce = false by rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show context.fuel.whnf = 0 by simpa [context] using hzero]
  unfold TypeChecker.Inner.whnf'.loop
  rfl

theorem inferTypeFVar
    (context : AddInductive.Context) (id : FVarId) (type : Expr)
    (recursionFuel : Nat)
    (hdepth : context.fuel.recDepth = recursionFuel + 1)
    (hfind : context.lctx.find? id =
      some (.cdecl index id name type bi kind)) :
    TypeChecker.M.run context.env context.safety context.lctx context.lparams
      context.fuel (TypeChecker.inferType (.fvar id)) = .ok type := by
  unfold TypeChecker.M.run TypeChecker.inferType TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.inferType' (.fvar id) true
      (TypeChecker.Methods.withFuel recursionFuel) context.toTypeChecker
      ({} : TypeChecker.State)) = .ok type
  rw [inferTypeFVarCore context id type
    (TypeChecker.Methods.withFuel recursionFuel) ({} : TypeChecker.State)
    Std.HashMap.getElem?_empty hfind]
  rfl

private def natMajorType : Expr :=
  AddInductive.consumeTypeAnnotations <|
    mkAppN (mkAppN natStats.indConsts[0]! natStats.params) #[]

private theorem natLocalContextMkForall_empty
    (lctx : LocalContext) (e : Expr) : lctx.mkForall #[] e = e := by
  unfold LocalContext.mkForall LocalContext.mkBinding
  change e.abstract #[] = e
  simpa using (Expr.abstract_eq e [] (.inl rfl) .nil)

private def natMajorContext (root : AddInductive.Context) :
    AddInductive.Context :=
  root.pushLocalDecl `t .default natMajorType

private def natMotiveType (root : AddInductive.Context) : Expr :=
  let majorContext := natMajorContext root
  majorContext.lctx.mkForall #[] <|
    majorContext.lctx.mkForall #[root.freshExpr] <|
      .sort (.param `u)

private def natMotiveContext (root : AddInductive.Context) :
    AddInductive.Context :=
  (natMajorContext root).pushLocalDecl `motive .default
    (AddInductive.consumeTypeAnnotations (natMotiveType root))

private def natInitialRecInfos (root : AddInductive.Context) :
    Array AddInductive.RecInfo :=
  #[{ motive := (natMajorContext root).freshExpr
      minors := #[]
      indices := #[]
      major := root.freshExpr }]

private def natZeroMinorType (root : AddInductive.Context) : Expr :=
  let context := natMotiveContext root
  let recInfos := natInitialRecInfos root
  let t := Expr.const ``Nat []
  let (itIdx, itIndices) := AddInductive.getIIndices natStats t
  let introApp := mkAppN
    (mkAppN (.const ``Nat.zero natStats.levels) natStats.params) #[]
  let motiveApp := Expr.app
    (mkAppN recInfos[itIdx]!.motive itIndices) introApp
  context.lctx.mkForall #[] <| context.lctx.mkForall #[] motiveApp

private def natZeroContext (root : AddInductive.Context) :
    AddInductive.Context :=
  (natMotiveContext root).pushLocalDecl `zero .default
    (AddInductive.consumeTypeAnnotations (natZeroMinorType root))

private def natAfterZeroRecInfos (root : AddInductive.Context) :
    Array AddInductive.RecInfo :=
  (natInitialRecInfos root).modify 0 fun info =>
    { info with minors := info.minors.push (natMotiveContext root).freshExpr }

private def natSuccArgContext (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo) : AddInductive.Context :=
  (natZeroContext root).pushLocalDecl binderName binderInfo
    (AddInductive.consumeTypeAnnotations (.const ``Nat []))

private def natSuccIHType (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo) : Expr :=
  let context := natSuccArgContext root binderName binderInfo
  context.lctx.mkForall #[] <|
    .app (natMajorContext root).freshExpr (natZeroContext root).freshExpr

private def natSuccIHContext (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo) : AddInductive.Context :=
  (natSuccArgContext root binderName binderInfo).pushLocalDecl
    (binderName.appendAfter "_ih") .default
    (AddInductive.consumeTypeAnnotations <|
      natSuccIHType root binderName binderInfo)

private def natSuccMinorType (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo) : Expr :=
  let context := natSuccIHContext root binderName binderInfo
  let n := (natZeroContext root).freshExpr
  let ih := (natSuccArgContext root binderName binderInfo).freshExpr
  let introApp := .app (.const ``Nat.succ []) n
  let motiveApp := .app (natMajorContext root).freshExpr introApp
  context.lctx.mkForall #[n] <| context.lctx.mkForall #[ih] motiveApp

private def natSuccContext (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo) : AddInductive.Context :=
  (natSuccIHContext root binderName binderInfo).pushLocalDecl `succ .default
    (AddInductive.consumeTypeAnnotations <|
      natSuccMinorType root binderName binderInfo)

private def natFinalRecInfos (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo) :
    Array AddInductive.RecInfo :=
  (natAfterZeroRecInfos root).modify 0 fun info =>
    { info with minors := info.minors.push (natSuccIHContext root
        binderName binderInfo).freshExpr }

private theorem natGetIIndices :
    AddInductive.getIIndices natStats (.const ``Nat []) = (0, #[]) := by
  have valid : AddInductive.isValidIndAppIdx natStats
      (.const ``Nat []) 0 = true := by
    simp +decide [AddInductive.isValidIndAppIdx, natStats,
      Expr.getAppFn, Expr.getAppArgs, Expr.getAppNumArgs]
  have found := AddInductive.isValidIndApp?_singleton_zero natStats
    (.const ``Nat []) (by decide) valid
  have args : (Expr.const ``Nat []).getAppArgs = #[] := by
    rw [Expr.getAppArgs_eq]
    rfl
  rw [AddInductive.getIIndices, found, args]
  rw [show natStats.params.size = 0 by rfl]
  apply Prod.ext
  · rfl
  · apply Array.eq_empty_of_size_eq_zero
    change ((#[] : Array Expr).toSubarray 0 0).copy.size = 0
    rw [Subarray.copy_eq_toArray, Subarray.size_toArray,
      Subarray.size_eq]
    rfl

private theorem natValidIndApp :
    AddInductive.isValidIndApp? natStats (.const ``Nat []) = some 0 := by
  apply AddInductive.isValidIndApp?_singleton_zero natStats
    (.const ``Nat []) (by decide)
  simp +decide [AddInductive.isValidIndAppIdx, natStats,
    Expr.getAppFn, Expr.getAppArgs, Expr.getAppNumArgs]

private theorem mkRecInfos_nat
    (root : AddInductive.Context) (binderName : Name)
    (binderInfo : BinderInfo)
    (rootRun : TypeChecker.CandidateLocalContextRun root)
    (familyInfo : InductiveVal)
    (hfind : root.env.find? ``Nat = some (.inductInfo familyInfo))
    (hwhnf : TypeChecker.M.run root.env root.safety root.lctx root.lparams
      root.fuel (TypeChecker.whnf (natSource binderName binderInfo).type) =
        .ok (.sort (.succ .zero)))
    (hdepth : root.fuel.recDepth = recursionFuel + 1)
    (hwhnfFuel : root.fuel.whnf = whnfFuel + 1)
    (hinductive : root.fuel.inductiveFuel = inductiveFuel + 2)
    (k : Array AddInductive.RecInfo → AddInductive.M α) :
    AddInductive.mkRecInfos natStats #[natSource binderName binderInfo]
      (.param `u) k root =
        k (natFinalRecInfos root binderName binderInfo)
          (natSuccContext root binderName binderInfo) := by
  have majorRun : TypeChecker.CandidateLocalContextRun
      (natMajorContext root) := by
    simpa [natMajorContext] using rootRun.push `t .default natMajorType
  have motiveRun : TypeChecker.CandidateLocalContextRun
      (natMotiveContext root) := by
    simpa [natMotiveContext] using majorRun.push `motive .default
      (AddInductive.consumeTypeAnnotations (natMotiveType root))
  have zeroRun : TypeChecker.CandidateLocalContextRun
      (natZeroContext root) := by
    simpa [natZeroContext] using motiveRun.push `zero .default
      (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
  have succArgRun : TypeChecker.CandidateLocalContextRun
      (natSuccArgContext root binderName binderInfo) := by
    simpa [natSuccArgContext] using zeroRun.push binderName binderInfo
      (AddInductive.consumeTypeAnnotations (.const ``Nat []))
  have nFind := zeroRun.push_findNew binderName binderInfo
    (AddInductive.consumeTypeAnnotations (.const ``Nat []))
  have nFind' : (natSuccArgContext root binderName binderInfo).lctx.find?
      (natZeroContext root).freshFVarId = some
        (.cdecl (natZeroContext root).lctx.decls.size
          (natZeroContext root).freshFVarId binderName
          (AddInductive.consumeTypeAnnotations (.const ``Nat []))
          binderInfo .default) := by
    simpa [natSuccArgContext] using nFind
  have natWhnf : TypeChecker.M.run root.env root.safety
      (natSuccArgContext root binderName binderInfo).lctx root.lparams root.fuel
      (TypeChecker.whnf (.const ``Nat [])) = .ok (.const ``Nat []) := by
    apply whnfInductiveConst
      (natSuccArgContext root binderName binderInfo) ``Nat familyInfo
      recursionFuel whnfFuel
    · simpa [natSuccArgContext, natZeroContext, natMotiveContext,
        natMajorContext, AddInductive.Context.pushLocalDecl] using hdepth
    · simpa [natSuccArgContext, natZeroContext, natMotiveContext,
        natMajorContext, AddInductive.Context.pushLocalDecl] using hwhnfFuel
    · simpa [natSuccArgContext, natZeroContext, natMotiveContext,
        natMajorContext, AddInductive.Context.pushLocalDecl] using hfind
  have nInfer : TypeChecker.M.run root.env root.safety
      (natSuccArgContext root binderName binderInfo).lctx root.lparams root.fuel
      (TypeChecker.inferType (natZeroContext root).freshExpr) =
        .ok (.const ``Nat []) := by
    have actual := inferTypeFVar (natSuccArgContext root binderName binderInfo)
      (natZeroContext root).freshFVarId
      (AddInductive.consumeTypeAnnotations (.const ``Nat [])) recursionFuel
      (by simpa [natSuccArgContext, natZeroContext, natMotiveContext,
        natMajorContext, AddInductive.Context.pushLocalDecl] using hdepth)
      nFind'
    simpa [natSuccArgContext, natZeroContext, natMotiveContext,
      natMajorContext, AddInductive.Context.pushLocalDecl,
      AddInductive.Context.freshExpr,
      AddInductive.consumeTypeAnnotations] using actual
  have natWhnfAtPush : TypeChecker.M.run
      ((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).env
      ((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).safety
      ((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).lctx
      ((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).lparams
      ((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).fuel
      (TypeChecker.whnf (.const ``Nat [])) = .ok (.const ``Nat []) := by
    simpa [natSuccArgContext, natZeroContext, natMotiveContext,
      natMajorContext, AddInductive.Context.pushLocalDecl] using natWhnf
  have nInferAtPush : TypeChecker.M.run
      ((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).env
      ((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).safety
      ((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).lctx
      ((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).lparams
      ((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).fuel
      (TypeChecker.inferType (natZeroContext root).freshExpr) =
        .ok (.const ``Nat []) := by
    simpa [natSuccArgContext, natZeroContext, natMotiveContext,
      natMajorContext, AddInductive.Context.pushLocalDecl] using nInfer
  have nUserName :
      (((natZeroContext root).pushLocalDecl binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))).lctx.get!
          (natZeroContext root).freshExpr.fvarId!).userName = binderName := by
    rw [show (natZeroContext root).freshExpr.fvarId! =
      (natZeroContext root).freshFVarId by rfl]
    simp [LocalContext.get!, nFind]
    rfl
  have nUserName' :
      (((natZeroContext root).pushLocalDecl binderName binderInfo
        (.const ``Nat [])).lctx.get!
          (natZeroContext root).freshExpr.fvarId!).userName = binderName := by
    simpa [AddInductive.consumeTypeAnnotations] using nUserName
  unfold AddInductive.mkRecInfos
  rw [AddInductive.mkRecInfos.loopInd1.eq_1]
  have hsize : 0 < #[natSource binderName binderInfo].size := by simp
  rw [dif_pos hsize]
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind]
  rw [show #[natSource binderName binderInfo][0].type =
      (natSource binderName binderInfo).type by rfl]
  simp only [AddInductive.liftTypeChecker_apply]
  rw [hwhnf]
  simp only [hinductive, AddInductive.mkRecInfos.loopArgs1,
    AddInductive.withLocalDecl_apply, AddInductive.getLCtx_apply,
    ReaderT.bind, Bind.bind, Except.bind, Pure.pure, ReaderT.pure,
    Except.pure]
  rw [AddInductive.mkRecInfos.loopInd1.eq_1]
  have hdone : ¬ 1 < #[natSource binderName binderInfo].size := by simp
  rw [dif_neg hdone]
  rw [AddInductive.mkRecInfos.loopInd2.eq_1]
  rw [dif_pos hsize]
  rw [show #[natSource binderName binderInfo][0] =
      natSource binderName binderInfo by rfl]
  rw [show (natSource binderName binderInfo).name = ``Nat by rfl]
  rw [show (natSource binderName binderInfo).ctors =
    [⟨``Nat.zero, .const ``Nat []⟩,
     ⟨``Nat.succ,
       .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩]
      by rfl]
  simp only [AddInductive.mkRecInfos.loopCtors,
    AddInductive.mkRecInfos.loopCtorArgs,
    readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
    Except.bind, AddInductive.Context.pushLocalDecl]
  rw [hinductive]
  simp only [AddInductive.mkRecInfos.loopCtorArgs.loop]
  rw [AddInductive.mkRecInfos.loopU.eq_1]
  have huempty : ¬ 0 < (#[] : Array Expr).size := by decide
  rw [dif_neg huempty]
  simp only [AddInductive.getLCtx_apply,
    AddInductive.withLocalDecl_apply, ReaderT.bind, Bind.bind, Except.bind,
    Pure.pure, ReaderT.pure, Except.pure]
  change AddInductive.mkRecInfos.loopCtors natStats ``Nat 0
    (natAfterZeroRecInfos root)
    [⟨``Nat.succ,
      .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩]
    (fun recInfos => AddInductive.mkRecInfos.loopInd2 natStats
      #[natSource binderName binderInfo] 1 recInfos k)
    (natZeroContext root) = _
  simp only [AddInductive.mkRecInfos.loopCtors,
    AddInductive.mkRecInfos.loopCtorArgs,
    readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
    Except.bind]
  rw [show (natZeroContext root).fuel.inductiveFuel =
      (inductiveFuel + 1) + 1 by
    simpa [natZeroContext, natMotiveContext, natMajorContext,
      AddInductive.Context.pushLocalDecl] using hinductive]
  simp only [AddInductive.mkRecInfos.loopCtorArgs.loop]
  rw [show natStats.params[0]? = none by rfl]
  simp only [AddInductive.withLocalDecl_apply, ReaderT.bind, Bind.bind,
    Except.bind]
  unfold AddInductive.isRecArg
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
    Except.bind]
  rw [show ((natZeroContext root).pushLocalDecl binderName binderInfo
      (AddInductive.consumeTypeAnnotations (.const ``Nat []))).fuel.inductiveFuel =
      (inductiveFuel + 1) + 1 by
    simpa [natZeroContext, natMotiveContext, natMajorContext,
      AddInductive.Context.pushLocalDecl] using hinductive]
  unfold AddInductive.isRecArg.loop
  simp only [AddInductive.liftTypeChecker_apply, ReaderT.bind, Bind.bind]
  rw [natWhnfAtPush]
  simp only [Except.bind]
  rw [natValidIndApp]
  simp only [Option.isSome, if_true, Pure.pure, ReaderT.pure,
    Except.pure, Except.bind]
  simp only [Expr.instantiate1_eq, Expr.instantiate1']
  rw [AddInductive.mkRecInfos.loopU.eq_1]
  have huone : 0 < ((#[] : Array Expr).push
      (natZeroContext root).freshExpr).size := by simp
  rw [dif_pos huone]
  simp only [AddInductive.mkRecInfos.loopUArgs,
    readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, AddInductive.liftTypeChecker_apply]
  rw [show ((#[] : Array Expr).push
      (natZeroContext root).freshExpr)[0] =
        (natZeroContext root).freshExpr by rfl]
  rw [nInferAtPush]
  simp only [Except.bind]
  rw [natWhnfAtPush]
  simp only [Except.bind]
  simp only [Pure.pure, ReaderT.pure, Except.pure, Except.bind]
  rw [show ((natZeroContext root).pushLocalDecl binderName binderInfo
      (AddInductive.consumeTypeAnnotations (.const ``Nat []))).fuel.inductiveFuel =
      (inductiveFuel + 1) + 1 by
    simpa [natZeroContext, natMotiveContext, natMajorContext,
      AddInductive.Context.pushLocalDecl] using hinductive]
  unfold AddInductive.mkRecInfos.loopUArgs.loop
  simp only [AddInductive.getLCtx_apply, Pure.pure, ReaderT.pure,
    Except.pure, AddInductive.withLocalDecl_apply, ReaderT.bind, Bind.bind,
    Except.bind]
  simp only [natGetIIndices]
  rw [AddInductive.mkRecInfos.loopU.eq_1]
  have hudone : ¬ 1 < ((#[] : Array Expr).push
      (natZeroContext root).freshExpr).size := by simp
  rw [dif_neg hudone]
  simp only [AddInductive.getLCtx_apply,
    AddInductive.withLocalDecl_apply, ReaderT.bind, Bind.bind, Except.bind,
    Pure.pure, ReaderT.pure, Except.pure]
  rw [AddInductive.mkRecInfos.loopInd2.eq_1]
  rw [dif_neg hdone]
  simp [nUserName', natSuccIHType, natLocalContextMkForall_empty,
    natAfterZeroRecInfos, natInitialRecInfos, natSuccIHContext,
    natSuccArgContext, natSuccMinorType, natSuccContext,
    natFinalRecInfos, natStats, natMajorType, mkAppN,
    AddInductive.consumeTypeAnnotations, Name.replacePrefix]

/-- Translation-facing canonical host type of the generated `Nat.rec`. -/
def natExpectedRecursorType : Expr :=
  Expr.forallE .anonymous
    (Expr.forallE .anonymous (.const ``Nat []) (.sort (.param `u)) .default)
    (Expr.forallE .anonymous
      (.app (.bvar 0) (.const ``Nat.zero []))
      (Expr.forallE .anonymous
        (Expr.forallE .anonymous (.const ``Nat [])
          (Expr.forallE .anonymous
            (.app (.bvar 2) (.bvar 0))
            (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 1)))
            .default)
          .default)
        (Expr.forallE .anonymous (.const ``Nat [])
          (.app (.bvar 3) (.bvar 0)) .default)
        .default)
      .default)
    .default

private def natGeneratedRecursorType (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo) : Expr :=
  let recInfos := natFinalRecInfos root binderName binderInfo
  AddInductive.declareRecursors.generatedRecursorType natStats
    (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
    (natSuccContext root binderName binderInfo).lctx recInfos[0]!

private theorem natMotiveType_eq
    (root : AddInductive.Context)
    (rootRun : TypeChecker.CandidateLocalContextRun root) :
    natMotiveType root =
      .forallE `t natMajorType (.sort (.param `u)) .default := by
  have majorFind := rootRun.push_findNew `t .default natMajorType
  have majorFind' : (natMajorContext root).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t natMajorType .default .default) := by
    simpa [natMajorContext] using majorFind
  unfold natMotiveType
  simp only [AddInductive.Context.freshExpr]
  rw [natLocalContextMkForall_empty,
    localContextMkForall_singleton majorFind'
      (by simp [Expr.looseBVarRange'])
      (by simp [natMajorType, natStats, mkAppN,
        AddInductive.consumeTypeAnnotations, Expr.looseBVarRange'])]
  rfl

private theorem natFinalRecInfos_eq (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo) :
    natFinalRecInfos root binderName binderInfo =
      #[{ motive := (natMajorContext root).freshExpr
          minors := #[(natMotiveContext root).freshExpr,
            (natSuccIHContext root binderName binderInfo).freshExpr]
          indices := #[]
          major := root.freshExpr }] := by
  rfl

private theorem natZeroMinorType_eq (root : AddInductive.Context) :
    natZeroMinorType root =
      .app (natMajorContext root).freshExpr (.const ``Nat.zero []) := by
  unfold natZeroMinorType
  simp only [natGetIIndices]
  simp [natInitialRecInfos, natStats, mkAppN,
    natLocalContextMkForall_empty]

private theorem natSuccIHType_eq (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo) :
    natSuccIHType root binderName binderInfo =
      .app (natMajorContext root).freshExpr
        (natZeroContext root).freshExpr := by
  simp [natSuccIHType, natLocalContextMkForall_empty]

private theorem natSuccMinorType_eq
    (root : AddInductive.Context) (binderName : Name)
    (binderInfo : BinderInfo)
    (rootRun : TypeChecker.CandidateLocalContextRun root) :
    natSuccMinorType root binderName binderInfo =
      .forallE binderName (.const ``Nat [])
        (.forallE (binderName.appendAfter "_ih")
          (.app (natMajorContext root).freshExpr (.bvar 0))
          (.app (natMajorContext root).freshExpr
            (.app (.const ``Nat.succ []) (.bvar 1))) .default)
        binderInfo := by
  have majorRun : TypeChecker.CandidateLocalContextRun
      (natMajorContext root) := by
    simpa [natMajorContext] using
      rootRun.push `t .default natMajorType
  have motiveRun : TypeChecker.CandidateLocalContextRun
      (natMotiveContext root) := by
    simpa [natMotiveContext] using
      majorRun.push `motive .default
        (AddInductive.consumeTypeAnnotations (natMotiveType root))
  have zeroRun : TypeChecker.CandidateLocalContextRun
      (natZeroContext root) := by
    simpa [natZeroContext] using
      motiveRun.push `zero .default
        (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
  have nRun : TypeChecker.CandidateLocalContextRun
      (natSuccArgContext root binderName binderInfo) := by
    simpa [natSuccArgContext] using
      zeroRun.push binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))
  have ihRun : TypeChecker.CandidateLocalContextRun
      (natSuccIHContext root binderName binderInfo) := by
    simpa [natSuccIHContext] using
      nRun.push (binderName.appendAfter "_ih") .default
        (AddInductive.consumeTypeAnnotations
          (natSuccIHType root binderName binderInfo))
  have nFind0 := zeroRun.push_findNew binderName binderInfo
    (AddInductive.consumeTypeAnnotations (.const ``Nat []))
  have nFind : (natSuccIHContext root binderName binderInfo).lctx.find?
      (natZeroContext root).freshFVarId = some
        (.cdecl (natZeroContext root).lctx.decls.size
          (natZeroContext root).freshFVarId binderName
          (AddInductive.consumeTypeAnnotations (.const ``Nat []))
          binderInfo .default) := by
    simpa [natSuccIHContext] using
      nRun.push_findOld (binderName.appendAfter "_ih") .default
        (AddInductive.consumeTypeAnnotations
          (natSuccIHType root binderName binderInfo)) nFind0
  have ihFind := nRun.push_findNew
    (binderName.appendAfter "_ih") .default
    (AddInductive.consumeTypeAnnotations
      (natSuccIHType root binderName binderInfo))
  have ihFind' : (natSuccIHContext root binderName binderInfo).lctx.find?
      (natSuccArgContext root binderName binderInfo).freshFVarId = some
        (.cdecl (natSuccArgContext root binderName binderInfo).lctx.decls.size
          (natSuccArgContext root binderName binderInfo).freshFVarId
          (binderName.appendAfter "_ih")
          (AddInductive.consumeTypeAnnotations
            (natSuccIHType root binderName binderInfo))
          .default .default) := by
    simpa [natSuccIHContext] using ihFind
  have nFindArg : (natSuccArgContext root binderName binderInfo).lctx.find?
      (natZeroContext root).freshFVarId = some
        (.cdecl (natZeroContext root).lctx.decls.size
          (natZeroContext root).freshFVarId binderName
          (AddInductive.consumeTypeAnnotations (.const ``Nat []))
          binderInfo .default) := by
    simpa [natSuccArgContext] using nFind0
  have motiveFind0 := majorRun.push_findNew `motive .default
    (AddInductive.consumeTypeAnnotations (natMotiveType root))
  have motiveFindMotive : (natMotiveContext root).lctx.find?
      (natMajorContext root).freshFVarId = some
        (.cdecl (natMajorContext root).lctx.decls.size
          (natMajorContext root).freshFVarId `motive
          (AddInductive.consumeTypeAnnotations (natMotiveType root))
          .default .default) := by
    simpa [natMotiveContext] using motiveFind0
  have motiveFindZero : (natZeroContext root).lctx.find?
      (natMajorContext root).freshFVarId = some
        (.cdecl (natMajorContext root).lctx.decls.size
          (natMajorContext root).freshFVarId `motive
          (AddInductive.consumeTypeAnnotations (natMotiveType root))
          .default .default) := by
    simpa [natZeroContext] using
      motiveRun.push_findOld `zero .default
        (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
        motiveFindMotive
  have motiveFindN : (natSuccArgContext root binderName binderInfo).lctx.find?
      (natMajorContext root).freshFVarId = some
        (.cdecl (natMajorContext root).lctx.decls.size
          (natMajorContext root).freshFVarId `motive
          (AddInductive.consumeTypeAnnotations (natMotiveType root))
          .default .default) := by
    simpa [natSuccArgContext] using
      zeroRun.push_findOld binderName binderInfo
        (AddInductive.consumeTypeAnnotations (.const ``Nat []))
        motiveFindZero
  have motive_ne_n : (natMajorContext root).freshFVarId ≠
      (natZeroContext root).freshFVarId := by
    intro equal
    have fresh := zeroRun.fresh
    rw [← equal, motiveFindZero] at fresh
    contradiction
  have motive_ne_ih : (natMajorContext root).freshFVarId ≠
      (natSuccArgContext root binderName binderInfo).freshFVarId := by
    intro equal
    have fresh := nRun.fresh
    rw [← equal, motiveFindN] at fresh
    contradiction
  have n_ne_ih : (natZeroContext root).freshFVarId ≠
      (natSuccArgContext root binderName binderInfo).freshFVarId := by
    intro equal
    have fresh := nRun.fresh
    rw [← equal, nFindArg] at fresh
    contradiction
  dsimp only [natSuccMinorType]
  change (natSuccIHContext root binderName binderInfo).lctx.mkForall
      #[.fvar (natZeroContext root).freshFVarId]
      ((natSuccIHContext root binderName binderInfo).lctx.mkForall
        #[.fvar (natSuccArgContext root binderName binderInfo).freshFVarId]
        (.app (natMajorContext root).freshExpr
          (.app (.const ``Nat.succ [])
            (.fvar (natZeroContext root).freshFVarId)))) = _
  rw [localContextMkForall_singleton ihFind'
      (by simp [AddInductive.Context.freshExpr, Expr.abstract1,
        Expr.looseBVarRange'])
      (by simp [natSuccIHType_eq, AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.abstract1,
        Expr.looseBVarRange']),
    localContextMkForall_singleton nFind
      (by
        have ih_ne_motive := motive_ne_ih.symm
        have ih_ne_n := n_ne_ih.symm
        simp [natSuccIHType_eq, AddInductive.consumeTypeAnnotations,
          AddInductive.Context.freshExpr, Expr.abstract1,
          ih_ne_motive, ih_ne_n, Expr.looseBVarRange'])
      (by simp [AddInductive.consumeTypeAnnotations,
        Expr.looseBVarRange'])]
  rw [natSuccIHType_eq]
  have ih_bne_motive :
      ((natSuccArgContext root binderName binderInfo).freshFVarId ==
        (natMajorContext root).freshFVarId) = false :=
    beq_eq_false_iff_ne.mpr motive_ne_ih.symm
  have ih_bne_n :
      ((natSuccArgContext root binderName binderInfo).freshFVarId ==
        (natZeroContext root).freshFVarId) = false :=
    beq_eq_false_iff_ne.mpr n_ne_ih.symm
  have n_ne_motive : (natZeroContext root).freshFVarId ≠
      (natMajorContext root).freshFVarId := motive_ne_n.symm
  simp [AddInductive.consumeTypeAnnotations,
    AddInductive.Context.freshExpr, Expr.abstract1, Expr.abstract_eq,
    n_ne_ih, n_ne_motive, motive_ne_n, motive_ne_ih,
    ih_bne_motive, ih_bne_n]

private def natRawExpectedRecursorType (binderName : Name)
    (binderInfo : BinderInfo) : Expr :=
  Expr.forallE `motive
    (Expr.forallE `t (.const ``Nat []) (.sort (.param `u)) .default)
    (Expr.forallE `zero
      (.app (.bvar 0) (.const ``Nat.zero []))
      (Expr.forallE `succ
        (Expr.forallE binderName (.const ``Nat [])
          (Expr.forallE (binderName.appendAfter "_ih")
            (.app (.bvar 2) (.bvar 0))
            (.app (.bvar 3) (.app (.const ``Nat.succ []) (.bvar 1)))
            .default)
          binderInfo)
        (Expr.forallE `t (.const ``Nat [])
          (.app (.bvar 3) (.bvar 0)) .default)
        .default)
      .default)
    .default

private theorem natGeneratedRecursorRaw_eq
    (root : AddInductive.Context) (binderName : Name)
    (binderInfo : BinderInfo)
    (rootRun : TypeChecker.CandidateLocalContextRun root) :
    let recInfos := natFinalRecInfos root binderName binderInfo
    ((natSuccContext root binderName binderInfo).lctx.mkForall
        natStats.params <|
      (natSuccContext root binderName binderInfo).lctx.mkForall
        (recInfos.map (·.motive)) <|
      (natSuccContext root binderName binderInfo).lctx.mkForall
        (recInfos.flatMap (·.minors)) <|
      (natSuccContext root binderName binderInfo).lctx.mkForall
        recInfos[0]!.indices <|
      (natSuccContext root binderName binderInfo).lctx.mkForall
        #[recInfos[0]!.major]
        (.app (mkAppN recInfos[0]!.motive recInfos[0]!.indices)
          recInfos[0]!.major)) =
      natRawExpectedRecursorType binderName binderInfo := by
  have majorRun : TypeChecker.CandidateLocalContextRun
      (natMajorContext root) := by
    simpa [natMajorContext] using rootRun.push `t .default natMajorType
  have motiveRun : TypeChecker.CandidateLocalContextRun
      (natMotiveContext root) := by
    simpa [natMotiveContext] using majorRun.push `motive .default
      (AddInductive.consumeTypeAnnotations (natMotiveType root))
  have zeroRun : TypeChecker.CandidateLocalContextRun
      (natZeroContext root) := by
    simpa [natZeroContext] using motiveRun.push `zero .default
      (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
  have nRun : TypeChecker.CandidateLocalContextRun
      (natSuccArgContext root binderName binderInfo) := by
    simpa [natSuccArgContext] using zeroRun.push binderName binderInfo
      (AddInductive.consumeTypeAnnotations (.const ``Nat []))
  have ihRun : TypeChecker.CandidateLocalContextRun
      (natSuccIHContext root binderName binderInfo) := by
    simpa [natSuccIHContext] using nRun.push
      (binderName.appendAfter "_ih") .default
      (AddInductive.consumeTypeAnnotations
        (natSuccIHType root binderName binderInfo))
  have succRun : TypeChecker.CandidateLocalContextRun
      (natSuccContext root binderName binderInfo) := by
    simpa [natSuccContext] using ihRun.push `succ .default
      (AddInductive.consumeTypeAnnotations
        (natSuccMinorType root binderName binderInfo))

  have tFindMajor0 := rootRun.push_findNew `t .default natMajorType
  have tFindMajor : (natMajorContext root).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t natMajorType .default .default) := by
    simpa [natMajorContext] using tFindMajor0
  have tFindMotive : (natMotiveContext root).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t natMajorType .default .default) := by
    simpa [natMotiveContext] using majorRun.push_findOld `motive .default
      (AddInductive.consumeTypeAnnotations (natMotiveType root)) tFindMajor
  have tFindZero : (natZeroContext root).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t natMajorType .default .default) := by
    simpa [natZeroContext] using motiveRun.push_findOld `zero .default
      (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
      tFindMotive
  have tFindN : (natSuccArgContext root binderName binderInfo).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t natMajorType .default .default) := by
    simpa [natSuccArgContext] using zeroRun.push_findOld binderName binderInfo
      (AddInductive.consumeTypeAnnotations (.const ``Nat [])) tFindZero
  have tFindIH : (natSuccIHContext root binderName binderInfo).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t natMajorType .default .default) := by
    simpa [natSuccIHContext] using nRun.push_findOld
      (binderName.appendAfter "_ih") .default
      (AddInductive.consumeTypeAnnotations
        (natSuccIHType root binderName binderInfo)) tFindN
  have tFind : (natSuccContext root binderName binderInfo).lctx.find?
      root.freshFVarId = some (.cdecl root.lctx.decls.size
        root.freshFVarId `t natMajorType .default .default) := by
    simpa [natSuccContext] using ihRun.push_findOld `succ .default
      (AddInductive.consumeTypeAnnotations
        (natSuccMinorType root binderName binderInfo)) tFindIH

  have motiveFind0 := majorRun.push_findNew `motive .default
    (AddInductive.consumeTypeAnnotations (natMotiveType root))
  have motiveFindMotive : (natMotiveContext root).lctx.find?
      (natMajorContext root).freshFVarId = some (.cdecl
        (natMajorContext root).lctx.decls.size
        (natMajorContext root).freshFVarId `motive
        (AddInductive.consumeTypeAnnotations (natMotiveType root))
        .default .default) := by
    simpa [natMotiveContext] using motiveFind0
  have motiveFindZero : (natZeroContext root).lctx.find?
      (natMajorContext root).freshFVarId = some (.cdecl
        (natMajorContext root).lctx.decls.size
        (natMajorContext root).freshFVarId `motive
        (AddInductive.consumeTypeAnnotations (natMotiveType root))
        .default .default) := by
    simpa [natZeroContext] using motiveRun.push_findOld `zero .default
      (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
      motiveFindMotive
  have motiveFindN : (natSuccArgContext root binderName binderInfo).lctx.find?
      (natMajorContext root).freshFVarId = some (.cdecl
        (natMajorContext root).lctx.decls.size
        (natMajorContext root).freshFVarId `motive
        (AddInductive.consumeTypeAnnotations (natMotiveType root))
        .default .default) := by
    simpa [natSuccArgContext] using zeroRun.push_findOld binderName binderInfo
      (AddInductive.consumeTypeAnnotations (.const ``Nat []))
      motiveFindZero
  have motiveFindIH : (natSuccIHContext root binderName binderInfo).lctx.find?
      (natMajorContext root).freshFVarId = some (.cdecl
        (natMajorContext root).lctx.decls.size
        (natMajorContext root).freshFVarId `motive
        (AddInductive.consumeTypeAnnotations (natMotiveType root))
        .default .default) := by
    simpa [natSuccIHContext] using nRun.push_findOld
      (binderName.appendAfter "_ih") .default
      (AddInductive.consumeTypeAnnotations
        (natSuccIHType root binderName binderInfo)) motiveFindN
  have motiveFind : (natSuccContext root binderName binderInfo).lctx.find?
      (natMajorContext root).freshFVarId = some (.cdecl
        (natMajorContext root).lctx.decls.size
        (natMajorContext root).freshFVarId `motive
        (AddInductive.consumeTypeAnnotations (natMotiveType root))
        .default .default) := by
    simpa [natSuccContext] using ihRun.push_findOld `succ .default
      (AddInductive.consumeTypeAnnotations
        (natSuccMinorType root binderName binderInfo)) motiveFindIH

  have zeroFind0 := motiveRun.push_findNew `zero .default
    (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
  have zeroFindZero : (natZeroContext root).lctx.find?
      (natMotiveContext root).freshFVarId = some (.cdecl
        (natMotiveContext root).lctx.decls.size
        (natMotiveContext root).freshFVarId `zero
        (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
        .default .default) := by
    simpa [natZeroContext] using zeroFind0
  have zeroFindN : (natSuccArgContext root binderName binderInfo).lctx.find?
      (natMotiveContext root).freshFVarId = some (.cdecl
        (natMotiveContext root).lctx.decls.size
        (natMotiveContext root).freshFVarId `zero
        (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
        .default .default) := by
    simpa [natSuccArgContext] using zeroRun.push_findOld binderName binderInfo
      (AddInductive.consumeTypeAnnotations (.const ``Nat [])) zeroFindZero
  have zeroFindIH : (natSuccIHContext root binderName binderInfo).lctx.find?
      (natMotiveContext root).freshFVarId = some (.cdecl
        (natMotiveContext root).lctx.decls.size
        (natMotiveContext root).freshFVarId `zero
        (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
        .default .default) := by
    simpa [natSuccIHContext] using nRun.push_findOld
      (binderName.appendAfter "_ih") .default
      (AddInductive.consumeTypeAnnotations
        (natSuccIHType root binderName binderInfo)) zeroFindN
  have zeroFind : (natSuccContext root binderName binderInfo).lctx.find?
      (natMotiveContext root).freshFVarId = some (.cdecl
        (natMotiveContext root).lctx.decls.size
        (natMotiveContext root).freshFVarId `zero
        (AddInductive.consumeTypeAnnotations (natZeroMinorType root))
        .default .default) := by
    simpa [natSuccContext] using ihRun.push_findOld `succ .default
      (AddInductive.consumeTypeAnnotations
        (natSuccMinorType root binderName binderInfo)) zeroFindIH
  have succFind0 := ihRun.push_findNew `succ .default
    (AddInductive.consumeTypeAnnotations
      (natSuccMinorType root binderName binderInfo))
  have succFind : (natSuccContext root binderName binderInfo).lctx.find?
      (natSuccIHContext root binderName binderInfo).freshFVarId = some
        (.cdecl (natSuccIHContext root binderName binderInfo).lctx.decls.size
          (natSuccIHContext root binderName binderInfo).freshFVarId `succ
          (AddInductive.consumeTypeAnnotations
            (natSuccMinorType root binderName binderInfo))
          .default .default) := by
    simpa [natSuccContext] using succFind0

  have zero_ne_succ : (natMotiveContext root).freshFVarId ≠
      (natSuccIHContext root binderName binderInfo).freshFVarId := by
    intro equal
    have fresh := ihRun.fresh
    rw [← equal, zeroFindIH] at fresh
    contradiction
  have t_ne_motive : root.freshFVarId ≠
      (natMajorContext root).freshFVarId := by
    intro equal
    have fresh := majorRun.fresh
    rw [← equal, tFindMajor] at fresh
    contradiction
  have motive_ne_zero : (natMajorContext root).freshFVarId ≠
      (natMotiveContext root).freshFVarId := by
    intro equal
    have fresh := motiveRun.fresh
    rw [← equal, motiveFindMotive] at fresh
    contradiction
  have motive_ne_succ : (natMajorContext root).freshFVarId ≠
      (natSuccIHContext root binderName binderInfo).freshFVarId := by
    intro equal
    have fresh := ihRun.fresh
    rw [← equal, motiveFindIH] at fresh
    contradiction
  have zero_bne_motive :
      ((natMotiveContext root).freshFVarId ==
        (natMajorContext root).freshFVarId) = false :=
    beq_eq_false_iff_ne.mpr motive_ne_zero.symm
  have succ_bne_motive :
      ((natSuccIHContext root binderName binderInfo).freshFVarId ==
        (natMajorContext root).freshFVarId) = false :=
    beq_eq_false_iff_ne.mpr motive_ne_succ.symm

  dsimp only
  rw [show natStats.params = #[] by rfl,
    show (natFinalRecInfos root binderName binderInfo).map (·.motive) =
      #[(natMajorContext root).freshExpr] by
        rw [natFinalRecInfos_eq]
        simp,
    show (natFinalRecInfos root binderName binderInfo).flatMap
        (·.minors) =
      #[(natMotiveContext root).freshExpr,
        (natSuccIHContext root binderName binderInfo).freshExpr] by
        rw [natFinalRecInfos_eq]
        simp,
    show (natFinalRecInfos root binderName binderInfo)[0]!.indices =
      #[] by
        rw [natFinalRecInfos_eq]
        rfl,
    show (natFinalRecInfos root binderName binderInfo)[0]!.major =
      root.freshExpr by
        rw [natFinalRecInfos_eq]
        rfl,
    show (natFinalRecInfos root binderName binderInfo)[0]!.motive =
      (natMajorContext root).freshExpr by
        rw [natFinalRecInfos_eq]
        rfl]
  simp only [AddInductive.Context.freshExpr]
  simp only [localContextMkForall_empty]
  rw [localContextMkForall_singleton tFind
      (by simp [natMajorType, natStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.abstract1,
        Expr.looseBVarRange'])
      (by simp [natMajorType, natStats, mkAppN,
        AddInductive.consumeTypeAnnotations, Expr.looseBVarRange']),
    localContextMkForall_pair zero_ne_succ zeroFind succFind
      (by simp [natMajorType, natStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.abstract1,
        t_ne_motive, zero_bne_motive, succ_bne_motive,
        zero_ne_succ,
        Expr.looseBVarRange'])
      (by simp [natZeroMinorType_eq root,
        natMajorType, natStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.abstract1,
        Expr.looseBVarRange'])
      (by simp [natSuccMinorType_eq root binderName binderInfo rootRun,
        natMajorType, natStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.abstract1,
        Expr.looseBVarRange']),
    localContextMkForall_singleton motiveFind
      (by simp [natZeroMinorType_eq root,
        natSuccMinorType_eq root binderName binderInfo rootRun,
        natMajorType, natStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.abstract1,
        t_ne_motive, zero_bne_motive, succ_bne_motive,
        zero_ne_succ,
        Expr.looseBVarRange'])
      (by simp [natMotiveType_eq root rootRun,
        natMajorType, natStats, mkAppN,
        AddInductive.consumeTypeAnnotations,
        AddInductive.Context.freshExpr, Expr.abstract1,
        Expr.looseBVarRange'])]
  rw [natMotiveType_eq root rootRun, natZeroMinorType_eq root,
    natSuccMinorType_eq root binderName binderInfo rootRun]
  simp [natRawExpectedRecursorType, natMajorType, natStats, mkAppN,
    AddInductive.consumeTypeAnnotations, AddInductive.Context.freshExpr,
    Expr.abstract1, Expr.abstract_eq, Name.replacePrefix, t_ne_motive,
    zero_bne_motive, succ_bne_motive, zero_ne_succ]

private theorem natGeneratedRecursorType_eqv
    (root : AddInductive.Context) (binderName : Name)
    (binderInfo : BinderInfo)
    (rootRun : TypeChecker.CandidateLocalContextRun root) :
    natGeneratedRecursorType root binderName binderInfo ==
      natExpectedRecursorType := by
  unfold natGeneratedRecursorType
  unfold AddInductive.declareRecursors.generatedRecursorType
  let raw : Expr :=
    let recInfos := natFinalRecInfos root binderName binderInfo
    (natSuccContext root binderName binderInfo).lctx.mkForall
        natStats.params <|
      (natSuccContext root binderName binderInfo).lctx.mkForall
          (recInfos.map (·.motive)) <|
        (natSuccContext root binderName binderInfo).lctx.mkForall
            (recInfos.flatMap (·.minors)) <|
          (natSuccContext root binderName binderInfo).lctx.mkForall
              recInfos[0]!.indices <|
            (natSuccContext root binderName binderInfo).lctx.mkForall
              #[recInfos[0]!.major]
              (.app (mkAppN recInfos[0]!.motive recInfos[0]!.indices)
                recInfos[0]!.major)
  change raw.inferImplicit 1000 false == natExpectedRecursorType
  have inferred : raw.inferImplicit 1000 false == raw :=
    inferImplicit_eqv raw 1000 false
  have raw_eq : raw = natRawExpectedRecursorType binderName binderInfo := by
    dsimp only [raw]
    exact natGeneratedRecursorRaw_eq root binderName binderInfo rootRun
  have assembled : raw ==
      natRawExpectedRecursorType binderName binderInfo := by
    rw [raw_eq]
    exact Expr.eqv_refl _
  have expected : natRawExpectedRecursorType binderName binderInfo ==
      natExpectedRecursorType := by
    unfold natRawExpectedRecursorType natExpectedRecursorType
    apply forallE_eqv
    · apply forallE_eqv <;> exact Expr.eqv_refl _
    · apply forallE_eqv
      · exact Expr.eqv_refl _
      · apply forallE_eqv
        · apply forallE_eqv
          · exact Expr.eqv_refl _
          · apply forallE_eqv <;> exact Expr.eqv_refl _
        · apply forallE_eqv <;> exact Expr.eqv_refl _
  exact BEq.trans inferred (BEq.trans assembled expected)

/-- Translation-facing canonical header of the generated `Nat.rec`. -/
def natExpectedRecursorVal : RecursorVal where
  name := ``Nat.rec
  levelParams := [`u]
  type := natExpectedRecursorType
  all := [``Nat]
  numParams := 0
  numIndices := 0
  numMotives := 1
  numMinors := 2
  rules := []
  k := false
  isUnsafe := false

/-- A successful canonical Nat recursor phase contains exactly the record
assembled by the producer; its recursive rule payload remains producer-owned. -/
theorem declareRecursors_nat_infos (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo)
    (rootRun : TypeChecker.CandidateLocalContextRun root)
    (familyInfo : InductiveVal)
    (hfind : root.env.find? ``Nat = some (.inductInfo familyInfo))
    (hwhnf : TypeChecker.M.run root.env root.safety root.lctx root.lparams
      root.fuel (TypeChecker.whnf (natSource binderName binderInfo).type) =
        .ok (.sort (.succ .zero)))
    (hdepth : root.fuel.recDepth = recursionFuel + 1)
    (hwhnfFuel : root.fuel.whnf = whnfFuel + 1)
    (hinductive : root.fuel.inductiveFuel = inductiveFuel + 2)
    {result : AddInductive.RecursorDeclarationResult}
    (run : AddInductive.declareRecursors natStats
      #[natSource binderName binderInfo] (.param `u) false root = .ok result) :
    ∃ rules, result.infos =
      [AddInductive.declareRecursors.generatedRecursorVal natStats
        #[natSource binderName binderInfo] (.param `u) false
        ((natFinalRecInfos root binderName binderInfo).map (·.motive))
        ((natFinalRecInfos root binderName binderInfo).flatMap (·.minors))
        (natSuccContext root binderName binderInfo).lctx root.lparams
        (root.safety != .safe) 0 (natSource binderName binderInfo)
        (natFinalRecInfos root binderName binderInfo)[0]! rules] := by
  unfold AddInductive.declareRecursors at run
  unfold AddInductive.declareRecursorsAt at run
  rw [mkRecInfos_nat root binderName binderInfo rootRun familyInfo hfind
    hwhnf hdepth hwhnfFuel hinductive] at run
  simp only [AddInductive.getLCtx_apply, ReaderT.bind, Bind.bind,
    Except.bind] at run
  cases hloop : StateT.run'
      (AddInductive.declareRecursors.loop natStats
        #[natSource binderName binderInfo] (.param `u) false
        (natFinalRecInfos root binderName binderInfo)
        ((natFinalRecInfos root binderName binderInfo).map (·.motive))
        ((natFinalRecInfos root binderName binderInfo).flatMap (·.minors))
        (natSuccContext root binderName binderInfo).lctx root.lparams
        (root.safety != .safe) root.allowPrimitive 0 root.env)
      0 (natSuccContext root binderName binderInfo) with
  | error error =>
      rw [hloop] at run
      contradiction
  | ok tail =>
      rw [hloop] at run
      simp only [Pure.pure, Except.pure] at run
      have result_eq := Except.ok.inj run
      subst result
      exact AddInductive.declareRecursors.loop_singleton_infos_eq
        (by simp) (by simp) hloop

@[simp] private theorem pushLocalDecl_fuel
    (context : AddInductive.Context) (name : Name)
    (binderInfo : BinderInfo) (type : Expr) :
    (context.pushLocalDecl name binderInfo type).fuel = context.fuel := rfl

/-- The recursive `Nat.succ` field makes a successful canonical recursor run
an operational certificate that the WHNF counter is positive and that the
inductive structural counter has at least two steps. -/
theorem declareRecursors_nat_fuel
    (root : AddInductive.Context) (binderName : Name)
    (binderInfo : BinderInfo)
    (recursionFuel : Nat)
    (hdepth : root.fuel.recDepth = recursionFuel + 1)
    (initialInductiveFuel : Nat)
    (hpositive : root.fuel.inductiveFuel = initialInductiveFuel + 1)
    (hwhnf : TypeChecker.M.run root.env root.safety root.lctx root.lparams
      root.fuel (TypeChecker.whnf (natSource binderName binderInfo).type) =
        .ok (.sort (.succ .zero)))
    {result : AddInductive.RecursorDeclarationResult}
    (run : AddInductive.declareRecursors natStats
      #[natSource binderName binderInfo] (.param `u) false root = .ok result) :
    (∃ whnfFuel, root.fuel.whnf = whnfFuel + 1) ∧
      ∃ inductiveFuel, root.fuel.inductiveFuel = inductiveFuel + 2 := by
  constructor
  · cases hw : root.fuel.whnf with
    | zero =>
      unfold AddInductive.declareRecursors at run
      unfold AddInductive.declareRecursorsAt at run
      unfold AddInductive.mkRecInfos at run
      rw [AddInductive.mkRecInfos.loopInd1.eq_1] at run
      rw [dif_pos (show 0 < #[natSource binderName binderInfo].size by simp)] at run
      simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind] at run
      rw [show #[natSource binderName binderInfo][0].type =
        (natSource binderName binderInfo).type by rfl] at run
      simp only [AddInductive.liftTypeChecker_apply] at run
      rw [hwhnf] at run
      simp only [Except.bind, AddInductive.mkRecInfos.loopArgs1,
        AddInductive.withLocalDecl_apply, AddInductive.getLCtx_apply,
        ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure] at run
      cases hi : root.fuel.inductiveFuel with
      | zero =>
          rw [hi] at run
          unfold AddInductive.mkRecInfos.loopArgs1 at run
          simp [throw, throwThe, MonadExceptOf.throw] at run
      | succ inductiveFuel =>
          rw [hi] at run
          unfold AddInductive.mkRecInfos.loopArgs1 at run
          simp only [AddInductive.withLocalDecl_apply,
            AddInductive.getLCtx_apply, ReaderT.bind, Bind.bind,
            Except.bind, Pure.pure, ReaderT.pure, Except.pure] at run
          rw [AddInductive.mkRecInfos.loopInd1.eq_1] at run
          rw [dif_neg (show ¬1 < #[natSource binderName binderInfo].size by simp)] at run
          rw [AddInductive.mkRecInfos.loopInd2.eq_1] at run
          rw [dif_pos (show 0 < #[natSource binderName binderInfo].size by simp)] at run
          rw [show #[natSource binderName binderInfo][0] =
            natSource binderName binderInfo by rfl] at run
          rw [show (natSource binderName binderInfo).name = ``Nat by rfl] at run
          rw [show (natSource binderName binderInfo).ctors = [
            ⟨``Nat.zero, .const ``Nat []⟩,
            ⟨``Nat.succ, .forallE binderName (.const ``Nat [])
              (.const ``Nat []) binderInfo⟩] by rfl] at run
          simp only [AddInductive.mkRecInfos.loopCtors,
            AddInductive.mkRecInfos.loopCtorArgs,
            readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
            ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
            Except.bind, pushLocalDecl_fuel, hi,
            AddInductive.mkRecInfos.loopCtorArgs.loop] at run
          rw [AddInductive.mkRecInfos.loopU.eq_1] at run
          rw [dif_neg (show ¬0 < (#[] : Array Expr).size by decide)] at run
          simp only [AddInductive.getLCtx_apply,
            AddInductive.withLocalDecl_apply, ReaderT.bind, Bind.bind,
            Except.bind, Pure.pure, ReaderT.pure, Except.pure] at run
          simp only [pushLocalDecl_fuel, hi,
            AddInductive.mkRecInfos.loopCtorArgs.loop] at run
          rw [show natStats.params[0]? = none by rfl] at run
          simp only [AddInductive.withLocalDecl_apply, ReaderT.bind,
            Bind.bind, Except.bind] at run
          unfold AddInductive.isRecArg at run
          simp only [readThe, MonadReader.read, MonadReaderOf.read,
            ReaderT.read, ReaderT.bind, Bind.bind, Pure.pure,
            ReaderT.pure, Except.pure, Except.bind] at run
          simp only [pushLocalDecl_fuel] at run
          rw [hi] at run
          unfold AddInductive.isRecArg.loop at run
          simp [AddInductive.liftTypeChecker_apply,
            ReaderT.bind, Bind.bind] at run
          rw [whnfConst_zero ``Nat recursionFuel hdepth hw] at run
          simp only [Except.bind] at run
          exfalso
          contradiction
    | succ whnfFuel => exact ⟨whnfFuel, rfl⟩
  · cases initialInductiveFuel with
    | zero =>
      have hone : root.fuel.inductiveFuel = 1 := by simpa using hpositive
      unfold AddInductive.declareRecursors at run
      unfold AddInductive.declareRecursorsAt at run
      unfold AddInductive.mkRecInfos at run
      rw [AddInductive.mkRecInfos.loopInd1.eq_1] at run
      rw [dif_pos (show 0 < #[natSource binderName binderInfo].size by simp)] at run
      simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind] at run
      rw [show #[natSource binderName binderInfo][0].type =
        (natSource binderName binderInfo).type by rfl] at run
      simp only [AddInductive.liftTypeChecker_apply] at run
      rw [hwhnf] at run
      simp only [Except.bind, AddInductive.mkRecInfos.loopArgs1,
        AddInductive.withLocalDecl_apply, AddInductive.getLCtx_apply,
        ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure] at run
      rw [hone] at run
      unfold AddInductive.mkRecInfos.loopArgs1 at run
      simp only [AddInductive.withLocalDecl_apply,
        AddInductive.getLCtx_apply, ReaderT.bind, Bind.bind,
        Except.bind, Pure.pure, ReaderT.pure, Except.pure] at run
      rw [AddInductive.mkRecInfos.loopInd1.eq_1] at run
      rw [dif_neg (show ¬1 < #[natSource binderName binderInfo].size by simp)] at run
      rw [AddInductive.mkRecInfos.loopInd2.eq_1] at run
      rw [dif_pos (show 0 < #[natSource binderName binderInfo].size by simp)] at run
      rw [show #[natSource binderName binderInfo][0] =
        natSource binderName binderInfo by rfl] at run
      rw [show (natSource binderName binderInfo).name = ``Nat by rfl] at run
      rw [show (natSource binderName binderInfo).ctors = [
        ⟨``Nat.zero, .const ``Nat []⟩,
        ⟨``Nat.succ, .forallE binderName (.const ``Nat [])
          (.const ``Nat []) binderInfo⟩] by rfl] at run
      simp only [AddInductive.mkRecInfos.loopCtors,
        AddInductive.mkRecInfos.loopCtorArgs,
        readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
        Except.bind, pushLocalDecl_fuel, hone,
        AddInductive.mkRecInfos.loopCtorArgs.loop] at run
      rw [AddInductive.mkRecInfos.loopU.eq_1] at run
      rw [dif_neg (show ¬0 < (#[] : Array Expr).size by decide)] at run
      simp only [AddInductive.getLCtx_apply,
        AddInductive.withLocalDecl_apply, ReaderT.bind, Bind.bind,
        Except.bind, Pure.pure, ReaderT.pure, Except.pure] at run
      simp only [pushLocalDecl_fuel, hone,
        AddInductive.mkRecInfos.loopCtorArgs.loop] at run
      rw [show natStats.params[0]? = none by rfl] at run
      simp only [AddInductive.withLocalDecl_apply, ReaderT.bind,
        Bind.bind, Except.bind] at run
      split at run <;>
        simp_all [AddInductive.mkRecInfos.loopCtorArgs.loop,
          throw, throwThe, MonadExceptOf.throw]
      all_goals
        split at * <;> simp_all
    | succ inductiveFuel =>
      exact ⟨inductiveFuel, by omega⟩

/-- Transport the canonical Nat recursor translation to the exact record
retained by a successful producer execution. -/
theorem declareRecursors_nat_evidence (root : AddInductive.Context)
    (binderName : Name) (binderInfo : BinderInfo)
    (rootRun : TypeChecker.CandidateLocalContextRun root)
    (lparams_eq : root.lparams = [])
    (safety_eq : root.safety = .safe)
    (familyInfo : InductiveVal)
    (hfind : root.env.find? ``Nat = some (.inductInfo familyInfo))
    (hwhnf : TypeChecker.M.run root.env root.safety root.lctx root.lparams
      root.fuel (TypeChecker.whnf (natSource binderName binderInfo).type) =
        .ok (.sort (.succ .zero)))
    (hdepth : root.fuel.recDepth = recursionFuel + 1)
    (hwhnfFuel : root.fuel.whnf = whnfFuel + 1)
    (hinductive : root.fuel.inductiveFuel = inductiveFuel + 2)
    {result : AddInductive.RecursorDeclarationResult}
    (run : AddInductive.declareRecursors natStats
      #[natSource binderName binderInfo] (.param `u) false root = .ok result)
    {ctorEnv : VEnv} {raw : VConstVal}
    (tr : TrConstVal .safe ctorEnv (.recInfo natExpectedRecursorVal) raw) :
    List.Forall₂
      (fun info raw => TrConstVal .safe ctorEnv (.recInfo info) raw)
      result.infos [raw] := by
  obtain ⟨rules, infos_eq⟩ := declareRecursors_nat_infos root binderName
    binderInfo rootRun familyInfo hfind hwhnf hdepth hwhnfFuel hinductive run
  rw [infos_eq]
  apply List.Forall₂.cons
  · apply VInductDecl.trConstVal_of_translation_header (tr := tr)
    · simp [AddInductive.declareRecursors.generatedRecursorVal,
        natExpectedRecursorVal, safety_eq, ConstantInfo.safety,
        ConstantInfo.isUnsafe, ConstantInfo.isPartial]
    · simp [AddInductive.declareRecursors.generatedRecursorVal,
        natExpectedRecursorVal, lparams_eq, AddInductive.getRecLevelParams,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal]
    · simpa [AddInductive.declareRecursors.generatedRecursorVal,
        natExpectedRecursorVal, natGeneratedRecursorType,
        ConstantInfo.type, ConstantInfo.toConstantVal, (· == ·)] using
        natGeneratedRecursorType_eqv root binderName binderInfo rootRun
    · rfl
  · exact .nil

/-- The translation-facing Nat header denotes the canonical Theory recursor
in every semantically reconstructed post-constructor environment. -/
theorem natExpectedRecursorTranslation {ctorEnv : VEnv}
    (generationEnv : VInductDecl.BlockGenerationEnv
      VPrimitiveInductive.natGeneration ctorEnv) :
    TrConstVal .safe ctorEnv (.recInfo natExpectedRecursorVal)
      VPrimitiveInductive.natGeneration.recursors[0] := by
  have familyLookup := generationEnv.familyConst
    VPrimitiveInductive.natGeneration.families[0]
    (List.getElem_mem (l := VPrimitiveInductive.natGeneration.families)
      (n := 0) (by decide))
  have zeroLookup := generationEnv.ctorConst
    VPrimitiveInductive.natGeneration.flatCtors[0]
    (List.getElem_mem (l := VPrimitiveInductive.natGeneration.flatCtors)
      (n := 0) (by decide))
  have succLookup := generationEnv.ctorConst
    VPrimitiveInductive.natGeneration.flatCtors[1]
    (List.getElem_mem (l := VPrimitiveInductive.natGeneration.flatCtors)
      (n := 1) (by decide))
  change ctorEnv.constants ``Nat =
    some VPrimitiveInductive.natType.toVConstant at familyLookup
  change ctorEnv.constants ``Nat.zero = some
    VPrimitiveInductive.natConstructors[0].toVConstant at zeroLookup
  change ctorEnv.constants ``Nat.succ = some
    VPrimitiveInductive.natConstructors[1].toVConstant at succLookup
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr ctorEnv [`u] [] natExpectedRecursorType
      VPrimitiveInductive.natGeneration.recursors[0].type := by
    apply TrTypeExpr.forallE
    · apply TrTypeExpr.forallE
      · exact .const familyLookup rfl rfl
      · apply TrTypeExpr.sort
        rfl
    · apply TrTypeExpr.forallE
      · apply TrTypeExpr.app
        · apply TrTypeExpr.bvar
          rfl
        · exact .const zeroLookup rfl rfl
      · apply TrTypeExpr.forallE
        · apply TrTypeExpr.forallE
          · exact .const familyLookup rfl rfl
          · apply TrTypeExpr.forallE
            · apply TrTypeExpr.app
              · apply TrTypeExpr.bvar
                rfl
              · apply TrTypeExpr.bvar
                rfl
            · apply TrTypeExpr.app
              · apply TrTypeExpr.bvar
                rfl
              · apply TrTypeExpr.app
                · exact .const succLookup rfl rfl
                · apply TrTypeExpr.bvar
                  rfl
        · apply TrTypeExpr.forallE
          · exact .const familyLookup rfl rfl
          · apply TrTypeExpr.app
            · apply TrTypeExpr.bvar
              rfl
            · apply TrTypeExpr.bvar
              rfl
  obtain ⟨sort, recursorType⟩ := generationEnv.recursor_wf
    (List.getElem_mem (l := VPrimitiveInductive.natGeneration.families)
      (n := 0) (by decide))
  rw [show (VPrimitiveInductive.natGeneration.recursor
      VPrimitiveInductive.natGeneration.families[0]).uvars = 1 by rfl]
    at recursorType
  have rawWF : VPrimitiveInductive.natGeneration.recursors[0].type.WF
      ctorEnv 1 [] := by
    refine ⟨.sort sort, ?_⟩
    change ctorEnv.HasType 1 []
      VPrimitiveInductive.natGeneration.recursors[0].type (.sort sort)
    simpa [VInductDecl.BlockGenerationChecked.recursors] using recursorType
  exact shape.to_trExprS generationEnv.ord trivial rawWF


end AddInductive.PrimitiveRecursorReplay
end Lean4Lean
