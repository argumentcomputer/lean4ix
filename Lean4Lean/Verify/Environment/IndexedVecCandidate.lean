import Lean4Lean.Verify.Environment.InductiveFixtures

namespace Lean4Lean.InductiveReplayFixtures
open Lean Meta
open Lean4Lean.InductiveFixtures

def indexedVecKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_indexedVecCandidate natMap

def indexedVecFamilyCandidateContext :
    Lean4Lean.AddInductive.Context where
  env := indexedVecKernelEnv
  lparams := indexedVecInfo.levelParams
  safety := .safe
  allowPrimitive := false

private theorem indexedVecKernel_lookup_nat :
    indexedVecKernelEnv.find? ``Nat = some natInfo := by
  change natMap.find?' ``Nat = some natInfo
  rw [natMap_wf.find?'_eq_find?, nat_type_map_lookup]

@[simp] private theorem indexedVecKernel_get_nat :
    indexedVecKernelEnv.get ``Nat = .ok natInfo := by
  simp only [Kernel.Environment.get, indexedVecKernel_lookup_nat,
    Pure.pure, Except.pure]

private def indexedVecParamName : Name :=
  indexedVecInfo.type.bindingName!

private def indexedVecIndexName : Name :=
  indexedVecInfo.type.bindingBody!.bindingName!

private def indexedVecParamCandidateContext :
    Lean4Lean.AddInductive.Context :=
  indexedVecFamilyCandidateContext.pushLocalDecl
    indexedVecParamName .default (.sort (.succ (.param `u)))

private def indexedVecIndexCandidateContext :
    Lean4Lean.AddInductive.Context :=
  indexedVecParamCandidateContext.pushLocalDecl
    indexedVecIndexName .default (.const ``Nat [])

private def indexedVecInnerKernel : Expr :=
  .forallE indexedVecIndexName (.const ``Nat [])
    (.sort (.succ (.param `u))) .default

private def indexedVecTerminalKernel : Expr :=
  .sort (.succ (.param `u))

@[simp] private theorem indexedVecInnerKernel_instantiate1 (arg : Expr) :
    indexedVecInnerKernel.instantiate1 arg = indexedVecInnerKernel := by
  simp [indexedVecInnerKernel, Expr.instantiate1_eq, Expr.instantiate1']

@[simp] private theorem indexedVecTerminalKernel_instantiate1 (arg : Expr) :
    indexedVecTerminalKernel.instantiate1 arg =
      indexedVecTerminalKernel := by
  simp [indexedVecTerminalKernel, Expr.instantiate1_eq,
    Expr.instantiate1']

@[simp] private theorem indexedVecInfo_levelParams :
    indexedVecInfo.levelParams = [`u] := rfl

/-- Reflexive binder-domain equality is an exact successful ordinary-checker
run in any candidate context with positive recursive fuel. -/
theorem candidateIsDefEqSelfValid
    (context : Lean4Lean.AddInductive.Context) (e : Expr)
    (fuel : Nat) (hfuel : context.fuel.recDepth = fuel + 1) :
    Lean4Lean.AddInductive.CandidateIsDefEqStep.Valid ⟨context, e, e⟩ := by
  unfold Lean4Lean.AddInductive.CandidateIsDefEqStep.Valid
  unfold Lean4Lean.TypeChecker.M.run Lean4Lean.TypeChecker.isDefEq
    Lean4Lean.TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hfuel]
  change Except.map (fun x : Bool × Lean4Lean.TypeChecker.State => x.1)
      (Lean4Lean.TypeChecker.Inner.isDefEq e e
        (Lean4Lean.TypeChecker.Methods.withFuel (fuel + 1))
        context.toTypeChecker ({} : Lean4Lean.TypeChecker.State)) = .ok true
  unfold Lean4Lean.TypeChecker.Inner.isDefEq
  rw [if_pos (Expr.eqv_refl e)]
  rfl

private def indexedVecTypeCheckerContext
    (lctx : LocalContext) : Lean4Lean.TypeChecker.Context where
  env := indexedVecKernelEnv
  lctx := lctx
  lparams := [`u]

@[simp] private theorem indexedVecFamily_checkLevel :
    Lean4Lean.TypeChecker.Inner.checkLevel
      indexedVecFamilyCandidateContext.toTypeChecker
        (.succ (.param `u)) = .ok () := by
  simp [Lean4Lean.TypeChecker.Inner.checkLevel,
    indexedVecFamilyCandidateContext, indexedVecInfo,
    Lean4Lean.AddInductive.Context.toTypeChecker,
    Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] private theorem indexedVec_checkLevel
    (lctx : LocalContext) :
    Lean4Lean.TypeChecker.Inner.checkLevel
      (indexedVecTypeCheckerContext lctx)
      (.succ (.param `u)) = .ok () := by
  simp [Lean4Lean.TypeChecker.Inner.checkLevel,
    indexedVecTypeCheckerContext,
    Level.getUndefParam, Level.forEach,
    Level.hasParam_eq, Level.hasParam']
  rfl

@[simp] private theorem indexedVecRecMGet (methods context state) :
    (get : Lean4Lean.TypeChecker.RecM Lean4Lean.TypeChecker.State)
        methods context state = .ok (state, state) := rfl

@[simp] private theorem indexedVecRecMReadContext
    (methods context state) :
    (readThe Lean4Lean.TypeChecker.Context :
        Lean4Lean.TypeChecker.RecM Lean4Lean.TypeChecker.Context)
      methods context state = .ok (context, state) := rfl

@[simp] private theorem indexedVecRecMModify
    (f : Lean4Lean.TypeChecker.State → Lean4Lean.TypeChecker.State)
    (methods context state) :
    (modify f : Lean4Lean.TypeChecker.RecM PUnit)
      methods context state = .ok (.unit, f state) := rfl

@[simp] private theorem indexedVecRecMPure
    {α} (a : α) (methods context state) :
    (pure a : Lean4Lean.TypeChecker.RecM α)
      methods context state = .ok (a, state) := rfl

@[simp] private theorem indexedVecRecMBind
    {α β} (x : Lean4Lean.TypeChecker.RecM α)
    (f : α → Lean4Lean.TypeChecker.RecM β)
    (methods context state) :
    (x >>= f) methods context state =
      match x methods context state with
      | .error e => .error e
      | .ok (a, state') => f a methods context state' := by
  simp [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  cases h : x methods context state with
  | error => rfl
  | ok value => cases value; rfl

@[simp] private theorem indexedVecRecMLiftExceptOk
    {α} (a : α) (methods context state) :
    (liftM (.ok a : Except Kernel.Exception α) :
      Lean4Lean.TypeChecker.RecM α) methods context state =
        .ok (a, state) := rfl

@[simp] private theorem indexedVecGetNGen
    (context : Lean4Lean.TypeChecker.Context)
    (state : Lean4Lean.TypeChecker.State) :
    (getNGen : Lean4Lean.TypeChecker.M NameGenerator) context state =
      .ok (state.ngen, state) := rfl

@[simp] private theorem indexedVecSetNGen
    (ngen : NameGenerator) (context : Lean4Lean.TypeChecker.Context)
    (state : Lean4Lean.TypeChecker.State) :
    (setNGen ngen : Lean4Lean.TypeChecker.M PUnit) context state =
      .ok (.unit, { state with ngen }) := rfl

@[simp] private theorem indexedVecMPure
    {α} (a : α) (context : Lean4Lean.TypeChecker.Context)
    (state : Lean4Lean.TypeChecker.State) :
    (pure a : Lean4Lean.TypeChecker.M α) context state =
      .ok (a, state) := rfl

@[simp] private theorem indexedVecRecMWithReader
    {α} (f : LocalContext → LocalContext)
    (x : Lean4Lean.TypeChecker.RecM α)
    (methods : Lean4Lean.TypeChecker.Methods)
    (context : Lean4Lean.TypeChecker.Context)
    (state : Lean4Lean.TypeChecker.State) :
    (MonadWithReaderOf.withReader (m := Lean4Lean.TypeChecker.RecM) f x)
      methods context state =
        x methods { context with lctx := f context.lctx } state := rfl

private theorem indexedVecWithLocalDecl
    {α} (name : Name) (bi : BinderInfo) (ty : Expr)
    (k : Expr → Lean4Lean.TypeChecker.RecM α)
    (methods : Lean4Lean.TypeChecker.Methods)
    (context : Lean4Lean.TypeChecker.Context)
    (state : Lean4Lean.TypeChecker.State) :
    (withLocalDecl (m := Lean4Lean.TypeChecker.RecM) name bi ty k)
      methods context state =
        k (.fvar ⟨state.ngen.curr⟩) methods
          { context with lctx :=
              (context.lctx.mkLocalDecl ⟨state.ngen.curr⟩ name ty bi) }
          { state with ngen := state.ngen.next } := rfl

@[simp] private theorem indexedVecEnsureSort
    (u : Level) (source : Expr)
    (methods : Lean4Lean.TypeChecker.Methods)
    (context : Lean4Lean.TypeChecker.Context)
    (state : Lean4Lean.TypeChecker.State) :
    Lean4Lean.TypeChecker.Inner.ensureSortCore (.sort u) source
      methods context state = .ok (.sort u, state) := by
  rfl

private theorem indexedVecInferTypeFuel
    (n e inferOnly context state) :
    Lean4Lean.TypeChecker.Inner.inferType e inferOnly
      (Lean4Lean.TypeChecker.Methods.withFuel (n + 1)) context state =
        Lean4Lean.TypeChecker.Inner.inferType' e inferOnly
          (Lean4Lean.TypeChecker.Methods.withFuel n) context state := rfl

@[simp] private theorem indexedVecInferTypeSortCore
    (n : Nat) (lctx : LocalContext)
    (state : Lean4Lean.TypeChecker.State)
    (hcache : state.inferTypeC[(.sort (.succ (.param `u)) : Expr)]? = none) :
    Lean4Lean.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Lean4Lean.TypeChecker.Methods.withFuel n)
      (indexedVecTypeCheckerContext lctx)
      state =
        .ok (.sort (.succ (.succ (.param `u))),
          { state with inferTypeC :=
              (state.inferTypeC.insert (.sort (.succ (.param `u)))
                (.sort (.succ (.succ (.param `u))))) }) := by
  unfold Lean4Lean.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

@[simp] private theorem indexedVecInferTypeSortCachedCore
    (n : Nat) (lctx : LocalContext)
    (state : Lean4Lean.TypeChecker.State)
    (hcache : state.inferTypeC[(.sort (.succ (.param `u)) : Expr)]? =
      some (.sort (.succ (.succ (.param `u))))) :
    Lean4Lean.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Lean4Lean.TypeChecker.Methods.withFuel n)
      (indexedVecTypeCheckerContext lctx)
      state = .ok (.sort (.succ (.succ (.param `u))), state) := by
  unfold Lean4Lean.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache]

@[simp] private theorem indexedVecInferConstantNat
    (lctx : LocalContext) :
    Lean4Lean.TypeChecker.Inner.inferConstant
      (indexedVecTypeCheckerContext lctx) ``Nat [] false =
        .ok (.sort (.succ .zero)) := by
  unfold Lean4Lean.TypeChecker.Inner.inferConstant
  simp [indexedVecTypeCheckerContext, indexedVecKernel_get_nat,
    natInfo, ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParams, ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams', Bind.bind, Except.bind,
    Pure.pure, Except.pure]

@[simp] private theorem indexedVecInferTypeNatCore
    (n : Nat) (lctx : LocalContext)
    (state : Lean4Lean.TypeChecker.State)
    (hcache : state.inferTypeC[(.const ``Nat [] : Expr)]? = none) :
    Lean4Lean.TypeChecker.Inner.inferType' (.const ``Nat []) false
      (Lean4Lean.TypeChecker.Methods.withFuel n)
      (indexedVecTypeCheckerContext lctx)
      state =
        .ok (.sort (.succ .zero),
          { state with inferTypeC :=
              (state.inferTypeC.insert (.const ``Nat [])
                (.sort (.succ .zero))) }) := by
  unfold Lean4Lean.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange', hcache,
    indexedVecInferConstantNat,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private def indexedVecRootSortState : Lean4Lean.TypeChecker.State :=
  { ({} : Lean4Lean.TypeChecker.State) with inferTypeC :=
      (({} : Lean4Lean.TypeChecker.State).inferTypeC.insert
        (.sort (.succ (.param `u)))
        (.sort (.succ (.succ (.param `u))))) }

@[simp] private theorem indexedVecRootSortCore :
    Lean4Lean.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Lean4Lean.TypeChecker.Methods.withFuel 9998)
      indexedVecFamilyCandidateContext.toTypeChecker
      ({} : Lean4Lean.TypeChecker.State) =
        .ok (.sort (.succ (.succ (.param `u))),
          indexedVecRootSortState) := by
  simpa [indexedVecFamilyCandidateContext,
    Lean4Lean.AddInductive.Context.toTypeChecker,
    indexedVecInfo, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal, indexedVecTypeCheckerContext,
    indexedVecRootSortState] using
      (indexedVecInferTypeSortCore 9998 ({} : LocalContext)
        ({} : Lean4Lean.TypeChecker.State) Std.HashMap.getElem?_empty)

private def indexedVecParamLctx : LocalContext :=
  ({} : LocalContext).mkLocalDecl
    ⟨indexedVecRootSortState.ngen.curr⟩ indexedVecParamName
    (.sort (.succ (.param `u))) .default

private def indexedVecAfterParamState : Lean4Lean.TypeChecker.State :=
  { indexedVecRootSortState with
    ngen := indexedVecRootSortState.ngen.next }

private def indexedVecNatState : Lean4Lean.TypeChecker.State :=
  { indexedVecAfterParamState with
    inferTypeC := indexedVecAfterParamState.inferTypeC.insert
      (.const ``Nat []) (.sort (.succ .zero)) }

private def indexedVecIndexLctx : LocalContext :=
  indexedVecParamLctx.mkLocalDecl
    ⟨indexedVecNatState.ngen.curr⟩ indexedVecIndexName
    (.const ``Nat []) .default

private def indexedVecAfterIndexState : Lean4Lean.TypeChecker.State :=
  { indexedVecNatState with ngen := indexedVecNatState.ngen.next }

private theorem indexedVecOuterWithLocalDecl
    {α} (k : Expr → Lean4Lean.TypeChecker.RecM α)
    (methods : Lean4Lean.TypeChecker.Methods) :
    (withLocalDecl (m := Lean4Lean.TypeChecker.RecM)
      indexedVecParamName .default (.sort (.succ (.param `u))) k)
        methods indexedVecFamilyCandidateContext.toTypeChecker
          indexedVecRootSortState =
      k (.fvar ⟨indexedVecRootSortState.ngen.curr⟩) methods
        { indexedVecFamilyCandidateContext.toTypeChecker with
          lctx := indexedVecParamLctx }
        indexedVecAfterParamState := by
  simpa [indexedVecParamLctx, indexedVecAfterParamState] using
    (indexedVecWithLocalDecl indexedVecParamName .default
      (.sort (.succ (.param `u))) k methods
      indexedVecFamilyCandidateContext.toTypeChecker indexedVecRootSortState)

private theorem indexedVecInnerWithLocalDecl
    {α} (k : Expr → Lean4Lean.TypeChecker.RecM α)
    (methods : Lean4Lean.TypeChecker.Methods) :
    (withLocalDecl (m := Lean4Lean.TypeChecker.RecM)
      indexedVecIndexName .default (.const ``Nat []) k)
        methods
          { indexedVecFamilyCandidateContext.toTypeChecker with
            lctx := indexedVecParamLctx }
          indexedVecNatState =
      k (.fvar ⟨indexedVecNatState.ngen.curr⟩) methods
        { indexedVecFamilyCandidateContext.toTypeChecker with
          lctx := indexedVecIndexLctx }
        indexedVecAfterIndexState := by
  simpa [indexedVecIndexLctx, indexedVecAfterIndexState] using
    (indexedVecWithLocalDecl indexedVecIndexName .default
      (.const ``Nat []) k methods
      { indexedVecFamilyCandidateContext.toTypeChecker with
        lctx := indexedVecParamLctx }
      indexedVecNatState)

@[simp] private theorem indexedVecNat_beq_sort :
    ((.const ``Nat [] : Expr) == .sort (.succ (.param `u))) = false := by
  change Expr.eqv (.const ``Nat []) (.sort (.succ (.param `u))) = false
  rw [Expr.eqv_eq]
  rfl

@[simp] private theorem indexedVecAfterIndexState_sort_cache :
    indexedVecAfterIndexState.inferTypeC[
      (.sort (.succ (.param `u)) : Expr)]? =
        some (.sort (.succ (.succ (.param `u)))) := by
  change
    (((({} : Lean4Lean.InferCache).insert
      (.sort (.succ (.param `u)))
      (.sort (.succ (.succ (.param `u))))).insert
      (.const ``Nat []) (.sort (.succ .zero)))[
        (.sort (.succ (.param `u)) : Expr)]?) = _
  rw [Std.HashMap.getElem?_insert, indexedVecNat_beq_sort]
  exact Std.HashMap.getElem?_insert_self

@[simp] private theorem indexedVecParamNatCore :
    Lean4Lean.TypeChecker.Inner.inferType' (.const ``Nat []) false
      (Lean4Lean.TypeChecker.Methods.withFuel 9998)
      { indexedVecFamilyCandidateContext.toTypeChecker with
        lctx := indexedVecParamLctx }
      indexedVecAfterParamState =
        .ok (.sort (.succ .zero), indexedVecNatState) := by
  simpa [indexedVecFamilyCandidateContext,
    Lean4Lean.AddInductive.Context.toTypeChecker,
    indexedVecInfo, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal, indexedVecTypeCheckerContext,
    indexedVecAfterParamState, indexedVecRootSortState,
    indexedVecNatState] using
      (indexedVecInferTypeNatCore 9998 indexedVecParamLctx
        indexedVecAfterParamState (by
          simp [indexedVecAfterParamState, indexedVecRootSortState]))

@[simp] private theorem indexedVecTerminalSortCore :
    Lean4Lean.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Lean4Lean.TypeChecker.Methods.withFuel 9998)
      { indexedVecFamilyCandidateContext.toTypeChecker with
        lctx := indexedVecIndexLctx }
      indexedVecAfterIndexState =
        .ok (.sort (.succ (.succ (.param `u))),
          indexedVecAfterIndexState) := by
  simpa [indexedVecFamilyCandidateContext,
    Lean4Lean.AddInductive.Context.toTypeChecker,
    indexedVecInfo, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal, indexedVecTypeCheckerContext,
    indexedVecAfterIndexState, indexedVecNatState,
    indexedVecAfterParamState, indexedVecRootSortState] using
      (indexedVecInferTypeSortCachedCore 9998 indexedVecIndexLctx
        indexedVecAfterIndexState indexedVecAfterIndexState_sort_cache)

private def indexedVecFamilyInferredLevel : Level :=
  mkLevelIMax' (.succ (.succ (.param `u)))
    (mkLevelIMax' (.succ .zero) (.succ (.succ (.param `u))))

private theorem indexedVecFamilyInferForall :
    Lean4Lean.TypeChecker.Inner.inferForall
      (.forallE indexedVecParamName (.sort (.succ (.param `u)))
        (.forallE indexedVecIndexName (.const ``Nat [])
          (.sort (.succ (.param `u))) .default) .default)
      false
      (Lean4Lean.TypeChecker.Methods.withFuel 9999)
      indexedVecFamilyCandidateContext.toTypeChecker
      ({} : Lean4Lean.TypeChecker.State) =
        .ok (.sort indexedVecFamilyInferredLevel,
          indexedVecAfterIndexState) := by
  unfold Lean4Lean.TypeChecker.Inner.inferForall
  simp only [Lean4Lean.TypeChecker.Inner.inferForall.loop]
  rw [show
    (.sort (.succ (.param `u)) : Expr).instantiateRev #[] =
      .sort (.succ (.param `u)) by
        simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecRootSortCore]
  simp only
  rw [indexedVecEnsureSort]
  simp only
  rw [indexedVecOuterWithLocalDecl]
  rw [show
    (.const ``Nat [] : Expr).instantiateRev
        (#[] |>.push (.fvar ⟨indexedVecRootSortState.ngen.curr⟩)) =
      .const ``Nat [] by
        simp [Expr.instantiateRev_eq, Expr.instantiate_eq,
          Expr.instantiate1']]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecParamNatCore]
  simp only
  rw [indexedVecEnsureSort]
  simp only
  rw [indexedVecInnerWithLocalDecl]
  rw [show
    (.sort (.succ (.param `u)) : Expr).instantiateRev
        ((#[] |>.push
          (.fvar ⟨indexedVecRootSortState.ngen.curr⟩)).push
          (.fvar ⟨indexedVecNatState.ngen.curr⟩)) =
      .sort (.succ (.param `u)) by
        simp [Expr.instantiateRev_eq, Expr.instantiate_eq,
          Expr.instantiate1']]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecTerminalSortCore]
  simp only
  rw [indexedVecEnsureSort]
  simp [indexedVecFamilyInferredLevel, Expr.sortLevel!,
    Pure.pure, ReaderT.pure,
    StateT.pure, Except.pure]

private def indexedVecFamilyCheckedState : Lean4Lean.TypeChecker.State :=
  { indexedVecAfterIndexState with
    inferTypeC := indexedVecAfterIndexState.inferTypeC.insert
      (.forallE indexedVecParamName (.sort (.succ (.param `u)))
        (.forallE indexedVecIndexName (.const ``Nat [])
          (.sort (.succ (.param `u))) .default) .default)
      (.sort indexedVecFamilyInferredLevel) }

private theorem indexedVecFamilyCheckTypeInner :
    Lean4Lean.TypeChecker.Inner.inferType indexedVecInfo.type false
      (Lean4Lean.TypeChecker.Methods.withFuel 10000)
      indexedVecFamilyCandidateContext.toTypeChecker
      ({} : Lean4Lean.TypeChecker.State) =
        .ok (.sort indexedVecFamilyInferredLevel,
          indexedVecFamilyCheckedState) := by
  change Lean4Lean.TypeChecker.Inner.inferType'
    (.forallE indexedVecParamName (.sort (.succ (.param `u)))
      (.forallE indexedVecIndexName (.const ``Nat [])
        (.sort (.succ (.param `u))) .default) .default)
    false (Lean4Lean.TypeChecker.Methods.withFuel 9999)
    indexedVecFamilyCandidateContext.toTypeChecker
    ({} : Lean4Lean.TypeChecker.State) = _
  unfold Lean4Lean.TypeChecker.Inner.inferType'
  simp [Expr.hasLooseBVars, Expr.looseBVarRange',
    indexedVecFamilyInferForall, indexedVecFamilyCheckedState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem indexedVecFamily_whnfM :
    Lean4Lean.TypeChecker.M.run
      indexedVecFamilyCandidateContext.env
      indexedVecFamilyCandidateContext.safety
      indexedVecFamilyCandidateContext.lctx
      indexedVecFamilyCandidateContext.lparams
      indexedVecFamilyCandidateContext.fuel
      (Lean4Lean.TypeChecker.whnf indexedVecInfo.type) =
        .ok indexedVecInfo.type := by
  rfl

private theorem indexedVecSort_checkTypeM (lctx : LocalContext) :
    Lean4Lean.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Lean4Lean.TypeChecker.checkType (.sort (.succ (.param `u)))) =
        .ok (.sort (.succ (.succ (.param `u)))) := by
  change Except.map
    (fun x : Expr × Lean4Lean.TypeChecker.State => x.1)
    (Lean4Lean.TypeChecker.Inner.inferType
      (.sort (.succ (.param `u))) false
      (Lean4Lean.TypeChecker.Methods.withFuel 10000)
      (indexedVecTypeCheckerContext lctx)
      ({} : Lean4Lean.TypeChecker.State)) = _
  rw [indexedVecInferTypeFuel 9999]
  rw [indexedVecInferTypeSortCore 9999 lctx
    ({} : Lean4Lean.TypeChecker.State) Std.HashMap.getElem?_empty]
  rfl

private theorem indexedVecSort_whnfM (lctx : LocalContext) :
    Lean4Lean.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Lean4Lean.TypeChecker.whnf (.sort (.succ (.param `u)))) =
        .ok (.sort (.succ (.param `u))) := by
  rfl

private theorem indexedVecNat_checkTypeM (lctx : LocalContext) :
    Lean4Lean.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Lean4Lean.TypeChecker.checkType (.const ``Nat [])) =
        .ok (.sort (.succ .zero)) := by
  change Except.map
    (fun x : Expr × Lean4Lean.TypeChecker.State => x.1)
    (Lean4Lean.TypeChecker.Inner.inferType (.const ``Nat []) false
      (Lean4Lean.TypeChecker.Methods.withFuel 10000)
      (indexedVecTypeCheckerContext lctx)
      ({} : Lean4Lean.TypeChecker.State)) = _
  rw [indexedVecInferTypeFuel 9999]
  rw [indexedVecInferTypeNatCore 9999 lctx
    ({} : Lean4Lean.TypeChecker.State) Std.HashMap.getElem?_empty]
  rfl

private theorem indexedVecUnfoldNat (lctx methods state) :
    Lean4Lean.TypeChecker.Inner.unfoldDefinition (.const ``Nat [])
      methods (indexedVecTypeCheckerContext lctx) state =
        .ok (none, state) := by
  change Lean4Lean.TypeChecker.Inner.unfoldDefinitionCore
    (.const ``Nat []) methods (indexedVecTypeCheckerContext lctx) state = _
  simp [Lean4Lean.TypeChecker.Inner.unfoldDefinitionCore,
    Lean4Lean.TypeChecker.Inner.isDelta, Expr.getAppFn,
    indexedVecTypeCheckerContext, indexedVecKernel_lookup_nat,
    natInfo, ConstantInfo.hasValue,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem indexedVecWhnfLoopNat (lctx methods state n) :
    Lean4Lean.TypeChecker.Inner.whnf'.loop (.const ``Nat []) (n + 1)
      methods (indexedVecTypeCheckerContext lctx) state =
        .ok (.const ``Nat [], state) := by
  unfold Lean4Lean.TypeChecker.Inner.whnf'.loop
  simp [indexedVecUnfoldNat]

private theorem indexedVecNat_whnfM (lctx : LocalContext) :
    Lean4Lean.TypeChecker.M.run indexedVecKernelEnv .safe lctx [`u]
      ({} : FuelConfig)
      (Lean4Lean.TypeChecker.whnf (.const ``Nat [])) =
        .ok (.const ``Nat []) := by
  change Except.map
    (fun x : Expr × Lean4Lean.TypeChecker.State => x.1)
    (Lean4Lean.TypeChecker.Inner.whnf' (.const ``Nat [])
      (Lean4Lean.TypeChecker.Methods.withFuel 9999)
      (indexedVecTypeCheckerContext lctx)
      ({} : Lean4Lean.TypeChecker.State)) = _
  unfold Lean4Lean.TypeChecker.Inner.whnf'
  simp
  rw [show
    (if (indexedVecTypeCheckerContext lctx).eagerReduce then
      (indexedVecTypeCheckerContext lctx).fuel.whnfEager
    else (indexedVecTypeCheckerContext lctx).fuel.whnf) = 100000 by rfl]
  rw [show 100000 = 99999 + 1 by rfl]
  rw [indexedVecWhnfLoopNat]
  simp [Functor.map, StateT.map, Except.map]

private def indexedVecInnerInferredLevel : Level :=
  mkLevelIMax' (.succ .zero) (.succ (.succ (.param `u)))

private def indexedVecInnerNatState : Lean4Lean.TypeChecker.State :=
  { ({} : Lean4Lean.TypeChecker.State) with
    inferTypeC := ({} : Lean4Lean.TypeChecker.State).inferTypeC.insert
      (.const ``Nat []) (.sort (.succ .zero)) }

private def indexedVecInnerCheckerLctx : LocalContext :=
  indexedVecParamCandidateContext.lctx.mkLocalDecl
    ⟨indexedVecInnerNatState.ngen.curr⟩ indexedVecIndexName
    (.const ``Nat []) .default

private def indexedVecInnerAfterIndexState :
    Lean4Lean.TypeChecker.State :=
  { indexedVecInnerNatState with
    ngen := indexedVecInnerNatState.ngen.next }

private def indexedVecInnerSortState : Lean4Lean.TypeChecker.State :=
  { indexedVecInnerAfterIndexState with
    inferTypeC := indexedVecInnerAfterIndexState.inferTypeC.insert
      (.sort (.succ (.param `u)))
      (.sort (.succ (.succ (.param `u)))) }

private def indexedVecInnerCheckedState : Lean4Lean.TypeChecker.State :=
  { indexedVecInnerSortState with
    inferTypeC := indexedVecInnerSortState.inferTypeC.insert
      indexedVecInnerKernel (.sort indexedVecInnerInferredLevel) }

@[simp] private theorem indexedVecInnerNatCore :
    Lean4Lean.TypeChecker.Inner.inferType' (.const ``Nat []) false
      (Lean4Lean.TypeChecker.Methods.withFuel 9998)
      indexedVecParamCandidateContext.toTypeChecker
      ({} : Lean4Lean.TypeChecker.State) =
        .ok (.sort (.succ .zero), indexedVecInnerNatState) := by
  simpa [indexedVecParamCandidateContext,
    indexedVecFamilyCandidateContext,
    Lean4Lean.AddInductive.Context.pushLocalDecl,
    Lean4Lean.AddInductive.Context.toTypeChecker,
    indexedVecInfo, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal, indexedVecTypeCheckerContext,
    indexedVecInnerNatState] using
      (indexedVecInferTypeNatCore 9998
        indexedVecParamCandidateContext.lctx
        ({} : Lean4Lean.TypeChecker.State) Std.HashMap.getElem?_empty)

private theorem indexedVecInnerCheckerWithLocalDecl
    {α} (k : Expr → Lean4Lean.TypeChecker.RecM α)
    (methods : Lean4Lean.TypeChecker.Methods) :
    (withLocalDecl (m := Lean4Lean.TypeChecker.RecM)
      indexedVecIndexName .default (.const ``Nat []) k)
        methods indexedVecParamCandidateContext.toTypeChecker
          indexedVecInnerNatState =
      k (.fvar ⟨indexedVecInnerNatState.ngen.curr⟩) methods
        { indexedVecParamCandidateContext.toTypeChecker with
          lctx := indexedVecInnerCheckerLctx }
        indexedVecInnerAfterIndexState := by
  simpa [indexedVecInnerCheckerLctx,
    indexedVecInnerAfterIndexState] using
      (indexedVecWithLocalDecl indexedVecIndexName .default
        (.const ``Nat []) k methods
        indexedVecParamCandidateContext.toTypeChecker
        indexedVecInnerNatState)

@[simp] private theorem indexedVecInnerTerminalSortCore :
    Lean4Lean.TypeChecker.Inner.inferType'
      (.sort (.succ (.param `u))) false
      (Lean4Lean.TypeChecker.Methods.withFuel 9998)
      { indexedVecParamCandidateContext.toTypeChecker with
        lctx := indexedVecInnerCheckerLctx }
      indexedVecInnerAfterIndexState =
        .ok (.sort (.succ (.succ (.param `u))),
          indexedVecInnerSortState) := by
  simpa [indexedVecParamCandidateContext,
    indexedVecFamilyCandidateContext,
    Lean4Lean.AddInductive.Context.pushLocalDecl,
    Lean4Lean.AddInductive.Context.toTypeChecker,
    indexedVecInfo, ConstantInfo.levelParams,
    ConstantInfo.toConstantVal, indexedVecTypeCheckerContext,
    indexedVecInnerAfterIndexState, indexedVecInnerNatState,
    indexedVecInnerSortState] using
      (indexedVecInferTypeSortCore 9998 indexedVecInnerCheckerLctx
        indexedVecInnerAfterIndexState (by
          simp [indexedVecInnerAfterIndexState,
            indexedVecInnerNatState]))

private theorem indexedVecInnerInferForall :
    Lean4Lean.TypeChecker.Inner.inferForall indexedVecInnerKernel false
      (Lean4Lean.TypeChecker.Methods.withFuel 9999)
      indexedVecParamCandidateContext.toTypeChecker
      ({} : Lean4Lean.TypeChecker.State) =
        .ok (.sort indexedVecInnerInferredLevel,
          indexedVecInnerSortState) := by
  unfold indexedVecInnerKernel
  unfold Lean4Lean.TypeChecker.Inner.inferForall
  simp only [Lean4Lean.TypeChecker.Inner.inferForall.loop]
  rw [show (.const ``Nat [] : Expr).instantiateRev #[] =
    .const ``Nat [] by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq]]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecInnerNatCore]
  simp only
  rw [indexedVecEnsureSort]
  simp only
  rw [indexedVecInnerCheckerWithLocalDecl]
  rw [show
    (.sort (.succ (.param `u)) : Expr).instantiateRev
      (#[] |>.push (.fvar ⟨indexedVecInnerNatState.ngen.curr⟩)) =
        .sort (.succ (.param `u)) by
      simp [Expr.instantiateRev_eq, Expr.instantiate_eq,
        Expr.instantiate1']]
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [indexedVecInferTypeFuel 9998]
  rw [indexedVecInnerTerminalSortCore]
  simp only
  rw [indexedVecEnsureSort]
  simp [indexedVecInnerInferredLevel, Expr.sortLevel!,
    Pure.pure, ReaderT.pure, StateT.pure, Except.pure]

private theorem indexedVecInner_checkTypeM :
    Lean4Lean.TypeChecker.M.run indexedVecKernelEnv .safe
      indexedVecParamCandidateContext.lctx [`u] ({} : FuelConfig)
      (Lean4Lean.TypeChecker.checkType indexedVecInnerKernel) =
        .ok (.sort indexedVecInnerInferredLevel) := by
  change Except.map
    (fun x : Expr × Lean4Lean.TypeChecker.State => x.1)
    (Lean4Lean.TypeChecker.Inner.inferType indexedVecInnerKernel false
      (Lean4Lean.TypeChecker.Methods.withFuel 10000)
      indexedVecParamCandidateContext.toTypeChecker
      ({} : Lean4Lean.TypeChecker.State)) = _
  change Except.map
    (fun x : Expr × Lean4Lean.TypeChecker.State => x.1)
    (Lean4Lean.TypeChecker.Inner.inferType' indexedVecInnerKernel false
      (Lean4Lean.TypeChecker.Methods.withFuel 9999)
      indexedVecParamCandidateContext.toTypeChecker
      ({} : Lean4Lean.TypeChecker.State)) = _
  unfold Lean4Lean.TypeChecker.Inner.inferType'
  simp [indexedVecInnerKernel, Expr.hasLooseBVars,
    Expr.looseBVarRange',
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [show
    Lean4Lean.TypeChecker.Inner.inferForall
      (.forallE indexedVecIndexName (.const ``Nat [])
        (.sort (.succ (.param `u))) .default)
      false (Lean4Lean.TypeChecker.Methods.withFuel 9999)
      indexedVecParamCandidateContext.toTypeChecker
      ({} : Lean4Lean.TypeChecker.State) =
        .ok (.sort indexedVecInnerInferredLevel,
          indexedVecInnerSortState) by
      simpa [indexedVecInnerKernel] using indexedVecInnerInferForall]
  rfl

private theorem indexedVecInner_whnfM :
    Lean4Lean.TypeChecker.M.run indexedVecKernelEnv .safe
      indexedVecParamCandidateContext.lctx [`u] ({} : FuelConfig)
      (Lean4Lean.TypeChecker.whnf indexedVecInnerKernel) =
        .ok indexedVecInnerKernel := by
  rfl

private theorem indexedVecFamilyCandidateFresh :
    indexedVecFamilyCandidateContext.lctx.find?
      indexedVecFamilyCandidateContext.freshFVarId = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := indexedVecFamilyCandidateContext.freshFVarId)
    LocalContext.WF.nil
  simpa [indexedVecFamilyCandidateContext, LocalContext.toList] using h

private theorem indexedVecParamCandidateFresh :
    indexedVecParamCandidateContext.lctx.find?
      indexedVecParamCandidateContext.freshFVarId = none := by
  have hroot := indexedVecFamilyCandidateFresh
  have hwf : indexedVecParamCandidateContext.lctx.WF := by
    simpa [indexedVecParamCandidateContext,
      Lean4Lean.AddInductive.Context.pushLocalDecl] using
      (LocalContext.WF.mkLocalDecl LocalContext.WF.nil hroot)
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := indexedVecParamCandidateContext.freshFVarId) hwf
  rw [h]
  simp only [indexedVecParamCandidateContext,
    indexedVecFamilyCandidateContext,
    Lean4Lean.AddInductive.Context.pushLocalDecl,
    Lean4Lean.AddInductive.Context.freshFVarId]
  rw [LocalContext.mkLocalDecl_toList]
  rw [show ({} : LocalContext).toList = [] by rfl]
  simp [NameGenerator.next, NameGenerator.curr]
  intro heq
  injection heq with hname
  injection hname with hidx
  omega

private theorem indexedVecFamily_checkTypeM :
    Lean4Lean.TypeChecker.M.run
      indexedVecFamilyCandidateContext.env
      indexedVecFamilyCandidateContext.safety
      indexedVecFamilyCandidateContext.lctx
      indexedVecFamilyCandidateContext.lparams
      indexedVecFamilyCandidateContext.fuel
      (Lean4Lean.TypeChecker.checkType indexedVecInfo.type) =
        .ok (.sort indexedVecFamilyInferredLevel) := by
  change Except.map
    (fun x : Expr × Lean4Lean.TypeChecker.State => x.1)
    (Lean4Lean.TypeChecker.Inner.inferType indexedVecInfo.type false
      (Lean4Lean.TypeChecker.Methods.withFuel 10000)
      indexedVecFamilyCandidateContext.toTypeChecker
      ({} : Lean4Lean.TypeChecker.State)) = _
  rw [indexedVecFamilyCheckTypeInner]
  rfl

private def indexedVecParamAnnotations :
    Lean4Lean.AddInductive.CandidateTypeAnnotations
      indexedVecTerminalKernel where
  consumed := indexedVecTerminalKernel
  trace := .identity _

private def indexedVecIndexAnnotations :
    Lean4Lean.AddInductive.CandidateTypeAnnotations (.const ``Nat []) where
  consumed := .const ``Nat []
  trace := .identity _

private theorem indexedVecParamAnnotationTrace_build :
    Lean4Lean.AddInductive.CandidateTypeAnnotationTrace.build
      indexedVecTerminalKernel =
        ⟨indexedVecTerminalKernel, .identity _⟩ := by
  simp [Lean4Lean.AddInductive.CandidateTypeAnnotationTrace.build,
    indexedVecTerminalKernel]

private theorem indexedVecIndexAnnotationTrace_build :
    Lean4Lean.AddInductive.CandidateTypeAnnotationTrace.build
      (.const ``Nat []) = ⟨.const ``Nat [], .identity _⟩ := by
  simp [Lean4Lean.AddInductive.CandidateTypeAnnotationTrace.build]

private theorem indexedVecParamAnnotations_build :
    Lean4Lean.AddInductive.buildCandidateTypeAnnotations
      indexedVecTerminalKernel = .ok indexedVecParamAnnotations := by
  unfold Lean4Lean.AddInductive.buildCandidateTypeAnnotations
  rw [indexedVecParamAnnotationTrace_build]
  rfl

private theorem indexedVecIndexAnnotations_build :
    Lean4Lean.AddInductive.buildCandidateTypeAnnotations
      (.const ``Nat []) = .ok indexedVecIndexAnnotations := by
  unfold Lean4Lean.AddInductive.buildCandidateTypeAnnotations
  rw [indexedVecIndexAnnotationTrace_build]
  rfl

private theorem indexedVecParamAnnotations_match :
    indexedVecParamAnnotations.Matches :=
  Lean4Lean.AddInductive.CandidateTypeAnnotations.matches_of_build
    indexedVecParamAnnotations indexedVecParamAnnotations_build

private theorem indexedVecIndexAnnotations_match :
    indexedVecIndexAnnotations.Matches :=
  Lean4Lean.AddInductive.CandidateTypeAnnotations.matches_of_build
    indexedVecIndexAnnotations indexedVecIndexAnnotations_build

private theorem indexedVecParamAnnotationsEq :
    Lean4Lean.AddInductive.CandidateIsDefEqStep.Valid
      ⟨indexedVecFamilyCandidateContext, indexedVecTerminalKernel,
        indexedVecParamAnnotations.consumed⟩ := by
  simpa [indexedVecParamAnnotations] using
    (candidateIsDefEqSelfValid indexedVecFamilyCandidateContext
      indexedVecTerminalKernel 9999 rfl)

private theorem indexedVecIndexAnnotationsEq :
    Lean4Lean.AddInductive.CandidateIsDefEqStep.Valid
      ⟨indexedVecParamCandidateContext, (.const ``Nat []),
        indexedVecIndexAnnotations.consumed⟩ := by
  simpa [indexedVecIndexAnnotations] using
    (candidateIsDefEqSelfValid indexedVecParamCandidateContext
      (.const ``Nat []) 9999 rfl)

private def indexedVecParamDomainCandidateTrace :
    Lean4Lean.AddInductive.CandidateExprTrace
      indexedVecFamilyCandidateContext indexedVecTerminalKernel :=
  .terminal indexedVecFamilyCandidateContext indexedVecTerminalKernel
    (.sort (.succ (.succ (.param `u)))) indexedVecTerminalKernel
    (by
      simpa [indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        indexedVecTerminalKernel] using
          indexedVecSort_checkTypeM
            indexedVecFamilyCandidateContext.lctx)
    (by
      simpa [indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        indexedVecTerminalKernel] using
          indexedVecSort_whnfM indexedVecFamilyCandidateContext.lctx)

private def indexedVecIndexDomainCandidateTrace :
    Lean4Lean.AddInductive.CandidateExprTrace
      indexedVecParamCandidateContext (.const ``Nat []) :=
  .terminal indexedVecParamCandidateContext (.const ``Nat [])
    (.sort (.succ .zero)) (.const ``Nat [])
    (by
      simpa [indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Lean4Lean.AddInductive.Context.pushLocalDecl] using
          indexedVecNat_checkTypeM indexedVecParamCandidateContext.lctx)
    (by
      simpa [indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Lean4Lean.AddInductive.Context.pushLocalDecl] using
          indexedVecNat_whnfM indexedVecParamCandidateContext.lctx)

private def indexedVecTerminalCandidateTrace :
    Lean4Lean.AddInductive.CandidateExprTrace
      indexedVecIndexCandidateContext
      (indexedVecTerminalKernel.instantiate1
        indexedVecParamCandidateContext.freshExpr) :=
  .terminal indexedVecIndexCandidateContext
    (indexedVecTerminalKernel.instantiate1
      indexedVecParamCandidateContext.freshExpr)
    (.sort (.succ (.succ (.param `u)))) indexedVecTerminalKernel
    (by
      simpa [indexedVecIndexCandidateContext,
        indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Lean4Lean.AddInductive.Context.pushLocalDecl] using
          indexedVecSort_checkTypeM indexedVecIndexCandidateContext.lctx)
    (by
      simpa [indexedVecIndexCandidateContext,
        indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Lean4Lean.AddInductive.Context.pushLocalDecl] using
          indexedVecSort_whnfM indexedVecIndexCandidateContext.lctx)

private def indexedVecInnerCandidateTrace :
    Lean4Lean.AddInductive.CandidateExprTrace
      indexedVecParamCandidateContext
      (indexedVecInnerKernel.instantiate1
        indexedVecFamilyCandidateContext.freshExpr) :=
  .forallE indexedVecParamCandidateContext
    (indexedVecInnerKernel.instantiate1
      indexedVecFamilyCandidateContext.freshExpr)
    (.sort indexedVecInnerInferredLevel)
    indexedVecIndexName (.const ``Nat []) indexedVecTerminalKernel
    .default indexedVecParamCandidateFresh indexedVecIndexAnnotations
    indexedVecIndexAnnotationsEq
    (by
      simpa [indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Lean4Lean.AddInductive.Context.pushLocalDecl] using
          indexedVecInner_checkTypeM)
    (by
      simpa [indexedVecParamCandidateContext,
        indexedVecFamilyCandidateContext, indexedVecInfo,
        ConstantInfo.levelParams, ConstantInfo.toConstantVal,
        Lean4Lean.AddInductive.Context.pushLocalDecl] using
          indexedVecInner_whnfM)
    indexedVecIndexDomainCandidateTrace indexedVecTerminalCandidateTrace

private def indexedVecFamilyCandidateTrace :
    Lean4Lean.AddInductive.CandidateExprTrace
      indexedVecFamilyCandidateContext indexedVecInfo.type :=
  .forallE indexedVecFamilyCandidateContext indexedVecInfo.type
    (.sort indexedVecFamilyInferredLevel)
    indexedVecParamName indexedVecTerminalKernel indexedVecInnerKernel
    .default indexedVecFamilyCandidateFresh indexedVecParamAnnotations
    indexedVecParamAnnotationsEq
    indexedVecFamily_checkTypeM
    (by
      simpa [indexedVecInfo, ConstantInfo.type,
        ConstantInfo.toConstantVal, indexedVecInnerKernel,
        indexedVecTerminalKernel] using indexedVecFamily_whnfM)
    indexedVecParamDomainCandidateTrace indexedVecInnerCandidateTrace

def indexedVecFamilyCandidate :
    Lean4Lean.AddInductive.CandidateExpr indexedVecInfo.type :=
  ⟨indexedVecFamilyCandidateContext, indexedVecFamilyCandidateTrace⟩

theorem indexedVecFamilyCandidate_view_eq :
    indexedVecFamilyCandidate.view = indexedVecInfo.type := by
  have habstract (context : Lean4Lean.AddInductive.Context) (e : Expr) :
      e.abstract #[context.freshExpr] =
        Expr.abstract1 context.freshFVarId e := by
    rw [show #[context.freshExpr] =
      ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl]
    simp only [Expr.abstract_eq, Expr.abstractList]
  simp only [indexedVecFamilyCandidate,
    Lean4Lean.AddInductive.CandidateExpr.view,
    indexedVecFamilyCandidateTrace,
    indexedVecInnerCandidateTrace, indexedVecParamDomainCandidateTrace,
    indexedVecIndexDomainCandidateTrace, indexedVecTerminalCandidateTrace,
    Lean4Lean.AddInductive.CandidateExprTrace.view]
  rw [habstract, habstract]
  simp [Expr.abstract1, indexedVecTerminalKernel,
    indexedVecFamilyCandidateContext,
    Lean4Lean.AddInductive.Context.pushLocalDecl,
    Lean4Lean.AddInductive.Context.freshFVarId,
    NameGenerator.next, NameGenerator.curr,
    indexedVecInfo, ConstantInfo.type, ConstantInfo.toConstantVal]
  constructor <;> rfl

/-- Every retained family-type candidate node preserves its kernel source.
This is the structural premise used by the semantic spine interpreter; it is
stronger than the root `view` equality because it covers both Pi domains and
the instantiated body under their exact candidate contexts. -/
theorem indexedVecFamilyCandidate_identity :
    Lean4Lean.TypeChecker.CandidateExprIdentity
      indexedVecFamilyCandidate.trace := by
  change Lean4Lean.TypeChecker.CandidateExprIdentity
    indexedVecFamilyCandidateTrace
  unfold indexedVecFamilyCandidateTrace
  refine .forallE (name := indexedVecParamName) (binderInfo := .default)
    (body := indexedVecInnerKernel)
    (annotations := indexedVecParamAnnotations)
    indexedVecParamDomainCandidateTrace indexedVecInnerCandidateTrace
    ?_ rfl (.terminal rfl) ?_
  · rfl
  · unfold indexedVecInnerCandidateTrace
    refine .forallE (name := indexedVecIndexName) (binderInfo := .default)
      (body := indexedVecTerminalKernel)
      (annotations := indexedVecIndexAnnotations)
      indexedVecIndexDomainCandidateTrace indexedVecTerminalCandidateTrace
      ?_ rfl (.terminal rfl) ?_
    · simpa only [Expr.instantiate1_eq, indexedVecInnerKernel] using
        indexedVecInnerKernel_instantiate1
          indexedVecFamilyCandidateContext.freshExpr
    · exact .terminal (by
        simpa only [Expr.instantiate1_eq] using
          (indexedVecTerminalKernel_instantiate1
            indexedVecParamCandidateContext.freshExpr).symm)

private theorem indexedVecParamDomainCandidateTrace_loop (fuel : Nat) :
    Lean4Lean.AddInductive.buildCandidateExpr.loop
      indexedVecFamilyCandidateContext indexedVecTerminalKernel
      (fuel + 1) = .ok indexedVecParamDomainCandidateTrace := by
  simpa only [indexedVecParamDomainCandidateTrace] using
    Lean4Lean.AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      indexedVecFamilyCandidateContext indexedVecTerminalKernel
      (.sort (.succ (.succ (.param `u)))) indexedVecTerminalKernel fuel
      indexedVecParamDomainCandidateTrace.rootCheck.valid
      indexedVecParamDomainCandidateTrace.rootWhnf_valid rfl

private theorem indexedVecIndexDomainCandidateTrace_loop (fuel : Nat) :
    Lean4Lean.AddInductive.buildCandidateExpr.loop
      indexedVecParamCandidateContext (.const ``Nat []) (fuel + 1) =
        .ok indexedVecIndexDomainCandidateTrace := by
  simpa only [indexedVecIndexDomainCandidateTrace] using
    Lean4Lean.AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      indexedVecParamCandidateContext (.const ``Nat [])
      (.sort (.succ .zero)) (.const ``Nat []) fuel
      indexedVecIndexDomainCandidateTrace.rootCheck.valid
      indexedVecIndexDomainCandidateTrace.rootWhnf_valid rfl

private theorem indexedVecTerminalCandidateTrace_loop (fuel : Nat) :
    Lean4Lean.AddInductive.buildCandidateExpr.loop
      indexedVecIndexCandidateContext
      (indexedVecTerminalKernel.instantiate1
        indexedVecParamCandidateContext.freshExpr)
      (fuel + 1) = .ok indexedVecTerminalCandidateTrace := by
  simpa only [indexedVecTerminalCandidateTrace] using
    Lean4Lean.AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
      indexedVecIndexCandidateContext
      (indexedVecTerminalKernel.instantiate1
        indexedVecParamCandidateContext.freshExpr)
      (.sort (.succ (.succ (.param `u)))) indexedVecTerminalKernel fuel
      indexedVecTerminalCandidateTrace.rootCheck.valid
      indexedVecTerminalCandidateTrace.rootWhnf_valid rfl

private theorem indexedVecInnerCandidateTrace_loop :
    Lean4Lean.AddInductive.buildCandidateExpr.loop
      indexedVecParamCandidateContext
      (indexedVecInnerKernel.instantiate1
        indexedVecFamilyCandidateContext.freshExpr) 999 =
        .ok indexedVecInnerCandidateTrace := by
  rw [show 999 = 998 + 1 by rfl]
  simpa only [indexedVecInnerCandidateTrace,
    indexedVecIndexCandidateContext] using
    (Lean4Lean.AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := indexedVecParamCandidateContext)
      (e := indexedVecInnerKernel.instantiate1
        indexedVecFamilyCandidateContext.freshExpr)
      (inferred := .sort indexedVecInnerInferredLevel)
      (fuel := 998) (name := indexedVecIndexName)
      (domain := .const ``Nat []) (body := indexedVecTerminalKernel)
      (binderInfo := .default) (hfresh := indexedVecParamCandidateFresh)
      (annotations := indexedVecIndexAnnotations)
      (hannotations := indexedVecIndexAnnotations_build)
      (hannotationsEq := indexedVecIndexAnnotationsEq)
      (hcheck := indexedVecInnerCandidateTrace.rootCheck.valid)
      (hrun := indexedVecInnerCandidateTrace.rootWhnf_valid)
      (domainCandidate := indexedVecIndexDomainCandidateTrace)
      (bodyCandidate := indexedVecTerminalCandidateTrace)
      (hdomain := by
        simpa using indexedVecIndexDomainCandidateTrace_loop 997)
      (hbody := by
        simpa [indexedVecIndexCandidateContext] using
          indexedVecTerminalCandidateTrace_loop 997))

private theorem indexedVecFamilyCandidateTrace_loop :
    Lean4Lean.AddInductive.buildCandidateExpr.loop
      indexedVecFamilyCandidateContext indexedVecInfo.type
      indexedVecFamilyCandidateContext.fuel.inductiveFuel =
        .ok indexedVecFamilyCandidateTrace := by
  change Lean4Lean.AddInductive.buildCandidateExpr.loop
    indexedVecFamilyCandidateContext indexedVecInfo.type (999 + 1) = _
  simpa only [indexedVecFamilyCandidateTrace,
    indexedVecParamCandidateContext] using
    (Lean4Lean.AddInductive.buildCandidateExpr_loop_of_whnf_forall
      (context := indexedVecFamilyCandidateContext)
      (e := indexedVecInfo.type)
      (inferred := .sort indexedVecFamilyInferredLevel)
      (fuel := 999) (name := indexedVecParamName)
      (domain := indexedVecTerminalKernel) (body := indexedVecInnerKernel)
      (binderInfo := .default) (hfresh := indexedVecFamilyCandidateFresh)
      (annotations := indexedVecParamAnnotations)
      (hannotations := indexedVecParamAnnotations_build)
      (hannotationsEq := indexedVecParamAnnotationsEq)
      (hcheck := indexedVecFamilyCandidateTrace.rootCheck.valid)
      (hrun := indexedVecFamilyCandidateTrace.rootWhnf_valid)
      (domainCandidate := indexedVecParamDomainCandidateTrace)
      (bodyCandidate := indexedVecInnerCandidateTrace)
      (hdomain := by
        simpa using indexedVecParamDomainCandidateTrace_loop 998)
      (hbody := by
        simpa [indexedVecParamCandidateContext] using
          indexedVecInnerCandidateTrace_loop))

/-- The executable candidate traversal preserves the real IndexedVec family
telescope and classifies its first binder as a parameter and its second as an
index in the subsequent family-validation pass. -/
theorem indexedVecFamily_candidateTrace :
    Lean4Lean.AddInductive.buildCandidateExpr indexedVecInfo.type
      indexedVecFamilyCandidateContext = .ok indexedVecFamilyCandidate := by
  unfold Lean4Lean.AddInductive.buildCandidateExpr
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  rw [indexedVecFamilyCandidateTrace_loop]
  rfl

/-- The executable IndexedVec family candidate retains its parameter and
index binders in order. -/
theorem indexedVecFamilyCandidate_spineLength :
    indexedVecFamilyCandidate.trace.spineLength = 2 := by
  rfl

theorem indexedVecFamilyCandidate_validationAnnotations :
    indexedVecFamilyCandidate.trace.validationAnnotations := by
  exact ⟨indexedVecParamAnnotations_match,
    indexedVecIndexAnnotations_match, trivial⟩

theorem indexedVecFamilyCandidate_terminalResult :
    indexedVecFamilyCandidate.trace.terminalResult =
      .sort (.succ (.param `u)) := by
  rfl

def indexedVecKernelNil : Constructor where
  name := indexedVecNilInfo.name
  type := indexedVecNilInfo.type

def indexedVecKernelCons : Constructor where
  name := indexedVecConsInfo.name
  type := indexedVecConsInfo.type

def indexedVecKernelType : InductiveType where
  name := indexedVecInfo.name
  type := indexedVecInfo.type
  ctors := [indexedVecKernelNil, indexedVecKernelCons]

def indexedVecCandidateInductiveStats :
    Lean4Lean.AddInductive.InductiveStats :=
  indexedVecFamilyCandidate.trace.singletonCandidateInductiveStats
    indexedVecKernelType 1 (.succ (.param `u))

private theorem indexedVecFamily_data_hasExprMVar_false :
    indexedVecInfo.type.data.hasExprMVar = false := by
  change indexedVecInfo.type.hasExprMVar = false
  rw [Expr.hasExprMVar_eq]
  rfl

private theorem indexedVecFamily_data_hasLevelMVar_false :
    indexedVecInfo.type.data.hasLevelMVar = false := by
  change indexedVecInfo.type.hasLevelMVar = false
  rw [Expr.hasLevelMVar_eq]
  simp [indexedVecInfo, ConstantInfo.type, ConstantInfo.toConstantVal,
    Expr.hasLevelMVar', Level.hasMVar_eq, Level.hasMVar']

private theorem indexedVecFamily_data_hasFVar_false :
    indexedVecInfo.type.data.hasFVar = false := by
  change indexedVecInfo.type.hasFVar = false
  rw [Expr.hasFVar_eq]
  rfl

private theorem indexedVecFamily_hasMVar_false :
    indexedVecInfo.type.hasMVar = false := by
  change (indexedVecInfo.type.data.hasExprMVar ||
    indexedVecInfo.type.data.hasLevelMVar) = false
  rw [indexedVecFamily_data_hasExprMVar_false,
    indexedVecFamily_data_hasLevelMVar_false]
  rfl

private theorem indexedVecFamily_hasFVar_false :
    indexedVecInfo.type.hasFVar = false := by
  exact indexedVecFamily_data_hasFVar_false

private theorem indexedVecFamily_closed :
    indexedVecFamilyCandidateContext.env.checkNoMVarNoFVar
      indexedVecKernelType.name indexedVecKernelType.type = .ok () := by
  unfold Kernel.Environment.checkNoMVarNoFVar
    Kernel.Environment.checkNoMVar Kernel.Environment.checkNoFVar
  rw [show indexedVecKernelType.type.hasMVar = false by
    simpa [indexedVecKernelType] using indexedVecFamily_hasMVar_false]
  rw [show indexedVecKernelType.type.hasFVar = false by
    simpa [indexedVecKernelType] using indexedVecFamily_hasFVar_false]
  rfl

private theorem indexedVecTerminal_ensureSortM :
    Lean4Lean.TypeChecker.M.run
      indexedVecFamilyCandidate.trace.terminalContext.env
      indexedVecFamilyCandidate.trace.terminalContext.safety
      indexedVecFamilyCandidate.trace.terminalContext.lctx
      indexedVecFamilyCandidate.trace.terminalContext.lparams
      indexedVecFamilyCandidate.trace.terminalContext.fuel
      (Lean4Lean.TypeChecker.ensureSort
        (.sort (.succ (.param `u)))) =
      .ok (.sort (.succ (.param `u))) := by
  rfl

/-- The real IndexedVec family telescope drives the complete singleton
family-validation pass with one parameter and one index. -/
theorem indexedVec_checkInductiveTypes
    (k : Lean4Lean.AddInductive.InductiveStats →
      Lean4Lean.AddInductive.M α) :
    Lean4Lean.AddInductive.checkInductiveTypes 1
        #[indexedVecKernelType] k indexedVecFamilyCandidateContext =
      k indexedVecCandidateInductiveStats
        indexedVecFamilyCandidate.trace.terminalContext := by
  simpa [indexedVecCandidateInductiveStats] using
    (Lean4Lean.AddInductive.CandidateExprTrace.checkInductiveTypes_singleton_of_candidate
      (indType := indexedVecKernelType)
      (candidate := indexedVecFamilyCandidate.trace)
      (nparams := 1) (resultLevel := .succ (.param `u)) (k := k)
      indexedVecFamily_closed (by decide) (by decide)
      ⟨indexedVecParamAnnotations_match,
        indexedVecIndexAnnotations_match, trivial⟩
      rfl indexedVecTerminal_ensureSortM)

theorem indexedVecCandidateInductiveStats_nindices :
    indexedVecCandidateInductiveStats.nindices = #[1] := by
  rfl

theorem indexedVecCandidateInductiveStats_params :
    indexedVecCandidateInductiveStats.params =
    #[indexedVecFamilyCandidateContext.freshExpr] := by
  rfl

theorem indexedVecCandidateInductiveStats_resultLevel :
    indexedVecCandidateInductiveStats.resultLevel =
    .succ (.param `u) := by
  rfl

theorem indexedVecCandidateInductiveStats_indConsts :
    indexedVecCandidateInductiveStats.indConsts =
    #[.const ``IndexedVec [.param `u]] := by
  rfl

/--
info: 'Lean4Lean.InductiveReplayFixtures.candidateIsDefEqSelfValid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq]
-/
#guard_msgs in
#print axioms candidateIsDefEqSelfValid

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecFamily_candidateTrace' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
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
#print axioms indexedVecFamily_candidateTrace

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVec_checkInductiveTypes' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.hasExprMVar_eq,
 Expr.hasFVar_eq,
 Expr.hasLevelMVar_eq,
 Expr.hasLevelParam_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
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
#print axioms indexedVec_checkInductiveTypes

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecCandidateInductiveStats_nindices' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
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
#print axioms indexedVecCandidateInductiveStats_nindices

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVecCandidateInductiveStats_params' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
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
#print axioms indexedVecCandidateInductiveStats_params

end Lean4Lean.InductiveReplayFixtures
