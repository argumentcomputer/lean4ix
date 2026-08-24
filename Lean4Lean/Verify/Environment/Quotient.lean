import Lean4Lean.Verify.Environment.Extension

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

/-! # Checked quotient initialization -/

/-- Closed form of the `Eq` type accepted by `checkEqType`. -/
def checkedEqType (u : Name) : Expr :=
  .forallE `α (.sort (.param u))
    (.forallE `a (.bvar 0) (.forallE `a (.bvar 1) .prop .default) .default) .implicit

private theorem checkedEqType_build (u : Name) :
    (ExprBuildT.run (m := Id) do
      withLocalDecl `α .implicit (.sort (.param u)) fun α => do
        let lctx : LocalContext ← read
        return lctx.mkForall #[α] <| .arrow α <| .arrow α .prop) = checkedEqType u := by
  simp only [ExprBuildT.run, withLocalDecl, MonadLocalNameGenerator.withFreshId,
    read, withReader, readThe, withTheReader, MonadWithReaderOf.withReader,
    MonadReaderOf.read, ReaderT.read]
  let ngen : NameGenerator := {}
  let lctx : LocalContext := {}
  let id : FVarId := ⟨ngen.curr⟩
  let lctx' := lctx.mkLocalDecl id `α (.sort (.param u)) .implicit
  change lctx'.mkForall #[Expr.fvar id]
    ((Expr.fvar id).arrow ((Expr.fvar id).arrow Expr.prop)) = checkedEqType u
  have lctxWF : lctx.WF := by exact .nil
  have fresh : lctx.find? id = none := by
    rw [lctxWF.find?_eq_find?_toList]
    simp [lctx, LocalContext.toList]
    intro x hx
    change some x ∈
      (PersistentArray.empty : PersistentArray (Option LocalDecl)).toList' at hx
    rw [PersistentArray.toList'_empty] at hx
    simp at hx
  have lctx'WF : lctx'.WF := lctxWF.mkLocalDecl fresh
  have idFind : lctx'.find? id = some (.cdecl lctx.decls.size id `α
      (.sort (.param u)) .implicit .default) := by
    rw [lctx'WF.find?_eq_find?_toList, LocalContext.mkLocalDecl_toList]
    simp [LocalDecl.fvarId]
  have hx : ∀ x ∈ [id], ∃ decl, lctx'.find? x = some decl := by
    intro x hx
    rw [List.mem_singleton] at hx
    subst x
    exact ⟨_, idFind⟩
  rw [LocalContext.mkForall]
  change LocalContext.mkBinding false lctx' ⟨[id].map Expr.fvar⟩
    ((Expr.fvar id).arrow ((Expr.fvar id).arrow Expr.prop)) = checkedEqType u
  rw [LocalContext.mkBinding_eq, LocalContext.mkBindingList_eq_fold hx (by simp)]
  simp [LocalContext.mkBindingList1, idFind, checkedEqType, lctx, id, ngen]
  rfl

private theorem checkedEqType_tr (u : Name) :
    trExprS? [u] [] (checkedEqType u) = some eqConst.type := by
  simp [checkedEqType, trExprS?, eqConst, VLevel.ofLevel, VLCtx.find?,
    VLCtx.next, VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
    VExpr.liftN, liftVar, Expr.prop]

/-- A successful shape check exposes the exact `Eq` metadata it inspected. -/
theorem checkEqType.shape {env : Environment} :
    (checkEqType env).WF fun _ =>
      ∃ info, env.find? ``Eq = some (.inductInfo info) ∧
        ∃ u, info.levelParams = [u] ∧ info.type == checkedEqType u := by
  intro _ h
  unfold checkEqType at h
  simp only [Environment.get] at h
  split at h <;> try contradiction
  rename_i ci hfind
  cases ci with
  | inductInfo info =>
    cases info
    rename_i constant numParams numIndices all ctors numNested isRec isUnsafe isReflexive
    cases constant
    rename_i name levelParams type
    cases levelParams with
    | nil => simp_all [( · >>= · ), Except.bind, pure, Pure.pure, Except.pure]
    | cons u us =>
      cases us with
      | cons u' us => simp_all [( · >>= · ), Except.bind, pure, Pure.pure, Except.pure]
      | nil =>
        refine ⟨_, hfind, u, rfl, ?_⟩
        simp only [pure_bind] at h
        split at h <;> try contradiction
        simp [( · >>= · ), Except.bind, pure, Pure.pure, Except.pure,
          ExprBuildT.run, withLocalDecl, MonadLocalNameGenerator.withFreshId,
          read, withReader, readThe, withTheReader, MonadWithReaderOf.withReader,
          MonadReaderOf.read, ReaderT.read, ReaderT.bind, ReaderT.pure] at h
        split at h
        · contradiction
        · rename_i firstResult firstOk
          split at firstOk <;> try contradiction
          rename_i condition
          have heqv : type ==
              (({ } : LocalContext).mkLocalDecl ⟨({ } : NameGenerator).curr⟩ `α
                  (.sort (.param u)) .implicit).mkForall
                #[Expr.fvar ⟨({ } : NameGenerator).curr⟩]
                ((Expr.fvar ⟨({ } : NameGenerator).curr⟩).arrow
                  ((Expr.fvar ⟨({ } : NameGenerator).curr⟩).arrow Expr.prop)) := by
            simpa [( · != · )] using condition
          have hbuild := checkedEqType_build u
          simp only [ExprBuildT.run, withLocalDecl,
            MonadLocalNameGenerator.withFreshId, read, withReader, readThe,
            withTheReader, MonadWithReaderOf.withReader, MonadReaderOf.read,
            ReaderT.read] at hbuild
          change
            (({ } : LocalContext).mkLocalDecl ⟨({ } : NameGenerator).curr⟩ `α
                (.sort (.param u)) .implicit).mkForall
              #[Expr.fvar ⟨({ } : NameGenerator).curr⟩]
              ((Expr.fvar ⟨({ } : NameGenerator).curr⟩).arrow
                ((Expr.fvar ⟨({ } : NameGenerator).curr⟩).arrow Expr.prop)) =
              checkedEqType u at hbuild
          rw [hbuild] at heqv
          exact heqv
  | _ => simp_all [( · >>= · ), Except.bind, pure, Pure.pure, Except.pure]

/-- Shape checking plus translated-history safety identifies the Theory `Eq`
constant at every safety level. -/
theorem checkEqType.quotReady {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) :
    (checkEqType env).WF fun _ =>
      ∀ safety, (ves.venv safety).QuotReady := by
  exact checkEqType.shape.mono fun _ h => by
    obtain ⟨info, hfind, u, hu, htype⟩ := h
    have hEqSafe : info.isUnsafe = false :=
      (wf.tr (safety := .unsafe)).inductInfo_safe hfind
    intro safety
    obtain ⟨ci, hci, htr⟩ := (wf.tr (safety := safety)).find? hfind (by
      simp [ConstantInfo.safety, ConstantInfo.isUnsafe, hEqSafe,
        ConstantInfo.isPartial, DefinitionSafety.le_safe])
    obtain ⟨_, huvars, htrExpr⟩ := htr
    dsimp [ConstantInfo.levelParams, ConstantInfo.toConstantVal,
      ConstantInfo.type] at huvars htrExpr
    have htrType : TrExprS (ves.venv safety) [u] [] (checkedEqType u) ci.type := by
      rw [hu] at htrExpr
      exact htrExpr.eqv htype
    have hcomputed := htrType.trExprS?_eq (by
      simp [checkedEqType, TrExprS.IsUnique, Expr.prop])
    have hciType : ci.type = eqConst.type := by
      exact Option.some.inj ((checkedEqType_tr u).symm.trans hcomputed).symm
    have hciUvars : ci.uvars = eqConst.uvars := by
      rw [hu] at huvars
      simpa [eqConst] using huvars.symm
    have hciEq : ci = eqConst := by
      cases ci with
      | mk ciUvars ciType =>
        dsimp only [VConstant.uvars, VConstant.type] at hciUvars hciType ⊢
        cases hciUvars
        cases hciType
        rfl
    rwa [hciEq] at hci

/-! ## Translation of the four closed quotient types -/

/-- Representation-only translation for closed declaration types.  Semantic
typing premises are recovered from the canonical Theory constant's `WF`
proof by `QuotTrTypeExpr.to_trExprS`. -/
private inductive QuotTrTypeExpr (env : VEnv) (Us : List Name) :
    VLCtx → Expr → VExpr → Prop where
  | bvar : Δ.find? (.inl i) = some (e, A) → QuotTrTypeExpr env Us Δ (.bvar i) e
  | sort : VLevel.ofLevel Us u = some u' → QuotTrTypeExpr env Us Δ (.sort u) (.sort u')
  | const :
    env.constants c = some ci →
    us.mapM (VLevel.ofLevel Us) = some us' →
    us.length = ci.uvars →
    QuotTrTypeExpr env Us Δ (.const c us) (.const c us')
  | app : QuotTrTypeExpr env Us Δ f f' → QuotTrTypeExpr env Us Δ a a' →
      QuotTrTypeExpr env Us Δ (.app f a) (.app f' a')
  | forallE : QuotTrTypeExpr env Us Δ ty ty' →
      QuotTrTypeExpr env Us ((none, .vlam ty') :: Δ) body body' →
      QuotTrTypeExpr env Us Δ (.forallE name ty body bi) (.forallE ty' body')

private theorem QuotTrTypeExpr.to_trExprS
    (H : QuotTrTypeExpr env Us Δ e e')
    (henv : env.Ordered)
    (hΔ : OnCtx Δ.toCtx (env.IsType Us.length))
    (hwf : e'.WF env Us.length Δ.toCtx) : TrExprS env Us Δ e e' := by
  induction H with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app _ _ ihf iha =>
    obtain ⟨A, B, htf, hta⟩ := hwf.app_inv henv hΔ
    exact .app htf hta (ihf hΔ ⟨_, htf⟩) (iha hΔ ⟨_, hta⟩)
  | forallE _ _ ihty ihbody =>
    obtain ⟨_, hwf⟩ := hwf
    obtain ⟨hty, hbody⟩ := VEnv.HasType.forallE_inv henv hwf
    obtain ⟨u, hty⟩ := hty
    obtain ⟨v, hbody⟩ := hbody
    exact .forallE ⟨u, hty⟩ ⟨v, hbody⟩
      (ihty hΔ ⟨_, hty⟩) (ihbody ⟨hΔ, ⟨u, hty⟩⟩ ⟨_, hbody⟩)

private theorem VConstant.type_wf {ci : VConstant} {env : VEnv} (h : ci.WF env) :
    ci.type.WF env ci.uvars [] := by
  obtain ⟨u, h⟩ := h
  exact ⟨.sort u, h⟩

local syntax "quot_tr_type_tac" : tactic
macro_rules
  | `(tactic| quot_tr_type_tac) => `(tactic|
    first
    | apply QuotTrTypeExpr.bvar; rfl
    | apply QuotTrTypeExpr.sort; rfl
    | apply QuotTrTypeExpr.const <;>
        (first | assumption | rfl | (dsimp; simp [VLevel.params']))
    | apply QuotTrTypeExpr.app <;> quot_tr_type_tac
    | apply QuotTrTypeExpr.forallE <;> quot_tr_type_tac)

private theorem quotTypeExpr_tr {env : VEnv} (henv : env.WF) :
    TrExprS env [`u] [] quotTypeExpr quotConst.type := by
  have hquotWF : quotConst.WF env := by
    unfold VConstant.WF quotConst
    refine ⟨_, by type_tac⟩
  apply QuotTrTypeExpr.to_trExprS (henv := henv.ordered) (hΔ := by trivial)
  · unfold quotTypeExpr quotConst
    quot_tr_type_tac
  · change quotConst.type.WF env quotConst.uvars []
    exact VConstant.type_wf hquotWF

private theorem quotMkTypeExpr_tr {env env' : VEnv} (henv : env.WF)
    (hadd : env.addConst ``Quot quotConst = some env') :
    TrExprS env' [`u] [] quotMkTypeExpr quotMkConst.type := by
  have hquotWF : quotConst.WF env := by
    unfold VConstant.WF quotConst
    refine ⟨_, by type_tac⟩
  have henv' : env'.Ordered := .const henv.ordered hquotWF hadd
  have hquot' := VEnv.addConst_self hadd
  have hmkWF : quotMkConst.WF env' := by
    unfold VConstant.WF quotMkConst
    refine ⟨_, by type_tac⟩
  apply QuotTrTypeExpr.to_trExprS (henv := henv') (hΔ := by trivial)
  · unfold quotMkTypeExpr quotMkConst
    simp only [mkApp2]
    quot_tr_type_tac
  · change quotMkConst.type.WF env' quotMkConst.uvars []
    exact VConstant.type_wf hmkWF

private theorem quotLiftTypeExpr_tr {env env₁ env₂ : VEnv} (henv : env.WF)
    (heq : env.constants ``Eq = some eqConst)
    (hquot : env.addConst ``Quot quotConst = some env₁)
    (hmk : env₁.addConst ``Quot.mk quotMkConst = some env₂) :
    TrExprS env₂ [`u, `v] [] quotLiftTypeExpr quotLiftConst.type := by
  have hquotWF : quotConst.WF env := by
    unfold VConstant.WF quotConst
    refine ⟨_, by type_tac⟩
  have henv₁ : env₁.Ordered := .const henv.ordered hquotWF hquot
  have hquot₁ := VEnv.addConst_self hquot
  have hmkWF : quotMkConst.WF env₁ := by
    unfold VConstant.WF quotMkConst
    refine ⟨_, by type_tac⟩
  have henv₂ : env₂.Ordered := .const henv₁ hmkWF hmk
  have hquot₂ := (VEnv.addConst_le hmk).constants hquot₁
  have heq₂ : env₂.constants ``Eq = some eqConst :=
    (VEnv.addConst_le hmk).constants ((VEnv.addConst_le hquot).constants heq)
  have hliftWF : quotLiftConst.WF env₂ := by
    unfold VConstant.WF quotLiftConst
    refine ⟨_, by type_tac⟩
  apply QuotTrTypeExpr.to_trExprS (henv := henv₂) (hΔ := by trivial)
  · unfold quotLiftTypeExpr quotLiftConst
    simp only [mkApp2, mkApp3]
    quot_tr_type_tac
  · change quotLiftConst.type.WF env₂ quotLiftConst.uvars []
    exact VConstant.type_wf hliftWF

private theorem quotIndTypeExpr_tr {env env₁ env₂ env₃ : VEnv} (henv : env.WF)
    (heq : env.constants ``Eq = some eqConst)
    (hquot : env.addConst ``Quot quotConst = some env₁)
    (hmk : env₁.addConst ``Quot.mk quotMkConst = some env₂)
    (hlift : env₂.addConst ``Quot.lift quotLiftConst = some env₃) :
    TrExprS env₃ [`u] [] quotIndTypeExpr quotIndConst.type := by
  have hquotWF : quotConst.WF env := by
    unfold VConstant.WF quotConst
    refine ⟨_, by type_tac⟩
  have henv₁ : env₁.Ordered := .const henv.ordered hquotWF hquot
  have hquot₁ := VEnv.addConst_self hquot
  have hmkWF : quotMkConst.WF env₁ := by
    unfold VConstant.WF quotMkConst
    refine ⟨_, by type_tac⟩
  have henv₂ : env₂.Ordered := .const henv₁ hmkWF hmk
  have hquot₂ := (VEnv.addConst_le hmk).constants hquot₁
  have hmk₂ := VEnv.addConst_self hmk
  have heq₂ : env₂.constants ``Eq = some eqConst :=
    (VEnv.addConst_le hmk).constants ((VEnv.addConst_le hquot).constants heq)
  have hliftWF : quotLiftConst.WF env₂ := by
    unfold VConstant.WF quotLiftConst
    refine ⟨_, by type_tac⟩
  have henv₃ : env₃.Ordered := .const henv₂ hliftWF hlift
  have hquot₃ := (VEnv.addConst_le hlift).constants hquot₂
  have hmk₃ := (VEnv.addConst_le hlift).constants hmk₂
  have hindWF : quotIndConst.WF env₃ := by
    unfold VConstant.WF quotIndConst
    refine ⟨_, by type_tac⟩
  apply QuotTrTypeExpr.to_trExprS (henv := henv₃) (hΔ := by trivial)
  · unfold quotIndTypeExpr quotIndConst
    simp only [mkApp2, mkApp3]
    quot_tr_type_tac
  · change quotIndConst.type.WF env₃ quotIndConst.uvars []
    exact VConstant.type_wf hindWF

/-! ## Pointwise quotient transaction -/

private theorem VEnv.exists_addConst_of_none
    {env : VEnv} {name : Name} {ci : VConstant}
    (h : env.constants name = none) : ∃ env', env.addConst name ci = some env' := by
  unfold VEnv.addConst
  rw [h]
  simp

/-- Replay the four host quotient metadata insertions as one Theory
`AddQuot` transaction. -/
private theorem TrEnv.exists_addQuot
    (htr : TrEnv safety env venv)
    (hready : venv.QuotReady)
    (hquot : env.find? ``Quot = none)
    (hmk : env.find? ``Quot.mk = none)
    (hlift : env.find? ``Quot.lift = none)
    (hind : env.find? ``Quot.ind = none) :
    ∃ venv', AddQuot env.constants
      ((((env.constants.insert ``Quot quotTypeInfo).insert ``Quot.mk quotMkInfo).insert
        ``Quot.lift quotLiftInfo).insert ``Quot.ind quotIndInfo)
      venv venv' := by
  have hqNone := htr.constants_eq_none hquot
  obtain ⟨venv₁, hqAdd⟩ := VEnv.exists_addConst_of_none
    (ci := quotConst) hqNone
  have hmkNone : venv₁.constants ``Quot.mk = none := by
    rw [VEnv.addConst_other hqAdd (by decide)]
    exact htr.constants_eq_none hmk
  obtain ⟨venv₂, hmkAdd⟩ := VEnv.exists_addConst_of_none
    (ci := quotMkConst) hmkNone
  have hliftNone : venv₂.constants ``Quot.lift = none := by
    rw [VEnv.addConst_other hmkAdd (by decide),
      VEnv.addConst_other hqAdd (by decide)]
    exact htr.constants_eq_none hlift
  obtain ⟨venv₃, hliftAdd⟩ := VEnv.exists_addConst_of_none
    (ci := quotLiftConst) hliftNone
  have hindNone : venv₃.constants ``Quot.ind = none := by
    rw [VEnv.addConst_other hliftAdd (by decide),
      VEnv.addConst_other hmkAdd (by decide),
      VEnv.addConst_other hqAdd (by decide)]
    exact htr.constants_eq_none hind
  obtain ⟨venv₄, hindAdd⟩ := VEnv.exists_addConst_of_none
    (ci := quotIndConst) hindNone
  have mapWF := htr.map_wf
  have hquotMap : env.constants.find? ``Quot = none := by
    rw [← mapWF.find?'_eq_find?]
    exact hquot
  have hmkMap₀ : env.constants.find? ``Quot.mk = none := by
    rw [← mapWF.find?'_eq_find?]
    exact hmk
  have hliftMap₀ : env.constants.find? ``Quot.lift = none := by
    rw [← mapWF.find?'_eq_find?]
    exact hlift
  have hindMap₀ : env.constants.find? ``Quot.ind = none := by
    rw [← mapWF.find?'_eq_find?]
    exact hind
  have mapWF₁ := mapWF.insert ``Quot quotTypeInfo hquotMap
  have hmkMap : (env.constants.insert ``Quot quotTypeInfo).find? ``Quot.mk = none := by
    rw [mapWF.find?_insert]
    simp [hmkMap₀]
  have mapWF₂ := mapWF₁.insert ``Quot.mk quotMkInfo hmkMap
  have hliftMap : ((env.constants.insert ``Quot quotTypeInfo).insert
      ``Quot.mk quotMkInfo).find? ``Quot.lift = none := by
    rw [mapWF₁.find?_insert, mapWF.find?_insert]
    simp [hliftMap₀]
  have mapWF₃ := mapWF₂.insert ``Quot.lift quotLiftInfo hliftMap
  have hindMap : (((env.constants.insert ``Quot quotTypeInfo).insert
      ``Quot.mk quotMkInfo).insert ``Quot.lift quotLiftInfo).find?
      ``Quot.ind = none := by
    rw [mapWF₂.find?_insert, mapWF₁.find?_insert, mapWF.find?_insert]
    simp [hindMap₀]
  refine ⟨venv₄.addDefEq quotDefEq,
    [`u], quotTypeExpr, venv₁, ?_, hquotMap, hqAdd,
    [`u], quotMkTypeExpr, venv₂, ?_, hmkMap, hmkAdd,
    [`u, `v], quotLiftTypeExpr, venv₃, ?_, hliftMap, hliftAdd,
    [`u], quotIndTypeExpr, venv₄, ?_, hindMap, hindAdd, rfl, rfl⟩
  · exact ⟨DefinitionSafety.le_rfl, rfl, quotTypeExpr_tr htr.wf⟩
  · exact ⟨DefinitionSafety.le_rfl, rfl, quotMkTypeExpr_tr htr.wf hqAdd⟩
  · exact ⟨DefinitionSafety.le_rfl, rfl,
      quotLiftTypeExpr_tr htr.wf hready hqAdd hmkAdd⟩
  · exact ⟨DefinitionSafety.le_rfl, rfl,
      quotIndTypeExpr_tr htr.wf hready hqAdd hmkAdd hliftAdd⟩

private theorem AddQuot.hasPrimitives
    (H : AddQuot C₁ C₂ env₁ env₂) (hp : env₁.HasPrimitives) :
    env₂.HasPrimitives := by
  obtain ⟨_, _, envA, _, _, haddA,
    _, _, envB, _, _, haddB,
    _, _, envC, _, _, haddC,
    _, _, envD, _, _, haddD, _, rfl⟩ := H
  exact ((((hp.addConst_of_not_primitive (by native_decide) haddA)
    |>.addConst_of_not_primitive (by native_decide) haddB)
    |>.addConst_of_not_primitive (by native_decide) haddC)
    |>.addConst_of_not_primitive (by native_decide) haddD).addDefEq

private theorem AddQuot.mono
    (hle : env₁ ≤ env₂)
    (H₁ : AddQuot C₁ C₁' env₁ env₁')
    (H₂ : AddQuot C₂ C₂' env₂ env₂') : env₁' ≤ env₂' := by
  obtain ⟨_, _, env1A, _, _, hadd1A,
    _, _, env1B, _, _, hadd1B,
    _, _, env1C, _, _, hadd1C,
    _, _, env1D, _, _, hadd1D, _, rfl⟩ := H₁
  obtain ⟨_, _, env2A, _, _, hadd2A,
    _, _, env2B, _, _, hadd2B,
    _, _, env2C, _, _, hadd2C,
    _, _, env2D, _, _, hadd2D, _, rfl⟩ := H₂
  apply VEnv.addDefEq_mono
  exact VEnv.addConst_mono
    (VEnv.addConst_mono
      (VEnv.addConst_mono
        (VEnv.addConst_mono hle hadd1A hadd2A)
        hadd1B hadd2B)
      hadd1C hadd2C)
    hadd1D hadd2D

/-! ## Readiness across the quotient-initialized flag -/

private noncomputable def ProjectionArtifact.markQuotInit
    (self : ProjectionArtifact env name info venv) :
    ProjectionArtifact (markQuotInit env) name info venv where
  view := self.view
  name_eq := self.name_eq
  viewWF := self.viewWF
  constructorInfo := self.constructorInfo
  constructor_find := self.constructor_find
  constructor_numParams_eq := self.constructor_numParams_eq
  constructor_numFields_eq := self.constructor_numFields_eq
  levelParams_length := self.levelParams_length
  numParams_eq := self.numParams_eq
  numIndices_eq := self.numIndices_eq
  ctors_eq := self.ctors_eq
  rawResult_sort := self.rawResult_sort
  programsWF := self.programsWF
  programsWF_mono := self.programsWF_mono

private theorem ProjectionReady.markQuotInit (self : ProjectionReady env venv) :
    ProjectionReady (markQuotInit env) venv where
  infer name info hfind hready := by
    obtain ⟨artifact⟩ := self.infer name info hfind hready
    exact ⟨artifact.markQuotInit⟩
  constructorNumParams view info hview hfields hfind :=
    self.constructorNumParams view info hview hfields hfind
  constructorNumParams_mono hle view info hview hfields hfind :=
    self.constructorNumParams_mono hle view info hview hfields hfind

private noncomputable def StructureEtaArtifact.markQuotInit
    (self : StructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    StructureEtaArtifact (markQuotInit env) familyName familyInfo
      constructorName constructorInfo venv where
  projection := self.projection.markQuotInit
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  etaOrdered := self.etaOrdered
  etaRegistered := self.etaRegistered

private theorem StructureEtaReady.markQuotInit (self : StructureEtaReady env venv) :
    StructureEtaReady (markQuotInit env) venv where
  resolve familyName familyInfo constructorName constructorInfo
      hfamily hconstructor hnonrec := by
    obtain ⟨artifact⟩ := self.resolve familyName familyInfo constructorName constructorInfo
      hfamily hconstructor hnonrec
    exact ⟨artifact.markQuotInit⟩

/-! ## Safety-indexed packaging -/

private theorem VEnvs.WF.addQuot
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (hquotInit : env.quotInit = false)
    (hready : ∀ safety, (ves.venv safety).QuotReady)
    (hquot : env.find? ``Quot = none)
    (hmk : env.find? ``Quot.mk = none)
    (hlift : env.find? ``Quot.lift = none)
    (hind : env.find? ``Quot.ind = none) :
    let env₁ := env.add quotTypeInfo
    let env₂ := env₁.add quotMkInfo
    let env₃ := env₂.add quotLiftInfo
    let env₄ := env₃.add quotIndInfo
    ∃ ves' : VEnvs, ves'.WF (markQuotInit env₄) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  dsimp only
  let env₁ := env.add quotTypeInfo
  let env₂ := env₁.add quotMkInfo
  let env₃ := env₂.add quotLiftInfo
  let env₄ := env₃.add quotIndInfo
  have htx (safety) : ∃ venv', AddQuot env.constants env₄.constants
      (ves.venv safety) venv' := by
    change ∃ venv', AddQuot env.constants
      ((((env.constants.insert ``Quot quotTypeInfo).insert ``Quot.mk quotMkInfo).insert
        ``Quot.lift quotLiftInfo).insert ``Quot.ind quotIndInfo)
      (ves.venv safety) venv'
    exact (wf.tr (safety := safety)).exists_addQuot (hready safety)
      hquot hmk hlift hind
  obtain ⟨ves', hadd⟩ := VEnvs.axiom_of_choice htx
  have trNew (safety) : TrEnv safety (markQuotInit env₄) (ves'.venv safety) := by
    change TrEnv' safety env₄.constants true (ves'.venv safety)
    have hold := wf.tr (safety := safety)
    change TrEnv' safety env.constants env.quotInit (ves.venv safety) at hold
    rw [hquotInit] at hold
    exact .quot (hready safety) (hadd safety) hold
  have leNew (safety) : ves.venv safety ≤ ves'.venv safety :=
    (hadd safety).le
  have mapWF := (wf.tr (safety := .safe)).map_wf
  have hquotMap : env.constants.find? ``Quot = none := by
    rw [← mapWF.find?'_eq_find?]
    exact hquot
  have mapWF₁ : env₁.constants.WF := by
    change (env.constants.insert ``Quot quotTypeInfo).WF
    exact mapWF.insert _ _ hquotMap
  have hmk₁ : env₁.find? ``Quot.mk = none := by
    rw [Environment.find?_add_eq mapWF quotTypeInfo hquot]
    rw [if_neg (by native_decide)]
    exact hmk
  have hmkMap : env₁.constants.find? ``Quot.mk = none := by
    rw [← mapWF₁.find?'_eq_find?]
    exact hmk₁
  have mapWF₂ : env₂.constants.WF := by
    change (env₁.constants.insert ``Quot.mk quotMkInfo).WF
    exact mapWF₁.insert _ _ hmkMap
  have hlift₂ : env₂.find? ``Quot.lift = none := by
    rw [Environment.find?_add_eq mapWF₁ quotMkInfo hmk₁,
      Environment.find?_add_eq mapWF quotTypeInfo hquot]
    have hne₁ : quotMkInfo.name ≠ ``Quot.lift := by native_decide
    have hne₂ : quotTypeInfo.name ≠ ``Quot.lift := by native_decide
    simp only [if_neg hne₁, if_neg hne₂]
    exact hlift
  have hliftMap : env₂.constants.find? ``Quot.lift = none := by
    rw [← mapWF₂.find?'_eq_find?]
    exact hlift₂
  have mapWF₃ : env₃.constants.WF := by
    change (env₂.constants.insert ``Quot.lift quotLiftInfo).WF
    exact mapWF₂.insert _ _ hliftMap
  have hind₃ : env₃.find? ``Quot.ind = none := by
    rw [Environment.find?_add_eq mapWF₂ quotLiftInfo hlift₂,
      Environment.find?_add_eq mapWF₁ quotMkInfo hmk₁,
      Environment.find?_add_eq mapWF quotTypeInfo hquot]
    have hne₁ : quotLiftInfo.name ≠ ``Quot.ind := by native_decide
    have hne₂ : quotMkInfo.name ≠ ``Quot.ind := by native_decide
    have hne₃ : quotTypeInfo.name ≠ ``Quot.ind := by native_decide
    simp only [if_neg hne₁, if_neg hne₂, if_neg hne₃]
    exact hind
  have safePrimitives₁ {n : Name} {ci : ConstantInfo}
      (hfind : env₁.find? n = some ci) (hp : Environment.primitives.contains n) :
      ci.safety = .safe ∧ ci.levelParams = [] :=
    safePrimitives_add' mapWF wf.safePrimitives quotTypeInfo hquot
      (by native_decide) hfind hp
  have safePrimitives₂ {n : Name} {ci : ConstantInfo}
      (hfind : env₂.find? n = some ci) (hp : Environment.primitives.contains n) :
      ci.safety = .safe ∧ ci.levelParams = [] :=
    safePrimitives_add' mapWF₁ safePrimitives₁ quotMkInfo hmk₁
      (by native_decide) hfind hp
  have safePrimitives₃ {n : Name} {ci : ConstantInfo}
      (hfind : env₃.find? n = some ci) (hp : Environment.primitives.contains n) :
      ci.safety = .safe ∧ ci.levelParams = [] :=
    safePrimitives_add' mapWF₂ safePrimitives₂ quotLiftInfo hlift₂
      (by native_decide) hfind hp
  have safePrimitives₄ {n : Name} {ci : ConstantInfo}
      (hfind : env₄.find? n = some ci) (hp : Environment.primitives.contains n) :
      ci.safety = .safe ∧ ci.levelParams = [] :=
    safePrimitives_add' mapWF₃ safePrimitives₃ quotIndInfo hind₃
      (by native_decide) hfind hp
  have readiness (safety) :
      ProjectionReady (markQuotInit env₄) (ves'.venv safety) ∧
      StructureEtaReady (markQuotInit env₄) (ves'.venv safety) := by
    have r₁ := Readiness.add (ci := quotTypeInfo) mapWF hquot
      (by simp [quotTypeInfo, Lean.ConstantInfo.ReadinessTransparent])
      (leNew safety) (trNew safety).wf
      (wf.projectionReady (safety := safety))
      (wf.structureEtaReady (safety := safety))
    have r₂ := Readiness.add (ci := quotMkInfo) mapWF₁ hmk₁
      (by simp [quotMkInfo, Lean.ConstantInfo.ReadinessTransparent])
      VEnv.LE.rfl (trNew safety).wf r₁.1 r₁.2
    have r₃ := Readiness.add (ci := quotLiftInfo) mapWF₂ hlift₂
      (by simp [quotLiftInfo, Lean.ConstantInfo.ReadinessTransparent])
      VEnv.LE.rfl (trNew safety).wf r₂.1 r₂.2
    have r₄ := Readiness.add (ci := quotIndInfo) mapWF₃ hind₃
      (by simp [quotIndInfo, Lean.ConstantInfo.ReadinessTransparent])
      VEnv.LE.rfl (trNew safety).wf r₃.1 r₃.2
    exact ⟨r₄.1.markQuotInit, r₄.2.markQuotInit⟩
  refine ⟨ves', {
    tr {safety} := trNew safety
    hasPrimitives {safety} := (hadd safety).hasPrimitives wf.hasPrimitives
    safePrimitives := ?_
    mono {safety safety'} hle := (hadd safety').mono (wf.mono hle) (hadd safety)
    projectionReady {safety} := (readiness safety).1
    structureEtaReady {safety} := (readiness safety).2 }, leNew⟩
  intro name ci hfind hp
  exact safePrimitives₄ hfind hp

/-- Checked quotient initialization preserves all safety-indexed models. -/
theorem addQuot.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) :
    (Environment.addQuot env).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold Environment.addQuot
  split
  · exact .pure ⟨ves, wf, fun _ => VEnv.LE.rfl⟩
  · rename_i hquotInit
    have hquotInit' : env.quotInit = false := by
      cases h : env.quotInit <;> simp_all
    refine (checkEqType.quotReady wf).bind fun _ hready => ?_
    have mapWF := (wf.tr (safety := .safe)).map_wf
    refine (checkName.WF mapWF ``Quot false).bind fun _ hquot => ?_
    refine (checkName.WF mapWF ``Quot.mk false).bind fun _ hmk => ?_
    refine (checkName.WF mapWF ``Quot.lift false).bind fun _ hlift => ?_
    refine (checkName.WF mapWF ``Quot.ind false).bind fun _ hind => ?_
    exact .pure (wf.addQuot hquotInit' hready hquot.1 hmk.1 hlift.1 hind.1)

end Lean4Lean
