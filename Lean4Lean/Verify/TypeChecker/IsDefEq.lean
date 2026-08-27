/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.TypeChecker.InferType
import Lean4Lean.Verify.EquivManager

open Lean4Lean

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

theorem isDefEqLambda.WF {c : VContext} {s : VState}
    {m} [mwf : c.MLCWF m]
    {fvs : List Expr} (hsubst : subst.toList.reverse = fvs)
    (hfvs : ∀ x ∈ fvs, x.looseBVarRange' = 0)
    (he₁ : (c.withMLC m).TrExprS (e₁.instantiateList fvs) ei₁')
    (he₂ : (c.withMLC m).TrExprS (e₂.instantiateList fvs) ei₂') :
    RecM.WF (c.withMLC m) s (isDefEqLambda e₁ e₂ subst) fun b _ =>
      b → (c.withMLC m).IsDefEqU ei₁' ei₂' := by
  unfold isDefEqLambda; let c' := c.withMLC m
  have hrev (e : Expr) : e.instantiateRev subst = e.instantiateList fvs := by
    rw [Expr.instantiateRev_eq,
      Expr.instantiate_eq _ _ (Or.inr (by simpa [← hsubst] using hfvs))]
    simp [hsubst]
  split <;>
    [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂;
      (simp [hrev]; exact isDefEq.WF he₁ he₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  simp at he₁ he₂
  let .lam (ty' := t₁') (body' := b₁') ⟨_, a1⟩ a2 a3 := he₁
  let .lam (ty' := t₂') (body' := b₂') b1 b2 b3 := he₂
  suffices ∀ {x s}
      (_ : match x with
        | none => d₁ == d₂
        | some x => x = d₂.instantiateList fvs),
      c'.IsDefEqU t₁' t₂' →
      (F x).WF c' s fun b _ => b → c'.IsDefEqU (t₁'.lam b₁') (t₂'.lam b₂') by
    split <;> rename_i h
    · refine .pureBind <| this ‹_› ?_
      exact a2.eqv (Expr.instantiateList_eqv h) |>.uniq c'.Ewf (.refl c'.Ewf c'.Δwf) b2
    simp [hrev]
    refine (isDefEq.WF a2 b2).bind fun b _ _ h1 => ?_
    split <;> [exact .pure nofun; rename_i h]
    simp at h; exact this rfl (h1 h)
  intros x s hx tt
  have tt' := tt.of_l c'.Ewf c'.Δwf a1
  have ⟨b₁'', a3', eq⟩ := a3.defeqDFC' c'.Ewf <| .cons (.refl c'.Ewf c'.Δwf) (by nofun) (.vlam tt')
  unfold F
  extract_lets d₂'
  have : d₂' = d₂.instantiateList fvs := by
    split at hx <;> [simp [d₂', hrev]; exact hx]
  clear_value d₂'
  subst this
  refine .withLocalDecl b2 b1 .rfl fun v mwf' _ _ _ => ?_
  have b3' := b3.inst_fvar c.Ewf mwf'.1.tr.wf
  have a3'' := a3'.inst_fvar c.Ewf mwf'.1.tr.wf
  rw [Expr.instantiateList_instantiate1_comm (by rfl), ← Expr.instantiateList] at a3'' b3'
  refine isDefEqLambda.WF (mwf := mwf') (fvs := .fvar v :: fvs)
    (by simp [hsubst]) (List.forall_mem_cons.2 ⟨rfl, hfvs⟩) a3'' b3'
    |>.mono fun _ _ _ h hb => ?_
  have ⟨_, bb⟩ := eq.symm.trans c'.Ewf mwf'.1.tr.wf.toCtx (h hb)
  exact ⟨_, .symm <| .lamDF tt'.symm <| bb.symm⟩

theorem isDefEqForall.WF {c : VContext} {s : VState}
    {m} [mwf : c.MLCWF m]
    {fvs : List Expr} (hsubst : subst.toList.reverse = fvs)
    (hfvs : ∀ x ∈ fvs, x.looseBVarRange' = 0)
    (he₁ : (c.withMLC m).TrExprS (e₁.instantiateList fvs) ei₁')
    (he₂ : (c.withMLC m).TrExprS (e₂.instantiateList fvs) ei₂') :
    RecM.WF (c.withMLC m) s (isDefEqForall e₁ e₂ subst) fun b _ =>
      b → (c.withMLC m).IsDefEqU ei₁' ei₂' := by
  unfold isDefEqForall; let c' := c.withMLC m
  have hrev (e : Expr) : e.instantiateRev subst = e.instantiateList fvs := by
    rw [Expr.instantiateRev_eq,
      Expr.instantiate_eq _ _ (Or.inr (by simpa [← hsubst] using hfvs))]
    simp [hsubst]
  split <;>
    [rename_i n₁ d₁ b₁ bi₁ n₂ d₂ b₂ bi₂;
      (simp [hrev]; exact isDefEq.WF he₁ he₂)]
  extract_lets F di₁ di₂; unfold di₁ di₂
  simp at he₁ he₂
  let .forallE (ty' := t₁') (body' := b₁') ⟨_, a1⟩ _ a2 a3 := he₁
  let .forallE (ty' := t₂') (body' := b₂') b1 ⟨_, bT⟩ b2 b3 := he₂
  suffices ∀ {x s}
      (_ : match x with
        | none => d₁ == d₂
        | some x => x = d₂.instantiateList fvs),
      c'.IsDefEqU t₁' t₂' →
      (F x).WF c' s fun b _ => b → c'.IsDefEqU (t₁'.forallE b₁') (t₂'.forallE b₂') by
    split <;> rename_i h
    · refine .pureBind <| this ‹_› ?_
      exact a2.eqv (Expr.instantiateList_eqv h) |>.uniq c'.Ewf (.refl c'.Ewf c'.Δwf) b2
    simp [hrev]
    refine (isDefEq.WF a2 b2).bind fun b _ _ h1 => ?_
    split <;> [exact .pure nofun; rename_i h]
    simp at h; exact this rfl (h1 h)
  intros x s hx tt
  have tt' := tt.of_l c'.Ewf c'.Δwf a1
  have ⟨b₁'', a3', eq⟩ := a3.defeqDFC' c'.Ewf <| .cons (.refl c'.Ewf c'.Δwf) (by nofun) (.vlam tt')
  unfold F
  extract_lets d₂'
  have : d₂' = d₂.instantiateList fvs := by
    split at hx <;> [simp [d₂', hrev]; exact hx]
  clear_value d₂'
  subst this
  refine .withLocalDecl b2 b1 .rfl fun v mwf' _ _ _ => ?_
  have b3' := b3.inst_fvar c.Ewf mwf'.1.tr.wf
  have a3'' := a3'.inst_fvar c.Ewf mwf'.1.tr.wf
  rw [Expr.instantiateList_instantiate1_comm (by rfl), ← Expr.instantiateList] at a3'' b3'
  refine isDefEqForall.WF (mwf := mwf') (fvs := .fvar v :: fvs)
    (by simp [hsubst]) (List.forall_mem_cons.2 ⟨rfl, hfvs⟩) a3'' b3'
    |>.mono fun _ _ _ h hb => ?_
  have bb := eq.symm.trans c'.Ewf mwf'.1.tr.wf.toCtx (h hb)
    |>.of_r c'.Ewf mwf'.1.tr.wf.toCtx bT
  exact ⟨_, .symm <| .forallEDF tt'.symm <| bb.symm⟩

theorem quickIsDefEq.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (quickIsDefEq e₁ e₂ useHash) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold quickIsDefEq
  refine .bind (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h => ?_
  · intro _ mwf wf _ s₁ eq
    simp [modifyGet, MonadStateOf.modifyGet, monadLift, MonadLift.monadLift, StateT.modifyGet,
      pure, Except.pure] at eq
    split at eq; rename_i b _ b' m hm
    change let s' := _; (_, s') = _ at eq; extract_lets s' at eq
    injection eq; subst b' s₁
    let ⟨_, _, a1, a2, ewf, a4⟩ := wf.ectx
    have ⟨ewf, _, h1⟩ := EquivManager.isEquiv.WF ewf hm
    refine let vs' := { s with toState := s' }; ⟨vs', rfl, .rfl, { wf with ectx := ?_ }, ?_⟩
    · exact ⟨_, _, a1, a2, ewf, a4⟩
    · intro h; apply (VEnv.IsDefEqU.weak'_iff c.Ewf a1 a2.toCtx).1
      exact (h1 h).uniq c.Ewf (a2.bvars_eq.trans c.mlctx.noBV)
        a1 (he₁.weakFV' c.Ewf a2 a1) (he₂.weakFV' c.Ewf a2 a1)
  split <;> [exact .pure fun _ => h ‹_›; split]
  · exact .toLBoolM <| c.withMLC_self ▸
      isDefEqLambda.WF (subst := #[]) (fvs := []) rfl nofun
        (c.withMLC_self ▸ he₁) (c.withMLC_self ▸ he₂)
  · exact .toLBoolM <| c.withMLC_self ▸
      isDefEqForall.WF (subst := #[]) (fvs := []) rfl nofun
        (c.withMLC_self ▸ he₁) (c.withMLC_self ▸ he₂)
  · have .sort hu := he₁; have .sort hv := he₂
    refine .pure fun h => ⟨_, .sortDF (.of_ofLevel hu) (.of_ofLevel hv) ?_⟩
    exact Level.isEquiv'_wf (toLBool_true.1 h) hu hv
  · let .mdata he₁ := he₁; let .mdata he₂ := he₂
    exact .toLBoolM <| isDefEq.WF he₁ he₂
  · cases he₁
  · rename_i a1 a2 _; refine .pure fun h => ?_
    simp at h; subst h; exact he₁.uniq c.Ewf (.refl c.Ewf c.Δwf) he₂
  · exact .pure nofun

theorem isDefEqArgs.WF {c : VContext} {s : VState}
    (H : ∃ e₁', c.TrExprS e₁.getAppFn e₁' ∧ ∃ e₂', c.TrExprS e₂.getAppFn e₂' ∧ c.IsDefEqU e₁' e₂')
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqArgs e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqArgs; split <;> (unfold Expr.getAppFn at H)
  · let .app a1 a2 a3 a4 := he₁
    let .app b1 b2 b3 b4 := he₂
    refine (isDefEq.WF a4 b4).bind fun _ _ _ h2 => ?_; extract_lets
    split <;> [exact .pure nofun; rename_i hb2]
    refine (isDefEqArgs.WF H a3 b3).mono fun _ _ _ h1 hb1 => ?_
    simp at hb2
    exact ⟨_, .appDF ((h1 hb1).of_l c.Ewf c.Δwf a1) ((h2 hb2).of_l c.Ewf c.Δwf a2)⟩
  · exact .pure nofun
  · exact .pure nofun
  · refine .pure fun _ => ?_
    simp [*] at H; let ⟨_, h1, _, h2, h3⟩ := H
    have a1 := he₁.uniq c.Ewf (.refl c.Ewf c.Δwf) h1
    have a2 := he₂.uniq c.Ewf (.refl c.Ewf c.Δwf) h2
    exact a1.trans c.Ewf c.Δwf h3 |>.trans c.Ewf c.Δwf a2.symm

theorem tryEtaExpansionCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaExpansionCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold tryEtaExpansionCore; split <;> [skip; exact .pure nofun]
  refine (inferType.WF he₂).bind fun _ _ _ ⟨ty₁, a1, a2, a3, a4⟩ => ?_
  refine (whnf.WF a3).bind fun _ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [skip; exact .pure nofun]
  let .forallE (ty' := ty') c1 c2 c3 c4 := b2
  replace a4 := a4.defeqU_r c.Ewf c.Δwf b3.symm
  -- have := b2.uniq c.Ewf (.refl c.Ewf c.Δwf) (.forallE c1 c2 c3 c4)
  refine (isDefEq.WF he₁ (.lam c1 c3 (.app (a4.weak c.Ewf) (.bvar .zero) (
    Expr.liftLooseBVars_eq_self (c.mlctx.noBV ▸ a2.closed).looseBVarRange_le ▸
      a2.weakBV c.Ewf (.skip (.vlam ty') .refl)) (.bvar rfl)))).mono fun _ _ _ h hb => ?_
  exact (h hb).trans c.Ewf c.Δwf ⟨_, .eta a4⟩

theorem tryEtaExpansion.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaExpansion e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  simp [tryEtaExpansion, orM, toBool]
  refine (tryEtaExpansionCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h rfl; skip]
  exact (tryEtaExpansionCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

private theorem AppStack.toSpineWF_of_isType {c : VContext}
    (H : AppStack c.venv c.lparams c.vlctx f f' args)
    (hf : c.HasType f' (VExpr.forallN As (.sort resultLevel)))
    (hfull : c.TrExprS (f.mkAppList args) full')
    (hfullType : c.venv.IsType c.lparams.length c.vlctx.toCtx full') :
    ∃ args', args.Forall₂ (c.TrExprS · ·) args' ∧
      c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (VExpr.forallN As (.sort resultLevel)) args' (.sort resultLevel) ∧
      c.TrExprS (f.mkAppList args) (VExpr.appN f' args') := by
  induction args generalizing f f' As full' with
  | nil =>
    let .head hhead := H
    cases As with
    | nil =>
      refine ⟨[], .nil, .nil, ?_⟩
      change c.TrExprS f f'
      exact hhead
    | cons A As =>
      obtain ⟨sortLevel, hfullSort⟩ := hfullType
      have hheadEq := hhead.uniq c.Ewf (.refl c.Ewf c.Δwf) hfull
      have hheadSort := hfullSort.defeqU_l c.Ewf c.Δwf hheadEq.symm
      have htypes := hf.uniqU c.Ewf c.Δwf hheadSort
      exact False.elim <|
        VEnv.IsDefEqU.sort_forallE_inv c.Ewf c.Δwf htypes.symm
  | cons arg args ih =>
    let .app hfun harg hhead hargTr Hrest := H
    cases As with
    | nil =>
      have htypes := hf.uniqU c.Ewf c.Δwf hfun
      exact False.elim <|
        VEnv.IsDefEqU.sort_forallE_inv c.Ewf c.Δwf htypes
    | cons A As =>
      have htypes := hf.uniqU c.Ewf c.Δwf hfun
      obtain ⟨⟨_, hdomain⟩, _, _hcodomain⟩ :=
        htypes.forallE_inv c.Ewf c.Δwf
      have hargA := harg.defeqU_r c.Ewf c.Δwf ⟨_, hdomain.symm⟩
      have htailType := hf.app hargA
      rw [VExpr.instN_forallN] at htailType
      obtain ⟨args', hargs, hspine, htailFull⟩ :=
        ih Hrest htailType (by simpa [Expr.mkAppList] using hfull)
          hfullType
      refine ⟨_ :: args', .cons hargTr hargs, .cons hargA ?_, ?_⟩
      · rw [VExpr.instN_forallN]
        rw [Nat.zero_add]
        rw [(show (VExpr.sort resultLevel).ClosedN 0 by trivial).instN_eq
          (e2 := _) (Nat.zero_le As.length)]
        exact hspine
      · simpa [Expr.mkAppList, VExpr.appN] using htailFull

private theorem forall₂_of_getElem? {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β},
      xs.length = ys.length →
      (∀ (i : Nat) (x : α) (y : β),
        xs[i]? = some x → ys[i]? = some y → R x y) →
      List.Forall₂ R xs ys
  | [], [], _, _ => .nil
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, h => by
      refine .cons (h 0 x y (by simp) (by simp)) ?_
      apply forall₂_of_getElem? (Nat.succ.inj hlen)
      intro i x' y' hx hy
      exact h (i + 1) x' y' (by simpa using hx) (by simpa using hy)


theorem tryEtaStructCore.WF_of_structureEta {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold tryEtaStructCore
  split <;> [skip; exact .pure nofun]
  refine .getEnv ?_
  refine (M.WF.liftExcept envGet.WF).lift.bind fun _ci _ _ hfind => ?_
  split <;> [skip; exact .pure nofun]
  extract_lets F1
  split <;> [skip; exact .pure nofun]
  rename_i hostHead ctorName ctorLevels hhead state hstate hostInfo ctorInfo
    hargs
  split <;> [skip; exact .pure nofun]
  rename_i hnonrec
  refine (inferType.WF he₁).bind fun _ _ _
    ⟨ty₁', _aBelow, _aTerm, aType, aTyped⟩ => ?_
  refine (inferType.WF he₂).bind fun _ _ _
    ⟨ty₂', _bBelow, _bTerm, bType, bTyped⟩ => ?_
  refine (isDefEq.WF aType bType).bind fun _ _ _ htypes => ?_
  split <;> [skip; exact .pure nofun]
  rename_i htypesTrue
  unfold F1
  obtain ⟨familyInfo, hfamily, ⟨artifact⟩⟩ :=
    c.structureEtaReady.resolveConstructor hfind hnonrec
  cases artifact with
  | ordinary artifact =>
    have hprograms : artifact.projection.view.ProgramsWF c.venv :=
      artifact.projection.viewWF.toProgramsWF_of_large
        c.Ewf.conversionRegular artifact.large
    have ⟨head', hstack⟩ := AppStack.build <|
      e₂.mkAppList_getAppArgsList ▸ he₂
    have hheadTr := hstack.tr
    rw [hhead] at hheadTr
    let .const (us' := levels) hconst hlevelsMap hlevelsHostLength := hheadTr
    have hviewConstructor := artifact.projection.viewWF.constructor_registered
    rw [artifact.constructor_name_eq] at hviewConstructor
    rw [hviewConstructor] at hconst
    cases hconst
    have hlevelsWF : ∀ level ∈ levels,
        level.WF c.lparams.length :=
      VLevel.WF.of_mapM_ofLevel hlevelsMap
    have hrawCtorUvars : artifact.projection.view.constructor.raw.uvars =
        artifact.projection.view.uvars :=
      artifact.projection.view.constructor_uvars_eq
    have hlevelsLength : levels.length = artifact.projection.view.uvars :=
      (List.mapM_eq_some.1 hlevelsMap).length_eq.symm.trans <|
        hlevelsHostLength.trans hrawCtorUvars
    have hctorHead : c.HasType (.const ctorName levels)
        (artifact.projection.view.constructor.raw.type.instL levels) :=
      VEnv.HasType.const hviewConstructor hlevelsWF
        (hlevelsLength.trans hrawCtorUvars.symm)
    let ctorBinders :=
      (artifact.projection.view.constructor.declaredBinders
        artifact.projection.view.nparams).map (VExpr.instL levels)
    let ctorResult :=
      (artifact.projection.view.constructor.rawResult
        artifact.projection.view.nparams).instL levels
    have hctorHeadShape : c.HasType (.const ctorName levels)
        (VExpr.forallN ctorBinders ctorResult) := by
      rw [artifact.projection.view.constructor.rawType_eq] at hctorHead
      simpa [ctorBinders, ctorResult, VProjectionView.nparams,
        VProjectionView.source, VExpr.instL_forallN] using hctorHead
    have hhostArgsLength : e₂.getAppArgsList.length =
        ctorInfo.numParams + ctorInfo.numFields := by
      simpa [Expr.getAppNumArgs_eq, ← Expr.getAppArgsList_reverse] using hargs
    have hnumParams : ctorInfo.numParams = artifact.projection.view.nparams := by
      exact (congrArg ConstructorVal.numParams
        artifact.constructor_info_eq).symm.trans
          artifact.projection.constructor_numParams_eq
    have hnumFields : ctorInfo.numFields = artifact.projection.view.fields.length := by
      exact (congrArg ConstructorVal.numFields
        artifact.constructor_info_eq).symm.trans
          artifact.projection.constructor_numFields_eq
    have hctorBindersLength : ctorBinders.length =
        artifact.projection.view.nparams +
          artifact.projection.view.fields.length := by
      calc
        ctorBinders.length =
            artifact.projection.view.constructorParams.length +
              artifact.projection.view.fields.length := by
          simp only [ctorBinders, List.length_map,
            VInductDecl.NormalizedCtor.declaredBinders, List.length_append,
            VProjectionView.constructorParams, VProjectionView.fields]
        _ = artifact.projection.view.nparams +
            artifact.projection.view.fields.length := by
          rw [artifact.projection.view.constructorParams_length]
    have hhostBinderLength : e₂.getAppArgsList.length = ctorBinders.length := by
      have hhostArity : e₂.getAppArgsList.length =
          artifact.projection.view.nparams +
            artifact.projection.view.fields.length := by
        simpa [hnumParams, hnumFields] using hhostArgsLength
      exact hhostArity.trans hctorBindersLength.symm
    obtain ⟨args', hargsTr, hargsSpine, hfullTr⟩ :=
      AppStack.toSpineWF hstack hctorHeadShape hhostBinderLength
    rw [e₂.mkAppList_getAppArgsList] at hfullTr
    have hargsLength : args'.length = artifact.projection.view.nparams +
        artifact.projection.view.fields.length :=
      hargsTr.length_eq.symm.trans <| by
        simpa [hnumParams, hnumFields] using hhostArgsLength
    let params := args'.take artifact.projection.view.nparams
    let fields := args'.drop artifact.projection.view.nparams
    have hargsSplit : args' = params ++ fields := by
      simp [params, fields]
    have hparamsLength : params.length = artifact.projection.view.nparams := by
      simp [params, hargsLength]
    have hfieldsLength : fields.length = artifact.projection.view.fields.length := by
      simp [fields, hargsLength]
    have hargsSpineSplit := hargsSpine
    rw [hargsSplit] at hargsSpineSplit
    obtain ⟨paramCursor, hparamRaw, hfieldsRaw⟩ :=
      hargsSpineSplit.split
    let ctorTail := VExpr.forallN
      (artifact.projection.view.fields.map (VExpr.instL levels)) ctorResult
    have hparamCtor : c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (VExpr.forallN
          (artifact.projection.view.constructorParams.map
            (VExpr.instL levels)) ctorTail)
        params paramCursor := by
      simpa [ctorBinders, ctorTail,
        VInductDecl.NormalizedCtor.declaredBinders,
        VProjectionView.constructorParams, VProjectionView.fields,
        List.map_append, VExpr.forallN_append] using hparamRaw
    have hparamsSpine :=
      artifact.projection.viewWF.familyParamsSpine_of_constructor
        c.Ewf.ordered levels hlevelsWF hlevelsLength params hparamsLength
        hparamCtor
    obtain ⟨declResultLevel, hdeclResult₀⟩ :=
      artifact.projection.viewWF.constructorDeclaredResult c.Ewf.ordered
    have hdeclResult₁ := hdeclResult₀.instL hlevelsWF
    have hdeclResult : c.venv.IsDefEq c.lparams.length
        ctorBinders.reverse ctorResult
        (artifact.projection.view.constructorTarget.instL levels)
        ((VExpr.sort declResultLevel).instL levels) := by
      simpa [ctorBinders, ctorResult, List.map_reverse] using hdeclResult₁
    have hdeclTel :=
      (artifact.projection.viewWF.constructorDeclared_onTel
        c.Ewf.ordered).instL hlevelsWF
    have hctorOnTel : c.venv.OnTel c.lparams.length [] ctorBinders := by
      simpa [ctorBinders] using hdeclTel
    have hctorCtxClosed : CtxClosed ctorBinders.reverse :=
      VEnv.CtxWF.closed c.Ewf.ordered <| by
        simpa using hctorOnTel.toOnCtx (by trivial)
    have hdeclResultΓ := hdeclResult.weakR c.Ewf.ordered hctorCtxClosed
      c.vlctx.toCtx
    have hargsTelLength : args'.length = ctorBinders.length :=
      hargsTr.length_eq.symm.trans hhostBinderLength
    have hresultEq := hargsSpine.instRev_defeq c.Ewf.ordered
      hargsTelLength hdeclResultΓ
    have htarget :
        (artifact.projection.view.constructorTarget.instL levels).instRev args' =
        artifact.projection.view.structureType levels params := by
      rw [hargsSplit]
      exact artifact.projection.viewWF.constructorTarget_instRev
        c.Ewf.ordered levels hlevelsLength params hparamsLength fields
          hfieldsLength
    rw [htarget] at hresultEq
    have hcanonicalRaw := hargsSpine.hasType_appN hctorHeadShape
    have hcanonical : c.HasType
        ((VExpr.const ctorName levels).appN args')
        (artifact.projection.view.structureType levels params) :=
      hcanonicalRaw.defeqU_r c.Ewf c.Δwf ⟨_, hresultEq⟩
    have hfullEq := hfullTr.uniq c.Ewf (.refl c.Ewf c.Δwf) he₂
    have hbStruct := hcanonical.defeqU_l c.Ewf c.Δwf hfullEq
    have hty₂Struct := bTyped.uniqU c.Ewf c.Δwf hbStruct
    have hty₁Struct := VEnv.IsDefEqU.trans c.Ewf c.Δwf
      (htypes htypesTrue) hty₂Struct
    have haStruct := aTyped.defeqU_r c.Ewf c.Δwf hty₁Struct
    have heta := artifact.eta c.Ewf c.Δwf hlevelsWF hlevelsLength
      hparamsLength ⟨_, hparamsSpine⟩ haStruct
    have hF1Size : F1.size = args'.length := by
      calc
        F1.size = F1.toList.length := by simp
        _ = e₂.getAppArgsList.length := by simp [F1, Expr.getAppArgs_toList]
        _ = args'.length := hargsTr.length_eq
    have hfieldData : ∀ (j : Nat), j < fields.length →
        ∃ code : VStructureView.ProjectionCode,
          (artifact.projection.view.projectionCodes levels params)[j]? =
            some code ∧
          c.TrExprS (.proj ctorInfo.induct j e₁)
            (.app code.projector e₁') ∧
          ∀ (hi : ctorInfo.numParams + j < F1.size),
            c.TrExprS F1[ctorInfo.numParams + j] fields[j] := by
      intro j hj
      have hcodeIdx : j <
          (artifact.projection.view.projectionCodes levels params).length := by
        simpa [hfieldsLength] using hj
      let code := (artifact.projection.view.projectionCodes levels params)[j]
      have hcode :
          (artifact.projection.view.projectionCodes levels params)[j]? =
            some code := List.getElem?_eq_getElem hcodeIdx
      have hprojector := hprograms c.Δwf hlevelsWF
        hlevelsLength hparamsLength ⟨_, hparamsSpine⟩ hcode
      have hprojSem : VProjectionView.TrProj c.venv c.lparams.length
          c.vlctx.toCtx artifact.projection.view levels params j e₁'
          (.app code.projector e₁') := {
        viewWF := artifact.projection.viewWF
        levelsWF := hlevelsWF
        levels_length := hlevelsLength
        params_length := hparamsLength
        paramsSpine := ⟨_, hparamsSpine⟩
        majorType := haStruct
        program := ⟨code, hcode, rfl, hprojector⟩ }
      have hprojTr : c.TrExprS (.proj ctorInfo.induct j e₁)
          (.app code.projector e₁') :=
        .proj he₁ ⟨.ordinary artifact.projection.view, levels, params,
          artifact.projection.name_eq, .ordinary hprojSem⟩
      refine ⟨code, hcode, hprojTr, ?_⟩
      intro hi
      have hselectedList :
          e₂.getAppArgsList[ctorInfo.numParams + j]? =
            some F1[ctorInfo.numParams + j] := by
        rw [← Expr.getAppArgs_toList]
        simp [F1]
      obtain ⟨translated, htranslated, htr⟩ :=
        Lean4Lean.List.Forall₂.getElem?_left hargsTr hselectedList
      have hfieldGet : args'[ctorInfo.numParams + j]? = some fields[j] := by
        rw [hargsSplit, List.getElem?_append_right]
        · simp [hnumParams, hparamsLength]
        · simp [hnumParams, hparamsLength]
      have : translated = fields[j] :=
        Option.some.inj (htranslated.symm.trans hfieldGet)
      subst translated
      exact htr
    rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
    simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
    let FieldEq := fun (j : Nat) => ∃ (field : VExpr)
        (code : VStructureView.ProjectionCode),
      fields[j]? = some field ∧
      (artifact.projection.view.projectionCodes levels params)[j]? = some code ∧
      c.IsDefEqU (.app code.projector e₁') field
    let etaStep (indices : List Nat)
        (hlow : ∀ i, i ∈ indices → ctorInfo.numParams ≤ i)
        (hhigh : ∀ i, i ∈ indices → i < F1.size) :
        (i : Nat) → i ∈ indices → Option Bool × PUnit →
          RecM (ForInStep (Option Bool × PUnit)) :=
      fun i hi r => tryEtaStructFieldStep e₁ ctorInfo.induct
        ctorInfo.numParams F1 i
        ⟨hlow i hi, hhigh i hi, by
          change (i - ctorInfo.numParams) % 1 = 0
          exact Nat.mod_one _⟩ r
    have etaLoopWF : ∀ (all indices : List Nat)
        (hsuffix : ∃ pre, pre ++ indices = all)
        (hlow : ∀ i, i ∈ all → ctorInfo.numParams ≤ i)
        (hhigh : ∀ i, i ∈ all → i < F1.size) {st : VState},
        RecM.WF c st
          (List.forIn'.loop all (etaStep all hlow hhigh) indices
            ⟨none, PUnit.unit⟩ hsuffix)
          fun r _ =>
            (r.1 = none →
              ∀ i, i ∈ indices → FieldEq (i - ctorInfo.numParams)) ∧
            r.1 ≠ some true := by
      intro all indices hsuffix hlow hhigh st
      induction indices generalizing st with
      | nil =>
        simp only [List.forIn'.loop]
        exact .pure (by simp)
      | cons i indices ih =>
        simp only [List.forIn'.loop]
        simp only [etaStep, tryEtaStructFieldStep]
        obtain ⟨pre, hprefix⟩ := hsuffix
        have hiAll : i ∈ all := by
          rw [← hprefix]
          simp
        have hlo := hlow i hiAll
        have hhi := hhigh i hiAll
        have hj : i - ctorInfo.numParams < fields.length := by
          rw [hF1Size, hargsLength, ← hnumParams,
            ← hfieldsLength] at hhi
          omega
        obtain ⟨code, hcode, hprojTr, hargTr⟩ :=
          hfieldData (i - ctorInfo.numParams) hj
        have hiEq : ctorInfo.numParams + (i - ctorInfo.numParams) = i :=
          Nat.add_sub_of_le hlo
        have hargBound :
            ctorInfo.numParams + (i - ctorInfo.numParams) < F1.size := by
          omega
        have hargTr' : c.TrExprS F1[i] fields[i - ctorInfo.numParams] := by
          simpa [hiEq] using hargTr hargBound
        simp only [bind_assoc]
        refine (isDefEq.WF hprojTr hargTr').bind fun b next _ hb => ?_
        by_cases hbtrue : b = true
        · simp only [hbtrue, if_pos, pure_bind]
          have hcur : FieldEq (i - ctorInfo.numParams) :=
            ⟨fields[i - ctorInfo.numParams], code,
              List.getElem?_eq_getElem hj, hcode, hb hbtrue⟩
          have hsuffixTail : ∃ pre, pre ++ indices = all := by
            refine ⟨pre ++ [i], ?_⟩
            simpa [List.append_assoc] using hprefix
          have htail : RecM.WF c next
              (List.forIn'.loop all (etaStep all hlow hhigh) indices
                ⟨none, PUnit.unit⟩ hsuffixTail)
              (fun r _ =>
                (r.1 = none →
                  ∀ k, k ∈ i :: indices →
                    FieldEq (k - ctorInfo.numParams)) ∧
                r.1 ≠ some true) :=
            (ih hsuffixTail (st := next)).mono
            (fun r _ _ hrest => ⟨fun hnone k hk => by
                rw [List.mem_cons] at hk
                rcases hk with rfl | hk
                · exact hcur
                · exact hrest.1 hnone k hk,
              hrest.2⟩)
          simpa only [etaStep, tryEtaStructFieldStep, pure_bind] using htail
        · simp only [hbtrue]
          exact .pure (by simp)
    have hparamsLe : ctorInfo.numParams ≤ F1.size := by
      rw [hF1Size, hargsLength, ← hnumParams]
      omega
    have hlowRange : ∀ i,
        i ∈ List.range' ctorInfo.numParams
          (F1.size - ctorInfo.numParams) →
        ctorInfo.numParams ≤ i := by
      intro i hi
      rcases List.mem_range'.mp hi with ⟨j, hj, rfl⟩
      omega
    have hhighRange : ∀ i,
        i ∈ List.range' ctorInfo.numParams
          (F1.size - ctorInfo.numParams) →
        i < F1.size := by
      intro i hi
      rcases List.mem_range'.mp hi with ⟨j, hj, rfl⟩
      omega
    have etaForInWF : ∀ {st : VState}, RecM.WF c st
        (List.forIn'
          (List.range' ctorInfo.numParams (F1.size - ctorInfo.numParams))
          ⟨none, PUnit.unit⟩
          (etaStep
            (List.range' ctorInfo.numParams
              (F1.size - ctorInfo.numParams)) hlowRange hhighRange))
        (fun r _ => (r.1 = none → ∀ i,
            i ∈ List.range' ctorInfo.numParams
              (F1.size - ctorInfo.numParams) →
            FieldEq (i - ctorInfo.numParams)) ∧
          r.1 ≠ some true) := by
      intro st
      exact etaLoopWF
        (List.range' ctorInfo.numParams (F1.size - ctorInfo.numParams))
        (List.range' ctorInfo.numParams (F1.size - ctorInfo.numParams))
        ⟨[], by simp⟩ hlowRange hhighRange
    change RecM.WF c _
      (do
        let r ← List.forIn'
          (List.range' ctorInfo.numParams (F1.size - ctorInfo.numParams))
          ⟨none, PUnit.unit⟩
          (etaStep
            (List.range' ctorInfo.numParams
              (F1.size - ctorInfo.numParams)) hlowRange hhighRange)
        match r.1 with
        | none => pure true
        | some a => pure a)
      (fun b _ => b = true → c.IsDefEqU e₁' e₂')
    refine etaForInWF.bind fun r next _ hr => ?_
    cases hr₁ : r.1 with
    | some b =>
      simp only
      refine .pure fun hbtrue => False.elim <|
        hr.2 (hr₁.trans (congrArg some hbtrue))
    | none =>
      simp only
      refine .pure fun _ => ?_
      have hrangeCount :
          F1.size - ctorInfo.numParams = fields.length := by
        rw [hF1Size, hargsLength, hnumParams, hfieldsLength]
        omega
      have hfieldEq : ∀ j, j < fields.length → FieldEq j := by
        intro j hj
        have hjmem : ctorInfo.numParams + j ∈
            List.range' ctorInfo.numParams
              (F1.size - ctorInfo.numParams) := by
          apply List.mem_range'.2
          exact ⟨j, by simpa [hrangeCount] using hj, by simp⟩
        simpa using hr.1 hr₁ (ctorInfo.numParams + j) hjmem
      let projections := artifact.projection.view.projectionArgs levels params
        (artifact.projection.view.specializedFields levels params).length e₁'
      have hprojectionCount :
          (artifact.projection.view.specializedFields levels params).length =
            fields.length := by
        simpa using hfieldsLength.symm
      have hprojectionsLength : projections.length = fields.length := by
        dsimp [projections]
        rw [artifact.projection.view.projectionArgs_length levels params
          (artifact.projection.view.specializedFields levels params).length
          e₁' (by simp)]
        exact hprojectionCount
      have hpointwise : List.Forall₂
          (fun a a' => a = a' ∨ c.IsDefEqU a a') projections fields := by
        apply forall₂_of_getElem? hprojectionsLength
        intro j projection field hprojection hfield
        have hj := (List.getElem?_eq_some_iff.mp hfield).1
        obtain ⟨field', code, hfield', hcode, hdefeq⟩ := hfieldEq j hj
        have hprojection' : projections[j]? =
            some (.app code.projector e₁') := by
          dsimp [projections, VProjectionView.projectionArgs]
          have hjspec : j <
              (artifact.projection.view.specializedFields levels params).length :=
            hprojectionCount.symm ▸ hj
          rw [List.getElem?_map, List.getElem?_take_of_lt hjspec, hcode]
          rfl
        have hpEq : projection = .app code.projector e₁' :=
          Option.some.inj (hprojection.symm.trans hprojection')
        have hfEq : field = field' :=
          Option.some.inj (hfield.symm.trans hfield')
        subst projection
        subst field
        exact .inr hdefeq
      let tailResult := VExpr.instRevAt ctorResult params
        artifact.projection.view.fields.length
      have hctorTailShape : VExpr.instRev ctorTail params =
          VExpr.forallN
            (artifact.projection.view.specializedFields levels params)
            tailResult := by
        simp only [ctorTail, tailResult, VExpr.instRev_forallN_projection,
          VProjectionView.specializedFields_eq, List.length_map]
        rw [VExpr.instRevAt_map_instL_zipIdx]
      have hconstructorParamsLength : params.length =
          artifact.projection.view.constructorParams.length := by
        exact hparamsLength.trans <| by
          exact artifact.projection.view.constructorParams_length.symm
      have hctorHeadPrefix : c.HasType (.const ctorName levels)
          (VExpr.forallN
            (artifact.projection.view.constructorParams.map
              (VExpr.instL levels)) ctorTail) := by
        simpa [ctorBinders, ctorTail,
          VInductDecl.NormalizedCtor.declaredBinders,
          VProjectionView.constructorParams, VProjectionView.fields,
          List.map_append, VExpr.forallN_append] using hctorHeadShape
      have hprefixSpine := hparamCtor.retarget
        (by simpa using hconstructorParamsLength) ctorTail
      rw [hctorTailShape] at hprefixSpine
      have hprefixType := hprefixSpine.hasType_appN hctorHeadPrefix
      have hprojectionSpine :=
        VProjectionView.ProgramsWF.projectionArgsSpine
          hprograms
          c.Ewf c.Δwf hlevelsWF hlevelsLength hparamsLength
          ⟨_, hparamsSpine⟩ haStruct tailResult
      have hprojectionDefEq := hprojectionSpine.defEq_of_pointwise
        c.Ewf c.Δwf (by simpa [projections] using hpointwise)
      have happEq := VEnv.IsDefEq.appN_defEq hprefixType
        hprojectionDefEq
      have happEqU : c.IsDefEqU
          (artifact.projection.view.etaRebuild levels params e₁')
          ((VExpr.const ctorName levels).appN args') := by
        refine ⟨VExpr.instRev tailResult projections, ?_⟩
        simpa [VProjectionView.etaRebuild, VExpr.appN_append, projections,
          artifact.constructor_name_eq, hargsSplit] using happEq
      exact VEnv.IsDefEqU.trans c.Ewf c.Δwf
        ⟨artifact.projection.view.structureType levels params, heta.symm⟩
        (VEnv.IsDefEqU.trans c.Ewf c.Δwf happEqU hfullEq)
  | restored artifact =>
    have hprograms : artifact.projection.view.OperationalProgramsWF c.venv :=
      artifact.projection.operationalProgramsWF_of_large
        c.Ewf.conversionRegular artifact.large
    have ⟨head', hstack⟩ := AppStack.build <|
      e₂.mkAppList_getAppArgsList ▸ he₂
    have hheadTr := hstack.tr
    rw [hhead] at hheadTr
    let .const (us' := levels) hconst hlevelsMap hlevelsHostLength := hheadTr
    have hviewConstructor := artifact.projection.viewWF.constructor
    rw [artifact.constructor_name_eq] at hviewConstructor
    rw [hviewConstructor] at hconst
    cases hconst
    have hlevelsWF : ∀ level ∈ levels,
        level.WF c.lparams.length :=
      VLevel.WF.of_mapM_ofLevel hlevelsMap
    have hrawCtorUvars : artifact.projection.view.sourceConstructor.uvars =
        artifact.projection.view.uvars :=
      artifact.projection.view.constructor_uvars_eq
    have hlevelsLength : levels.length = artifact.projection.view.uvars :=
      (List.mapM_eq_some.1 hlevelsMap).length_eq.symm.trans <|
        hlevelsHostLength.trans hrawCtorUvars
    have hctorHead : c.HasType (.const ctorName levels)
        (artifact.projection.view.sourceConstructor.type.instL levels) :=
      VEnv.HasType.const hviewConstructor hlevelsWF
        (hlevelsLength.trans hrawCtorUvars.symm)
    let ctorResult :=
      (VExpr.dropN artifact.projection.view.nparams
        artifact.projection.view.sourceConstructor.type).resultOf
    let ctorBinders :=
      (artifact.projection.view.constructorParams ++
        artifact.projection.view.fields).map (VExpr.instL levels)
    have hsourceCtorShape :
        artifact.projection.view.sourceConstructor.type =
          VExpr.forallN artifact.projection.view.constructorParams
            (VExpr.forallN artifact.projection.view.fields ctorResult) := by
      simp [VRestoredBlockStructureView.constructorParams,
        VRestoredBlockStructureView.fields, ctorResult,
        VInductDecl.forallN_ctorFields_resultOf,
        VExpr.forallN_telN_dropN]
    have hctorHeadShape : c.HasType (.const ctorName levels)
        (VExpr.forallN ctorBinders (ctorResult.instL levels)) := by
      rw [hsourceCtorShape] at hctorHead
      simpa [ctorBinders, List.map_append, VExpr.forallN_append,
        VExpr.instL_forallN] using hctorHead
    have hhostArgsLength : e₂.getAppArgsList.length =
        ctorInfo.numParams + ctorInfo.numFields := by
      simpa [Expr.getAppNumArgs_eq, ← Expr.getAppArgsList_reverse] using hargs
    have hnumParams : ctorInfo.numParams = artifact.projection.view.nparams := by
      exact (congrArg ConstructorVal.numParams
        artifact.constructor_info_eq).symm.trans
          artifact.projection.constructor_numParams_eq
    have hnumFields : ctorInfo.numFields = artifact.projection.view.fields.length := by
      exact (congrArg ConstructorVal.numFields
        artifact.constructor_info_eq).symm.trans
          artifact.projection.constructor_numFields_eq
    have hctorBindersLength : ctorBinders.length =
        artifact.projection.view.nparams +
          artifact.projection.view.fields.length := by
      calc
        ctorBinders.length =
            artifact.projection.view.constructorParams.length +
              artifact.projection.view.fields.length := by
          simp only [ctorBinders, List.length_map, List.length_append]
        _ = artifact.projection.view.nparams +
            artifact.projection.view.fields.length := by
          rw [artifact.projection.view.constructorParams_length]
    have hhostBinderLength : e₂.getAppArgsList.length = ctorBinders.length := by
      have hhostArity : e₂.getAppArgsList.length =
          artifact.projection.view.nparams +
            artifact.projection.view.fields.length := by
        simpa [hnumParams, hnumFields] using hhostArgsLength
      exact hhostArity.trans hctorBindersLength.symm
    obtain ⟨args', hargsTr, hargsSpine, hfullTr⟩ :=
      AppStack.toSpineWF hstack hctorHeadShape hhostBinderLength
    rw [e₂.mkAppList_getAppArgsList] at hfullTr
    have hargsLength : args'.length = artifact.projection.view.nparams +
        artifact.projection.view.fields.length :=
      hargsTr.length_eq.symm.trans <| by
        simpa [hnumParams, hnumFields] using hhostArgsLength
    let params := args'.take artifact.projection.view.nparams
    let fields := args'.drop artifact.projection.view.nparams
    have hargsSplit : args' = params ++ fields := by
      simp [params, fields]
    have hparamsLength : params.length = artifact.projection.view.nparams := by
      simp [params, hargsLength]
    have hfieldsLength : fields.length = artifact.projection.view.fields.length := by
      simp [fields, hargsLength]
    have hargsSpineSplit := hargsSpine
    rw [hargsSplit] at hargsSpineSplit
    obtain ⟨paramCursor, hparamRaw, hfieldsRaw⟩ :=
      hargsSpineSplit.split
    let ctorTail := VExpr.forallN
      (artifact.projection.view.fields.map (VExpr.instL levels))
        (ctorResult.instL levels)
    have hparamCtor : c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (VExpr.forallN
          (artifact.projection.view.constructorParams.map
            (VExpr.instL levels)) ctorTail)
        params paramCursor := by
      simpa [ctorBinders, ctorTail,
        List.map_append, VExpr.forallN_append] using hparamRaw
    have hparamsSpine :=
      artifact.projection.parameterLayout.familyParamsSpine_of_constructor
        c.Ewf.ordered levels hlevelsWF hlevelsLength params hparamsLength
        hparamCtor
    have hcanonicalRaw := hargsSpine.hasType_appN hctorHeadShape
    have hconstructorPrefix :=
      artifact.projection.parameterLayout.constructorPrefix_hasType
        c.Ewf.conversionRegular artifact.projection.recEntriesClosed
        levels hlevelsWF hlevelsLength params hparamsLength
          ⟨_, hparamsSpine⟩
    have hfieldsSpecializedLength : fields.length =
        (artifact.projection.view.specializedFields levels params).length := by
      simpa [VRestoredBlockStructureView.specializedFields] using hfieldsLength
    have hcanonicalApplication : c.HasType
        (VExpr.appN
          (VExpr.appN
            (.const artifact.projection.view.constructorName levels) params)
          fields)
        ((ctorResult.instL levels).instRev args') := by
      simpa [artifact.constructor_name_eq, hargsSplit, VExpr.appN_append] using
        hcanonicalRaw
    have hcanonical₀ := VEnv.HasType.appN_canonical
      c.Ewf.conversionRegular c.Δwf hfieldsSpecializedLength
        hconstructorPrefix hcanonicalApplication
    have hcanonicalResult :
        VExpr.instRev
          ((artifact.projection.view.structureType levels params).liftN
            (artifact.projection.view.specializedFields levels params).length)
          fields = artifact.projection.view.structureType levels params := by
      rw [← hfieldsSpecializedLength]
      exact VExpr.instRev_liftN_len fields _
    rw [hcanonicalResult] at hcanonical₀
    have hcanonical : c.HasType
        ((VExpr.const ctorName levels).appN args')
        (artifact.projection.view.structureType levels params) :=
      by simpa [artifact.constructor_name_eq, hargsSplit,
        VExpr.appN_append] using hcanonical₀
    have hfullEq := hfullTr.uniq c.Ewf (.refl c.Ewf c.Δwf) he₂
    have hbStruct := hcanonical.defeqU_l c.Ewf c.Δwf hfullEq
    have hty₂Struct := bTyped.uniqU c.Ewf c.Δwf hbStruct
    have hty₁Struct := VEnv.IsDefEqU.trans c.Ewf c.Δwf
      (htypes htypesTrue) hty₂Struct
    have haStruct := aTyped.defeqU_r c.Ewf c.Δwf hty₁Struct
    have heta := artifact.eta c.Ewf c.Δwf hlevelsWF hlevelsLength
      hparamsLength ⟨_, hparamsSpine⟩ haStruct
    have hF1Size : F1.size = args'.length := by
      calc
        F1.size = F1.toList.length := by simp
        _ = e₂.getAppArgsList.length := by simp [F1, Expr.getAppArgs_toList]
        _ = args'.length := hargsTr.length_eq
    have hrestoredFieldData : ∀ (j : Nat), j < fields.length →
        ∃ code : VStructureView.ProjectionCode,
          (artifact.projection.view.operationalProjectionCodes levels params)[j]? =
            some code ∧
          c.TrExprS (.proj ctorInfo.induct j e₁)
            (.app code.projector e₁') ∧
          ∀ (hi : ctorInfo.numParams + j < F1.size),
            c.TrExprS F1[ctorInfo.numParams + j] fields[j] := by
      intro j hj
      have hcodeIdx : j <
          (artifact.projection.view.operationalProjectionCodes levels params).length := by
        simpa [hfieldsLength] using hj
      let code :=
        (artifact.projection.view.operationalProjectionCodes levels params)[j]
      have hcode :
          (artifact.projection.view.operationalProjectionCodes levels params)[j]? =
            some code := List.getElem?_eq_getElem hcodeIdx
      have hprojector := hprograms c.Δwf hlevelsWF
        hlevelsLength hparamsLength ⟨_, hparamsSpine⟩ hcode
      have hprojSem : VRestoredBlockStructureView.TrProj c.venv
          c.lparams.length
          c.vlctx.toCtx artifact.projection.view levels params j e₁'
          (.app code.projector e₁') := {
        viewWF := artifact.projection.viewWF
        parameterLayout := artifact.projection.parameterLayout
        codeNaturality := artifact.projection.codeNaturality
        recEntriesClosed := artifact.projection.recEntriesClosed
        levelsWF := hlevelsWF
        levels_length := hlevelsLength
        params_length := hparamsLength
        paramsSpine := ⟨_, hparamsSpine⟩
        majorType := haStruct
        program := ⟨code, hcode, rfl, hprojector⟩ }
      have hprojTr : c.TrExprS (.proj ctorInfo.induct j e₁)
          (.app code.projector e₁') :=
        .proj he₁ ⟨.restored artifact.projection.view, levels, params,
          artifact.projection.name_eq, .restored hprojSem⟩
      refine ⟨code, hcode, hprojTr, ?_⟩
      intro hi
      have hselectedList :
          e₂.getAppArgsList[ctorInfo.numParams + j]? =
            some F1[ctorInfo.numParams + j] := by
        rw [← Expr.getAppArgs_toList]
        simp [F1]
      obtain ⟨translated, htranslated, htr⟩ :=
        Lean4Lean.List.Forall₂.getElem?_left hargsTr hselectedList
      have hfieldGet : args'[ctorInfo.numParams + j]? = some fields[j] := by
        rw [hargsSplit, List.getElem?_append_right]
        · simp [hnumParams, hparamsLength]
        · simp [hnumParams, hparamsLength]
      have : translated = fields[j] :=
        Option.some.inj (htranslated.symm.trans hfieldGet)
      subst translated
      exact htr
    rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
    simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
    let FieldEq := fun (j : Nat) => ∃ (field : VExpr)
        (code : VStructureView.ProjectionCode),
      fields[j]? = some field ∧
      (artifact.projection.view.operationalProjectionCodes levels params)[j]? = some code ∧
      c.IsDefEqU (.app code.projector e₁') field
    let etaStep (indices : List Nat)
        (hlow : ∀ i, i ∈ indices → ctorInfo.numParams ≤ i)
        (hhigh : ∀ i, i ∈ indices → i < F1.size) :
        (i : Nat) → i ∈ indices → Option Bool × PUnit →
          RecM (ForInStep (Option Bool × PUnit)) :=
      fun i hi r => tryEtaStructFieldStep e₁ ctorInfo.induct
        ctorInfo.numParams F1 i
        ⟨hlow i hi, hhigh i hi, by
          change (i - ctorInfo.numParams) % 1 = 0
          exact Nat.mod_one _⟩ r
    have etaLoopWF : ∀ (all indices : List Nat)
        (hsuffix : ∃ pre, pre ++ indices = all)
        (hlow : ∀ i, i ∈ all → ctorInfo.numParams ≤ i)
        (hhigh : ∀ i, i ∈ all → i < F1.size) {st : VState},
        RecM.WF c st
          (List.forIn'.loop all (etaStep all hlow hhigh) indices
            ⟨none, PUnit.unit⟩ hsuffix)
          fun r _ =>
            (r.1 = none →
              ∀ i, i ∈ indices → FieldEq (i - ctorInfo.numParams)) ∧
            r.1 ≠ some true := by
      intro all indices hsuffix hlow hhigh st
      induction indices generalizing st with
      | nil =>
        simp only [List.forIn'.loop]
        exact .pure (by simp)
      | cons i indices ih =>
        simp only [List.forIn'.loop]
        simp only [etaStep, tryEtaStructFieldStep]
        obtain ⟨pre, hprefix⟩ := hsuffix
        have hiAll : i ∈ all := by
          rw [← hprefix]
          simp
        have hlo := hlow i hiAll
        have hhi := hhigh i hiAll
        have hj : i - ctorInfo.numParams < fields.length := by
          rw [hF1Size, hargsLength, ← hnumParams,
            ← hfieldsLength] at hhi
          omega
        obtain ⟨code, hcode, hprojTr, hargTr⟩ :=
          hrestoredFieldData (i - ctorInfo.numParams) hj
        have hiEq : ctorInfo.numParams + (i - ctorInfo.numParams) = i :=
          Nat.add_sub_of_le hlo
        have hargBound :
            ctorInfo.numParams + (i - ctorInfo.numParams) < F1.size := by
          omega
        have hargTr' : c.TrExprS F1[i] fields[i - ctorInfo.numParams] := by
          simpa [hiEq] using hargTr hargBound
        simp only [bind_assoc]
        refine (isDefEq.WF hprojTr hargTr').bind fun b next _ hb => ?_
        by_cases hbtrue : b = true
        · simp only [hbtrue, if_pos, pure_bind]
          have hcur : FieldEq (i - ctorInfo.numParams) :=
            ⟨fields[i - ctorInfo.numParams], code,
              List.getElem?_eq_getElem hj, hcode, hb hbtrue⟩
          have hsuffixTail : ∃ pre, pre ++ indices = all := by
            refine ⟨pre ++ [i], ?_⟩
            simpa [List.append_assoc] using hprefix
          have htail : RecM.WF c next
              (List.forIn'.loop all (etaStep all hlow hhigh) indices
                ⟨none, PUnit.unit⟩ hsuffixTail)
              (fun r _ =>
                (r.1 = none →
                  ∀ k, k ∈ i :: indices →
                    FieldEq (k - ctorInfo.numParams)) ∧
                r.1 ≠ some true) :=
            (ih hsuffixTail (st := next)).mono
            (fun r _ _ hrest => ⟨fun hnone k hk => by
                rw [List.mem_cons] at hk
                rcases hk with rfl | hk
                · exact hcur
                · exact hrest.1 hnone k hk,
              hrest.2⟩)
          simpa only [etaStep, tryEtaStructFieldStep, pure_bind] using htail
        · simp only [hbtrue]
          exact .pure (by simp)
    have hparamsLe : ctorInfo.numParams ≤ F1.size := by
      rw [hF1Size, hargsLength, ← hnumParams]
      omega
    have hlowRange : ∀ i,
        i ∈ List.range' ctorInfo.numParams
          (F1.size - ctorInfo.numParams) →
        ctorInfo.numParams ≤ i := by
      intro i hi
      rcases List.mem_range'.mp hi with ⟨j, hj, rfl⟩
      omega
    have hhighRange : ∀ i,
        i ∈ List.range' ctorInfo.numParams
          (F1.size - ctorInfo.numParams) →
        i < F1.size := by
      intro i hi
      rcases List.mem_range'.mp hi with ⟨j, hj, rfl⟩
      omega
    have etaForInWF : ∀ {st : VState}, RecM.WF c st
        (List.forIn'
          (List.range' ctorInfo.numParams (F1.size - ctorInfo.numParams))
          ⟨none, PUnit.unit⟩
          (etaStep
            (List.range' ctorInfo.numParams
              (F1.size - ctorInfo.numParams)) hlowRange hhighRange))
        (fun r _ => (r.1 = none → ∀ i,
            i ∈ List.range' ctorInfo.numParams
              (F1.size - ctorInfo.numParams) →
            FieldEq (i - ctorInfo.numParams)) ∧
          r.1 ≠ some true) := by
      intro st
      exact etaLoopWF
        (List.range' ctorInfo.numParams (F1.size - ctorInfo.numParams))
        (List.range' ctorInfo.numParams (F1.size - ctorInfo.numParams))
        ⟨[], by simp⟩ hlowRange hhighRange
    change RecM.WF c _
      (do
        let r ← List.forIn'
          (List.range' ctorInfo.numParams (F1.size - ctorInfo.numParams))
          ⟨none, PUnit.unit⟩
          (etaStep
            (List.range' ctorInfo.numParams
              (F1.size - ctorInfo.numParams)) hlowRange hhighRange)
        match r.1 with
        | none => pure true
        | some a => pure a)
      (fun b _ => b = true → c.IsDefEqU e₁' e₂')
    refine etaForInWF.bind fun r next _ hr => ?_
    cases hr₁ : r.1 with
    | some b =>
      simp only
      refine .pure fun hbtrue => False.elim <|
        hr.2 (hr₁.trans (congrArg some hbtrue))
    | none =>
      simp only
      refine .pure fun _ => ?_
      have hrangeCount :
          F1.size - ctorInfo.numParams = fields.length := by
        rw [hF1Size, hargsLength, hnumParams, hfieldsLength]
        omega
      have hfieldEq : ∀ j, j < fields.length → FieldEq j := by
        intro j hj
        have hjmem : ctorInfo.numParams + j ∈
            List.range' ctorInfo.numParams
              (F1.size - ctorInfo.numParams) := by
          apply List.mem_range'.2
          exact ⟨j, by simpa [hrangeCount] using hj, by simp⟩
        simpa using hr.1 hr₁ (ctorInfo.numParams + j) hjmem
      let projections := artifact.projection.view.operationalProjectionArgs levels params
        (artifact.projection.view.specializedFields levels params).length e₁'
      have hprojectionCount :
          (artifact.projection.view.specializedFields levels params).length =
            fields.length := by
        simpa using hfieldsLength.symm
      have hprojectionsLength : projections.length = fields.length := by
        dsimp [projections]
        rw [artifact.projection.view.operationalProjectionArgs_length levels params
          (artifact.projection.view.specializedFields levels params).length
          e₁' (by simp)]
        exact hprojectionCount
      have hpointwise : List.Forall₂
          (fun a a' => a = a' ∨ c.IsDefEqU a a') projections fields := by
        apply forall₂_of_getElem? hprojectionsLength
        intro j projection field hprojection hfield
        have hj := (List.getElem?_eq_some_iff.mp hfield).1
        obtain ⟨field', code, hfield', hcode, hdefeq⟩ := hfieldEq j hj
        have hprojection' : projections[j]? =
            some (.app code.projector e₁') := by
          dsimp [projections, VRestoredBlockStructureView.operationalProjectionArgs]
          have hjspec : j <
              (artifact.projection.view.specializedFields levels params).length :=
            hprojectionCount.symm ▸ hj
          rw [List.getElem?_map, List.getElem?_take_of_lt hjspec, hcode]
          rfl
        have hpEq : projection = .app code.projector e₁' :=
          Option.some.inj (hprojection.symm.trans hprojection')
        have hfEq : field = field' :=
          Option.some.inj (hfield.symm.trans hfield')
        subst projection
        subst field
        exact .inr hdefeq
      let restoredTailResult :=
        (artifact.projection.view.structureType levels params).liftN
          (artifact.projection.view.specializedFields levels params).length
      have hprefixType : c.HasType
          (VExpr.appN (.const ctorName levels) params)
          (VExpr.forallN
            (artifact.projection.view.specializedFields levels params)
            restoredTailResult) := by
        simpa [restoredTailResult, artifact.constructor_name_eq] using
          hconstructorPrefix
      have hprojectionSpine :=
        hprograms.operationalProjectionArgsSpine
          artifact.projection.parameterLayout.toLayoutWF
          c.Ewf.conversionRegular artifact.projection.recEntriesClosed
          c.Δwf hlevelsWF hlevelsLength hparamsLength
          ⟨_, hparamsSpine⟩ haStruct restoredTailResult
      have hprojectionDefEq := hprojectionSpine.defEq_of_pointwise
        c.Ewf c.Δwf (by simpa [projections] using hpointwise)
      have happEq := VEnv.IsDefEq.appN_defEq hprefixType
        hprojectionDefEq
      have happEqU : c.IsDefEqU
          (artifact.projection.view.operationalEtaRebuild levels params e₁')
          ((VExpr.const ctorName levels).appN args') := by
        refine ⟨VExpr.instRev restoredTailResult projections, ?_⟩
        simpa [VRestoredBlockStructureView.operationalEtaRebuild,
          VExpr.appN_append, projections, artifact.constructor_name_eq,
          hargsSplit] using happEq
      exact VEnv.IsDefEqU.trans c.Ewf c.Δwf
        ⟨artifact.projection.view.structureType levels params, heta.symm⟩
        (VEnv.IsDefEqU.trans c.Ewf c.Δwf happEqU hfullEq)


theorem tryEtaStructCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStructCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  tryEtaStructCore.WF_of_structureEta he₁ he₂

theorem tryEtaStruct.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryEtaStruct e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  simp [tryEtaStruct, orM, toBool]
  refine (tryEtaStructCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h rfl; skip]
  exact (tryEtaStructCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

theorem isDefEqApp.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqApp e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqApp; split <;> [skip; exact .pure nofun]
  rw [Expr.withApp_eq, Expr.withApp_eq]
  have ⟨_, he₁'⟩ := AppStack.build <| e₁.mkAppList_getAppArgsList ▸ he₁
  have ⟨_, he₂'⟩ := AppStack.build <| e₂.mkAppList_getAppArgsList ▸ he₂
  refine (isDefEq.WF he₁'.tr he₂'.tr).bind fun _ _ _ h => ?_
  split <;> [skip; exact .pure nofun]
  split <;> [rename_i eq; exact .pure nofun]
  let rec loop.WF {s args₁ args₂ f₁ f₂ f₁' f₂' eq i} (l₁ r₁ l₂ r₂)
      (h₁ : args₁.toList = l₁ ++ r₁) (hi₁ : l₁.length = i)
      (h₂ : args₂.toList = l₂ ++ r₂) (hi₂ : l₂.length = i)
      (he₁ : AppStack c.venv c.lparams c.vlctx (.mkAppList f₁ l₁) f₁' r₁)
      (he₂ : AppStack c.venv c.lparams c.vlctx (.mkAppList f₂ l₂) f₂' r₂)
      (H1 : c.IsDefEqU f₁' f₂') :
      RecM.WF c s (loop args₁ args₂ eq i) fun b _ => b →
        ∀ e₁', c.TrExprS (f₁.mkAppList args₁.toList) e₁' →
        ∀ e₂', c.TrExprS (f₂.mkAppList args₂.toList) e₂' → c.IsDefEqU e₁' e₂' := by
    unfold loop; split <;> rename_i h
    · have hr₁ : r₁.length > 0 := by simp [← Array.length_toList, h₁] at h; omega
      have hr₂ : r₂.length > 0 := by simp [eq, ← Array.length_toList, h₂] at h; omega
      let .app (a := a₁) (as := r₁) a1 a2 a3 a4 a5 := he₁
      let .app (a := a₂) (as := r₂) b1 b2 b3 b4 b5 := he₂
      simp [
        show args₁[i] = a₁ by cases args₁; cases h₁; simp [hi₁],
        show args₂[i] = a₂ by cases args₂; cases h₂; simp [hi₂]]
      refine (isDefEq.WF a4 b4).bind fun _ _ _ h => ?_
      split <;> [skip; exact .pure nofun]
      have H := (H1.of_l c.Ewf c.Δwf a1).appDF <| (h ‹_›).of_l c.Ewf c.Δwf a2
      exact loop.WF (l₁ ++ [a₁]) r₁ (l₂ ++ [a₂]) r₂
        (by simp [h₁]) (by simp [hi₁]) (by simp [h₂]) (by simp [hi₂])
        (by simp [a5]) (by simp [b5]) ⟨_, H⟩
    · have hr₁ : r₁.length = 0 := by simp [← Array.length_toList, h₁] at h; omega
      have hr₂ : r₂.length = 0 := by simp [eq, ← Array.length_toList, h₂] at h; omega
      simp at hr₁ hr₂; subst r₁ r₂; simp at h₁ h₂; subst l₁ l₂
      refine .pure fun _ _ h1 _ h2 => ?_
      have u1 := h1.uniq c.Ewf (.refl c.Ewf c.Δwf) he₁.tr
      have u2 := h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he₂.tr
      exact u1.trans c.Ewf c.Δwf H1 |>.trans c.Ewf c.Δwf u2.symm
  refine loop.WF [] _ [] _ (i := 0) (by simp [Expr.getAppArgs_toList]) rfl
    (by simp [Expr.getAppArgs_toList]) rfl he₁' he₂' (h ‹_›) |>.mono fun _ _ _ h2 hb => ?_
  simp [Expr.getAppArgs_toList, Expr.mkAppList_getAppArgsList] at h2
  exact h2 hb _ he₁ _ he₂

theorem isDefEqProofIrrel.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqProofIrrel e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqProofIrrel
  refine (inferType.WF he₁).bind fun _ _ _ ⟨_, a1, a2, a3, a4⟩ => ?_
  refine (isProp.WF a3).bind fun _ _ _ h1 => ?_
  split <;> [exact .pure nofun; skip]
  rename_i h; simp at h
  refine (inferType.WF he₂).bind fun _ _ _ ⟨_, b1, b2, b3, b4⟩ => .toLBoolM ?_
  refine (isDefEq.WF a3 b3).mono fun _ _ _ h2 hb => ?_
  exact ⟨_, .proofIrrel (h1 h) a4 (b4.defeqU_r c.Ewf c.Δwf (h2 hb).symm)⟩

theorem cacheFailure.WF {c : VContext} {s : VState} :
    (cacheFailure e₁ e₂).WF c s fun _ _ => True := by
  rintro wf _ _ ⟨⟩
  exact ⟨{ s with toState := _ }, rfl, .rfl, { wf with }, ⟨⟩⟩

theorem tryUnfoldProjApp.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    (tryUnfoldProjApp e).WF c s fun oe _ =>
    ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold tryUnfoldProjApp; extract_lets f
  split <;> [exact .pure nofun; skip]
  refine (whnfCore.WF he).bind fun _ _ _ h => ?_
  refine .pure fun _ => ?_
  split <;> rintro ⟨⟩; exact h

def _root_.Lean4Lean.TypeChecker.ReductionStatus.WF
    (c : VContext) (e₁' e₂' : VExpr) (allowContinue := false) : ReductionStatus → Prop
  | .continue e₁ e₂ => allowContinue ∧ c.TrExpr e₁ e₁' ∧ c.TrExpr e₂ e₂'
  | .unknown e₁ e₂ | .false e₁ e₂ => c.TrExpr e₁ e₁' ∧ c.TrExpr e₂ e₂'
  | .true => c.IsDefEqU e₁' e₂'

theorem _root_.Lean4Lean.TypeChecker.ReductionStatus.WF.bool
    (H1 : c.TrExpr e₁ e₁') (H2 : c.TrExpr e₂ e₂') (H : b = true → c.IsDefEqU e₁' e₂') :
    ReductionStatus.WF c e₁' e₂' allowContinue (.bool e₁ e₂ b) :=
  match b with
  | .false => ⟨H1, H2⟩
  | .true => H rfl

theorem _root_.Lean4Lean.TypeChecker.ReductionStatus.WF.defeq
    (h1 : c.IsDefEqU e₁' e₁'') (h2 : c.IsDefEqU e₂' e₂'')
    (H : ReductionStatus.WF c e₁' e₂' ac r) : ReductionStatus.WF c e₁'' e₂'' ac r :=
  match r, H with
  | .continue .., ⟨a1, a2, a3⟩ =>
    ⟨a1, a2.defeq c.Ewf c.Δwf h1, a3.defeq c.Ewf c.Δwf h2⟩
  | .unknown .., ⟨a2, a3⟩ | .false .., ⟨a2, a3⟩ =>
    ⟨a2.defeq c.Ewf c.Δwf h1, a3.defeq c.Ewf c.Δwf h2⟩
  | .true, h => h1.symm.trans c.Ewf c.Δwf h |>.trans c.Ewf c.Δwf h2

theorem lazyDeltaReductionStep.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (lazyDeltaReductionStep e₁ e₂).WF c s fun r _ => r.WF c e₁' e₂' true := by
  unfold lazyDeltaReductionStep
  refine .getEnv ?_; extract_lets delta cont F1 F2
  have hdelta {s e e' ci} (he : c.TrExprS e e') (H : isDelta c.env e = some ci) :
      (delta e).WF c s fun r _ => c.TrExpr r e' := by
    let ⟨n, h1, ⟨_, h2⟩, ls, h3, _⟩ := isDelta_is_some.1 H
    have ⟨_, stk⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
    have .const a1 a2 a3 := h3 ▸ stk.tr
    have ⟨b1, b2, b3, b4⟩ := c.trenv.find?_uniq h1 a1
    refine (unfoldDefinition.WF he).bind fun oe _ _ H => ?_
    obtain _ | e' := oe; · cases H h1 h2 h3 (a3.trans b3.symm)
    have ⟨_, _, c1, c2⟩ := H
    exact (whnfCore.WF c1).mono fun x _ _ h => h.2.defeq c.Ewf c.Δwf c2
  have hcont {s e₁ e₂} (he₁ : c.TrExpr e₁ e₁') (he₂ : c.TrExpr e₂ e₂') :
      (cont e₁ e₂).WF c s fun r _ => r.WF c e₁' e₂' true := by
    let ⟨_, se₁, de₁⟩ := he₁; let ⟨_, se₂, de₂⟩ := he₂
    refine (quickIsDefEq.WF se₁ se₂).bind fun _ _ _ h => .pure ?_; split
    · exact ⟨rfl, he₁, he₂⟩
    · exact de₁.symm.trans c.Ewf c.Δwf (h rfl) |>.trans c.Ewf c.Δwf de₂
    · exact ⟨he₁, he₂⟩
  split
  · exact .pure ⟨he₁.trExpr c.Ewf c.Δwf, he₂.trExpr c.Ewf c.Δwf⟩
  · refine (tryUnfoldProjApp.WF he₂).bind fun _ _ _ h => ?_; split
    · exact hcont (he₁.trExpr c.Ewf c.Δwf) (h _ rfl).2
    · exact (hdelta he₁ ‹_›).bind fun _ _ _ h => hcont h (he₂.trExpr c.Ewf c.Δwf)
  · refine (tryUnfoldProjApp.WF he₁).bind fun _ _ _ h => ?_; split
    · exact hcont (h _ rfl).2 (he₂.trExpr c.Ewf c.Δwf)
    · exact (hdelta he₂ ‹_›).bind fun _ _ _ h => hcont (he₁.trExpr c.Ewf c.Δwf) h
  rename_i dt dt' hd1 hd2; extract_lets ht hs; split <;> [skip; split]
  · exact (hdelta he₂ ‹_›).bind fun _ _ _ h => hcont (he₁.trExpr c.Ewf c.Δwf) h
  · exact (hdelta he₁ ‹_›).bind fun _ _ _ h => hcont h (he₂.trExpr c.Ewf c.Δwf)
  have hF1 {s} : (F1 ⟨⟩).WF c s fun r _ => r.WF c e₁' e₂' true :=
    (hdelta he₁ ‹_›).bind fun _ _ _ h1 => (hdelta he₂ ‹_›).bind fun _ _ _ h2 => hcont h1 h2
  refine .get ?_; split <;> [skip; exact hF1]
  split <;> [skip; exact cacheFailure.WF.lift.bind fun _ _ _ _ => hF1]
  rename_i h1 h2; simp at h1
  cases ptrEqConstantInfo_eq h1.1.1.2
  have ⟨n₁, b1₁, ⟨_, b2₁⟩, ls₁, b3₁, _⟩ := isDelta_is_some.1 hd1
  have ⟨n₂, b1₂, ⟨_, b2₂⟩, ls₂, b3₂, _⟩ := isDelta_is_some.1 hd2
  simp [b3₁, b3₂, Expr.constLevels!] at h2
  have ⟨_, stk₁⟩ := AppStack.build (e₁.mkAppList_getAppArgsList ▸ he₁)
  have ⟨_, stk₂⟩ := AppStack.build (e₂.mkAppList_getAppArgsList ▸ he₂)
  have .const (us' := ls₁) c1₁ c2₁ c3₁ := b3₁ ▸ stk₁.tr
  have .const (us' := ls₂) c1₂ c2₂ c3₂ := b3₂ ▸ stk₂.tr
  cases (c.trenv.find?_uniq b1₁ c1₁).1
  cases (c.trenv.find?_uniq b1₂ c1₂).1
  cases c1₁.symm.trans c1₂
  have := VEnv.IsDefEq.constDF c1₁
    (Γ := c.vlctx.toCtx) (.of_mapM_ofLevel c2₁) (.of_mapM_ofLevel c2₂)
    ((List.mapM_eq_some.1 c2₁).length_eq.symm.trans c3₁)
    (Level.isEquivList_wf h2 c2₁ c2₂)
  refine (isDefEqArgs.WF ⟨_, stk₁.tr, _, stk₂.tr, _, this⟩ he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [skip; exact cacheFailure.WF.lift.bind fun _ _ _ _ => hF1]
  exact .pure <| h ‹_›

theorem isNatZero_wf {c : VContext} (H : isNatZero e) (h : c.TrExprS e e') : e' = .natZero := by
  have h1 : c.TrExprS (.lit (.natVal 0)) e' := by
    simp [isNatZero] at H; obtain H|H := H
    · have := h.eqv H; exact .lit (this.nat_of_natZero c.Ewf c.hasPrimitives) this
    · split at H <;> [exact h; cases H]
  have := TrExprS.lit_has_type (l := .natVal 0) h1
  exact h1.unique (by trivial) (TrExprS.natLit c.hasPrimitives this 0).1

theorem isNatSuccOf?_wf {c : VContext} (H : isNatSuccOf? e = some e₁)
    (h : c.TrExprS e e') : ∃ x, c.TrExprS e₁ x ∧ e' = .app .natSucc x := by
  unfold isNatSuccOf? at H; split at H <;> cases H
  · rename_i n
    have := TrExprS.lit_has_type (l := .natVal (n+1)) h
    refine ⟨_, (TrExprS.natLit c.hasPrimitives this n).1, ?_⟩
    exact h.unique (by trivial) (TrExprS.natLit c.hasPrimitives this (n+1)).1
  · let .app a1 a2 a3 a4 := h
    let .const b1 b2 b3 := a3
    cases c.hasPrimitives.natSucc b1
    simp at b3; subst b3; simp at b2; subst b2
    exact ⟨_, a4, rfl⟩

theorem isDefEqOffset.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (isDefEqOffset e₁ e₂).WF c s fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqOffset; split
  · rename_i h; simp at h
    cases isNatZero_wf h.1 he₁; cases isNatZero_wf h.2 he₂
    exact .pure fun _ => .refl <| he₁.wf c.Ewf c.Δwf
  · split <;> [skip; exact .pure nofun]
    obtain ⟨_, a1, rfl⟩ := isNatSuccOf?_wf ‹_› he₁
    obtain ⟨_, b1, rfl⟩ := isNatSuccOf?_wf ‹_› he₂
    refine .toLBoolM <| (isDefEqCore.WF a1 b1).mono fun _ _ _ h hb => ?_
    let ⟨_, de'⟩ := he₁.wf c.Ewf c.Δwf
    let ⟨_, _, c1, c2⟩ := de'.hasType.1.app_inv c.Ewf c.Δwf
    exact ⟨_, c1.appDF <| (h hb).of_l c.Ewf c.Δwf c2⟩

theorem lazyDeltaReduction.loop.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    (lazyDeltaReduction.loop e₁ e₂ n).WF c s fun r _ => r.WF c e₁' e₂' := by
  induction n generalizing s e₁ e₂ e₁' e₂' with | zero => exact .throw | succ n ih
  unfold loop; extract_lets F1
  refine (isDefEqOffset.WF he₁ he₂).bind fun _ _ _ h => ?_; split
  · exact .pure <| .bool (he₁.trExpr c.Ewf c.Δwf) (he₂.trExpr c.Ewf c.Δwf) fun hb =>
      h (by simpa using hb)
  suffices hF1 : ∀ {s}, (F1 ⟨⟩).WF c s fun r _ => r.WF c e₁' e₂' by
    refine .readThe ?_; split <;> [skip; exact hF1]
    refine (reduceNat.WF he₁).bind fun _ _ _ h => ?_; split
    · have ⟨_, a1, a2⟩ := (h _ rfl).2
      refine (isDefEqCore.WF a1 he₂).bind fun _ _ _ h => ?_
      refine .pure <| .bool ⟨_, a1, a2⟩ (he₂.trExpr c.Ewf c.Δwf) fun hb => ?_
      exact a2.symm.trans c.Ewf c.Δwf (h hb)
    refine (reduceNat.WF he₂).bind fun _ _ _ h => ?_; split
    · have ⟨_, a1, a2⟩ := (h _ rfl).2
      refine (isDefEqCore.WF he₁ a1).bind fun _ _ _ h => ?_
      refine .pure <| .bool (he₁.trExpr c.Ewf c.Δwf) ⟨_, a1, a2⟩ fun hb => ?_
      exact (h hb).trans c.Ewf c.Δwf a2
    exact hF1
  intro s; unfold F1; refine .getEnv ?_
  refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h => ?_
  split <;> [cases h _ rfl; skip]
  refine (M.WF.liftExcept reduceNative.WF).lift.bind fun _ _ _ h => ?_
  split <;> [cases h _ rfl; skip]
  refine (lazyDeltaReductionStep.WF he₁ he₂).bind fun r _ _ h => ?_
  cases r with
  | «continue» =>
    let ⟨_, ⟨_, a1, a2⟩, ⟨_, b1, b2⟩⟩ := h
    exact (ih a1 b1).mono fun _ _ _ h => h.defeq a2 b2
  | _ => exact .pure h

theorem tryStringLitExpansionCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryStringLitExpansionCore e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold tryStringLitExpansionCore; iterate 3 split <;> [skip; exact .pure nofun]
  let .lit _ he₁ := he₁
  exact .toLBoolM <| isDefEqCore.WF he₁ he₂

theorem tryStringLitExpansion.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (tryStringLitExpansion e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  refine (tryStringLitExpansionCore.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [skip; exact .pure h]
  exact (tryStringLitExpansionCore.WF he₂ he₁).mono fun _ _ _ h hb => (h hb).symm

theorem isDefEqUnitLike.WF_of_structureEta {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqUnitLike e₁ e₂)
      fun b _ => b = .true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqUnitLike
  refine (inferType.WF he₁).bind fun _ _ _
    ⟨ty₁', _aBelow, _aTerm, aType, aTyped⟩ => ?_
  refine (whnf.WF aType).bind fun normalizedType _ _
    ⟨_aWhnfBelow, tType', tTypeTr, tTypeEq⟩ => ?_
  split <;> [skip; exact .pure nofun]
  rename_i _ familyName hostLevels hhead
  refine .getEnv ?_
  refine (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ hfamily => ?_
  split <;> [skip; exact .pure nofun]
  rename_i _ familyDeclName familyLevelParams familyRawType hostNumParams
    familyAll ctorName familyNumNested familyUnsafe familyReflexive
  refine (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ hctor => ?_
  split <;> [skip; exact .pure nofun]
  rename_i _ ctorDeclName ctorLevelParams ctorRawType ctorInduct ctorIndex
    ctorNumParams ctorUnsafe
  split <;> [skip; exact .pure nofun]
  rename_i hstructure
  refine (inferType.WF he₂).bind fun _ _ _
    ⟨ty₂', _bBelow, _bTerm, bType, bTyped⟩ => ?_
  refine (isDefEqCore.WF tTypeTr bType).mono fun _ _ _ h hb => ?_
  let familyInfo : InductiveVal := {
    name := familyDeclName
    levelParams := familyLevelParams
    type := familyRawType
    numParams := hostNumParams
    numIndices := 0
    all := familyAll
    ctors := [ctorName]
    numNested := familyNumNested
    isRec := false
    isUnsafe := familyUnsafe
    isReflexive := familyReflexive }
  let constructorInfo : ConstructorVal := {
    name := ctorDeclName
    levelParams := ctorLevelParams
    type := ctorRawType
    induct := ctorInduct
    cidx := ctorIndex
    numParams := ctorNumParams
    numFields := 0
    isUnsafe := ctorUnsafe }
  obtain ⟨artifact⟩ := c.structureEtaReady.resolve familyName familyInfo ctorName
    constructorInfo hfamily hctor hstructure
  cases artifact with
  | ordinary artifact =>
    have ⟨head', hstack⟩ := AppStack.build <|
      normalizedType.mkAppList_getAppArgsList ▸ tTypeTr
    have hheadTr := hstack.tr
    rw [hhead] at hheadTr
    let .const (us' := levels) hconst hlevelsMap hlevelsHostLength := hheadTr
    have hviewFamily := artifact.projection.viewWF.family
    rw [artifact.projection.name_eq] at hviewFamily
    rw [hviewFamily] at hconst
    cases hconst
    have hlevelsWF : ∀ level ∈ levels,
        level.WF c.lparams.length :=
      VLevel.WF.of_mapM_ofLevel hlevelsMap
    have hsourceUvars :
        artifact.projection.view.familyRaw.uvars =
          artifact.projection.view.uvars :=
      artifact.projection.view.family_uvars_eq
    have hlevelsLength : levels.length = artifact.projection.view.uvars :=
      (List.mapM_eq_some.1 hlevelsMap).length_eq.symm.trans
        (hlevelsHostLength.trans hsourceUvars)
    have hfamilyHead : c.HasType (.const familyName levels)
        (artifact.projection.view.familyType.instL levels) :=
      by
        simpa [artifact.projection.name_eq] using
          artifact.projection.viewWF.familyConst_hasType c.Ewf.ordered
            (Γ := c.vlctx.toCtx) levels hlevelsWF hlevelsLength
    let rawParams := artifact.projection.view.rawParams.map
      (VExpr.instL levels)
    have hfamilyHeadShape : c.HasType (.const familyName levels)
        (VExpr.forallN rawParams
          (.sort (artifact.projection.view.resultLevel.inst levels))) := by
      simpa [rawParams, artifact.projection.view.familyType_eq_forallN,
        VExpr.instL_forallN, VExpr.forallN,
        VExpr.instL] using hfamilyHead
    have htTypeIsType : c.venv.IsType c.lparams.length c.vlctx.toCtx tType' :=
      (aTyped.isType c.Ewf.ordered c.Δwf).defeqU_l c.Ewf c.Δwf
        tTypeEq.symm
    have normalizedTypeTr : c.TrExprS
        (normalizedType.getAppFn.mkAppList normalizedType.getAppArgsList)
        tType' := by
      rw [normalizedType.mkAppList_getAppArgsList]
      exact tTypeTr
    obtain ⟨params, _hparamsTr, hparamsSpine, hfullTr⟩ :=
      AppStack.toSpineWF_of_isType
        (f := normalizedType.getAppFn)
        (args := normalizedType.getAppArgsList)
        (full' := tType') hstack hfamilyHeadShape
        normalizedTypeTr htTypeIsType
    have hparamsLength : params.length = artifact.projection.view.nparams :=
      hparamsSpine.forallN_sort_length.trans <| by
        simpa [rawParams] using
          artifact.projection.view.rawParams_length
    have hfamilyShape : artifact.projection.view.familyType.instL levels =
        VExpr.forallN rawParams
          (.sort (artifact.projection.view.resultLevel.inst levels)) := by
      simp [rawParams, artifact.projection.view.familyType_eq_forallN,
        VExpr.instL_forallN, VExpr.forallN, VExpr.instL]
    have hparamsFamily : c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (artifact.projection.view.familyType.instL levels) params
        (.sort (artifact.projection.view.resultLevel.inst levels)) := by
      rw [hfamilyShape]
      exact hparamsSpine
    have hfullStruct : c.TrExprS normalizedType
        (artifact.projection.view.structureType levels params) := by
      rw [← normalizedType.mkAppList_getAppArgsList]
      simpa [VProjectionView.structureType,
        artifact.projection.name_eq] using hfullTr
    have hfullEq := hfullStruct.uniq c.Ewf (.refl c.Ewf c.Δwf) tTypeTr
    have hstructTy₁ := VEnv.IsDefEqU.trans c.Ewf c.Δwf hfullEq tTypeEq
    have hstructTy₂ := VEnv.IsDefEqU.trans c.Ewf c.Δwf hfullEq (h hb)
    have haStruct := aTyped.defeqU_r c.Ewf c.Δwf hstructTy₁.symm
    have hbStruct := bTyped.defeqU_r c.Ewf c.Δwf hstructTy₂.symm
    have heta₁ := artifact.eta c.Ewf c.Δwf hlevelsWF hlevelsLength
      hparamsLength ⟨_, hparamsFamily⟩ haStruct
    have heta₂ := artifact.eta c.Ewf c.Δwf hlevelsWF hlevelsLength
      hparamsLength ⟨_, hparamsFamily⟩ hbStruct
    have hfieldsLength : artifact.projection.view.fields.length = 0 := by
      calc
        artifact.projection.view.fields.length =
            artifact.projection.constructorInfo.numFields :=
          artifact.projection.constructor_numFields_eq.symm
        _ = constructorInfo.numFields :=
          congrArg ConstructorVal.numFields artifact.constructor_info_eq
        _ = 0 := rfl
    have hfields : artifact.projection.view.fields = [] :=
      List.length_eq_zero_iff.mp hfieldsLength
    have hrebuild :
        artifact.projection.view.etaRebuild levels params e₁' =
          artifact.projection.view.etaRebuild levels params e₂' := by
      simp [VProjectionView.etaRebuild, VProjectionView.projectionArgs,
        VProjectionView.specializedFields_eq, hfields]
    rw [hrebuild] at heta₁
    exact VEnv.IsDefEqU.trans c.Ewf c.Δwf ⟨_, heta₁.symm⟩ ⟨_, heta₂⟩
  | restored artifact =>
    have ⟨head', hstack⟩ := AppStack.build <|
      normalizedType.mkAppList_getAppArgsList ▸ tTypeTr
    have hheadTr := hstack.tr
    rw [hhead] at hheadTr
    let .const (us' := levels) hconst hlevelsMap hlevelsHostLength := hheadTr
    have hviewFamily := artifact.projection.viewWF.family
    rw [artifact.projection.name_eq] at hviewFamily
    rw [hviewFamily] at hconst
    cases hconst
    have hlevelsWF : ∀ level ∈ levels,
        level.WF c.lparams.length :=
      VLevel.WF.of_mapM_ofLevel hlevelsMap
    have hsourceUvars :
        artifact.projection.view.sourceFamily.uvars =
          artifact.projection.view.uvars :=
      artifact.projection.view.family_uvars_eq
    have hlevelsLength : levels.length = artifact.projection.view.uvars :=
      (List.mapM_eq_some.1 hlevelsMap).length_eq.symm.trans
        (hlevelsHostLength.trans hsourceUvars)
    have hfamilyHead : c.HasType (.const familyName levels)
        (artifact.projection.view.familyType.instL levels) :=
      by
        simpa [artifact.projection.name_eq] using
          artifact.projection.viewWF.familyConst_hasType c.Ewf.ordered
            (Γ := c.vlctx.toCtx) levels hlevelsWF hlevelsLength
    let rawParams := artifact.projection.view.rawParams.map
      (VExpr.instL levels)
    have hfamilyHeadShape : c.HasType (.const familyName levels)
        (VExpr.forallN rawParams
          (.sort (artifact.projection.view.resultLevel.inst levels))) := by
      simpa [rawParams, artifact.projection.view.familyType_eq_forallN,
        VExpr.instL_forallN, VExpr.forallN,
        VExpr.instL] using hfamilyHead
    have htTypeIsType : c.venv.IsType c.lparams.length c.vlctx.toCtx tType' :=
      (aTyped.isType c.Ewf.ordered c.Δwf).defeqU_l c.Ewf c.Δwf
        tTypeEq.symm
    have normalizedTypeTr : c.TrExprS
        (normalizedType.getAppFn.mkAppList normalizedType.getAppArgsList)
        tType' := by
      rw [normalizedType.mkAppList_getAppArgsList]
      exact tTypeTr
    obtain ⟨params, _hparamsTr, hparamsSpine, hfullTr⟩ :=
      AppStack.toSpineWF_of_isType
        (f := normalizedType.getAppFn)
        (args := normalizedType.getAppArgsList)
        (full' := tType') hstack hfamilyHeadShape
        normalizedTypeTr htTypeIsType
    have hparamsLength : params.length = artifact.projection.view.nparams :=
      hparamsSpine.forallN_sort_length.trans <| by
        simpa [rawParams] using
          artifact.projection.view.rawParams_length
    have hfamilyShape : artifact.projection.view.familyType.instL levels =
        VExpr.forallN rawParams
          (.sort (artifact.projection.view.resultLevel.inst levels)) := by
      simp [rawParams, artifact.projection.view.familyType_eq_forallN,
        VExpr.instL_forallN, VExpr.forallN, VExpr.instL]
    have hparamsFamily : c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (artifact.projection.view.familyType.instL levels) params
        (.sort (artifact.projection.view.resultLevel.inst levels)) := by
      rw [hfamilyShape]
      exact hparamsSpine
    have hfullStruct : c.TrExprS normalizedType
        (artifact.projection.view.structureType levels params) := by
      rw [← normalizedType.mkAppList_getAppArgsList]
      simpa [VRestoredBlockStructureView.structureType,
        artifact.projection.name_eq] using hfullTr
    have hfullEq := hfullStruct.uniq c.Ewf (.refl c.Ewf c.Δwf) tTypeTr
    have hstructTy₁ := VEnv.IsDefEqU.trans c.Ewf c.Δwf hfullEq tTypeEq
    have hstructTy₂ := VEnv.IsDefEqU.trans c.Ewf c.Δwf hfullEq (h hb)
    have haStruct := aTyped.defeqU_r c.Ewf c.Δwf hstructTy₁.symm
    have hbStruct := bTyped.defeqU_r c.Ewf c.Δwf hstructTy₂.symm
    have heta₁ := artifact.eta c.Ewf c.Δwf hlevelsWF hlevelsLength
      hparamsLength ⟨_, hparamsFamily⟩ haStruct
    have heta₂ := artifact.eta c.Ewf c.Δwf hlevelsWF hlevelsLength
      hparamsLength ⟨_, hparamsFamily⟩ hbStruct
    have hfieldsLength : artifact.projection.view.fields.length = 0 := by
      calc
        artifact.projection.view.fields.length =
            artifact.projection.constructorInfo.numFields :=
          artifact.projection.constructor_numFields_eq.symm
        _ = constructorInfo.numFields :=
          congrArg ConstructorVal.numFields artifact.constructor_info_eq
        _ = 0 := rfl
    have hfields : artifact.projection.view.fields = [] :=
      List.length_eq_zero_iff.mp hfieldsLength
    have hrebuild :
        artifact.projection.view.operationalEtaRebuild levels params e₁' =
          artifact.projection.view.operationalEtaRebuild levels params e₂' := by
      simp [VRestoredBlockStructureView.operationalEtaRebuild, VRestoredBlockStructureView.operationalProjectionArgs,
        VRestoredBlockStructureView.specializedFields, hfields]
    rw [hrebuild] at heta₁
    exact VEnv.IsDefEqU.trans c.Ewf c.Δwf ⟨_, heta₁.symm⟩ ⟨_, heta₂⟩

theorem isDefEqUnitLike.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqUnitLike e₁ e₂) fun b _ => b = .true → c.IsDefEqU e₁' e₂' :=
  isDefEqUnitLike.WF_of_structureEta he₁ he₂

theorem lazyDeltaProjReduction.finish.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS (.proj n₁ i e₁) e₁') (he₂ : c.TrExprS (.proj n₂ i e₂) e₂') :
    (finish i e₁ e₂).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
  unfold finish
  refine (reduceProjCore.WF he₁).bind fun _ _ _ h1 => ?_; extract_lets F
  have hF {s} : (F ⟨⟩).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
    have .proj a1 a2 := he₁; have .proj b1 b2 := he₂
    refine (isDefEqCore.WF a1 b1).mono fun _ _ _ h hb => ?_
    exact a2.uniq c.Ewf (.refl c.Δwf.toCtx) b2 (h hb)
  split <;> [have ⟨a1, _, a2, a3⟩ := h1 _ rfl; exact .pureBind hF]
  refine (reduceProjCore.WF he₂).bind fun _ _ _ h2 => ?_
  split <;> [have ⟨b1, _, b2, b3⟩ := h2 _ rfl; exact .pureBind hF]
  exact (isDefEqCore.WF a2 b2).mono fun _ _ _ h hb =>
    a3.symm.trans c.Ewf c.Δwf <| (h hb).trans c.Ewf c.Δwf b3

theorem lazyDeltaProjReduction.loop.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS (.proj n₁ i e₁) e₁') (he₂ : c.TrExprS (.proj n₂ i e₂) e₂') :
    (loop i e₁ e₂ n).WF c s fun r _ => r → c.IsDefEqU e₁' e₂' := by
  induction n generalizing s e₁ e₂ e₁' e₂' with | zero => exact .throw | succ n ih
  unfold loop; have .proj a1 a2 := he₁; have .proj b1 b2 := he₂
  refine (lazyDeltaReductionStep.WF a1 b1).bind fun _ _ _ h => ?_; split
  · have ⟨_, ⟨_, c1, c2⟩, ⟨_, d1, d2⟩⟩ := h
    have ⟨_, e1⟩ := a2.defeqDFC c.Ewf (.refl c.Δwf.toCtx) c2.symm
    have ⟨_, e2⟩ := b2.defeqDFC c.Ewf (.refl c.Δwf.toCtx) d2.symm
    refine (ih (.proj c1 e1) (.proj d1 e2)).mono fun _ _ _ h hb => ?_
    have f1 := e1.uniq c.Ewf (.refl c.Δwf.toCtx) a2 c2
    have f2 := e2.uniq c.Ewf (.refl c.Δwf.toCtx) b2 d2
    exact f1.symm.trans c.Ewf c.Δwf <| (h hb).trans c.Ewf c.Δwf f2
  · exact .pure fun _ => a2.uniq c.Ewf (.refl c.Δwf.toCtx) b2 h
  all_goals
    have ⟨⟨_, c1, c2⟩, ⟨_, d1, d2⟩⟩ := h
    have ⟨_, e1⟩ := a2.defeqDFC c.Ewf (.refl c.Δwf.toCtx) c2.symm
    have ⟨_, e2⟩ := b2.defeqDFC c.Ewf (.refl c.Δwf.toCtx) d2.symm
    refine (finish.WF (.proj c1 e1) (.proj d1 e2)).mono fun _ _ _ h hb => ?_
    have f1 := e1.uniq c.Ewf (.refl c.Δwf.toCtx) a2 c2
    have f2 := e2.uniq c.Ewf (.refl c.Δwf.toCtx) b2 d2
    exact f1.symm.trans c.Ewf c.Δwf <| (h hb).trans c.Ewf c.Δwf f2

theorem isDefEqCore'.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqCore' e₁ e₂) fun b _ => b = true → c.IsDefEqU e₁' e₂' := by
  unfold isDefEqCore'; extract_lets F1
  refine (quickIsDefEq.WF he₁ he₂).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun hb => h (by simpa using hb); skip]
  refine .readThe ?_
  suffices ∀ {s}, RecM.WF c s (F1 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split <;> [rename_i h1; exact this]
    refine (whnf.WF he₁).bind fun _ _ _ ⟨_, _, a1, a2⟩ => ?_
    split <;> [rename_i h2; exact this]
    refine .pure fun _ => ?_
    simp [Expr.isConstOf] at h1 h2
    split at h1 <;> simp at h1; cases h1.2; split at h2 <;> simp at h2; cases h2
    let .const b1 b2 b3 := he₂
    let .const c1 c2 c3 := a1
    cases c.hasPrimitives.boolTrue b1
    cases c.hasPrimitives.boolTrue c1
    simp at b3 c3; subst b3 c3; simp at b2 c2; subst b2 c2
    exact a2.symm
  intro; unfold F1
  refine (whnfCore.WF he₁).bind fun _ _ _ ⟨_, e₁', a1, a2⟩ => ?_
  refine (whnfCore.WF he₂).bind fun _ _ _ ⟨_, e₂', b1, b2⟩ => ?_
  extract_lets F2
  refine .mono (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h hb =>
    a2.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf b2
  suffices ∀ {s}, RecM.WF c s (F2 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split <;> [skip; exact this]
    refine (quickIsDefEq.WF a1 b1).bind fun _ _ _ h => ?_
    split <;> [skip; exact this]
    exact .pure fun hb => h (by simpa using hb)
  intro; unfold F2
  refine (isDefEqProofIrrel.WF a1 b1).bind fun _ _ _ h => ?_
  split
  · exact .pure fun hb => h (by simpa using hb)
  refine (lazyDeltaReduction.loop.WF a1 b1).readThe.bind fun _ _ _ h => ?_; split
  · cases h.1
  · exact .pure fun _ => h
  · exact .pure nofun
  have ⟨⟨e₁', c1, c4⟩, ⟨e₂', d1, d4⟩⟩ := h
  refine .mono (Q := fun b _ => b = true → c.IsDefEqU e₁' e₂') ?_ fun _ _ _ h hb =>
    c4.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf d4
  extract_lets F3
  suffices ∀ {s}, RecM.WF c s (F3 ⟨⟩) fun b _ => b = true → c.IsDefEqU e₁' e₂' by
    split
    · split <;> [rename_i h2; exact this]
      refine .pure fun _ => ?_
      simp at h2; cases h2.1
      have .const c1 c2 c3 := c1; have .const d1 d2 d3 := d1
      cases d1.symm.trans c1
      have := VEnv.IsDefEq.constDF c1
        (Γ := c.vlctx.toCtx) (.of_mapM_ofLevel c2) (.of_mapM_ofLevel d2)
        ((List.mapM_eq_some.1 c2).length_eq.symm.trans c3)
        (Level.isEquivList_wf h2.2 c2 d2)
      exact this.toU
    · split <;> [rename_i h; exact this]
      simp at h; subst h
      exact .pure fun _ => c1.uniq c.Ewf (.refl c.Ewf c.Δwf) d1
    · split <;> [rename_i h2; exact this]; simp at h2; subst h2
      refine (lazyDeltaProjReduction.loop.WF c1 d1).bind fun _ _ _ h => ?_
      split <;> [refine .pure fun _ => h ‹_›; exact this]
    · exact this
  intro; unfold F3
  refine (whnfCore.WF c1).bind fun _ _ _ ⟨_, e₁'', c5, c6⟩ => ?_
  refine (whnfCore.WF d1).bind fun _ _ _ ⟨_, e₂'', d5, d6⟩ => ?_
  split
  · exact (isDefEqCore.WF c5 d5).mono fun _ _ _ h hb =>
      c6.symm.trans c.Ewf c.Δwf (h (by simpa using hb)) |>.trans c.Ewf c.Δwf d6
  refine (isDefEqApp.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryEtaExpansion.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryEtaStruct.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  refine (tryStringLitExpansion.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun hb => h (by simpa using hb); skip]
  refine (isDefEqUnitLike.WF c1 d1).bind fun _ _ _ h => ?_
  split <;> [exact .pure fun _ => h ‹_›; skip]
  exact .pure nofun
