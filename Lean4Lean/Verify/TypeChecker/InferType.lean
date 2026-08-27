/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.EquivManager

open Lean4Lean

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem ensureForallCore.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi := by
  simp [ensureForallCore]; split
  · let .forallE .. := e
    exact .pure ⟨.rfl, he.trExpr c.Ewf c.Δwf, _, _, _, _, rfl⟩
  refine (whnf.WF he).bind fun e _ _ ⟨hb, he⟩ => ?_; split
  · let .forallE .. := e
    exact .pure ⟨hb, he, _, _, _, _, rfl⟩
  exact .getEnv <| .getLCtx .throw

theorem ensureForallCore.WF' {c : VContext} {s : VState} (he : c.TrExpr e e') :
    RecM.WF c s (ensureForallCore e e₀) fun e1 _ => c.FVarsBelow e e1 ∧
      c.TrExpr e1 e' ∧ ∃ name ty body bi, e1 = .forallE name ty body bi :=
  let ⟨_, he, eq⟩ := he
  (ensureForallCore.WF he).mono fun _ _ _ ⟨h1, h2, h3⟩ =>
    ⟨h1, h2.defeq c.Ewf c.Δwf eq, h3⟩

theorem checkLevel.WF {c : VContext} (H : l.hasMVar' = false) :
    (checkLevel c.toContext l).WF fun _ => ∃ u', VLevel.ofLevel c.lparams l = some u' := by
  simp [checkLevel]; split <;> [exact .throw; refine .pure ?_]
  exact Level.getUndefParam_none H (by rename_i h; simpa using h)

theorem inferFVar.WF {c : VContext} :
    (inferFVar c.toContext name).WF fun ty => ∃ e' ty', c.TrTyping (.fvar name) ty e' ty' := by
  simp [inferFVar, ← c.lctx_eq]; split <;> [refine .pure ?_; exact .throw]
  rename_i decl h
  rw [c.trlctx.1.find?_eq_find?_toList] at h
  have := List.find?_some h; simp at this; subst this
  let ⟨e', ty', h1, _, h2, _, h3⟩ :=
    c.trlctx.find?_of_mem c.Ewf (List.mem_of_find?_eq_some h)
  exact ⟨_, _, h2, .fvar h1, h3, c.Δwf.find?_wf c.Ewf h1⟩

theorem inferConstant.WF {c : VContext}
    (H : ∀ l ∈ ls, l.hasMVar' = false)
    (hinf : inferOnly = true → ∃ e', c.TrExprS (.const name ls) e') :
    (inferConstant c.toContext name ls inferOnly).WF fun ty =>
      ∃ e' ty', c.TrTyping (.const name ls) ty e' ty' := by
  simp [inferConstant]; refine envGet.WF.bind fun ci eq1 => ?_
  have : (ls.foldlM (fun b a => checkLevel c.toContext a) PUnit.unit).WF fun _ =>
      ∃ ls', ls.Forall₂ (VLevel.ofLevel c.lparams · = some ·) ls' := by
    clear hinf
    induction ls with
    | nil => exact .pure ⟨_, .nil⟩
    | cons l ls ih =>
      simp at H
      refine (checkLevel.WF H.1).bind fun ⟨⟩ ⟨_, h1⟩ => ?_
      exact (ih H.2).le fun _ ⟨_, h2⟩ => ⟨_, .cons h1 h2⟩
  split <;> [rename_i h1; exact .throw]
  have main {e'} (he : c.TrExprS (.const name ls) e') : ∃ e' ty',
      c.TrTyping (.const name ls) (ci.instantiateTypeLevelParamsCpp ls) e' ty' := by
    let .const h4 H' eq := id he
    have ⟨_, _, h5, h6⟩ := c.trenv.find?_uniq eq1 h4
    have H := List.mapM_eq_some.1 H'
    have s0 := h6.instLCpp c.Ewf (Δ := []) trivial H' (h5.trans eq.symm)
    have s1 := s0.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
    rw [(c.Ewf.ordered.closedC h4).instL.liftN_eq (Nat.le_refl _)] at s1
    have ⟨_, s1, s2⟩ := s1
    refine ⟨_, _, ?_, he, s1, .defeqU_r c.Ewf c.Δwf s2.symm ?_⟩
    · intro _ _ _; exact s0.fvarsIn.mono nofun
    · exact .const h4 (.of_mapM_ofLevel H') (H.length_eq.symm.trans eq)
  split
  · split <;> [exact .throw; rename_i h2]
    generalize eq1 : _ <$> (_ : Except Exception _) = F
    generalize eq2 : (fun ty : Expr => _) = P
    suffices ci.isPartial = false ∨ c.safety ≠ .safe → F.WF P by
      split <;> [skip; exact this (.inl (ConstantInfo.isPartial.eq_2 _ ‹_›))]
      split <;> [exact .throw; apply this]
      rename_i h; simpa [Decidable.or_iff_not_imp_left, ConstantInfo.isPartial] using h
    subst eq1 eq2; intro h3
    refine this.map fun _ ⟨_, H⟩ => ?_
    have ⟨_, h4, _, h5, h6⟩ := c.trenv.find? eq1 <| by
      revert h2 h3
      simp [ConstantInfo.safety]
      split <;> simp +contextual [*]
      split <;> simp [DefinitionSafety.le_safe, *]
      cases c.safety <;> decide
    have eq := h1.symm.trans h5
    exact main (.const h4 (List.mapM_eq_some.2 H) eq)
  · simp_all; let ⟨_, h⟩ := hinf; refine .pure (main h)

theorem inferLambda.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLambda n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei ∧
      ∀ ty, FVarsIn (AllAbove c.vlctx P) ty → FVarsIn (AllAbove c.vlctx P) (m.mkForall n hn ty))
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLambda.loop inferOnly arr e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' ty', c.TrTyping e₀ ty e' ty' := by
  unfold inferLambda.loop
  have harr0 : ∀ x ∈ arr.reverse, x.looseBVarRange' = 0 := by
    intro x hx
    have : x ∈ (m.fvarRevList n hn).map Expr.fvar :=
      harr ▸ List.mem_reverse.2 (by simpa using hx)
    simp at this
    obtain ⟨_, _, rfl⟩ := this
    rfl
  have hrev (e : Expr) :
      e.instantiateRev arr = e.instantiateList arr.toList.reverse := by
    rw [Expr.instantiateRev_eq, Expr.instantiate_eq _ _ (Or.inr harr0)]
    simp
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  simp [hrev, harr, -bind_pure_comp]
  split
  · rename_i name dom body bi
    generalize eqF : withLocalDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ∃ _, _) = P
    rw [Expr.instantiateList_lam] at hei; subst ei
    have main {s₁} (le₁ : s ≤ s₁) {dom'}
        (domty : (c.withMLC m).venv.IsType
          (c.withMLC m).lparams.length (c.withMLC m).vlctx.toCtx dom')
        (hdom : (c.withMLC m).TrExprS (dom.instantiateList fvs) dom')
        (hbody : inferOnly = true → ∃ body',
          TrExprS c.venv c.lparams ((none, .vlam dom') :: m.vlctx)
            (body.instantiateList fvs 1) body') :
        F.WF (c.withMLC m) s₁ P := by
      refine .stateWF fun wf => ?_
      have hdom' := hdom.trExpr c.Ewf mwf.1.tr.wf
      subst eqF eqP
      refine .withLocalDecl hdom domty le₁ fun a mwf' s' le₂ res => ?_
      have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
      refine inferLambda.loop.WF (Nat.succ_le_succ hn) (by simp [hdrop])
        (by simp [← eqfvs, harr]) ?_ (by simp; rfl) ?_ (hr.2.mono fun _ => .tail _) ?_
      · rw [he₀, eqfvs, ← eq]; simp; congr 2
        refine (FVarsIn.abstract_instantiate1 ((hr.2.instantiateList ?_ _).mono ?_)).symm
        · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
        · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
      · intro P hP he
        have ⟨h1, h2, h3⟩ := hbelow _ hP he
        refine ⟨⟨h1, fun _ => (fvarsIn_iff.1 h2.1).1⟩, ?_, fun ty hty => h3 _ ⟨h2.1, hty.abstract1⟩⟩
        rw [eqfvs, ← eq]
        refine h2.2.instantiate1 fun h => ?_
        exact res.elim (wf.ngen_wf _ (m.dropN_fvars_subset n hn (hdrop ▸ h)))
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
    split
    · subst inferOnly
      refine (checkType.WF ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
      · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (ensureSortCore.WF h2).bind_le le fun _ _ le ⟨h4, h5, _⟩ => ?_
      obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort _, h5⟩ := h5
      have domty := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
      have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
      exact main le domty' h1 nofun
    · simp_all; let ⟨_, h1⟩ := hinf
      have .lam (ty' := dom') (body' := body') domty hdom hbody := h1
      exact main .rfl domty hdom _ hbody
  · subst ei
    refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', hb, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, h2', e2⟩ := h2.trExpr c.Ewf.ordered wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2''⟩ := mwf.1.mkLambda_trS c.Ewf h1 h3 n hn
    have h3' := (mwf.1.mkForall_trS c.Ewf h2' (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2'' h3'
    refine mwf.1.mkForall_eq _ _
      (m.noBV ▸ h2'.closed).looseBVarRange_zero (eqfvs ▸ harr) ▸
      ⟨_, _, fun P hP he => ?_, he₀ ▸ h1', h3', h2''⟩
    have ⟨c1, c2, c3⟩ := hbelow _ hP he
    have := c3 _ <| FVarsBelow.cheapBetaReduce (m.noBV ▸ h2.closed) _ c1 <| hb _ c1 c2
    exact this.mp (fun _ => id) h3'.fvarsIn

theorem inferLambda.WF
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLambda e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferLambda.loop.WF (Nat.zero_le _) rfl rfl rfl rfl ?_ h1) hinf
  exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h, fun _ => id⟩

theorem inferForall.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkForall n hn ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hus : us.toList.reverse.Forall₂ (VLevel.ofLevel c.lparams · = some ·) us')
    (hΔ : m.vlctx.SortList c.venv c.lparams.length us')
    (hlen : us'.length = n)
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferForall.loop inferOnly arr us e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' u, c.TrTyping e₀ ty e' (.sort u) := by
  unfold inferForall.loop
  have harr0 : ∀ x ∈ arr.reverse, x.looseBVarRange' = 0 := by
    intro x hx
    have : x ∈ (m.fvarRevList n hn).map Expr.fvar :=
      harr ▸ List.mem_reverse.2 (by simpa using hx)
    simp at this
    obtain ⟨_, _, rfl⟩ := this
    rfl
  have hrev (e : Expr) :
      e.instantiateRev arr = e.instantiateList arr.toList.reverse := by
    rw [Expr.instantiateRev_eq, Expr.instantiate_eq _ _ (Or.inr harr0)]
    simp
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  simp [hrev, harr, -bind_pure_comp]
  split
  · rename_i name dom body bi
    rw [Expr.instantiateList_forallE] at hei; subst ei
    refine (inferType.WF' ?_ ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
    · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    · intro h; let ⟨_, .forallE _ _ h _⟩ := hinf h; exact ⟨_, h⟩
    refine (ensureSortCore.WF h2).bind_le le fun _ _ le ⟨h4, h5, _⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort h4, h5⟩ := h5
    refine .stateWF fun wf => ?_
    have domty := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
    have domty' : (c.withMLC m).IsType dom' := ⟨_, domty⟩
    refine .withLocalDecl h1 domty' le fun a mwf' s' le₂ res => ?_
    have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
    refine inferForall.loop.WF (Nat.succ_le_succ hn) (by simp [hdrop])
      (by simp [eqfvs, harr]) ?_ (by simp [eqfvs]; rfl) (hr.2.mono fun _ => .tail _)
      (by simpa using ⟨h4, hus⟩) (.cons hΔ domty) (by simp [hlen]) ?_
    · simp [he₀, ← eq]; congr 2
      refine (FVarsIn.abstract_instantiate1 ((hr.2.instantiateList ?_ _).mono ?_)).symm
      · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
      · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
    · intro h; let ⟨_, .forallE (body' := body') _ _ hdom₁ hbody₁⟩ := hinf h
      refine have hΔ := .refl c.Ewf mwf.1.tr.wf; have H := hdom₁.uniq c.Ewf hΔ h1; ?_
      have H := H.of_r c.Ewf mwf.1.tr.wf.toCtx domty
      have ⟨_, hbody₂⟩ := hbody₁.defeqDFC c.Ewf <| .cons hΔ (ofv := none) nofun (.vlam H)
      exact eq ▸ ⟨_, hbody₂.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
  · subst ei; refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', _, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine (ensureSortCore.WF h2).bind fun _ _ le₂ ⟨h4, h5, _⟩ => ?_
    obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort (u' := u') h4, h5⟩ := h5
    obtain ⟨us, rfl⟩ : ∃ l, ⟨List.reverse l⟩ = us := ⟨us.toList.reverse, by simp⟩
    simp [Expr.sortLevel!] at hus ⊢
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx h5.symm
    let ⟨h1', h2'⟩ := mwf.1.mkForall_trS c.Ewf h1 ⟨_, h3⟩ n hn
    have ⟨_, h3', h4'⟩ := mkForall_hasType hus hΔ h4 h3 n hn (hus.length_eq.trans hlen)
    simp [hdrop] at h1' h2' h4'
    refine have h := .sort h3'; .pure ⟨_, _, fun _ _ _ => h.fvarsIn, he₀ ▸ h1', h, h4'⟩

theorem inferForall.WF
    (hr : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferForall e inferOnly).WF c s fun ty _ => ∃ e' u, c.TrTyping e ty e' (.sort u) :=
  (c.withMLC_self ▸ inferForall.loop.WF (Nat.zero_le _) rfl rfl rfl rfl hr .nil .nil rfl) hinf

theorem inferApp.loop.WF {c : VContext} {s : VState}
    {ll lm lr : List _}
    (stk : AppStack c.venv c.lparams c.vlctx (.mkAppRevList e lm) e' lr)
    (hbelow : FVarsBelow c.vlctx e fType)
    (hfty : c.TrExpr (fType.instantiateList lm) fty') (hety : c.HasType e' fty')
    (hargs : args = ll ++ lm.reverse ++ lr)
    (hj : j = ll.length) (hi : i = ll.length + lm.length)
    (hlm : ∀ x ∈ lm, x.looseBVarRange' = 0) :
    RecM.WF c s (inferApp.loop e₀ ⟨args⟩ fType j i) fun ty _ =>
      ∃ e₁' ty', c.TrTyping (e.mkAppRevList lm |>.mkAppList lr) ty e₁' ty' := by
  subst i j; rw [inferApp.loop.eq_def]
  simp [hargs]
  have henv := c.Ewf; have hΔ := c.Δwf
  have hrev (l : List Expr) (hl : ∀ x ∈ l, x.looseBVarRange' = 0) (e : Expr) :
      e.instantiate l.toArray = e.instantiateList l :=
    (Expr.instantiate_eq _ _ (Or.inr (by simpa using hl))).trans (by simp)
  have hrev0 := hrev lm hlm
  have hrevRange (g : Expr) (pre post : List Expr) :
      g.instantiateRevRange pre.length (pre.length + lm.length)
          (pre ++ (lm.reverse ++ post)).toArray =
        g.instantiateList lm := by
    rw [Expr.instantiateRevRange_eq _ _ (by omega) (by simp), Expr.instantiateRev_eq]
    rw [← hrev0 g]
    congr 1
    rw [← Array.toList_inj]
    simp
  cases lr with simp
  | cons a lr =>
    let .app hf' ha' hf ha stk := stk
    have uf := hf'.uniqU henv hΔ hety
    have ha0 := c.mlctx.noBV ▸ ha.closed
    split
    · rw [Expr.instantiateList_forallE] at hfty
      let ⟨_, .forallE _ _ hty hbody, h3⟩ := hfty
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF (lm := a::lm) stk ?_ ?_ (.app hf' ha') (by simp) rfl rfl
        (by simp; exact ⟨ha0.looseBVarRange_zero, hlm⟩)
      · exact fun _ hP he => (hbelow _ hP he).2
      simp [← Expr.instantiateList_instantiate1_comm ha0.looseBVarRange_zero]
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
    · rw [hrevRange]
      refine (ensureForallCore.WF' hfty).bind fun _ _ _ ⟨hb, ⟨_, h2, h3⟩, eq⟩ => ?_
      obtain ⟨name, ty, body, bi, rfl⟩ := eq; simp [Expr.bindingBody!]
      let .forallE _ _ hty hbody := h2
      have ⟨⟨_, uA⟩, _, uB⟩ := h3.trans henv hΔ uf.symm |>.forallE_inv henv hΔ
      refine inferApp.loop.WF (ll := ll ++ lm.reverse) (lm := [a]) stk ?_ ?_
        (.app hf' ha') (by simp) (by simp) (by simp)
        (by simpa using ha0.looseBVarRange_zero)
      · intro _ hP he
        have ⟨he, hlm⟩ := FVarsIn.appRevList.1 he
        exact (hb _ hP <| (hbelow _ hP he).instantiateList hlm).2
      exact .inst henv hΔ (ha'.defeqU_r henv hΔ ⟨_, uA.symm⟩) ⟨_, hbody, _, uB⟩ (ha.trExpr henv hΔ)
  | nil =>
    have hrange := hrevRange fType ll []
    simp at hrange
    rw [hrange]
    have ⟨_, hfty, h2⟩ := hfty
    refine .pure ⟨_, _, fun _ hP he => ?_, stk.tr, hfty, hety.defeqU_r henv hΔ h2.symm⟩
    have ⟨he, hlm⟩ := FVarsIn.appRevList.1 he
    exact (hbelow _ hP he).instantiateList hlm

theorem inferApp.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (inferApp e) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' := by
  rw [inferApp, Expr.withApp_eq, Expr.getAppArgs_eq]
  have ⟨_, he'⟩ := AppStack.build <| e.mkAppList_getAppArgsList ▸ he
  refine (inferType.WF he'.tr).bind fun ty _ _ ⟨ty', hb, _, hty', ety⟩ => ?_
  have henv := c.Ewf; have hΔ := c.Δwf
  refine (inferApp.loop.WF (ll := []) (lm := []) he' hb
      (hty'.trExpr henv hΔ) ety rfl rfl rfl (by simp)).le
    fun _ _ _ ⟨_, _, hb, h1, h2, h3⟩ => ?_
  have := (e.mkAppList_getAppArgsList ▸ h1).uniq henv (.refl henv hΔ) he
  exact ⟨_, e.mkAppList_getAppArgsList ▸ hb, he, h2, h3.defeqU_l henv hΔ this⟩

theorem inferLet.loop.WF {c : VContext} {e₀ : Expr}
    {m} [mwf : c.MLCWF m] {n} (hn : n ≤ m.length) (nds hnds)
    (hdrop : m.dropN n hn = c.mlctx)
    (harr : arr.toList.reverse = (m.fvarRevList n hn).map .fvar)
    (he₀ : e₀ = m.mkLet n hn nds hnds ei)
    (hei : e.instantiateList ((m.fvarRevList n hn).map .fvar) = ei)
    (hbelow : ∀ P, IsFVarUpSet P c.vlctx → FVarsIn P e₀ →
      IsFVarUpSet (AllAbove c.vlctx P) m.vlctx ∧ FVarsIn (AllAbove c.vlctx P) ei ∧
      ∀ ty, FVarsIn (AllAbove c.vlctx P) ty → FVarsIn (AllAbove c.vlctx P) (m.mkForall n hn ty))
    (hr : e.FVarsIn (· ∈ m.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', (c.withMLC m).TrExprS ei e') :
    (inferLet.loop inferOnly arr e).WF (c.withMLC m) s fun ty _ =>
      ∃ e' ty', c.TrTyping e₀ ty e' ty' := by
  have harr0 : ∀ x ∈ arr.reverse, x.looseBVarRange' = 0 := by
    intro x hx
    have : x ∈ (m.fvarRevList n hn).map Expr.fvar :=
      harr ▸ List.mem_reverse.2 (by simpa using hx)
    simp at this
    obtain ⟨_, _, rfl⟩ := this
    rfl
  have hrev (e : Expr) :
      e.instantiateRev arr = e.instantiateList arr.toList.reverse := by
    rw [Expr.instantiateRev_eq, Expr.instantiate_eq _ _ (Or.inr harr0)]
    simp
  generalize eqfvs : (m.fvarRevList n hn).map Expr.fvar = fvs at *
  unfold inferLet.loop
  simp [hrev, harr, -bind_pure_comp]
  split
  · rename_i name dom val body nd
    generalize eqF : withLetDecl (m := RecM) _ _ _ _ = F
    generalize eqP : (fun ty x => ∃ _, _) = P
    rw [Expr.instantiateList_letE] at hei; subst ei
    have main {s₁} (le₁ : s ≤ s₁) {dom' val'}
        (hdom : (c.withMLC m).TrExprS (dom.instantiateList fvs) dom')
        (hval : (c.withMLC m).TrExprS (val.instantiateList fvs) val')
        (valty : (c.withMLC m).venv.HasType
          (c.withMLC m).lparams.length (c.withMLC m).vlctx.toCtx val' dom')
        (hbody : inferOnly = true → ∃ body',
          TrExprS c.venv c.lparams ((none, .vlet dom' val') :: m.vlctx)
            (body.instantiateList fvs 1) body') :
        F.WF (c.withMLC m) s₁ P := by
      refine .stateWF fun wf => ?_
      have hdom' := hdom.trExpr c.Ewf mwf.1.tr.wf
      subst eqF eqP
      refine .withLetDecl hdom hval valty le₁ fun a mwf' s' le₂ res => ?_
      have eq := @Expr.instantiateList_instantiate1_comm body fvs (.fvar a) (by trivial)
      refine inferLet.loop.WF (Nat.succ_le_succ hn) (some nd :: nds)
        (by simp [hnds]) (by simp [hdrop]) (by simp [← eqfvs, harr])
        ?_ (by simp; rfl) ?_ (hr.2.2.mono fun _ => .tail _) ?_
      · rw [he₀, eqfvs, ← eq]; simp [MLCtx.mkLetArg]; congr 2
        refine (FVarsIn.abstract_instantiate1 ((hr.2.2.instantiateList ?_ _).mono ?_)).symm
        · simp [← eqfvs, FVarsIn]; exact m.fvarRevList_prefix.subset
        · rintro _ h rfl; exact (mwf'.1.tr.wf.2.1 _ _ rfl).1 h
      · intro P hP he
        have ⟨h1, h2, h3⟩ := hbelow _ hP he
        refine ⟨⟨h1, fun _ => ?_⟩, ?_, fun ty hty => h3 _ ?_⟩
        · simp [or_imp, forall_and]
          exact ⟨(fvarsIn_iff.1 h2.1).1, (fvarsIn_iff.1 h2.2.1).1⟩
        · rw [eqfvs, ← eq]
          refine h2.2.2.instantiate1 fun h => ?_
          exact res.elim (wf.ngen_wf _ (m.dropN_fvars_subset n hn (hdrop ▸ h)))
        · simp; split <;> rename_i h
          · exact ⟨h2.1, h2.2.1, hty.abstract1⟩
          · rw [Expr.lowerLooseBVars_eq_instantiate (v := .sort .zero) (by simpa using h)]
            exact hty.abstract1.instantiate1 rfl
      · intro h; let ⟨_, hbody⟩ := hbody h
        exact eqfvs.symm ▸ eq ▸ ⟨_, hbody.inst_fvar c.Ewf.ordered mwf'.1.tr.wf⟩
    split
    · subst inferOnly
      refine (checkType.WF ?_).bind fun uv _ le ⟨dom', uv', _, h1, h2, h3⟩ => ?_
      · apply hr.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (ensureSortCore.WF h2).bind
        fun _ _ le₂ ⟨h4, h5, _⟩ => ?_
      obtain ⟨_, rfl⟩ := h4; let ⟨_, .sort _, h5⟩ := h5; have le := le.trans le₂
      refine (checkType.WF ?_).bind_le le fun ty _ le ⟨val', ty', _, h4, h5, h6⟩ => ?_
      · apply hr.2.1.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
      refine (isDefEq.WF h5 h1).bind_le le fun b _ le h7 => ?_
      cases b <;> simp
      · exact .getEnv <| .getLCtx .throw
      have valty := h6.defeqU_r c.Ewf mwf.1.tr.wf.toCtx (h7 rfl)
      exact main le h1 h4 valty nofun
    · simp_all; let ⟨_, h1⟩ := hinf
      have .letE (ty' := dom') (body' := body') valty hdom hval hbody := h1
      exact main .rfl hdom hval valty _ hbody
  · subst ei; refine (inferType.WF' ?_ hinf).bind fun ty _ _ ⟨e', ty', hb, h1, h2, h3⟩ => ?_
    · apply hr.instantiateList; simp [← eqfvs]; exact m.fvarRevList_prefix.subset
    refine .stateWF fun wf => .getLCtx <| .pure ?_
    have ⟨_, hty, e2⟩ := h2.trExpr c.Ewf.ordered wf.trctx.wf
      |>.cheapBetaReduce c.Ewf wf.trctx.wf m.noBV
    have h3 := h3.defeqU_r c.Ewf mwf.1.tr.wf.toCtx e2.symm
    let ⟨h1', h2'⟩ := mwf.1.mkLet_trS c.Ewf h1 h3 n hn nds hnds
    have h3' := (mwf.1.mkForall_trS c.Ewf hty (h3.isType c.Ewf mwf.1.tr.wf.toCtx) n hn).1
    simp [hdrop] at h1' h2' h3'
    erw [mwf.1.mkForall_eq _ _
      (m.noBV ▸ hty.closed).looseBVarRange_zero (eqfvs ▸ harr)]
    refine ⟨_, _, fun P hP he => ?_, he₀ ▸ h1', h3', h2'⟩
    have ⟨c1, c2, c3⟩ := hbelow _ hP he
    have := c3 _ <| FVarsBelow.cheapBetaReduce (m.noBV ▸ h2.closed) _ c1 <| hb _ c1 c2
    refine this.mp (fun _ => id) h3'.fvarsIn
termination_by e

theorem inferLet.WF
    (hr : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferLet e inferOnly).WF c s fun ty _ =>
      ∃ e' ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (c.withMLC_self ▸ inferLet.loop.WF (Nat.zero_le _) [] rfl rfl rfl rfl rfl ?_ hr) hinf
  exact fun P hP he => ⟨(AllAbove.wf wf.trctx.wf.fvwf).2 hP, he.mono fun _ h _ => h, fun _ => id⟩

theorem AppStack.toSpineWF {c : VContext}
    (H : AppStack c.venv c.lparams c.vlctx f f' args)
    (hf : c.HasType f' (VExpr.forallN As C))
    (hlen : args.length = As.length) :
    ∃ args', args.Forall₂ (c.TrExprS · ·) args' ∧
      c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (VExpr.forallN As C) args' (VExpr.instRev C args') ∧
      c.TrExprS (f.mkAppList args) (VExpr.appN f' args') := by
  exact Lean4Lean.AppStack.toSpineWF H c.Ewf c.Δwf hf hlen

theorem invalidProj.WF {c : VContext} {s : VState} :
    (invalidProj e : RecM α).WF c s Q := by
  unfold invalidProj
  exact .getEnv <| .getLCtx .throw

theorem inferProjParams.WF {c : VContext} {s : VState}
    (hargs : args.Forall₂ (c.TrExprS · ·) args')
    (hrBelow : c.FVarsBelow proj r)
    (hargsBelow : ∀ arg ∈ args, c.FVarsBelow proj arg)
    (hr : c.TrExpr r R)
    (hspine : c.venv.SpineWF c.lparams.length c.vlctx.toCtx
      R args' T) :
    (inferProjParams proj args r).WF c s fun out _ =>
      c.FVarsBelow proj out ∧ c.TrExpr out T := by
  induction hargs generalizing r R s with
  | nil =>
      simp [inferProjParams] at hspine ⊢
      exact hspine.nil_inv ▸ .pure ⟨hrBelow, hr⟩
  | @cons arg arg' args args' harg hargs ih =>
      simp only [inferProjParams]
      have hargBelow := hargsBelow arg (by simp)
      have hargsBelow' : ∀ arg ∈ args, c.FVarsBelow proj arg := by
        intro arg harg
        exact hargsBelow arg (by simp [harg])
      obtain ⟨A, B, rfl, hargType, hrest⟩ := hspine.cons_inv
      obtain ⟨r', hrS, hrEq⟩ := hr
      refine (whnf.WF hrS).bind fun out s' _
        ⟨houtBelow, ⟨out', hout, houtEq⟩⟩ => ?_
      have houtEq := houtEq.trans c.Ewf c.Δwf hrEq
      cases out with
      | forallE name dom body bi =>
        let .forallE hdomTy hbodyTy hdom hbody := hout
        have hforallEq := houtEq.forallE_inv c.Ewf c.Δwf
        obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
        have hargType' := hargType.defeqU_r c.Ewf c.Δwf
          ⟨_, hdomEq.symm⟩
        have hnext : c.TrExpr (body.instantiate1 arg) (B.inst arg') := by
          simpa only [Expr.instantiate1_eq] using
            (.inst c.Ewf c.Δwf hargType'
              ⟨_, hbody, _, hbodyEq⟩ (harg.trExpr c.Ewf c.Δwf))
        have hnextBelow : c.FVarsBelow proj (body.instantiate1 arg) := by
          intro P hP hproj
          have houtFVars := (hrBelow.trans houtBelow) P hP hproj
          simpa only [Expr.instantiate1_eq] using
            houtFVars.2.instantiate1 (hargBelow P hP hproj)
        exact ih hnextBelow hargsBelow' hnext hrest
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit |
          mdata | proj => exact invalidProj.WF

/-- WHNF preserves a source Pi syntactically.  Projection support owns that
source shape, so sparse runtime checking does not need to rediscover it from
the translated expression. -/
theorem whnf.WF_forall {c : VContext} {s : VState} :
    (whnf (.forallE name domain body binderInfo)).WF c s fun out _ =>
      out = .forallE name domain body binderInfo := by
  intro methods methodsWF
  exact methodsWF.whnf_forall

/-- Consume constructor parameters in lockstep with a producer-owned
projection spine. -/
theorem inferProjParams.WF_support {c : VContext} {s : VState}
    (hargs : args.Forall₂ (fun _ _ => True) args')
    (support : ProjectionSpineSupport (args.length + remaining) r target) :
    (inferProjParams proj args r).WF c s fun out _ =>
      ∃ cursor, target.consumeForalls? args' = some cursor ∧
        ProjectionSpineSupport remaining out cursor := by
  induction hargs generalizing r target s with
  | nil =>
      simp only [List.length_nil, Nat.zero_add] at support
      exact .pure ⟨target, rfl, support⟩
  | @cons arg arg' args args' _ hargs ih =>
      have support' : ProjectionSpineSupport
          (args.length + remaining + 1) r target := by
        have countEq : args.length + 1 + remaining =
            args.length + remaining + 1 := by omega
        exact countEq ▸ support
      cases support' with
      | @cons _ sourceBody targetBody sourceName sourceDomain
          sourceBinderInfo targetDomain skip tail =>
        simp only [inferProjParams]
        refine whnf.WF_forall.bind fun out nextState _ outEq => ?_
        subst out
        have nextSupport := tail.instN
          (sourceArgument := arg) (targetArgument := arg') (depth := 0)
        simpa only [Expr.instantiate1_eq, VExpr.consumeForalls?] using
          (ih (s := nextState) nextSupport)

/-- Consume the typed constructor-parameter prefix of a split projection
support witness.  Once all parameters have been instantiated, the exact
field-only dependency spine is exposed. -/
theorem inferProjParams.WF_fieldSupport {c : VContext} {s : VState}
    (hargs : args.Forall₂ (fun _ _ => True) args')
    (support : ProjectionFieldSpineSupport args.length fieldCount r target) :
    (inferProjParams proj args r).WF c s fun out _ =>
      ∃ cursor, target.consumeForalls? args' = some cursor ∧
        ProjectionSpineSupport fieldCount out cursor := by
  induction hargs generalizing r target s with
  | nil =>
      cases support with
      | fields fieldSupport => exact .pure ⟨target, rfl, fieldSupport⟩
  | @cons arg arg' args args' _ hargs ih =>
      cases support with
      | @param _ _ sourceBody targetBody sourceName sourceDomain
          sourceBinderInfo targetDomain tail =>
        simp only [inferProjParams]
        refine whnf.WF_forall.bind fun out nextState _ outEq => ?_
        subst out
        have nextSupport := tail.instN
          (sourceArgument := arg) (targetArgument := arg') (depth := 0)
        simpa only [Expr.instantiate1_eq, VExpr.consumeForalls?] using
          (ih (s := nextState) nextSupport)

/-- The ordinary typing proof and the producer-owned projection support refer
to the same deterministic parameter-consumption execution. -/
theorem inferProjParams.WF_withSupport {c : VContext} {s : VState}
    (hargs : args.Forall₂ (c.TrExprS · ·) args')
    (hrBelow : c.FVarsBelow proj r)
    (hargsBelow : ∀ arg ∈ args, c.FVarsBelow proj arg)
    (hr : c.TrExpr r target)
    (hspine : c.venv.SpineWF c.lparams.length c.vlctx.toCtx
      target args' result)
    (support : ProjectionSpineSupport
      (args.length + remaining) r target) :
    (inferProjParams proj args r).WF c s fun out _ =>
      c.FVarsBelow proj out ∧ c.TrExpr out result ∧
        ProjectionSpineSupport remaining out result := by
  have erased : args.Forall₂ (fun _ _ => True) args' :=
    Lean4Lean.List.Forall₂.imp (fun _ _ _ => trivial) hargs
  refine ((inferProjParams.WF hargs hrBelow hargsBelow hr hspine).and_const
    (inferProjParams.WF_support erased support)).mono
      fun out finalState stateLE ⟨⟨below, translation⟩,
        cursor, consumed, cursorSupport⟩ => ?_
  have expected := hspine.toSparse.consumeForalls_eq
  have cursorEq : cursor = result :=
    Option.some.inj (consumed.symm.trans expected)
  subst cursor
  exact ⟨below, translation, cursorSupport⟩

/-- Typed parameter inference and the split producer contract describe the
same deterministic execution.  Parameter typing supplies the translated
result; the split witness supplies dependency support only for the remaining
field suffix. -/
theorem inferProjParams.WF_withFieldSupport {c : VContext} {s : VState}
    (hargs : args.Forall₂ (c.TrExprS · ·) args')
    (hrBelow : c.FVarsBelow proj r)
    (hargsBelow : ∀ arg ∈ args, c.FVarsBelow proj arg)
    (hr : c.TrExpr r target)
    (hspine : c.venv.SpineWF c.lparams.length c.vlctx.toCtx
      target args' result)
    (support : ProjectionFieldSpineSupport
      args.length fieldCount r target) :
    (inferProjParams proj args r).WF c s fun out _ =>
      c.FVarsBelow proj out ∧ c.TrExpr out result ∧
        ProjectionSpineSupport fieldCount out result := by
  have erased : args.Forall₂ (fun _ _ => True) args' :=
    Lean4Lean.List.Forall₂.imp (fun _ _ _ => trivial) hargs
  refine ((inferProjParams.WF hargs hrBelow hargsBelow hr hspine).and_const
    (inferProjParams.WF_fieldSupport erased support)).mono
      fun out finalState stateLE ⟨⟨below, translation⟩,
        cursor, consumed, cursorSupport⟩ => ?_
  have expected := hspine.toSparse.consumeForalls_eq
  have cursorEq : cursor = result :=
    Option.some.inj (consumed.symm.trans expected)
  subst cursor
  exact ⟨below, translation, cursorSupport⟩

theorem inferProjFields.WF {c : VContext} {s : VState}
    {view : VProjectionView} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {tailResult cursor : VExpr}
    (hstruct : c.TrExprS struct major)
    (hview : view.LayoutWF c.venv)
    (hlevels : ∀ level ∈ levels, level.WF c.lparams.length)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (view.familyType.instL levels) params (.sort resultLevel))
    (hprograms : view.ProgramsWF c.venv)
    (hname : view.name = typeName)
    (hmajor : c.HasType major (view.structureType levels params))
    (hrBelow : c.FVarsBelow proj r)
    (hstructBelow : c.FVarsBelow proj struct)
    (hbound : fieldIdx + count <
      (view.specializedFields levels params).length)
    (hr : c.TrExpr r cursor)
    (hcursor : VExpr.consumeForalls?
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.projectionArgs levels params fieldIdx major) = some cursor) :
    (inferProjFields proj typeName struct maybePropType fieldIdx count r).WF
      c s fun out _ =>
        ∃ cursor',
          VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params (fieldIdx + count) major) =
              some cursor' ∧
          c.FVarsBelow proj out ∧ c.TrExpr out cursor' := by
  induction count generalizing s r cursor fieldIdx with
  | zero =>
      simp only [inferProjFields, Nat.add_zero]
      exact .pure ⟨cursor, hcursor, hrBelow, hr⟩
  | succ count ih =>
      simp only [inferProjFields]
      have hfieldIdx : fieldIdx <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : fieldIdx <
          (view.projectionCodes levels params).length := by
        simpa using hfieldIdx
      let code := (view.projectionCodes levels params)[fieldIdx]
      have hcode :
          (view.projectionCodes levels params)[fieldIdx]? = some code :=
        List.getElem?_eq_getElem hcodeIdx
      have hargsLength :
          (view.projectionArgs levels params fieldIdx major).length =
            fieldIdx :=
        view.projectionArgs_length levels params fieldIdx major
          (Nat.le_of_lt hcodeIdx)
      obtain ⟨field, semanticBody, hfield, hconsume⟩ :=
        VExpr.consumeForalls?_forallN_domain
          (view.specializedFields levels params) tailResult
          (view.projectionArgs levels params fieldIdx major)
          (by simpa [hargsLength] using hfieldIdx)
      rw [hargsLength] at hfield
      have hcursorShape : cursor =
          .forallE
            (field.instRevAt
              (view.projectionArgs levels params fieldIdx major) 0)
            semanticBody :=
        Option.some.inj (hcursor.symm.trans hconsume)
      subst cursor
      obtain ⟨field', typeBody, hfield', htypeFn,
          hprojectorField⟩ :=
        hprograms.projector_hasType_field c.Ewf c.Δwf hlevels
          hlevelsLength hparamsLength hparamsSpine hcode hmajor
      have hfieldEq : field' = field :=
        Option.some.inj (hfield'.symm.trans hfield)
      subst field'
      have hprojector := hprograms c.Δwf hlevels hlevelsLength
        hparamsLength hparamsSpine hcode
      have hprojSem : VProjectionView.TrProj c.venv c.lparams.length
          c.vlctx.toCtx
          view levels params fieldIdx major (.app code.projector major) := {
        viewWF := hview
        levelsWF := hlevels
        levels_length := hlevelsLength
        params_length := hparamsLength
        paramsSpine := hparamsSpine
        majorType := hmajor
        program := ⟨code, hcode, rfl, hprojector⟩ }
      have hprojStrict : c.TrExprS (.proj typeName fieldIdx struct)
          (.app code.projector major) :=
        .proj hstruct ⟨.ordinary view, levels, params, hname,
          .ordinary hprojSem⟩
      obtain ⟨r', hrS, hrEq⟩ := hr
      refine (whnf.WF hrS).bind fun out nextState _
        ⟨houtBelow, ⟨out', hout, houtEq⟩⟩ => ?_
      have houtEq := houtEq.trans c.Ewf c.Δwf hrEq
      cases out with
      | forallE name dom body bi =>
        let .forallE hdomTy hbodyTy hdom hbody := hout
        have hforallEq := houtEq.forallE_inv c.Ewf c.Δwf
        obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
        have hprojectorField' := hprojectorField.defeqU_r
          c.Ewf c.Δwf ⟨_, hdomEq.symm⟩
        have hnext : c.TrExpr
            (body.instantiate1 (.proj typeName fieldIdx struct))
            (semanticBody.inst (.app code.projector major)) := by
          simpa only [Expr.instantiate1_eq] using
            (.inst c.Ewf c.Δwf hprojectorField'
              ⟨_, hbody, _, hbodyEq⟩
              (hprojStrict.trExpr c.Ewf.ordered c.Δwf))
        have hnextBelow : c.FVarsBelow proj
            (body.instantiate1 (.proj typeName fieldIdx struct)) := by
          intro P hP hproj
          have houtFVars := (hrBelow.trans houtBelow) P hP hproj
          have hfieldProj : FVarsIn P
              (.proj typeName fieldIdx struct) := by
            simpa [FVarsIn] using hstructBelow P hP hproj
          simpa only [Expr.instantiate1_eq] using
            houtFVars.2.instantiate1 hfieldProj
        have hconsumeNext : VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params (fieldIdx + 1) major) =
              some (semanticBody.inst (.app code.projector major)) := by
          rw [view.projectionArgs_succ levels params fieldIdx major hcode]
          rw [VExpr.consumeForalls?_append, hconsume]
          rfl
        have hbound' : fieldIdx + 1 + count <
            (view.specializedFields levels params).length := by omega
        have hrec (recState : VState) :=
          ih (s := recState) hnextBelow hbound' hnext hconsumeNext
        simp only
        split
        · refine (isProp.WF hdom).bind fun _ propState _ _ => ?_
          split
          · exact invalidProj.WF
          · simpa only [pure_bind, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using hrec propState
        · simpa only [pure_bind, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using hrec nextState
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit |
          mdata | proj => exact invalidProj.WF

/-- Dense restored counterpart of `inferProjFields.WF`.  The operational
program family supplies every restored projector, while the retained
constructor layout identifies its result with the corresponding source
field. -/
theorem inferProjFields.WF_restored {c : VContext} {s : VState}
    {view : VRestoredBlockStructureView} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {tailResult cursor : VExpr}
    (hstruct : c.TrExprS struct major)
    (hview : view.ConstructorParameterLayoutWF c.venv)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (recEntriesClosed :
      VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (hlevels : ∀ level ∈ levels, level.WF c.lparams.length)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (view.familyType.instL levels) params (.sort resultLevel))
    (hprograms : view.OperationalProgramsWF c.venv)
    (hname : view.name = typeName)
    (hmajor : c.HasType major (view.structureType levels params))
    (hrBelow : c.FVarsBelow proj r)
    (hstructBelow : c.FVarsBelow proj struct)
    (hbound : fieldIdx + count <
      (view.specializedFields levels params).length)
    (hr : c.TrExpr r cursor)
    (hcursor : VExpr.consumeForalls?
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.operationalProjectionArgs levels params fieldIdx major) =
        some cursor) :
    (inferProjFields proj typeName struct maybePropType fieldIdx count r).WF
      c s fun out _ =>
        ∃ cursor',
          VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.operationalProjectionArgs levels params
              (fieldIdx + count) major) = some cursor' ∧
          c.FVarsBelow proj out ∧ c.TrExpr out cursor' := by
  induction count generalizing s r cursor fieldIdx with
  | zero =>
      simp only [inferProjFields, Nat.add_zero]
      exact .pure ⟨cursor, hcursor, hrBelow, hr⟩
  | succ count ih =>
      simp only [inferProjFields]
      have hfieldIdx : fieldIdx <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : fieldIdx <
          (view.operationalProjectionCodes levels params).length := by
        simpa using hfieldIdx
      let code := (view.operationalProjectionCodes levels params)[fieldIdx]
      have hcode :
          (view.operationalProjectionCodes levels params)[fieldIdx]? =
            some code :=
        List.getElem?_eq_getElem hcodeIdx
      have hargsLength :
          (view.operationalProjectionArgs levels params fieldIdx major).length =
            fieldIdx :=
        view.operationalProjectionArgs_length levels params fieldIdx major
          (Nat.le_of_lt hcodeIdx)
      obtain ⟨field, semanticBody, hfield, hconsume⟩ :=
        VExpr.consumeForalls?_forallN_domain
          (view.specializedFields levels params) tailResult
          (view.operationalProjectionArgs levels params fieldIdx major)
          (by simpa [hargsLength] using hfieldIdx)
      rw [hargsLength] at hfield
      have hcursorShape : cursor =
          .forallE
            (field.instRevAt
              (view.operationalProjectionArgs levels params fieldIdx major) 0)
            semanticBody :=
        Option.some.inj (hcursor.symm.trans hconsume)
      subst cursor
      have hprojector := hprograms c.Δwf hlevels hlevelsLength
        hparamsLength hparamsSpine hcode
      obtain ⟨field', _projectorDomain, typeBody, hfield', htypeFn,
          hprojectorField⟩ :=
        hview.toLayoutWF.operationalProjector_hasType_field_of_type
          c.Ewf.conversionRegular recEntriesClosed hlevelsLength c.Δwf
          hcode hprojector hmajor
      have hfieldEq : field' = field :=
        Option.some.inj (hfield'.symm.trans hfield)
      subst field'
      have hprojSem : VRestoredBlockStructureView.TrProj c.venv
          c.lparams.length c.vlctx.toCtx view levels params fieldIdx major
          (.app code.projector major) := {
        viewWF := hview.toFamilyLayoutWF
        parameterLayout := hview
        codeNaturality := codeNaturality
        recEntriesClosed := recEntriesClosed
        levelsWF := hlevels
        levels_length := hlevelsLength
        params_length := hparamsLength
        paramsSpine := hparamsSpine
        majorType := hmajor
        program := ⟨code, hcode, rfl, hprojector⟩ }
      have hprojStrict : c.TrExprS (.proj typeName fieldIdx struct)
          (.app code.projector major) :=
        .proj hstruct ⟨.restored view, levels, params, hname,
          .restored hprojSem⟩
      obtain ⟨r', hrS, hrEq⟩ := hr
      refine (whnf.WF hrS).bind fun out nextState _
        ⟨houtBelow, ⟨out', hout, houtEq⟩⟩ => ?_
      have houtEq := houtEq.trans c.Ewf c.Δwf hrEq
      cases out with
      | forallE name dom body bi =>
        let .forallE hdomTy hbodyTy hdom hbody := hout
        have hforallEq := houtEq.forallE_inv c.Ewf c.Δwf
        obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
        have hprojectorField' := hprojectorField.defeqU_r
          c.Ewf c.Δwf ⟨_, hdomEq.symm⟩
        have hnext : c.TrExpr
            (body.instantiate1 (.proj typeName fieldIdx struct))
            (semanticBody.inst (.app code.projector major)) := by
          simpa only [Expr.instantiate1_eq] using
            (.inst c.Ewf c.Δwf hprojectorField'
              ⟨_, hbody, _, hbodyEq⟩
              (hprojStrict.trExpr c.Ewf.ordered c.Δwf))
        have hnextBelow : c.FVarsBelow proj
            (body.instantiate1 (.proj typeName fieldIdx struct)) := by
          intro P hP hproj
          have houtFVars := (hrBelow.trans houtBelow) P hP hproj
          have hfieldProj : FVarsIn P
              (.proj typeName fieldIdx struct) := by
            simpa [FVarsIn] using hstructBelow P hP hproj
          simpa only [Expr.instantiate1_eq] using
            houtFVars.2.instantiate1 hfieldProj
        have hconsumeNext : VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.operationalProjectionArgs levels params
              (fieldIdx + 1) major) =
              some (semanticBody.inst (.app code.projector major)) := by
          rw [view.operationalProjectionArgs_succ levels params fieldIdx major
            hcode]
          rw [VExpr.consumeForalls?_append, hconsume]
          rfl
        have hbound' : fieldIdx + 1 + count <
            (view.specializedFields levels params).length := by omega
        have hrec (recState : VState) :=
          ih (s := recState) hnextBelow hbound' hnext hconsumeNext
        simp only
        split
        · refine (isProp.WF hdom).bind fun _ propState _ _ => ?_
          split
          · exact invalidProj.WF
          · simpa only [pure_bind, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using hrec propState
        · simpa only [pure_bind, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using hrec nextState
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit |
          mdata | proj => exact invalidProj.WF

theorem inferProjFields.WF_runtimeBlock {c : VContext} {s : VState}
    {view : VBlockStructureView} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {tailResult cursor : VExpr}
    {majorCursor constructorCursor : VExpr}
    (hstruct : c.TrExprS struct major)
    (hview : view.LayoutWF c.venv)
    (hlevels : ∀ level ∈ levels, level.WF c.lparams.length)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (view.familyType.instL levels) params (.sort resultLevel))
    (hname : view.name = typeName)
    (hmajor : c.HasType major (view.structureType levels params))
    (hrBelow : c.FVarsBelow proj r)
    (hstructBelow : c.FVarsBelow proj struct)
    (hbound : fieldIdx + count <
      (view.specializedFields levels params).length)
    (hr : c.TrExpr r cursor)
    (hcursor : VExpr.consumeForalls?
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.operationalProjectionArgs levels params fieldIdx major) =
        some cursor)
    (runtime : view.OperationalRuntimePrefix c.venv c.lparams.length
      c.vlctx.toCtx levels params fieldIdx)
    (semanticSupport : ProjectionSpineSupport (count + 1) r cursor)
    (majorSupport : ProjectionSpineSupport (count + 1) r majorCursor)
    (hmajorCursor :
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero)).consumeForalls?
          (view.operationalProjectionArgs levels
            (params.map (VExpr.liftN 1)) fieldIdx (.bvar 0)) =
        some majorCursor)
    (constructorSupport :
      ProjectionSpineSupport (count + 1) r constructorCursor)
    (hconstructorCursor :
      let fields := view.specializedFields levels params
      let fieldCount := fields.length
      (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
        (.sort .zero)).consumeForalls?
          (((view.operationalProjectionCodes levels params).take fieldIdx).map
            fun prior => .app (prior.projector.liftN fieldCount)
              (view.projectionConstructorApp levels params fields)) =
        some constructorCursor)
    (hsmallMaybe : view.generation.elimination = .small →
      maybePropType = true) :
    (inferProjFields proj typeName struct maybePropType fieldIdx count r).WF
      c s fun out _ =>
        ∃ cursor' majorCursor' constructorCursor',
          VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.operationalProjectionArgs levels params
              (fieldIdx + count) major) = some cursor' ∧
          (VExpr.forallN
            (view.specializedFields levels (params.map (VExpr.liftN 1)))
            (.sort .zero)).consumeForalls?
              (view.operationalProjectionArgs levels
                (params.map (VExpr.liftN 1)) (fieldIdx + count) (.bvar 0)) =
            some majorCursor' ∧
          (let fields := view.specializedFields levels params
           let fieldCount := fields.length
           (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
             (.sort .zero)).consumeForalls?
               (((view.operationalProjectionCodes levels params).take
                 (fieldIdx + count)).map fun prior =>
                   .app (prior.projector.liftN fieldCount)
                     (view.projectionConstructorApp levels params fields)) =
             some constructorCursor') ∧
          c.FVarsBelow proj out ∧ c.TrExpr out cursor' ∧
          ProjectionSpineSupport 1 out cursor' ∧
          ProjectionSpineSupport 1 out majorCursor' ∧
          ProjectionSpineSupport 1 out constructorCursor' ∧
          view.OperationalRuntimePrefix c.venv c.lparams.length
            c.vlctx.toCtx levels params (fieldIdx + count) := by
  induction count generalizing s r cursor majorCursor constructorCursor fieldIdx with
  | zero =>
      simp only [inferProjFields, Nat.add_zero]
      exact .pure ⟨cursor, majorCursor, constructorCursor, hcursor,
        hmajorCursor, hconstructorCursor, hrBelow, hr, semanticSupport,
        majorSupport, constructorSupport, runtime⟩
  | succ count ih =>
      simp only [inferProjFields]
      have hfieldIdx : fieldIdx <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : fieldIdx <
          (view.operationalProjectionCodes levels params).length := by
        simpa using hfieldIdx
      let code := (view.operationalProjectionCodes levels params)[fieldIdx]
      have hcode :
          (view.operationalProjectionCodes levels params)[fieldIdx]? =
            some code :=
        List.getElem?_eq_getElem hcodeIdx
      cases semanticSupport with
      | @cons semanticRemaining sourceBody semanticBody sourceName sourceDomain
          sourceBinderInfo semanticDomain semanticSkip semanticTail =>
        cases majorSupport with
        | @cons majorRemaining _ majorBody _ _ _ majorDomain majorSkip majorTail =>
          cases constructorSupport with
          | @cons constructorRemaining _ constructorBody _ _ _ constructorDomain
              constructorSkip constructorTail =>
            refine whnf.WF_forall.bind fun out nextState _ outEq => ?_
            subst out
            obtain ⟨strictTarget, strictTranslation, targetEq⟩ := hr
            let .forallE hdomTy hbodyTy hdom hbody := strictTranslation
            have hforallEq := targetEq.forallE_inv c.Ewf c.Δwf
            obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
            have hbodyTranslation : TrExpr c.venv c.lparams
                ((none, .vlam _) :: c.vlctx) sourceBody semanticBody :=
              ⟨_, hbody, _, hbodyEq⟩
            have bodyClosedOne : Closed sourceBody 1 := by
              have closed := hbody.closed
              simpa only [VLCtx.bvars, c.mlctx.noBV, Nat.zero_add] using closed
            have hargsLength :
                (view.operationalProjectionArgs levels params fieldIdx major).length =
                  fieldIdx :=
              view.operationalProjectionArgs_length levels params fieldIdx major
                (Nat.le_of_lt hcodeIdx)
            obtain ⟨field, semanticTailBody, hfield, hconsume⟩ :=
              VExpr.consumeForalls?_forallN_domain
                (view.specializedFields levels params) tailResult
                (view.operationalProjectionArgs levels params fieldIdx major)
                (by simpa [hargsLength] using hfieldIdx)
            rw [hargsLength] at hfield
            have hsemanticDomain : semanticDomain =
                field.instRevAt
                  (view.operationalProjectionArgs levels params fieldIdx major) 0 := by
              have cursorShape :
                  (.forallE semanticDomain semanticBody : VExpr) =
                    .forallE
                      (field.instRevAt
                        (view.operationalProjectionArgs levels params fieldIdx major) 0)
                      semanticTailBody :=
                Option.some.inj (hcursor.symm.trans hconsume)
              injection cursorShape
            have hsemanticBody : semanticBody = semanticTailBody := by
              have cursorShape :
                  (.forallE semanticDomain semanticBody : VExpr) =
                    .forallE
                      (field.instRevAt
                        (view.operationalProjectionArgs levels params fieldIdx major) 0)
                      semanticTailBody :=
                Option.some.inj (hcursor.symm.trans hconsume)
              injection cursorShape
            subst semanticTailBody
            cases dependency : sourceBody.hasLooseBVar 0 with
            | false =>
              simp only [dependency, Bool.false_and, Bool.false_eq_true,
                if_false]
              have structuralClosed :
                  sourceBody.hasLooseBVar' 0 = false := by
                rw [← Expr.hasLooseBVar_eq]
                exact dependency
              have bodyClosedZero : Closed sourceBody 0 :=
                bodyClosedOne.zero_of_one_of_hasLooseBVar_false structuralClosed
              let sourceArgument : Expr :=
                .proj typeName fieldIdx struct
              let semanticArgument : VExpr := .app code.projector major
              let majorArgument : VExpr :=
                (code.liftN 1 0).projector.app (.bvar 0)
              let fields := view.specializedFields levels params
              let fieldCount := fields.length
              let constructorArgument : VExpr :=
                (code.liftN fieldCount 0).projector.app
                  (view.projectionConstructorApp levels params fields)
              have hnext : c.TrExpr
                  (sourceBody.instantiate1 sourceArgument)
                  (semanticBody.inst semanticArgument) := by
                simpa only [Expr.instantiate1_eq] using
                  Lean4Lean.TrExpr.instantiate1_skipped c.Ewf c.Δwf hdomTy
                    hbodyTranslation bodyClosedZero
                    (semanticSkip structuralClosed) sourceArgument semanticArgument
              have hnextBelow : c.FVarsBelow proj
                  (sourceBody.instantiate1 sourceArgument) := by
                rw [Expr.instantiate1_eq,
                  Expr.instantiate1_eq_self bodyClosedZero.looseBVarRange_zero]
                intro P hP hproj
                exact (hrBelow P hP hproj).2
              have semanticSupportNext : ProjectionSpineSupport (count + 1)
                  (sourceBody.instantiate1 sourceArgument)
                  (semanticBody.inst semanticArgument) := by
                simpa only [sourceArgument, semanticArgument,
                  Expr.instantiate1_eq] using
                  semanticTail.instN
                    (sourceArgument := sourceArgument)
                    (targetArgument := semanticArgument) (depth := 0)
              have majorSupportNext : ProjectionSpineSupport (count + 1)
                  (sourceBody.instantiate1 sourceArgument)
                  (majorBody.inst majorArgument) := by
                simpa only [sourceArgument, majorArgument,
                  Expr.instantiate1_eq] using
                  majorTail.instN
                    (sourceArgument := sourceArgument)
                    (targetArgument := majorArgument) (depth := 0)
              have constructorSupportNext : ProjectionSpineSupport (count + 1)
                  (sourceBody.instantiate1 sourceArgument)
                  (constructorBody.inst constructorArgument) := by
                simpa only [sourceArgument, constructorArgument,
                  Expr.instantiate1_eq] using
                  constructorTail.instN
                    (sourceArgument := sourceArgument)
                    (targetArgument := constructorArgument) (depth := 0)
              have runtimeNext := runtime.snocSkip hview hparamsLength
                hmajorCursor (majorSkip structuralClosed)
                hconstructorCursor (constructorSkip structuralClosed) hcode
              have hcursorNext : VExpr.consumeForalls?
                  (VExpr.forallN (view.specializedFields levels params) tailResult)
                  (view.operationalProjectionArgs levels params
                    (fieldIdx + 1) major) =
                    some (semanticBody.inst semanticArgument) := by
                rw [view.operationalProjectionArgs_succ levels params
                  fieldIdx major hcode]
                rw [VExpr.consumeForalls?_append, hcursor]
                rfl
              let paramsLift := params.map (VExpr.liftN 1)
              have hcodesLift := hview.operationalProjectionCodes_liftN
                levels params hparamsLength 1 0
              have hcodeLift :
                  (view.operationalProjectionCodes levels paramsLift)[fieldIdx]? =
                    some (code.liftN 1 0) := by
                rw [← hcodesLift, List.getElem?_map, hcode]
                rfl
              have hmajorCursorNext :
                  (VExpr.forallN
                    (view.specializedFields levels (params.map (VExpr.liftN 1)))
                    (.sort .zero)).consumeForalls?
                      (view.operationalProjectionArgs levels
                        (params.map (VExpr.liftN 1)) (fieldIdx + 1) (.bvar 0)) =
                    some (majorBody.inst majorArgument) := by
                rw [view.operationalProjectionArgs_succ levels paramsLift
                  fieldIdx (.bvar 0) hcodeLift]
                rw [VExpr.consumeForalls?_append, hmajorCursor]
                rfl
              have hconstructorCursorNext :
                  (let fields := view.specializedFields levels params
                   let fieldCount := fields.length
                   (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
                     (.sort .zero)).consumeForalls?
                       (((view.operationalProjectionCodes levels params).take
                         (fieldIdx + 1)).map fun prior =>
                           .app (prior.projector.liftN fieldCount)
                             (view.projectionConstructorApp levels params fields)) =
                     some (constructorBody.inst constructorArgument)) := by
                simp only [List.take_add_one, hcode, Option.toList_some,
                  List.map_append, List.map_singleton,
                  VExpr.consumeForalls?_append, hconstructorCursor,
                  constructorArgument, fields, fieldCount]
                rfl
              have hboundNext : fieldIdx + 1 + count <
                  (view.specializedFields levels params).length := by omega
              have hrec := ih (s := nextState) hnextBelow hboundNext hnext
                hcursorNext runtimeNext semanticSupportNext majorSupportNext
                hmajorCursorNext constructorSupportNext hconstructorCursorNext
              simpa only [pure_bind, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm] using hrec
            | true =>
              let sourceArgument : Expr :=
                .proj typeName fieldIdx struct
              let semanticArgument : VExpr := .app code.projector major
              let majorArgument : VExpr :=
                (code.liftN 1 0).projector.app (.bvar 0)
              let fields := view.specializedFields levels params
              let fieldCount := fields.length
              let constructorArgument : VExpr :=
                (code.liftN fieldCount 0).projector.app
                  (view.projectionConstructorApp levels params fields)
              have continueWithProjector (continuationState : VState)
                  (hprojector : c.HasType code.projector
                    (.forallE (view.structureType levels params)
                      (.app code.typeFn.lift (.bvar 0)))) :
                  (inferProjFields proj typeName struct maybePropType
                    (fieldIdx + 1) count
                    (sourceBody.instantiate1 sourceArgument)).WF
                    c continuationState fun out _ =>
                      ∃ cursor' majorCursor' constructorCursor',
                        VExpr.consumeForalls?
                          (VExpr.forallN
                            (view.specializedFields levels params) tailResult)
                          (view.operationalProjectionArgs levels params
                            (fieldIdx + 1 + count) major) = some cursor' ∧
                        (VExpr.forallN
                          (view.specializedFields levels
                            (params.map (VExpr.liftN 1)))
                          (.sort .zero)).consumeForalls?
                            (view.operationalProjectionArgs levels
                              (params.map (VExpr.liftN 1))
                              (fieldIdx + 1 + count) (.bvar 0)) =
                          some majorCursor' ∧
                        (let fields := view.specializedFields levels params
                         let fieldCount := fields.length
                         (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
                           (.sort .zero)).consumeForalls?
                             (((view.operationalProjectionCodes levels params).take
                               (fieldIdx + 1 + count)).map fun prior =>
                                 .app (prior.projector.liftN fieldCount)
                                   (view.projectionConstructorApp levels params fields)) =
                           some constructorCursor') ∧
                        c.FVarsBelow proj out ∧ c.TrExpr out cursor' ∧
                        ProjectionSpineSupport 1 out cursor' ∧
                        ProjectionSpineSupport 1 out majorCursor' ∧
                        ProjectionSpineSupport 1 out constructorCursor' ∧
                        view.OperationalRuntimePrefix c.venv c.lparams.length
                          c.vlctx.toCtx levels params
                            (fieldIdx + 1 + count) := by
                obtain ⟨projectorField, typeBody, hprojectorField,
                    htypeFn, hprojectorFieldType⟩ :=
                  view.operationalProjector_hasType_field_of_type
                    c.Ewf.conversionRegular c.Δwf hcode hprojector hmajor
                have hprojectorFieldEq : projectorField = field :=
                  Option.some.inj (hprojectorField.symm.trans hfield)
                subst projectorField
                rw [← hsemanticDomain] at hprojectorFieldType
                have hprojectorFieldType' :=
                  hprojectorFieldType.defeqU_r c.Ewf c.Δwf
                    ⟨_, hdomEq.symm⟩
                have hprojSem : VProjectionView.TrProj c.venv
                    c.lparams.length c.vlctx.toCtx (.block view)
                    levels params fieldIdx major semanticArgument := {
                  viewWF := VProjectionView.LayoutWF.ofBlock hview
                  levelsWF := hlevels
                  levels_length := hlevelsLength
                  params_length := hparamsLength
                  paramsSpine := hparamsSpine
                  majorType := hmajor
                  program := ⟨code, hcode, rfl, hprojector⟩ }
                have hprojStrict : c.TrExprS sourceArgument semanticArgument :=
                  .proj hstruct ⟨.ordinary (.block view), levels, params,
                    hname, .ordinary hprojSem⟩
                have hnext : c.TrExpr
                    (sourceBody.instantiate1 sourceArgument)
                    (semanticBody.inst semanticArgument) := by
                  simpa only [sourceArgument, semanticArgument,
                    Expr.instantiate1_eq] using
                    (.inst c.Ewf c.Δwf hprojectorFieldType'
                      hbodyTranslation
                      (hprojStrict.trExpr c.Ewf.ordered c.Δwf))
                have hnextBelow : c.FVarsBelow proj
                    (sourceBody.instantiate1 sourceArgument) := by
                  intro P hP hproj
                  have bodyFVars := (hrBelow P hP hproj).2
                  have projectionFVars : FVarsIn P sourceArgument := by
                    simpa [sourceArgument, FVarsIn] using
                      hstructBelow P hP hproj
                  simpa only [Expr.instantiate1_eq] using
                    bodyFVars.instantiate1 projectionFVars
                have semanticSupportNext : ProjectionSpineSupport (count + 1)
                    (sourceBody.instantiate1 sourceArgument)
                    (semanticBody.inst semanticArgument) := by
                  simpa only [sourceArgument, semanticArgument,
                    Expr.instantiate1_eq] using
                    semanticTail.instN
                      (sourceArgument := sourceArgument)
                      (targetArgument := semanticArgument) (depth := 0)
                have majorSupportNext : ProjectionSpineSupport (count + 1)
                    (sourceBody.instantiate1 sourceArgument)
                    (majorBody.inst majorArgument) := by
                  simpa only [sourceArgument, majorArgument,
                    Expr.instantiate1_eq] using
                    majorTail.instN
                      (sourceArgument := sourceArgument)
                      (targetArgument := majorArgument) (depth := 0)
                have constructorSupportNext : ProjectionSpineSupport (count + 1)
                    (sourceBody.instantiate1 sourceArgument)
                    (constructorBody.inst constructorArgument) := by
                  simpa only [sourceArgument, constructorArgument,
                    Expr.instantiate1_eq] using
                    constructorTail.instN
                      (sourceArgument := sourceArgument)
                      (targetArgument := constructorArgument) (depth := 0)
                have runtimeNext := runtime.snocTyped hview c.Ewf c.Δwf
                  hlevels hlevelsLength hparamsLength hparamsSpine hcode
                  hprojector
                have hcursorNext : VExpr.consumeForalls?
                    (VExpr.forallN
                      (view.specializedFields levels params) tailResult)
                    (view.operationalProjectionArgs levels params
                      (fieldIdx + 1) major) =
                      some (semanticBody.inst semanticArgument) := by
                  rw [view.operationalProjectionArgs_succ levels params
                    fieldIdx major hcode]
                  rw [VExpr.consumeForalls?_append, hcursor]
                  rfl
                let paramsLift := params.map (VExpr.liftN 1)
                have hcodesLift := hview.operationalProjectionCodes_liftN
                  levels params hparamsLength 1 0
                have hcodeLift :
                    (view.operationalProjectionCodes levels paramsLift)[fieldIdx]? =
                      some (code.liftN 1 0) := by
                  rw [← hcodesLift, List.getElem?_map, hcode]
                  rfl
                have hmajorCursorNext :
                    (VExpr.forallN
                      (view.specializedFields levels
                        (params.map (VExpr.liftN 1)))
                      (.sort .zero)).consumeForalls?
                        (view.operationalProjectionArgs levels
                          (params.map (VExpr.liftN 1))
                          (fieldIdx + 1) (.bvar 0)) =
                      some (majorBody.inst majorArgument) := by
                  rw [view.operationalProjectionArgs_succ levels paramsLift
                    fieldIdx (.bvar 0) hcodeLift]
                  rw [VExpr.consumeForalls?_append, hmajorCursor]
                  rfl
                have hconstructorCursorNext :
                    (let fields := view.specializedFields levels params
                     let fieldCount := fields.length
                     (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
                       (.sort .zero)).consumeForalls?
                         (((view.operationalProjectionCodes levels params).take
                           (fieldIdx + 1)).map fun prior =>
                             .app (prior.projector.liftN fieldCount)
                               (view.projectionConstructorApp levels params fields)) =
                       some (constructorBody.inst constructorArgument)) := by
                  simp only [List.take_add_one, hcode, Option.toList_some,
                    List.map_append, List.map_singleton,
                    VExpr.consumeForalls?_append, hconstructorCursor,
                    constructorArgument, fields, fieldCount]
                  rfl
                have hboundNext : fieldIdx + 1 + count <
                    (view.specializedFields levels params).length := by omega
                have hrec := ih (s := continuationState) hnextBelow hboundNext
                  hnext hcursorNext runtimeNext semanticSupportNext
                  majorSupportNext hmajorCursorNext constructorSupportNext
                  hconstructorCursorNext
                simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                  using hrec
              cases maybePropType with
              | false =>
                simp only [Bool.and_false, Bool.false_eq_true, if_false]
                have large : view.generation.elimination = .large := by
                  cases mode : view.generation.elimination with
                  | large => rfl
                  | small =>
                    have impossible := hsmallMaybe mode
                    contradiction
                have motiveLevel :=
                  view.motiveLevel_projectionLevels_of_large large
                    code.fieldSort levels
                have hprojector :=
                  hview.operationalProgram_hasType_of_runtimePrefix c.Ewf
                    runtime c.Δwf hlevels hlevelsLength hparamsLength
                    hparamsSpine hcode motiveLevel
                simpa only [sourceArgument, Nat.add_assoc, Nat.add_left_comm,
                  Nat.add_comm] using
                  (continueWithProjector nextState hprojector)
              | true =>
                simp only [dependency, Bool.and_true, if_true]
                refine (isProp.WF hdom).bind fun propResult propState _ hprop => ?_
                cases propResult with
                | false =>
                  simp only [Bool.not_false, Bool.true_eq_false, if_true]
                  exact invalidProj.WF
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, if_false]
                  cases mode : view.generation.elimination with
                  | large =>
                    have motiveLevel :=
                      view.motiveLevel_projectionLevels_of_large mode
                        code.fieldSort levels
                    have hprojector :=
                      hview.operationalProgram_hasType_of_runtimePrefix c.Ewf
                        runtime c.Δwf hlevels hlevelsLength hparamsLength
                        hparamsSpine hcode motiveLevel
                    simpa only [sourceArgument, Nat.add_assoc,
                      Nat.add_left_comm, Nat.add_comm] using
                      (continueWithProjector propState hprojector)
                  | small =>
                    have htypeFn :=
                      hview.operationalProjectionTypeFn_hasType_of_sparse
                        c.Ewf c.Δwf hlevels hlevelsLength hparamsLength
                        hparamsSpine hcode runtime.1
                    obtain ⟨typedField, htypedField, htyped⟩ :=
                      view.operationalField_hasType_of_typeFn
                        c.Ewf.conversionRegular c.Δwf hcode htypeFn hmajor
                    have typedFieldEq : typedField = field :=
                      Option.some.inj (htypedField.symm.trans hfield)
                    subst typedField
                    rw [← hsemanticDomain] at htyped
                    have htypedStrict := htyped.defeqU_l c.Ewf c.Δwf
                      ⟨_, hdomEq.symm⟩
                    have hpropStrict := hprop rfl
                    have hsortEq := htypedStrict.uniqU c.Ewf c.Δwf hpropStrict
                    have fieldSortZero :=
                      VEnv.IsDefEqU.sort_inv c.Ewf c.Δwf hsortEq
                    have hprojector :=
                      hview.operationalProgram_hasType_of_runtimePrefix_small
                        c.Ewf runtime mode fieldSortZero c.Δwf hlevels
                        hlevelsLength hparamsLength hparamsSpine hcode
                    simpa only [sourceArgument, Nat.add_assoc,
                      Nat.add_left_comm, Nat.add_comm] using
                      (continueWithProjector propState hprojector)

theorem inferProjFields.WF_runtimeRestored {c : VContext} {s : VState}
    {view : VRestoredBlockStructureView} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {tailResult cursor : VExpr}
    {majorCursor constructorCursor : VExpr}
    (hstruct : c.TrExprS struct major)
    (hview : view.ConstructorParameterLayoutWF c.venv)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (recEntriesClosed :
      VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (hlevels : ∀ level ∈ levels, level.WF c.lparams.length)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (view.familyType.instL levels) params (.sort resultLevel))
    (hname : view.name = typeName)
    (hmajor : c.HasType major (view.structureType levels params))
    (hrBelow : c.FVarsBelow proj r)
    (hstructBelow : c.FVarsBelow proj struct)
    (hbound : fieldIdx + count <
      (view.specializedFields levels params).length)
    (hr : c.TrExpr r cursor)
    (hcursor : VExpr.consumeForalls?
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.operationalProjectionArgs levels params fieldIdx major) =
        some cursor)
    (runtime : view.OperationalRuntimePrefix c.venv c.lparams.length
      c.vlctx.toCtx levels params fieldIdx)
    (semanticSupport : ProjectionSpineSupport (count + 1) r cursor)
    (majorSupport : ProjectionSpineSupport (count + 1) r majorCursor)
    (hmajorCursor :
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero)).consumeForalls?
          (view.operationalProjectionArgs levels
            (params.map (VExpr.liftN 1)) fieldIdx (.bvar 0)) =
        some majorCursor)
    (constructorSupport :
      ProjectionSpineSupport (count + 1) r constructorCursor)
    (hconstructorCursor :
      let fields := view.specializedFields levels params
      let fieldCount := fields.length
      (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
        (.sort .zero)).consumeForalls?
          (((view.operationalProjectionCodes levels params).take fieldIdx).map
            fun prior => .app (prior.projector.liftN fieldCount)
              (view.projectionConstructorApp levels params fields)) =
        some constructorCursor)
    (hsmallMaybe : view.elimination = .small →
      maybePropType = true) :
    (inferProjFields proj typeName struct maybePropType fieldIdx count r).WF
      c s fun out _ =>
        ∃ cursor' majorCursor' constructorCursor',
          VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.operationalProjectionArgs levels params
              (fieldIdx + count) major) = some cursor' ∧
          (VExpr.forallN
            (view.specializedFields levels (params.map (VExpr.liftN 1)))
            (.sort .zero)).consumeForalls?
              (view.operationalProjectionArgs levels
                (params.map (VExpr.liftN 1)) (fieldIdx + count) (.bvar 0)) =
            some majorCursor' ∧
          (let fields := view.specializedFields levels params
           let fieldCount := fields.length
           (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
             (.sort .zero)).consumeForalls?
               (((view.operationalProjectionCodes levels params).take
                 (fieldIdx + count)).map fun prior =>
                   .app (prior.projector.liftN fieldCount)
                     (view.projectionConstructorApp levels params fields)) =
             some constructorCursor') ∧
          c.FVarsBelow proj out ∧ c.TrExpr out cursor' ∧
          ProjectionSpineSupport 1 out cursor' ∧
          ProjectionSpineSupport 1 out majorCursor' ∧
          ProjectionSpineSupport 1 out constructorCursor' ∧
          view.OperationalRuntimePrefix c.venv c.lparams.length
            c.vlctx.toCtx levels params (fieldIdx + count) := by
  induction count generalizing s r cursor majorCursor constructorCursor fieldIdx with
  | zero =>
      simp only [inferProjFields, Nat.add_zero]
      exact .pure ⟨cursor, majorCursor, constructorCursor, hcursor,
        hmajorCursor, hconstructorCursor, hrBelow, hr, semanticSupport,
        majorSupport, constructorSupport, runtime⟩
  | succ count ih =>
      simp only [inferProjFields]
      have hfieldIdx : fieldIdx <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : fieldIdx <
          (view.operationalProjectionCodes levels params).length := by
        simpa using hfieldIdx
      let code := (view.operationalProjectionCodes levels params)[fieldIdx]
      have hcode :
          (view.operationalProjectionCodes levels params)[fieldIdx]? =
            some code :=
        List.getElem?_eq_getElem hcodeIdx
      cases semanticSupport with
      | @cons semanticRemaining sourceBody semanticBody sourceName sourceDomain
          sourceBinderInfo semanticDomain semanticSkip semanticTail =>
        cases majorSupport with
        | @cons majorRemaining _ majorBody _ _ _ majorDomain majorSkip majorTail =>
          cases constructorSupport with
          | @cons constructorRemaining _ constructorBody _ _ _ constructorDomain
              constructorSkip constructorTail =>
            refine whnf.WF_forall.bind fun out nextState _ outEq => ?_
            subst out
            obtain ⟨strictTarget, strictTranslation, targetEq⟩ := hr
            let .forallE hdomTy hbodyTy hdom hbody := strictTranslation
            have hforallEq := targetEq.forallE_inv c.Ewf c.Δwf
            obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
            have hbodyTranslation : TrExpr c.venv c.lparams
                ((none, .vlam _) :: c.vlctx) sourceBody semanticBody :=
              ⟨_, hbody, _, hbodyEq⟩
            have bodyClosedOne : Closed sourceBody 1 := by
              have closed := hbody.closed
              simpa only [VLCtx.bvars, c.mlctx.noBV, Nat.zero_add] using closed
            have hargsLength :
                (view.operationalProjectionArgs levels params fieldIdx major).length =
                  fieldIdx :=
              view.operationalProjectionArgs_length levels params fieldIdx major
                (Nat.le_of_lt hcodeIdx)
            obtain ⟨field, semanticTailBody, hfield, hconsume⟩ :=
              VExpr.consumeForalls?_forallN_domain
                (view.specializedFields levels params) tailResult
                (view.operationalProjectionArgs levels params fieldIdx major)
                (by simpa [hargsLength] using hfieldIdx)
            rw [hargsLength] at hfield
            have hsemanticDomain : semanticDomain =
                field.instRevAt
                  (view.operationalProjectionArgs levels params fieldIdx major) 0 := by
              have cursorShape :
                  (.forallE semanticDomain semanticBody : VExpr) =
                    .forallE
                      (field.instRevAt
                        (view.operationalProjectionArgs levels params fieldIdx major) 0)
                      semanticTailBody :=
                Option.some.inj (hcursor.symm.trans hconsume)
              injection cursorShape
            have hsemanticBody : semanticBody = semanticTailBody := by
              have cursorShape :
                  (.forallE semanticDomain semanticBody : VExpr) =
                    .forallE
                      (field.instRevAt
                        (view.operationalProjectionArgs levels params fieldIdx major) 0)
                      semanticTailBody :=
                Option.some.inj (hcursor.symm.trans hconsume)
              injection cursorShape
            subst semanticTailBody
            cases dependency : sourceBody.hasLooseBVar 0 with
            | false =>
              simp only [dependency, Bool.false_and, Bool.false_eq_true,
                if_false]
              have structuralClosed :
                  sourceBody.hasLooseBVar' 0 = false := by
                rw [← Expr.hasLooseBVar_eq]
                exact dependency
              have bodyClosedZero : Closed sourceBody 0 :=
                bodyClosedOne.zero_of_one_of_hasLooseBVar_false structuralClosed
              let sourceArgument : Expr :=
                .proj typeName fieldIdx struct
              let semanticArgument : VExpr := .app code.projector major
              let majorArgument : VExpr :=
                (code.liftN 1 0).projector.app (.bvar 0)
              let fields := view.specializedFields levels params
              let fieldCount := fields.length
              let constructorArgument : VExpr :=
                (code.liftN fieldCount 0).projector.app
                  (view.projectionConstructorApp levels params fields)
              have hnext : c.TrExpr
                  (sourceBody.instantiate1 sourceArgument)
                  (semanticBody.inst semanticArgument) := by
                simpa only [Expr.instantiate1_eq] using
                  Lean4Lean.TrExpr.instantiate1_skipped c.Ewf c.Δwf hdomTy
                    hbodyTranslation bodyClosedZero
                    (semanticSkip structuralClosed) sourceArgument semanticArgument
              have hnextBelow : c.FVarsBelow proj
                  (sourceBody.instantiate1 sourceArgument) := by
                rw [Expr.instantiate1_eq,
                  Expr.instantiate1_eq_self bodyClosedZero.looseBVarRange_zero]
                intro P hP hproj
                exact (hrBelow P hP hproj).2
              have semanticSupportNext : ProjectionSpineSupport (count + 1)
                  (sourceBody.instantiate1 sourceArgument)
                  (semanticBody.inst semanticArgument) := by
                simpa only [sourceArgument, semanticArgument,
                  Expr.instantiate1_eq] using
                  semanticTail.instN
                    (sourceArgument := sourceArgument)
                    (targetArgument := semanticArgument) (depth := 0)
              have majorSupportNext : ProjectionSpineSupport (count + 1)
                  (sourceBody.instantiate1 sourceArgument)
                  (majorBody.inst majorArgument) := by
                simpa only [sourceArgument, majorArgument,
                  Expr.instantiate1_eq] using
                  majorTail.instN
                    (sourceArgument := sourceArgument)
                    (targetArgument := majorArgument) (depth := 0)
              have constructorSupportNext : ProjectionSpineSupport (count + 1)
                  (sourceBody.instantiate1 sourceArgument)
                  (constructorBody.inst constructorArgument) := by
                simpa only [sourceArgument, constructorArgument,
                  Expr.instantiate1_eq] using
                  constructorTail.instN
                    (sourceArgument := sourceArgument)
                    (targetArgument := constructorArgument) (depth := 0)
              have runtimeNext := runtime.snocSkip codeNaturality recEntriesClosed hparamsLength
                hmajorCursor (majorSkip structuralClosed)
                hconstructorCursor (constructorSkip structuralClosed) hcode
              have hcursorNext : VExpr.consumeForalls?
                  (VExpr.forallN (view.specializedFields levels params) tailResult)
                  (view.operationalProjectionArgs levels params
                    (fieldIdx + 1) major) =
                    some (semanticBody.inst semanticArgument) := by
                rw [view.operationalProjectionArgs_succ levels params
                  fieldIdx major hcode]
                rw [VExpr.consumeForalls?_append, hcursor]
                rfl
              let paramsLift := params.map (VExpr.liftN 1)
              have hcodesLift := view.operationalProjectionCodes_liftN codeNaturality recEntriesClosed
                levels params hparamsLength 1 0
              have hcodeLift :
                  (view.operationalProjectionCodes levels paramsLift)[fieldIdx]? =
                    some (code.liftN 1 0) := by
                rw [← hcodesLift, List.getElem?_map, hcode]
                rfl
              have hmajorCursorNext :
                  (VExpr.forallN
                    (view.specializedFields levels (params.map (VExpr.liftN 1)))
                    (.sort .zero)).consumeForalls?
                      (view.operationalProjectionArgs levels
                        (params.map (VExpr.liftN 1)) (fieldIdx + 1) (.bvar 0)) =
                    some (majorBody.inst majorArgument) := by
                rw [view.operationalProjectionArgs_succ levels paramsLift
                  fieldIdx (.bvar 0) hcodeLift]
                rw [VExpr.consumeForalls?_append, hmajorCursor]
                rfl
              have hconstructorCursorNext :
                  (let fields := view.specializedFields levels params
                   let fieldCount := fields.length
                   (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
                     (.sort .zero)).consumeForalls?
                       (((view.operationalProjectionCodes levels params).take
                         (fieldIdx + 1)).map fun prior =>
                           .app (prior.projector.liftN fieldCount)
                             (view.projectionConstructorApp levels params fields)) =
                     some (constructorBody.inst constructorArgument)) := by
                simp only [List.take_add_one, hcode, Option.toList_some,
                  List.map_append, List.map_singleton,
                  VExpr.consumeForalls?_append, hconstructorCursor,
                  constructorArgument, fields, fieldCount]
                rfl
              have hboundNext : fieldIdx + 1 + count <
                  (view.specializedFields levels params).length := by omega
              have hrec := ih (s := nextState) hnextBelow hboundNext hnext
                hcursorNext runtimeNext semanticSupportNext majorSupportNext
                hmajorCursorNext constructorSupportNext hconstructorCursorNext
              simpa only [pure_bind, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm] using hrec
            | true =>
              let sourceArgument : Expr :=
                .proj typeName fieldIdx struct
              let semanticArgument : VExpr := .app code.projector major
              let majorArgument : VExpr :=
                (code.liftN 1 0).projector.app (.bvar 0)
              let fields := view.specializedFields levels params
              let fieldCount := fields.length
              let constructorArgument : VExpr :=
                (code.liftN fieldCount 0).projector.app
                  (view.projectionConstructorApp levels params fields)
              have continueWithProjector (continuationState : VState)
                  (hprojector : c.HasType code.projector
                    (.forallE (view.structureType levels params)
                      (.app code.typeFn.lift (.bvar 0)))) :
                  (inferProjFields proj typeName struct maybePropType
                    (fieldIdx + 1) count
                    (sourceBody.instantiate1 sourceArgument)).WF
                    c continuationState fun out _ =>
                      ∃ cursor' majorCursor' constructorCursor',
                        VExpr.consumeForalls?
                          (VExpr.forallN
                            (view.specializedFields levels params) tailResult)
                          (view.operationalProjectionArgs levels params
                            (fieldIdx + 1 + count) major) = some cursor' ∧
                        (VExpr.forallN
                          (view.specializedFields levels
                            (params.map (VExpr.liftN 1)))
                          (.sort .zero)).consumeForalls?
                            (view.operationalProjectionArgs levels
                              (params.map (VExpr.liftN 1))
                              (fieldIdx + 1 + count) (.bvar 0)) =
                          some majorCursor' ∧
                        (let fields := view.specializedFields levels params
                         let fieldCount := fields.length
                         (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
                           (.sort .zero)).consumeForalls?
                             (((view.operationalProjectionCodes levels params).take
                               (fieldIdx + 1 + count)).map fun prior =>
                                 .app (prior.projector.liftN fieldCount)
                                   (view.projectionConstructorApp levels params fields)) =
                           some constructorCursor') ∧
                        c.FVarsBelow proj out ∧ c.TrExpr out cursor' ∧
                        ProjectionSpineSupport 1 out cursor' ∧
                        ProjectionSpineSupport 1 out majorCursor' ∧
                        ProjectionSpineSupport 1 out constructorCursor' ∧
                        view.OperationalRuntimePrefix c.venv c.lparams.length
                          c.vlctx.toCtx levels params
                            (fieldIdx + 1 + count) := by
                obtain ⟨projectorField, _projectorDomain, typeBody, hprojectorField,
                    htypeFn, hprojectorFieldType⟩ :=
                  hview.toLayoutWF.operationalProjector_hasType_field_of_type
                    c.Ewf.conversionRegular recEntriesClosed hlevelsLength c.Δwf hcode hprojector hmajor
                have hprojectorFieldEq : projectorField = field :=
                  Option.some.inj (hprojectorField.symm.trans hfield)
                subst projectorField
                rw [← hsemanticDomain] at hprojectorFieldType
                have hprojectorFieldType' :=
                  hprojectorFieldType.defeqU_r c.Ewf c.Δwf
                    ⟨_, hdomEq.symm⟩
                have hprojSem : VRestoredBlockStructureView.TrProj c.venv
                    c.lparams.length c.vlctx.toCtx view
                    levels params fieldIdx major semanticArgument := {
                  viewWF := hview.toFamilyLayoutWF
                  parameterLayout := hview
                  codeNaturality := codeNaturality
                  recEntriesClosed := recEntriesClosed
                  levelsWF := hlevels
                  levels_length := hlevelsLength
                  params_length := hparamsLength
                  paramsSpine := hparamsSpine
                  majorType := hmajor
                  program := ⟨code, hcode, rfl, hprojector⟩ }
                have hprojStrict : c.TrExprS sourceArgument semanticArgument :=
                  .proj hstruct ⟨.restored view, levels, params, hname,
                    .restored hprojSem⟩
                have hnext : c.TrExpr
                    (sourceBody.instantiate1 sourceArgument)
                    (semanticBody.inst semanticArgument) := by
                  simpa only [sourceArgument, semanticArgument,
                    Expr.instantiate1_eq] using
                    (.inst c.Ewf c.Δwf hprojectorFieldType'
                      hbodyTranslation
                      (hprojStrict.trExpr c.Ewf.ordered c.Δwf))
                have hnextBelow : c.FVarsBelow proj
                    (sourceBody.instantiate1 sourceArgument) := by
                  intro P hP hproj
                  have bodyFVars := (hrBelow P hP hproj).2
                  have projectionFVars : FVarsIn P sourceArgument := by
                    simpa [sourceArgument, FVarsIn] using
                      hstructBelow P hP hproj
                  simpa only [Expr.instantiate1_eq] using
                    bodyFVars.instantiate1 projectionFVars
                have semanticSupportNext : ProjectionSpineSupport (count + 1)
                    (sourceBody.instantiate1 sourceArgument)
                    (semanticBody.inst semanticArgument) := by
                  simpa only [sourceArgument, semanticArgument,
                    Expr.instantiate1_eq] using
                    semanticTail.instN
                      (sourceArgument := sourceArgument)
                      (targetArgument := semanticArgument) (depth := 0)
                have majorSupportNext : ProjectionSpineSupport (count + 1)
                    (sourceBody.instantiate1 sourceArgument)
                    (majorBody.inst majorArgument) := by
                  simpa only [sourceArgument, majorArgument,
                    Expr.instantiate1_eq] using
                    majorTail.instN
                      (sourceArgument := sourceArgument)
                      (targetArgument := majorArgument) (depth := 0)
                have constructorSupportNext : ProjectionSpineSupport (count + 1)
                    (sourceBody.instantiate1 sourceArgument)
                    (constructorBody.inst constructorArgument) := by
                  simpa only [sourceArgument, constructorArgument,
                    Expr.instantiate1_eq] using
                    constructorTail.instN
                      (sourceArgument := sourceArgument)
                      (targetArgument := constructorArgument) (depth := 0)
                have runtimeNext := runtime.snocTyped hview codeNaturality recEntriesClosed c.Ewf c.Δwf
                  hlevels hlevelsLength hparamsLength hparamsSpine hcode
                  hprojector
                have hcursorNext : VExpr.consumeForalls?
                    (VExpr.forallN
                      (view.specializedFields levels params) tailResult)
                    (view.operationalProjectionArgs levels params
                      (fieldIdx + 1) major) =
                      some (semanticBody.inst semanticArgument) := by
                  rw [view.operationalProjectionArgs_succ levels params
                    fieldIdx major hcode]
                  rw [VExpr.consumeForalls?_append, hcursor]
                  rfl
                let paramsLift := params.map (VExpr.liftN 1)
                have hcodesLift := view.operationalProjectionCodes_liftN codeNaturality recEntriesClosed
                  levels params hparamsLength 1 0
                have hcodeLift :
                    (view.operationalProjectionCodes levels paramsLift)[fieldIdx]? =
                      some (code.liftN 1 0) := by
                  rw [← hcodesLift, List.getElem?_map, hcode]
                  rfl
                have hmajorCursorNext :
                    (VExpr.forallN
                      (view.specializedFields levels
                        (params.map (VExpr.liftN 1)))
                      (.sort .zero)).consumeForalls?
                        (view.operationalProjectionArgs levels
                          (params.map (VExpr.liftN 1))
                          (fieldIdx + 1) (.bvar 0)) =
                      some (majorBody.inst majorArgument) := by
                  rw [view.operationalProjectionArgs_succ levels paramsLift
                    fieldIdx (.bvar 0) hcodeLift]
                  rw [VExpr.consumeForalls?_append, hmajorCursor]
                  rfl
                have hconstructorCursorNext :
                    (let fields := view.specializedFields levels params
                     let fieldCount := fields.length
                     (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
                       (.sort .zero)).consumeForalls?
                         (((view.operationalProjectionCodes levels params).take
                           (fieldIdx + 1)).map fun prior =>
                             .app (prior.projector.liftN fieldCount)
                               (view.projectionConstructorApp levels params fields)) =
                       some (constructorBody.inst constructorArgument)) := by
                  simp only [List.take_add_one, hcode, Option.toList_some,
                    List.map_append, List.map_singleton,
                    VExpr.consumeForalls?_append, hconstructorCursor,
                    constructorArgument, fields, fieldCount]
                  rfl
                have hboundNext : fieldIdx + 1 + count <
                    (view.specializedFields levels params).length := by omega
                have hrec := ih (s := continuationState) hnextBelow hboundNext
                  hnext hcursorNext runtimeNext semanticSupportNext
                  majorSupportNext hmajorCursorNext constructorSupportNext
                  hconstructorCursorNext
                simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                  using hrec
              cases maybePropType with
              | false =>
                simp only [Bool.and_false, Bool.false_eq_true, if_false]
                have large : view.elimination = .large := by
                  cases mode : view.elimination with
                  | large => rfl
                  | small =>
                    have impossible := hsmallMaybe mode
                    contradiction
                have motiveLevel :=
                  view.motiveLevel_projectionLevels_of_large large
                    code.fieldSort levels
                have hprojector :=
                  hview.operationalProjector_hasType_of_runtimePrefix c.Ewf codeNaturality recEntriesClosed
                    runtime c.Δwf hlevels hlevelsLength hparamsLength
                    hparamsSpine hcode motiveLevel
                simpa only [sourceArgument, Nat.add_assoc, Nat.add_left_comm,
                  Nat.add_comm] using
                  (continueWithProjector nextState hprojector)
              | true =>
                simp only [dependency, Bool.and_true, if_true]
                refine (isProp.WF hdom).bind fun propResult propState _ hprop => ?_
                cases propResult with
                | false =>
                  simp only [Bool.not_false, Bool.true_eq_false, if_true]
                  exact invalidProj.WF
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, if_false]
                  cases mode : view.elimination with
                  | large =>
                    have motiveLevel :=
                      view.motiveLevel_projectionLevels_of_large mode
                        code.fieldSort levels
                    have hprojector :=
                      hview.operationalProjector_hasType_of_runtimePrefix c.Ewf codeNaturality recEntriesClosed
                        runtime c.Δwf hlevels hlevelsLength hparamsLength
                        hparamsSpine hcode motiveLevel
                    simpa only [sourceArgument, Nat.add_assoc,
                      Nat.add_left_comm, Nat.add_comm] using
                      (continueWithProjector propState hprojector)
                  | small =>
                    have htypeFn :=
                      hview.operationalProjectionTypeFn_hasType_of_sparse
                        c.Ewf codeNaturality recEntriesClosed c.Δwf hlevels hlevelsLength hparamsLength
                        hparamsSpine hcode runtime.1
                    obtain ⟨typedField, htypedField, htyped⟩ :=
                      view.operationalField_hasType_of_typeFn hview.toLayoutWF
                        c.Ewf.conversionRegular recEntriesClosed hlevelsLength c.Δwf hcode htypeFn hmajor
                    have typedFieldEq : typedField = field :=
                      Option.some.inj (htypedField.symm.trans hfield)
                    subst typedField
                    rw [← hsemanticDomain] at htyped
                    have htypedStrict := htyped.defeqU_l c.Ewf c.Δwf
                      ⟨_, hdomEq.symm⟩
                    have hpropStrict := hprop rfl
                    have hsortEq := htypedStrict.uniqU c.Ewf c.Δwf hpropStrict
                    have fieldSortZero :=
                      VEnv.IsDefEqU.sort_inv c.Ewf c.Δwf hsortEq
                    have hprojector :=
                      hview.operationalProjector_hasType_of_runtimePrefix_small
                        c.Ewf codeNaturality recEntriesClosed runtime mode fieldSortZero c.Δwf hlevels
                        hlevelsLength hparamsLength hparamsSpine hcode
                    simpa only [sourceArgument, Nat.add_assoc,
                      Nat.add_left_comm, Nat.add_comm] using
                      (continueWithProjector propState hprojector)


/-- Finish a runtime-backed projection after the source loop has consumed
exactly the preceding fields.  The remaining source Pi and all three
producer-aligned cursors select the requested field without constructing any
earlier projector that the runtime skipped. -/
theorem inferProjResult.WF_runtimeBlock {c : VContext} {s : VState}
    {view : VBlockStructureView} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {tailResult cursor : VExpr}
    {majorCursor constructorCursor : VExpr}
    (hstruct : c.TrExprS struct major)
    (hview : view.LayoutWF c.venv)
    (hlevels : ∀ level ∈ levels, level.WF c.lparams.length)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (view.familyType.instL levels) params (.sort resultLevel))
    (hname : view.name = typeName)
    (hmajor : c.HasType major (view.structureType levels params))
    (hrBelow : c.FVarsBelow (.proj typeName fieldIdx struct) r)
    (hbound : fieldIdx < (view.specializedFields levels params).length)
    (hr : c.TrExpr r cursor)
    (hcursor : VExpr.consumeForalls?
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.operationalProjectionArgs levels params fieldIdx major) =
        some cursor)
    (runtime : view.OperationalRuntimePrefix c.venv c.lparams.length
      c.vlctx.toCtx levels params fieldIdx)
    (semanticSupport : ProjectionSpineSupport 1 r cursor)
    (majorSupport : ProjectionSpineSupport 1 r majorCursor)
    (hmajorCursor :
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero)).consumeForalls?
          (view.operationalProjectionArgs levels
            (params.map (VExpr.liftN 1)) fieldIdx (.bvar 0)) =
        some majorCursor)
    (constructorSupport : ProjectionSpineSupport 1 r constructorCursor)
    (hconstructorCursor :
      let fields := view.specializedFields levels params
      let fieldCount := fields.length
      (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
        (.sort .zero)).consumeForalls?
          (((view.operationalProjectionCodes levels params).take fieldIdx).map
            fun prior => .app (prior.projector.liftN fieldCount)
              (view.projectionConstructorApp levels params fields)) =
        some constructorCursor)
    (hsmallMaybe : view.generation.elimination = .small →
      maybePropType = true) :
    (do
      let .forallE _ dom _ _ ← whnf r | invalidProj proj
      if maybePropType then
        if !(← isProp dom) then invalidProj proj
      pure dom).WF c s fun dom _ =>
        ∃ proj' ty', c.TrTyping (.proj typeName fieldIdx struct)
          dom proj' ty' := by
  have hcodeIdx : fieldIdx <
      (view.operationalProjectionCodes levels params).length := by
    simpa using hbound
  let code := (view.operationalProjectionCodes levels params)[fieldIdx]
  have hcode :
      (view.operationalProjectionCodes levels params)[fieldIdx]? = some code :=
    List.getElem?_eq_getElem hcodeIdx
  cases semanticSupport with
  | @cons semanticRemaining sourceBody semanticBody sourceName sourceDomain
      sourceBinderInfo semanticDomain semanticSkip semanticTail =>
    cases majorSupport with
    | @cons majorRemaining _ majorBody _ _ _ majorDomain majorSkip majorTail =>
      cases constructorSupport with
      | @cons constructorRemaining _ constructorBody _ _ _ constructorDomain
          constructorSkip constructorTail =>
        refine whnf.WF_forall.bind fun out nextState _ outEq => ?_
        subst out
        obtain ⟨strictTarget, strictTranslation, targetEq⟩ := hr
        let .forallE hdomTy hbodyTy hdom hbody := strictTranslation
        have hforallEq := targetEq.forallE_inv c.Ewf c.Δwf
        obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
        have hargsLength :
            (view.operationalProjectionArgs levels params fieldIdx major).length =
              fieldIdx :=
          view.operationalProjectionArgs_length levels params fieldIdx major
            (Nat.le_of_lt hcodeIdx)
        obtain ⟨field, semanticTailBody, hfield, hconsume⟩ :=
          VExpr.consumeForalls?_forallN_domain
            (view.specializedFields levels params) tailResult
            (view.operationalProjectionArgs levels params fieldIdx major)
            (by simpa [hargsLength] using hbound)
        rw [hargsLength] at hfield
        have hsemanticDomain : semanticDomain =
            field.instRevAt
              (view.operationalProjectionArgs levels params fieldIdx major) 0 := by
          have cursorShape :
              (.forallE semanticDomain semanticBody : VExpr) =
                .forallE
                  (field.instRevAt
                    (view.operationalProjectionArgs levels params fieldIdx major)
                    0)
                  semanticTailBody :=
            Option.some.inj (hcursor.symm.trans hconsume)
          injection cursorShape
        subst semanticDomain
        have hdomBelow : c.FVarsBelow
            (.proj typeName fieldIdx struct) sourceDomain := by
          intro P hP hproj
          exact (hrBelow P hP hproj).1
        have resultOfProjector
            (hprojector : c.venv.HasType c.lparams.length c.vlctx.toCtx
              code.projector
              (.forallE (view.structureType levels params)
                (.app code.typeFn.lift (.bvar 0)))) :
            ∃ proj' ty', c.TrTyping (.proj typeName fieldIdx struct)
              sourceDomain proj' ty' := by
          obtain ⟨field', typeBody, hfield', htypeFn,
              hprojectorField⟩ :=
            VBlockStructureView.operationalProjector_hasType_field_of_type
              c.Ewf.conversionRegular c.Δwf hcode hprojector hmajor
          have hfieldEq : field' = field :=
            Option.some.inj (hfield'.symm.trans hfield)
          subst field'
          have hprojectorField' := hprojectorField.defeqU_r
            c.Ewf c.Δwf ⟨_, hdomEq.symm⟩
          have hprojSem : VProjectionView.TrProj c.venv
              c.lparams.length c.vlctx.toCtx (.block view) levels params
              fieldIdx major (.app code.projector major) := {
            viewWF := .ofBlock hview
            levelsWF := hlevels
            levels_length := hlevelsLength
            params_length := hparamsLength
            paramsSpine := hparamsSpine
            majorType := hmajor
            program := ⟨code, hcode, rfl, hprojector⟩ }
          have hprojStrict : c.TrExprS (.proj typeName fieldIdx struct)
              (.app code.projector major) :=
            .proj hstruct ⟨.ordinary (.block view), levels, params, hname,
              .ordinary hprojSem⟩
          exact ⟨.app code.projector major, _, hdomBelow, hprojStrict,
            hdom, hprojectorField'⟩
        cases maybePropType with
        | false =>
          simp only [if_false]
          have large : view.generation.elimination = .large := by
            cases mode : view.generation.elimination with
            | large => rfl
            | small =>
              have impossible := hsmallMaybe mode
              contradiction
          have motiveLevel :=
            view.motiveLevel_projectionLevels_of_large large code.fieldSort
              levels
          have hprojector :=
            hview.operationalProgram_hasType_of_runtimePrefix c.Ewf runtime
              c.Δwf hlevels hlevelsLength hparamsLength hparamsSpine hcode
              motiveLevel
          exact .pure (resultOfProjector hprojector)
        | true =>
          simp only [if_true]
          refine (isProp.WF hdom).bind fun propResult propState _ hprop => ?_
          cases propResult with
          | false =>
            simp only [Bool.not_false, if_true]
            exact invalidProj.WF
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, if_false]
            cases mode : view.generation.elimination with
            | large =>
              have motiveLevel :=
                view.motiveLevel_projectionLevels_of_large mode
                  code.fieldSort levels
              have hprojector :=
                hview.operationalProgram_hasType_of_runtimePrefix c.Ewf
                  runtime c.Δwf hlevels hlevelsLength hparamsLength
                  hparamsSpine hcode motiveLevel
              exact .pure (resultOfProjector hprojector)
            | small =>
              have htypeFn :=
                hview.operationalProjectionTypeFn_hasType_of_sparse c.Ewf
                  c.Δwf hlevels hlevelsLength hparamsLength hparamsSpine
                  hcode runtime.1
              obtain ⟨typedField, htypedField, htyped⟩ :=
                view.operationalField_hasType_of_typeFn
                  c.Ewf.conversionRegular c.Δwf hcode htypeFn hmajor
              have typedFieldEq : typedField = field :=
                Option.some.inj (htypedField.symm.trans hfield)
              subst typedField
              have htypedStrict := htyped.defeqU_l c.Ewf c.Δwf
                ⟨_, hdomEq.symm⟩
              have hpropStrict := hprop rfl
              have hsortEq := htypedStrict.uniqU c.Ewf c.Δwf hpropStrict
              have fieldSortZero :=
                VEnv.IsDefEqU.sort_inv c.Ewf c.Δwf hsortEq
              have hprojector :=
                hview.operationalProgram_hasType_of_runtimePrefix_small
                  c.Ewf runtime mode fieldSortZero c.Δwf hlevels
                  hlevelsLength hparamsLength hparamsSpine hcode
              exact .pure (resultOfProjector hprojector)

/-- Restored counterpart of `inferProjResult.WF_runtimeBlock`, consuming
the exact producer-owned restored runtime cursors. -/
theorem inferProjResult.WF_runtimeRestored {c : VContext} {s : VState}
    {view : VRestoredBlockStructureView} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {tailResult cursor : VExpr}
    {majorCursor constructorCursor : VExpr}
    (hstruct : c.TrExprS struct major)
    (hview : view.ConstructorParameterLayoutWF c.venv)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (recEntriesClosed :
      VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (hlevels : ∀ level ∈ levels, level.WF c.lparams.length)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      c.venv.SpineWF c.lparams.length c.vlctx.toCtx
        (view.familyType.instL levels) params (.sort resultLevel))
    (hname : view.name = typeName)
    (hmajor : c.HasType major (view.structureType levels params))
    (hrBelow : c.FVarsBelow (.proj typeName fieldIdx struct) r)
    (hbound : fieldIdx < (view.specializedFields levels params).length)
    (hr : c.TrExpr r cursor)
    (hcursor : VExpr.consumeForalls?
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.operationalProjectionArgs levels params fieldIdx major) =
        some cursor)
    (runtime : view.OperationalRuntimePrefix c.venv c.lparams.length
      c.vlctx.toCtx levels params fieldIdx)
    (semanticSupport : ProjectionSpineSupport 1 r cursor)
    (majorSupport : ProjectionSpineSupport 1 r majorCursor)
    (hmajorCursor :
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero)).consumeForalls?
          (view.operationalProjectionArgs levels
            (params.map (VExpr.liftN 1)) fieldIdx (.bvar 0)) =
        some majorCursor)
    (constructorSupport : ProjectionSpineSupport 1 r constructorCursor)
    (hconstructorCursor :
      let fields := view.specializedFields levels params
      let fieldCount := fields.length
      (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
        (.sort .zero)).consumeForalls?
          (((view.operationalProjectionCodes levels params).take fieldIdx).map
            fun prior => .app (prior.projector.liftN fieldCount)
              (view.projectionConstructorApp levels params fields)) =
        some constructorCursor)
    (hsmallMaybe : view.elimination = .small →
      maybePropType = true) :
    (do
      let .forallE _ dom _ _ ← whnf r | invalidProj proj
      if maybePropType then
        if !(← isProp dom) then invalidProj proj
      pure dom).WF c s fun dom _ =>
        ∃ proj' ty', c.TrTyping (.proj typeName fieldIdx struct)
          dom proj' ty' := by
  have hcodeIdx : fieldIdx <
      (view.operationalProjectionCodes levels params).length := by
    simpa using hbound
  let code := (view.operationalProjectionCodes levels params)[fieldIdx]
  have hcode :
      (view.operationalProjectionCodes levels params)[fieldIdx]? = some code :=
    List.getElem?_eq_getElem hcodeIdx
  cases semanticSupport with
  | @cons semanticRemaining sourceBody semanticBody sourceName sourceDomain
      sourceBinderInfo semanticDomain semanticSkip semanticTail =>
    cases majorSupport with
    | @cons majorRemaining _ majorBody _ _ _ majorDomain majorSkip majorTail =>
      cases constructorSupport with
      | @cons constructorRemaining _ constructorBody _ _ _ constructorDomain
          constructorSkip constructorTail =>
        refine whnf.WF_forall.bind fun out nextState _ outEq => ?_
        subst out
        obtain ⟨strictTarget, strictTranslation, targetEq⟩ := hr
        let .forallE hdomTy hbodyTy hdom hbody := strictTranslation
        have hforallEq := targetEq.forallE_inv c.Ewf c.Δwf
        obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
        have hargsLength :
            (view.operationalProjectionArgs levels params fieldIdx major).length =
              fieldIdx :=
          view.operationalProjectionArgs_length levels params fieldIdx major
            (Nat.le_of_lt hcodeIdx)
        obtain ⟨field, semanticTailBody, hfield, hconsume⟩ :=
          VExpr.consumeForalls?_forallN_domain
            (view.specializedFields levels params) tailResult
            (view.operationalProjectionArgs levels params fieldIdx major)
            (by simpa [hargsLength] using hbound)
        rw [hargsLength] at hfield
        have hsemanticDomain : semanticDomain =
            field.instRevAt
              (view.operationalProjectionArgs levels params fieldIdx major) 0 := by
          have cursorShape :
              (.forallE semanticDomain semanticBody : VExpr) =
                .forallE
                  (field.instRevAt
                    (view.operationalProjectionArgs levels params fieldIdx major)
                    0)
                  semanticTailBody :=
            Option.some.inj (hcursor.symm.trans hconsume)
          injection cursorShape
        subst semanticDomain
        have hdomBelow : c.FVarsBelow
            (.proj typeName fieldIdx struct) sourceDomain := by
          intro P hP hproj
          exact (hrBelow P hP hproj).1
        have resultOfProjector
            (hprojector : c.venv.HasType c.lparams.length c.vlctx.toCtx
              code.projector
              (.forallE (view.structureType levels params)
                (.app code.typeFn.lift (.bvar 0)))) :
            ∃ proj' ty', c.TrTyping (.proj typeName fieldIdx struct)
              sourceDomain proj' ty' := by
          obtain ⟨field', _projectorDomain, typeBody, hfield', htypeFn,
              hprojectorField⟩ :=
            hview.toLayoutWF.operationalProjector_hasType_field_of_type
              c.Ewf.conversionRegular recEntriesClosed hlevelsLength c.Δwf
                hcode hprojector hmajor
          have hfieldEq : field' = field :=
            Option.some.inj (hfield'.symm.trans hfield)
          subst field'
          have hprojectorField' := hprojectorField.defeqU_r
            c.Ewf c.Δwf ⟨_, hdomEq.symm⟩
          have hprojSem : VRestoredBlockStructureView.TrProj c.venv
              c.lparams.length c.vlctx.toCtx view levels params fieldIdx major
              (.app code.projector major) := {
            viewWF := hview.toFamilyLayoutWF
            parameterLayout := hview
            codeNaturality := codeNaturality
            recEntriesClosed := recEntriesClosed
            levelsWF := hlevels
            levels_length := hlevelsLength
            params_length := hparamsLength
            paramsSpine := hparamsSpine
            majorType := hmajor
            program := ⟨code, hcode, rfl, hprojector⟩ }
          have hprojStrict : c.TrExprS (.proj typeName fieldIdx struct)
              (.app code.projector major) :=
            .proj hstruct ⟨.restored view, levels, params, hname,
              .restored hprojSem⟩
          exact ⟨.app code.projector major, _, hdomBelow, hprojStrict,
            hdom, hprojectorField'⟩
        cases maybePropType with
        | false =>
          simp only [if_false]
          have large : view.elimination = .large := by
            cases mode : view.elimination with
            | large => rfl
            | small =>
              have impossible := hsmallMaybe mode
              contradiction
          have motiveLevel :=
            view.motiveLevel_projectionLevels_of_large large code.fieldSort
              levels
          have hprojector :=
            hview.operationalProjector_hasType_of_runtimePrefix c.Ewf codeNaturality recEntriesClosed runtime
              c.Δwf hlevels hlevelsLength hparamsLength hparamsSpine hcode
              motiveLevel
          exact .pure (resultOfProjector hprojector)
        | true =>
          simp only [if_true]
          refine (isProp.WF hdom).bind fun propResult propState _ hprop => ?_
          cases propResult with
          | false =>
            simp only [Bool.not_false, if_true]
            exact invalidProj.WF
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, if_false]
            cases mode : view.elimination with
            | large =>
              have motiveLevel :=
                view.motiveLevel_projectionLevels_of_large mode
                  code.fieldSort levels
              have hprojector :=
                hview.operationalProjector_hasType_of_runtimePrefix c.Ewf codeNaturality recEntriesClosed
                  runtime c.Δwf hlevels hlevelsLength hparamsLength
                  hparamsSpine hcode motiveLevel
              exact .pure (resultOfProjector hprojector)
            | small =>
              have htypeFn :=
                hview.operationalProjectionTypeFn_hasType_of_sparse c.Ewf
                  codeNaturality recEntriesClosed c.Δwf hlevels hlevelsLength hparamsLength hparamsSpine
                  hcode runtime.1
              obtain ⟨typedField, htypedField, htyped⟩ :=
                view.operationalField_hasType_of_typeFn hview.toLayoutWF
                  c.Ewf.conversionRegular recEntriesClosed hlevelsLength c.Δwf hcode htypeFn hmajor
              have typedFieldEq : typedField = field :=
                Option.some.inj (htypedField.symm.trans hfield)
              subst typedField
              have htypedStrict := htyped.defeqU_l c.Ewf c.Δwf
                ⟨_, hdomEq.symm⟩
              have hpropStrict := hprop rfl
              have hsortEq := htypedStrict.uniqU c.Ewf c.Δwf hpropStrict
              have fieldSortZero :=
                VEnv.IsDefEqU.sort_inv c.Ewf c.Δwf hsortEq
              have hprojector :=
                hview.operationalProjector_hasType_of_runtimePrefix_small
                  c.Ewf codeNaturality recEntriesClosed runtime mode fieldSortZero c.Δwf hlevels
                  hlevelsLength hparamsLength hparamsSpine hcode
              exact .pure (resultOfProjector hprojector)



theorem inferProj.WF
    (heBelow : c.FVarsBelow e ety)
    (he : c.TrExprS e e') (hty : c.TrExprS ety ety')
    (hasty : c.HasType e' ety') :
    (inferProj st i e ety).WF c s fun ty _ =>
      ∃ proj' ty', c.TrTyping (.proj st i e) ty proj' ty' := by
  unfold inferProj
  refine (whnf.WF hty).bind fun type _ _ ⟨htypeBelow, htype⟩ => ?_
  have hprojBelowType : c.FVarsBelow (.proj st i e) type := by
    intro P hP hproj
    exact htypeBelow P hP (heBelow P hP (by simpa [FVarsIn] using hproj))
  obtain ⟨type', htypeS, htypeEq⟩ := htype
  rw [Expr.withApp_eq]
  have ⟨family', hstack⟩ := AppStack.build
    (type.mkAppList_getAppArgsList ▸ htypeS)
  simp only
  split
  · rename_i familyName familyLevels hfamilyShape
    refine .getEnv ?_
    by_cases hname : st = familyName
    · subst st
      have hnameTest : (familyName != familyName) = false := by simp
      rw [hnameTest]
      refine (M.WF.liftExcept envGet.WF).lift.bind fun ci _ _ hfind => ?_
      split
      · rename_i info
        split
        · rename_i constructor hctors
          split
          · rename_i hready
            split
            · exact invalidProj.WF
            · rename_i hargs
              obtain ⟨resolution⟩ :=
                c.projectionReady.infer familyName info hfind hready
              cases resolution with
              | ordinary artifact =>
                have hhead := hstack.tr
                rw [hfamilyShape] at hhead
                let .const (us' := levels') hfamilyConst hlevelsMap
                  hlevelsLength := hhead
                have hviewFamily := artifact.viewWF.family
                rw [artifact.name_eq] at hviewFamily
                rw [hviewFamily] at hfamilyConst
                cases hfamilyConst
                have hlevelsWF : ∀ level ∈ levels',
                    level.WF c.lparams.length :=
                  VLevel.WF.of_mapM_ofLevel hlevelsMap
                have hlevelsFamilyLength : levels'.length =
                    artifact.view.familyRaw.uvars :=
                  (List.mapM_eq_some.1 hlevelsMap).length_eq.symm.trans
                    hlevelsLength
                have hlevelsLength' : levels'.length = artifact.view.uvars := by
                  exact hlevelsFamilyLength.trans artifact.view.family_uvars_eq
                have hargsSize : type.getAppArgs.size =
                    info.numParams + info.numIndices := by
                  simpa using hargs
                have hargsLength : type.getAppArgsList.length =
                    artifact.view.nparams := by
                  rw [← Expr.getAppArgs_toList]
                  simp [hargsSize,
                    artifact.numParams_eq, artifact.numIndices_eq]
                have hfamilyType : c.HasType (.const familyName levels')
                    (artifact.view.familyType.instL levels') := by
                  simpa [artifact.name_eq] using
                    artifact.viewWF.familyConst_hasType c.Ewf.ordered
                      (Γ := c.vlctx.toCtx) levels' hlevelsWF hlevelsLength'
                have hfamilyTypeShape : c.HasType (.const familyName levels')
                    (VExpr.forallN
                      (artifact.view.rawParams.map (VExpr.instL levels'))
                      (.sort (artifact.view.resultLevel.inst levels'))) := by
                  simpa [artifact.view.familyType_eq_forallN,
                    VExpr.instL_forallN, VExpr.instL] using hfamilyType
                have hargsRawLength : type.getAppArgsList.length =
                    (artifact.view.rawParams.map
                      (VExpr.instL levels')).length := by
                  simpa [artifact.view.rawParams_length] using hargsLength
                obtain ⟨params', hparamsTr, hparamsSpineRaw, htypeFull⟩ :=
                  AppStack.toSpineWF hstack hfamilyTypeShape hargsRawLength
                rw [type.mkAppList_getAppArgsList] at htypeFull
                have htypeAppliedEq := htypeFull.uniq c.Ewf
                  (.refl c.Ewf c.Δwf) htypeS
                have hmajorType : c.HasType e'
                    (artifact.view.structureType levels' params') := by
                  apply hasty.defeqU_r c.Ewf c.Δwf
                  have := (htypeAppliedEq.trans c.Ewf c.Δwf htypeEq).symm
                  simpa [VProjectionView.structureType,
                    artifact.name_eq] using this
                have hparamsLength : params'.length =
                    artifact.view.nparams :=
                  hparamsTr.length_eq.symm.trans hargsLength
                have hparamsRawLength : params'.length =
                    (artifact.view.rawParams.map
                      (VExpr.instL levels')).length :=
                  hparamsTr.length_eq.symm.trans hargsRawLength
                have hparamsSpine : ∃ resultLevel,
                    c.venv.SpineWF c.lparams.length c.vlctx.toCtx
                      (artifact.view.familyType.instL levels') params'
                      (.sort resultLevel) := by
                  refine ⟨artifact.view.resultLevel.inst levels', ?_⟩
                  rw [VExpr.instRev_closedN params' (by trivial)] at hparamsSpineRaw
                  simpa [artifact.view.familyType_eq_forallN,
                    VExpr.instL_forallN, VExpr.forallN,
                    VExpr.instRev, VExpr.instL] using hparamsSpineRaw
                have hconstructorName :
                    constructor = artifact.view.constructorName := by
                  have := hctors.symm.trans artifact.ctors_eq
                  simpa using this
                refine (M.WF.liftExcept envGet.WF).lift.bind
                  fun c_info _ _ hctorFind => ?_
                cases c_info with
                | ctorInfo ctorInfo =>
                  simp only
                  split
                  · rename_i hidxHost
                    have hctorInfoEq :
                        ctorInfo = artifact.constructorInfo := by
                      rw [hconstructorName, artifact.constructor_find] at hctorFind
                      exact ConstantInfo.ctorInfo.inj
                        (Option.some.inj hctorFind.symm)
                    have hiFields : i <
                        (artifact.view.specializedFields levels' params').length := by
                      rw [hctorInfoEq,
                        artifact.constructor_numFields_eq] at hidxHost
                      simpa using hidxHost
                    have hviewConstructor : c.venv.constants constructor =
                        some artifact.view.constructor.raw.toVConstant := by
                      simpa [hconstructorName] using
                        artifact.viewWF.constructor_registered
                    obtain ⟨_, hctorTr⟩ :=
                      c.trenv.find?_uniq hctorFind hviewConstructor
                    have hrawCtorUvars :
                        artifact.view.constructor.raw.uvars =
                          artifact.view.uvars := by
                      exact artifact.view.constructor_uvars_eq
                    have hctorLevelLength :
                        ctorInfo.levelParams.length = familyLevels.length :=
                      hctorTr.2.1.trans <| hrawCtorUvars.trans <|
                        hlevelsLength'.symm.trans
                          (List.mapM_eq_some.1 hlevelsMap).length_eq.symm
                    have hctorType₀ := hctorTr.2.2.instLCpp c.Ewf
                      (Us := c.lparams) (ls' := levels') (Δ := [])
                      trivial hlevelsMap hctorLevelLength
                    have hctorType := hctorType₀.weakFV c.Ewf
                      (.from_nil c.mlctx.noBV) c.Δwf
                    rw [(c.Ewf.ordered.closedC
                      hviewConstructor).instL.liftN_eq
                        (Nat.le_refl _)] at hctorType
                    let ctorTail := VExpr.forallN
                      (artifact.view.fields.map (VExpr.instL levels'))
                      ((artifact.view.constructor.rawResult
                        artifact.view.nparams).instL levels')
                    rw [artifact.view.constructor.rawType_eq] at hctorType
                    have hinstantiate :
                        ((.ctorInfo ctorInfo : ConstantInfo)
                          |>.instantiateTypeLevelParamsCpp familyLevels) =
                        ctorInfo.type.instantiateLevelParamsCpp
                          ctorInfo.levelParams familyLevels := rfl
                    have hctorTypeShape : c.TrExpr
                        ((.ctorInfo ctorInfo : ConstantInfo)
                          |>.instantiateTypeLevelParamsCpp familyLevels)
                        (VExpr.forallN
                          (artifact.view.constructorParams.map
                            (VExpr.instL levels')) ctorTail) := by
                      simpa [ConstantInfo.instantiateTypeLevelParamsCpp,
                        ConstantInfo.type, ConstantInfo.levelParams,
                        ConstantInfo.toConstantVal, ctorTail,
                        VInductDecl.NormalizedCtor.declaredBinders,
                        VProjectionView.nparams,
                        VProjectionView.source,
                        VProjectionView.constructor,
                        VProjectionView.constructorParams,
                        VProjectionView.fields,
                        VExpr.instL_forallN, VExpr.forallN_append,
                        List.map_append] using hctorType
                    have hctorTypeBelow : c.FVarsBelow (.proj familyName i e)
                        ((.ctorInfo ctorInfo : ConstantInfo)
                          |>.instantiateTypeLevelParamsCpp familyLevels) := by
                      intro P _ _
                      simpa [ConstantInfo.instantiateTypeLevelParamsCpp,
                        ConstantInfo.type, ConstantInfo.levelParams,
                        ConstantInfo.toConstantVal] using
                          hctorType₀.fvarsIn.mono nofun
                    have hparamArgsEq :
                        List.take info.numParams type.getAppArgs.toList =
                          type.getAppArgsList := by
                      simp [Expr.getAppArgs_toList, artifact.numParams_eq,
                        ← hargsLength]
                    have hparamArgsTr :
                        (List.take info.numParams
                          type.getAppArgs.toList).Forall₂
                          (c.TrExprS · ·) params' := by
                      simpa [hparamArgsEq] using hparamsTr
                    have hparamArgsBelow : ∀ arg ∈
                        List.take info.numParams type.getAppArgs.toList,
                        c.FVarsBelow (.proj familyName i e) arg := by
                      intro arg harg P hP hproj
                      apply FVarsIn.getAppArgsList
                        (hprojBelowType P hP hproj)
                      simpa [hparamArgsEq] using harg
                    have hctorParamsSpine :=
                      artifact.viewWF.constructorParamsSpine c.Ewf.ordered
                        levels' hlevelsWF hlevelsLength' params' hparamsLength
                        hparamsSpine ctorTail
                    refine (M.WF.liftExcept envGet.WF).lift.bind
                      fun rec_info _ _ hrecFind => ?_
                    cases rec_info with
                    | recInfo recInfo =>
                      obtain ⟨rawRecursor, hviewRecursor, hrawRecUvars⟩ :=
                        artifact.viewWF.recursor_registered
                      have hrecursorName : mkRecName familyName =
                          artifact.view.recursorName := by
                        simpa only [mkRecName, VProjectionView.recursorName] using
                          congrArg (fun name => name.str "rec")
                            artifact.name_eq.symm
                      rw [← hrecursorName] at hviewRecursor
                      obtain ⟨_, hrecTr⟩ :=
                        c.trenv.find?_uniq hrecFind hviewRecursor
                      have hrecLevelLength : recInfo.levelParams.length =
                          artifact.view.recUvars :=
                        hrecTr.2.1.trans hrawRecUvars
                      cases artifact.programs with
                      | dense programs =>
                          refine (inferProjParams.WF hparamArgsTr hctorTypeBelow
                            hparamArgsBelow hctorTypeShape hctorParamsSpine).bind
                              fun r _ _ hr => ?_
                          obtain ⟨hrBelow, hr⟩ := hr
                          let tailResult :=
                            ((artifact.view.constructor.rawResult
                              artifact.view.nparams).instL levels').instRevAt
                                params' artifact.view.fields.length
                          have hctorTailInst : ctorTail.instRev params' =
                              VExpr.forallN
                                (artifact.view.specializedFields levels' params')
                                tailResult := by
                            simp [ctorTail, tailResult,
                              VExpr.instRev_forallN_projection,
                              VProjectionView.specializedFields_eq,
                              VExpr.instRevAt_map_instL_zipIdx]
                          rw [hctorTailInst] at hr
                          refine (getSortLevel.WF htypeS).bind
                            fun sortLevel nextState _ _ => ?_
                          split
                          · exact invalidProj.WF
                          · rename_i hrecGate
                            have hstructBelow : c.FVarsBelow
                                (.proj familyName i e) e := by
                              intro P _ hproj
                              simpa [FVarsIn] using hproj
                            have hcursorZero : VExpr.consumeForalls?
                                (VExpr.forallN
                                  (artifact.view.specializedFields levels' params')
                                  tailResult)
                                (artifact.view.projectionArgs levels' params' 0 e') =
                                  some (VExpr.forallN
                                    (artifact.view.specializedFields levels' params')
                                    tailResult) := by
                              rfl
                            refine (inferProjFields.WF he artifact.viewWF hlevelsWF
                              hlevelsLength' hparamsLength hparamsSpine
                              programs.programsWF artifact.name_eq hmajorType
                              hrBelow hstructBelow (by simpa using hiFields) hr
                              hcursorZero).bind
                                fun r _ _ hr => ?_
                            obtain ⟨cursor, hcursor, hrBelow, hr⟩ := hr
                            have hcursor' : VExpr.consumeForalls?
                                (VExpr.forallN
                                  (artifact.view.specializedFields levels' params')
                                  tailResult)
                                (artifact.view.projectionArgs levels' params' i e') =
                                  some cursor := by
                              simpa using hcursor
                            have hcodeIdx : i <
                                (artifact.view.projectionCodes levels' params').length := by
                              simpa using hiFields
                            let code :=
                              (artifact.view.projectionCodes levels' params')[i]
                            have hcode :
                                (artifact.view.projectionCodes levels' params')[i]? =
                                  some code :=
                              List.getElem?_eq_getElem hcodeIdx
                            have hprojectionArgsLength :
                                (artifact.view.projectionArgs levels' params' i e').length =
                                  i :=
                              artifact.view.projectionArgs_length levels' params' i e'
                                (Nat.le_of_lt hcodeIdx)
                            obtain ⟨field, semanticBody, hfield, hconsume⟩ :=
                              VExpr.consumeForalls?_forallN_domain
                                (artifact.view.specializedFields levels' params')
                                tailResult
                                (artifact.view.projectionArgs levels' params' i e')
                                (by simpa [hprojectionArgsLength] using hiFields)
                            rw [hprojectionArgsLength] at hfield
                            have hcursorShape : cursor =
                                .forallE
                                  (field.instRevAt
                                    (artifact.view.projectionArgs levels' params' i e') 0)
                                  semanticBody :=
                              Option.some.inj (hcursor'.symm.trans hconsume)
                            subst cursor
                            have hprograms : artifact.view.ProgramsWF c.venv :=
                              programs.programsWF
                            obtain ⟨field', typeBody, hfield', htypeFn,
                                hprojectorField⟩ :=
                              hprograms.projector_hasType_field
                                c.Ewf c.Δwf hlevelsWF hlevelsLength' hparamsLength
                                hparamsSpine hcode hmajorType
                            have hfieldEq : field' = field :=
                              Option.some.inj (hfield'.symm.trans hfield)
                            subst field'
                            have hprojector := hprograms c.Δwf hlevelsWF
                              hlevelsLength' hparamsLength hparamsSpine hcode
                            have hprojSem : VProjectionView.TrProj c.venv
                                c.lparams.length c.vlctx.toCtx artifact.view levels' params' i e'
                                (.app code.projector e') := {
                              viewWF := artifact.viewWF
                              levelsWF := hlevelsWF
                              levels_length := hlevelsLength'
                              params_length := hparamsLength
                              paramsSpine := hparamsSpine
                              majorType := hmajorType
                              program := ⟨code, hcode, rfl, hprojector⟩ }
                            have hprojStrict : c.TrExprS (.proj familyName i e)
                                (.app code.projector e') :=
                              .proj he ⟨.ordinary artifact.view, levels', params',
                                artifact.name_eq, .ordinary hprojSem⟩
                            obtain ⟨r', hrS, hrEq⟩ := hr
                            refine (whnf.WF hrS).bind fun out _ _
                              ⟨houtBelow, ⟨out', hout, houtEq⟩⟩ => ?_
                            have houtEq := houtEq.trans c.Ewf c.Δwf hrEq
                            cases out with
                            | forallE name dom body bi =>
                              let .forallE hdomTy hbodyTy hdom hbody := hout
                              have hforallEq := houtEq.forallE_inv c.Ewf c.Δwf
                              obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
                              have hprojectorField' := hprojectorField.defeqU_r
                                c.Ewf c.Δwf ⟨_, hdomEq.symm⟩
                              have hdomBelow : c.FVarsBelow
                                  (.proj familyName i e) dom := by
                                intro P hP hproj
                                exact ((hrBelow.trans houtBelow) P hP hproj).1
                              have hresult : ∃ proj' ty',
                                  c.TrTyping (.proj familyName i e) dom proj' ty' :=
                                ⟨.app code.projector e', _, hdomBelow, hprojStrict,
                                  hdom, hprojectorField'⟩
                              simp only
                              split
                              · refine (isProp.WF hdom).bind fun _ _ _ _ => ?_
                                split
                                · exact invalidProj.WF
                                · exact .pure hresult
                              · exact .pure hresult
                            | bvar | fvar | mvar | sort | const | app | lam | letE |
                                lit | mdata | proj => exact invalidProj.WF
                      | runtimeBlock selected view_eq spineSupport =>
                        have hselectedViewWF :
                            (VProjectionView.block selected).LayoutWF c.venv := by
                          simpa [view_eq] using artifact.viewWF
                        have selectedLayout : selected.LayoutWF c.venv := by
                          have checked :=
                            hselectedViewWF.materialize c.Ewf.ordered
                          cases checked with
                          | block layout => exact layout
                        have hlevelsLengthSelected : levels'.length =
                            selected.uvars := by
                          simpa [view_eq, VProjectionView.uvars,
                            VProjectionView.source] using hlevelsLength'
                        have hparamsLengthSelected : params'.length =
                            selected.nparams := by
                          simpa [view_eq, VProjectionView.nparams,
                            VProjectionView.source] using hparamsLength
                        have hparamsSpineSelected : ∃ resultLevel,
                            c.venv.SpineWF c.lparams.length c.vlctx.toCtx
                              (selected.familyType.instL levels') params'
                              (.sort resultLevel) := by
                          simpa [view_eq, VProjectionView.familyType,
                            VProjectionView.familyRaw] using hparamsSpine
                        have hnameSelected : selected.name = familyName := by
                          simpa [view_eq, VProjectionView.name,
                            VProjectionView.familyRaw] using artifact.name_eq
                        have hmajorTypeSelected : c.HasType e'
                            (selected.structureType levels' params') := by
                          simpa [view_eq, VProjectionView.structureType,
                            VProjectionView.name,
                            VProjectionView.familyRaw,
                            VBlockStructureView.structureType] using hmajorType
                        have hiFieldsSelected : i <
                            (selected.specializedFields levels' params').length := by
                          simpa [view_eq,
                            VProjectionView.specializedFields] using hiFields
                        have hrecLevelLengthSelected :
                            recInfo.levelParams.length =
                              selected.generation.recUvars := by
                          simpa [view_eq, VProjectionView.recUvars] using
                            hrecLevelLength
                        have hinfoLevelLengthSelected :
                            info.levelParams.length = selected.uvars := by
                          simpa [view_eq, VProjectionView.uvars,
                            VProjectionView.source] using
                              artifact.levelParams_length
                        rw [← hctorInfoEq] at spineSupport
                        have semanticFull := spineSupport.blockSemanticInstL
                          (parameters := ctorInfo.levelParams)
                          (sourceLevels := familyLevels)
                          (targetLevels := levels')
                        have semanticFull' : ProjectionSpineSupport
                            ((List.take info.numParams
                              type.getAppArgs.toList).length +
                                selected.fields.length)
                            ((.ctorInfo ctorInfo : ConstantInfo)
                              |>.instantiateTypeLevelParamsCpp familyLevels)
                            (VExpr.forallN
                              (selected.constructorParams.map
                                (VExpr.instL levels'))
                              (VExpr.forallN
                                (selected.fields.map (VExpr.instL levels'))
                                ((selected.constructor.rawResult
                                  selected.nparams).instL levels'))) := by
                          simpa [ConstantInfo.instantiateTypeLevelParamsCpp,
                            ConstantInfo.type, ConstantInfo.levelParams,
                            ConstantInfo.toConstantVal,
                            hparamArgsTr.length_eq,
                            hparamsLengthSelected] using
                              semanticFull
                        let selectedTail := VExpr.forallN
                          (selected.fields.map (VExpr.instL levels'))
                          ((selected.constructor.rawResult selected.nparams).instL
                            levels')
                        have hctorTypeShapeSelected : c.TrExpr
                            ((.ctorInfo ctorInfo : ConstantInfo)
                              |>.instantiateTypeLevelParamsCpp familyLevels)
                            (VExpr.forallN
                              (selected.constructorParams.map
                                (VExpr.instL levels')) selectedTail) := by
                          simpa [view_eq, ctorTail, selectedTail,
                            VProjectionView.constructorParams,
                            VProjectionView.constructor,
                            VProjectionView.nparams,
                            VProjectionView.source,
                            VProjectionView.fields,
                            VBlockStructureView.constructorParams,
                            VBlockStructureView.fields] using hctorTypeShape
                        have hctorParamsSpineSelected :=
                          selectedLayout.constructorParamsSpine c.Ewf.ordered
                            levels' hlevelsWF hlevelsLengthSelected params'
                            hparamsLengthSelected hparamsSpineSelected selectedTail
                        refine (inferProjParams.WF_withSupport hparamArgsTr
                          hctorTypeBelow hparamArgsBelow hctorTypeShapeSelected
                          hctorParamsSpineSelected semanticFull').bind
                            fun r _ _ hr => ?_
                        obtain ⟨hrBelow, hr, semanticSupport⟩ := hr
                        let tailResult :=
                          ((selected.constructor.rawResult selected.nparams).instL
                            levels').instRevAt params' selected.fields.length
                        have hselectedTailInst : selectedTail.instRev params' =
                            VExpr.forallN
                              (selected.specializedFields levels' params')
                              tailResult := by
                          simp [selectedTail, tailResult,
                            VExpr.instRev_forallN_projection,
                            VBlockStructureView.specializedFields,
                            VExpr.instRevAt_map_instL_zipIdx]
                        rw [hselectedTailInst] at hr semanticSupport
                        refine (getSortLevel.WF htypeS).bind
                          fun sortLevel nextState _ _ => ?_
                        split
                        · exact invalidProj.WF
                        · rename_i hrecGate
                          have hstructBelow : c.FVarsBelow
                              (.proj familyName i e) e := by
                            intro P _ hproj
                            simpa [FVarsIn] using hproj
                          let fieldCount :=
                            (selected.specializedFields levels' params').length
                          have hfieldCount : fieldCount = selected.fields.length := by
                            simp [fieldCount,
                              VBlockStructureView.specializedFields]
                          have semanticSupportFields : ProjectionSpineSupport
                              fieldCount r
                              (VExpr.forallN
                                (selected.specializedFields levels' params')
                                tailResult) := by
                            simpa [fieldCount, hfieldCount] using semanticSupport
                          have hfieldsBound : i + 1 ≤ fieldCount := by
                            dsimp only [fieldCount]
                            omega
                          have semanticPrefix :=
                            semanticSupportFields.prefix hfieldsBound
                          have runtimeSupport :=
                            semanticSupportFields.retargetForallN
                          have majorSupportAll₀ := runtimeSupport.liftN
                            (amount := 1) (depth := 0)
                          have hmajorFields :=
                            selectedLayout.specializedFields_liftN levels' params'
                              hparamsLengthSelected 1 0
                          rw [VExpr.liftN_forallN, ← hmajorFields] at majorSupportAll₀
                          have majorSupportAll : ProjectionSpineSupport
                              fieldCount r
                              (VExpr.forallN
                                (selected.specializedFields levels'
                                  (params'.map (VExpr.liftN 1)))
                                (.sort .zero)) := by
                            simpa [VExpr.liftN] using majorSupportAll₀
                          have majorPrefix :=
                            majorSupportAll.prefix hfieldsBound
                          have constructorSupportAll₀ := runtimeSupport.liftN
                            (amount := fieldCount) (depth := 0)
                          rw [VExpr.liftN_forallN] at constructorSupportAll₀
                          have constructorSupportAll : ProjectionSpineSupport
                              fieldCount r
                              (VExpr.forallN
                                (VExpr.liftTelN fieldCount
                                  (selected.specializedFields levels' params') 0)
                                (.sort .zero)) := by
                            simpa [VExpr.liftN] using
                              constructorSupportAll₀
                          have constructorPrefix :=
                            constructorSupportAll.prefix hfieldsBound
                          have hsmallMaybe :
                              selected.generation.elimination = .small →
                                (!sortLevel.isNeverZero) = true := by
                            intro mode
                            have hrecEq : recInfo.levelParams.length =
                                info.levelParams.length := by
                              calc
                                recInfo.levelParams.length =
                                    selected.generation.recUvars :=
                                  hrecLevelLengthSelected
                                _ = selected.uvars := by
                                  simp [VInductDecl.BlockGenerationChecked.recUvars,
                                    mode]
                                _ = info.levelParams.length :=
                                  hinfoLevelLengthSelected.symm
                            cases hmaybe : (!sortLevel.isNeverZero) with
                            | true => rfl
                            | false => simp [hmaybe, hrecEq] at hrecGate
                          have hcursorZero :
                              (VExpr.forallN
                                (selected.specializedFields levels' params')
                                tailResult).consumeForalls?
                                  (selected.operationalProjectionArgs levels'
                                    params' 0 e') =
                                some (VExpr.forallN
                                  (selected.specializedFields levels' params')
                                  tailResult) := by
                            rfl
                          have hmajorCursorZero :
                              (VExpr.forallN
                                (selected.specializedFields levels'
                                  (params'.map (VExpr.liftN 1)))
                                (.sort .zero)).consumeForalls?
                                  (selected.operationalProjectionArgs levels'
                                    (params'.map (VExpr.liftN 1)) 0 (.bvar 0)) =
                                some (VExpr.forallN
                                  (selected.specializedFields levels'
                                    (params'.map (VExpr.liftN 1)))
                                  (.sort .zero)) := by
                            rfl
                          have hconstructorCursorZero :
                              (VExpr.forallN
                                (VExpr.liftTelN fieldCount
                                  (selected.specializedFields levels' params') 0)
                                (.sort .zero)).consumeForalls? [] =
                                some (VExpr.forallN
                                  (VExpr.liftTelN fieldCount
                                    (selected.specializedFields levels' params') 0)
                                  (.sort .zero)) := by
                            rfl
                          refine (inferProjFields.WF_runtimeBlock he selectedLayout
                            hlevelsWF hlevelsLengthSelected hparamsLengthSelected
                            hparamsSpineSelected hnameSelected hmajorTypeSelected
                            hrBelow hstructBelow (by simpa using hiFieldsSelected)
                            hr hcursorZero
                            (VBlockStructureView.OperationalRuntimePrefix.zero
                              selected c.venv c.lparams.length c.vlctx.toCtx
                              levels' params')
                            semanticPrefix majorPrefix hmajorCursorZero
                            constructorPrefix (by
                              simpa [fieldCount] using hconstructorCursorZero)
                            hsmallMaybe).bind fun r _ _ runtimeResult => ?_
                          obtain ⟨cursor, majorCursor, constructorCursor,
                            hcursor, hmajorCursor, hconstructorCursor, hrBelow, hr,
                            semanticOne, majorOne, constructorOne, runtime⟩ :=
                              runtimeResult
                          have hcursor' :
                              (VExpr.forallN
                                (selected.specializedFields levels' params')
                                tailResult).consumeForalls?
                                  (selected.operationalProjectionArgs levels'
                                    params' i e') = some cursor := by
                            simpa only [Nat.zero_add] using hcursor
                          have hmajorCursor' :
                              (VExpr.forallN
                                (selected.specializedFields levels'
                                  (params'.map (VExpr.liftN 1)))
                                (.sort .zero)).consumeForalls?
                                  (selected.operationalProjectionArgs levels'
                                    (params'.map (VExpr.liftN 1)) i (.bvar 0)) =
                                some majorCursor := by
                            simpa only [Nat.zero_add] using hmajorCursor
                          have hconstructorCursor' :
                              let fields := selected.specializedFields levels' params'
                              let fieldCount := fields.length
                              (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
                                (.sort .zero)).consumeForalls?
                                  (((selected.operationalProjectionCodes levels'
                                    params').take i).map fun prior =>
                                      .app (prior.projector.liftN fieldCount)
                                        (selected.projectionConstructorApp levels'
                                          params' fields)) =
                                some constructorCursor := by
                            simpa only [Nat.zero_add] using hconstructorCursor
                          have runtime' :
                              selected.OperationalRuntimePrefix c.venv
                                c.lparams.length c.vlctx.toCtx levels' params' i := by
                            simpa only [Nat.zero_add] using runtime
                          exact inferProjResult.WF_runtimeBlock
                            (typeName := familyName) (fieldIdx := i)
                            (struct := e) (major := e')
                            (tailResult := tailResult)
                            (maybePropType := !sortLevel.isNeverZero)
                            he selectedLayout hlevelsWF hlevelsLengthSelected
                            hparamsLengthSelected hparamsSpineSelected
                            hnameSelected hmajorTypeSelected hrBelow
                            hiFieldsSelected hr hcursor' runtime' semanticOne
                            majorOne hmajorCursor' constructorOne
                            hconstructorCursor' hsmallMaybe
                    | axiomInfo | defnInfo | thmInfo | opaqueInfo | quotInfo |
                        inductInfo | ctorInfo => exact invalidProj.WF
                  · exact invalidProj.WF
                | axiomInfo | defnInfo | thmInfo | opaqueInfo | quotInfo |
                    inductInfo | recInfo => exact invalidProj.WF
              | restored artifact =>
                have hhead := hstack.tr
                rw [hfamilyShape] at hhead
                let .const (us' := levels') hfamilyConst hlevelsMap
                  hlevelsLength := hhead
                have hviewFamily := artifact.viewWF.family
                rw [artifact.name_eq] at hviewFamily
                rw [hviewFamily] at hfamilyConst
                cases hfamilyConst
                have hlevelsWF : ∀ level ∈ levels',
                    level.WF c.lparams.length :=
                  VLevel.WF.of_mapM_ofLevel hlevelsMap
                have hlevelsFamilyLength : levels'.length =
                    artifact.view.sourceFamily.uvars :=
                  (List.mapM_eq_some.1 hlevelsMap).length_eq.symm.trans
                    hlevelsLength
                have hlevelsLength' : levels'.length = artifact.view.uvars := by
                  exact hlevelsFamilyLength.trans artifact.view.family_uvars_eq
                have hargsSize : type.getAppArgs.size =
                    info.numParams + info.numIndices := by
                  simpa using hargs
                have hargsLength : type.getAppArgsList.length =
                    artifact.view.nparams := by
                  rw [← Expr.getAppArgs_toList]
                  simp [hargsSize,
                    artifact.numParams_eq, artifact.numIndices_eq]
                have hfamilyType : c.HasType (.const familyName levels')
                    (artifact.view.familyType.instL levels') := by
                  simpa [artifact.name_eq] using
                    artifact.viewWF.familyConst_hasType c.Ewf.ordered
                      (Γ := c.vlctx.toCtx) levels' hlevelsWF hlevelsLength'
                have hfamilyTypeShape : c.HasType (.const familyName levels')
                    (VExpr.forallN
                      (artifact.view.rawParams.map (VExpr.instL levels'))
                      (.sort (artifact.view.resultLevel.inst levels'))) := by
                  simpa [artifact.view.familyType_eq_forallN,
                    VExpr.instL_forallN, VExpr.instL] using hfamilyType
                have hargsRawLength : type.getAppArgsList.length =
                    (artifact.view.rawParams.map
                      (VExpr.instL levels')).length := by
                  simpa [artifact.view.rawParams_length] using hargsLength
                obtain ⟨params', hparamsTr, hparamsSpineRaw, htypeFull⟩ :=
                  AppStack.toSpineWF hstack hfamilyTypeShape hargsRawLength
                rw [type.mkAppList_getAppArgsList] at htypeFull
                have htypeAppliedEq := htypeFull.uniq c.Ewf
                  (.refl c.Ewf c.Δwf) htypeS
                have hmajorType : c.HasType e'
                    (artifact.view.structureType levels' params') := by
                  apply hasty.defeqU_r c.Ewf c.Δwf
                  have := (htypeAppliedEq.trans c.Ewf c.Δwf htypeEq).symm
                  simpa [VRestoredBlockStructureView.structureType,
                    artifact.name_eq] using this
                have hparamsLength : params'.length =
                    artifact.view.nparams :=
                  hparamsTr.length_eq.symm.trans hargsLength
                have hparamsSpine : ∃ resultLevel,
                    c.venv.SpineWF c.lparams.length c.vlctx.toCtx
                      (artifact.view.familyType.instL levels') params'
                      (.sort resultLevel) := by
                  refine ⟨artifact.view.resultLevel.inst levels', ?_⟩
                  rw [VExpr.instRev_closedN params' (by trivial)] at hparamsSpineRaw
                  simpa [artifact.view.familyType_eq_forallN,
                    VExpr.instL_forallN, VExpr.forallN,
                    VExpr.instRev, VExpr.instL] using hparamsSpineRaw
                have hconstructorName :
                    constructor = artifact.view.constructorName := by
                  have := hctors.symm.trans artifact.ctors_eq
                  simpa using this
                refine (M.WF.liftExcept envGet.WF).lift.bind
                  fun c_info _ _ hctorFind => ?_
                cases c_info with
                | ctorInfo ctorInfo =>
                  simp only
                  split
                  · rename_i hidxHost
                    have hctorInfoEq :
                        ctorInfo = artifact.constructorInfo := by
                      rw [hconstructorName, artifact.constructor_find] at hctorFind
                      exact ConstantInfo.ctorInfo.inj
                        (Option.some.inj hctorFind.symm)
                    have hiFields : i <
                        (artifact.view.specializedFields levels' params').length := by
                      rw [hctorInfoEq,
                        artifact.constructor_numFields_eq] at hidxHost
                      simpa [VRestoredBlockStructureView.specializedFields] using
                        hidxHost
                    have hviewConstructor : c.venv.constants constructor =
                        some artifact.view.sourceConstructor.toVConstant := by
                      simpa [hconstructorName] using artifact.viewWF.constructor
                    obtain ⟨_, hctorTr⟩ :=
                      c.trenv.find?_uniq hctorFind hviewConstructor
                    have hrawCtorUvars :
                        artifact.view.sourceConstructor.uvars =
                          artifact.view.uvars :=
                      artifact.view.constructor_uvars_eq
                    have hctorLevelLength :
                        ctorInfo.levelParams.length = familyLevels.length :=
                      hctorTr.2.1.trans <| hrawCtorUvars.trans <|
                        hlevelsLength'.symm.trans
                          (List.mapM_eq_some.1 hlevelsMap).length_eq.symm
                    have hctorType₀ := hctorTr.2.2.instLCpp c.Ewf
                      (Us := c.lparams) (ls' := levels') (Δ := [])
                      trivial hlevelsMap hctorLevelLength
                    have hctorType := hctorType₀.weakFV c.Ewf
                      (.from_nil c.mlctx.noBV) c.Δwf
                    rw [(c.Ewf.ordered.closedC
                      hviewConstructor).instL.liftN_eq
                        (Nat.le_refl _)] at hctorType
                    let ctorResult :=
                      (VExpr.dropN artifact.view.nparams
                        artifact.view.sourceConstructor.type).resultOf
                    let ctorTail := VExpr.forallN
                      (artifact.view.fields.map (VExpr.instL levels'))
                      (ctorResult.instL levels')
                    have hsourceCtorShape :
                        artifact.view.sourceConstructor.type =
                          VExpr.forallN artifact.view.constructorParams
                            (VExpr.forallN artifact.view.fields ctorResult) := by
                      simp [VRestoredBlockStructureView.constructorParams,
                        VRestoredBlockStructureView.fields, ctorResult,
                        VInductDecl.forallN_ctorFields_resultOf,
                        VExpr.forallN_telN_dropN]
                    rw [hsourceCtorShape] at hctorType
                    have hctorTypeShape : c.TrExpr
                        ((.ctorInfo ctorInfo : ConstantInfo)
                          |>.instantiateTypeLevelParamsCpp familyLevels)
                        (VExpr.forallN
                          (artifact.view.constructorParams.map
                            (VExpr.instL levels')) ctorTail) := by
                      simpa [ConstantInfo.instantiateTypeLevelParamsCpp,
                        ConstantInfo.type, ConstantInfo.levelParams,
                        ConstantInfo.toConstantVal, ctorTail,
                        VExpr.instL_forallN] using hctorType
                    have hctorTypeBelow : c.FVarsBelow (.proj familyName i e)
                        ((.ctorInfo ctorInfo : ConstantInfo)
                          |>.instantiateTypeLevelParamsCpp familyLevels) := by
                      intro P _ _
                      simpa [ConstantInfo.instantiateTypeLevelParamsCpp,
                        ConstantInfo.type, ConstantInfo.levelParams,
                        ConstantInfo.toConstantVal] using
                          hctorType₀.fvarsIn.mono nofun
                    have hparamArgsEq :
                        List.take info.numParams type.getAppArgs.toList =
                          type.getAppArgsList := by
                      simp [Expr.getAppArgs_toList, artifact.numParams_eq,
                        ← hargsLength]
                    have hparamArgsTr :
                        (List.take info.numParams
                          type.getAppArgs.toList).Forall₂
                          (c.TrExprS · ·) params' := by
                      simpa [hparamArgsEq] using hparamsTr
                    have hparamArgsBelow : ∀ arg ∈
                        List.take info.numParams type.getAppArgs.toList,
                        c.FVarsBelow (.proj familyName i e) arg := by
                      intro arg harg P hP hproj
                      apply FVarsIn.getAppArgsList
                        (hprojBelowType P hP hproj)
                      simpa [hparamArgsEq] using harg
                    have hctorParamsSpine :=
                      artifact.parameterLayout.constructorParamsSpine
                        c.Ewf.ordered levels' hlevelsWF hlevelsLength' params'
                        hparamsLength hparamsSpine ctorTail
                    refine (M.WF.liftExcept envGet.WF).lift.bind
                      fun rec_info _ _ hrecFind => ?_
                    cases rec_info with
                    | recInfo recInfo =>
                      have hrecursorName : mkRecName familyName =
                          artifact.view.recursorName := by
                        simpa only [mkRecName,
                          VRestoredBlockStructureView.recursorName] using
                          congrArg (fun name => name.str "rec")
                            artifact.name_eq.symm
                      have hrecInfoEq : recInfo = artifact.recursorInfo := by
                        rw [hrecursorName, artifact.recursor_find] at hrecFind
                        exact ConstantInfo.recInfo.inj
                          (Option.some.inj hrecFind.symm)
                      have hrecLevelLength : recInfo.levelParams.length =
                          artifact.view.recUvars := by
                        rw [hrecInfoEq]
                        exact artifact.recursor_levelParams_length
                      cases artifact.programs with
                      | dense programs =>
                          refine (inferProjParams.WF hparamArgsTr hctorTypeBelow
                            hparamArgsBelow hctorTypeShape hctorParamsSpine).bind
                              fun r _ _ hr => ?_
                          obtain ⟨hrBelow, hr⟩ := hr
                          let tailResult := (ctorResult.instL levels').instRevAt
                            params' artifact.view.fields.length
                          have hctorTailInst : ctorTail.instRev params' =
                              VExpr.forallN
                                (artifact.view.specializedFields levels' params')
                                tailResult := by
                            simp [ctorTail, tailResult,
                              VExpr.instRev_forallN_projection,
                              VRestoredBlockStructureView.specializedFields,
                              VExpr.instRevAt_map_instL_zipIdx]
                          rw [hctorTailInst] at hr
                          refine (getSortLevel.WF htypeS).bind
                            fun sortLevel nextState _ _ => ?_
                          split
                          · exact invalidProj.WF
                          · rename_i hrecGate
                            have hstructBelow : c.FVarsBelow
                                (.proj familyName i e) e := by
                              intro P _ hproj
                              simpa [FVarsIn] using hproj
                            have hcursorZero : VExpr.consumeForalls?
                                (VExpr.forallN
                                  (artifact.view.specializedFields levels' params')
                                  tailResult)
                                (artifact.view.operationalProjectionArgs
                                  levels' params' 0 e') =
                                  some (VExpr.forallN
                                    (artifact.view.specializedFields levels' params')
                                    tailResult) := by
                              rfl
                            refine (inferProjFields.WF_restored he
                              artifact.parameterLayout artifact.codeNaturality
                              artifact.recEntriesClosed hlevelsWF hlevelsLength'
                              hparamsLength hparamsSpine programs.programsWF
                              artifact.name_eq hmajorType hrBelow hstructBelow
                              (by simpa using hiFields) hr hcursorZero).bind
                                fun r _ _ hr => ?_
                            obtain ⟨cursor, hcursor, hrBelow, hr⟩ := hr
                            have hcursor' : VExpr.consumeForalls?
                                (VExpr.forallN
                                  (artifact.view.specializedFields levels' params')
                                  tailResult)
                                (artifact.view.operationalProjectionArgs
                                  levels' params' i e') = some cursor := by
                              simpa using hcursor
                            have hcodeIdx : i <
                                (artifact.view.operationalProjectionCodes
                                  levels' params').length := by
                              simpa using hiFields
                            let code :=
                              (artifact.view.operationalProjectionCodes
                                levels' params')[i]
                            have hcode :
                                (artifact.view.operationalProjectionCodes
                                  levels' params')[i]? = some code :=
                              List.getElem?_eq_getElem hcodeIdx
                            have hprojectionArgsLength :
                                (artifact.view.operationalProjectionArgs
                                  levels' params' i e').length = i :=
                              artifact.view.operationalProjectionArgs_length
                                levels' params' i e' (Nat.le_of_lt hcodeIdx)
                            obtain ⟨field, semanticBody, hfield, hconsume⟩ :=
                              VExpr.consumeForalls?_forallN_domain
                                (artifact.view.specializedFields levels' params')
                                tailResult
                                (artifact.view.operationalProjectionArgs
                                  levels' params' i e')
                                (by simpa [hprojectionArgsLength] using hiFields)
                            rw [hprojectionArgsLength] at hfield
                            have hcursorShape : cursor =
                                .forallE
                                  (field.instRevAt
                                    (artifact.view.operationalProjectionArgs
                                      levels' params' i e') 0)
                                  semanticBody :=
                              Option.some.inj (hcursor'.symm.trans hconsume)
                            subst cursor
                            have hprograms :
                                artifact.view.OperationalProgramsWF c.venv :=
                              programs.programsWF
                            have hprojector := hprograms c.Δwf hlevelsWF
                              hlevelsLength' hparamsLength hparamsSpine hcode
                            obtain ⟨field', _projectorDomain, typeBody, hfield',
                                htypeFn, hprojectorField⟩ :=
                              artifact.parameterLayout.toLayoutWF
                                |>.operationalProjector_hasType_field_of_type
                                  c.Ewf.conversionRegular
                                  artifact.recEntriesClosed hlevelsLength' c.Δwf
                                  hcode hprojector hmajorType
                            have hfieldEq : field' = field :=
                              Option.some.inj (hfield'.symm.trans hfield)
                            subst field'
                            have hprojSem :
                                VRestoredBlockStructureView.TrProj c.venv
                                  c.lparams.length c.vlctx.toCtx artifact.view
                                  levels' params' i e'
                                  (.app code.projector e') := {
                              viewWF := artifact.viewWF
                              parameterLayout := artifact.parameterLayout
                              codeNaturality := artifact.codeNaturality
                              recEntriesClosed := artifact.recEntriesClosed
                              levelsWF := hlevelsWF
                              levels_length := hlevelsLength'
                              params_length := hparamsLength
                              paramsSpine := hparamsSpine
                              majorType := hmajorType
                              program := ⟨code, hcode, rfl, hprojector⟩ }
                            have hprojStrict : c.TrExprS (.proj familyName i e)
                                (.app code.projector e') :=
                              .proj he ⟨.restored artifact.view, levels', params',
                                artifact.name_eq, .restored hprojSem⟩
                            obtain ⟨r', hrS, hrEq⟩ := hr
                            refine (whnf.WF hrS).bind fun out _ _
                              ⟨houtBelow, ⟨out', hout, houtEq⟩⟩ => ?_
                            have houtEq := houtEq.trans c.Ewf c.Δwf hrEq
                            cases out with
                            | forallE name dom body bi =>
                              let .forallE hdomTy hbodyTy hdom hbody := hout
                              have hforallEq := houtEq.forallE_inv c.Ewf c.Δwf
                              obtain ⟨⟨_, hdomEq⟩, _, hbodyEq⟩ := hforallEq
                              have hprojectorField' := hprojectorField.defeqU_r
                                c.Ewf c.Δwf ⟨_, hdomEq.symm⟩
                              have hdomBelow : c.FVarsBelow
                                  (.proj familyName i e) dom := by
                                intro P hP hproj
                                exact ((hrBelow.trans houtBelow) P hP hproj).1
                              have hresult : ∃ proj' ty',
                                  c.TrTyping (.proj familyName i e) dom proj' ty' :=
                                ⟨.app code.projector e', _, hdomBelow, hprojStrict,
                                  hdom, hprojectorField'⟩
                              simp only
                              split
                              · refine (isProp.WF hdom).bind fun _ _ _ _ => ?_
                                split
                                · exact invalidProj.WF
                                · exact .pure hresult
                              · exact .pure hresult
                            | bvar | fvar | mvar | sort | const | app | lam |
                                letE | lit | mdata | proj => exact invalidProj.WF
                      | runtime spineSupport =>
                        rw [← hctorInfoEq] at spineSupport
                        have semanticFull := spineSupport.instL
                          (parameters := ctorInfo.levelParams)
                          (sourceLevels := familyLevels)
                          (targetLevels := levels')
                        have semanticFull' : ProjectionFieldSpineSupport
                            (List.take info.numParams
                              type.getAppArgs.toList).length
                            artifact.view.fields.length
                            ((.ctorInfo ctorInfo : ConstantInfo)
                              |>.instantiateTypeLevelParamsCpp familyLevels)
                            (VExpr.forallN
                              (artifact.view.constructorParams.map
                                (VExpr.instL levels')) ctorTail) := by
                          simpa [ConstantInfo.instantiateTypeLevelParamsCpp,
                            ConstantInfo.type, ConstantInfo.levelParams,
                            ConstantInfo.toConstantVal,
                            hparamArgsTr.length_eq, hparamsLength,
                            hsourceCtorShape, ctorTail,
                            VExpr.instL_forallN] using semanticFull
                        refine (inferProjParams.WF_withFieldSupport hparamArgsTr
                          hctorTypeBelow hparamArgsBelow hctorTypeShape
                          hctorParamsSpine semanticFull').bind
                            fun r _ _ hr => ?_
                        obtain ⟨hrBelow, hr, semanticSupport⟩ := hr
                        let tailResult := (ctorResult.instL levels').instRevAt
                          params' artifact.view.fields.length
                        have hctorTailInst : ctorTail.instRev params' =
                            VExpr.forallN
                              (artifact.view.specializedFields levels' params')
                              tailResult := by
                          simp [ctorTail, tailResult,
                            VExpr.instRev_forallN_projection,
                            VRestoredBlockStructureView.specializedFields,
                            VExpr.instRevAt_map_instL_zipIdx]
                        rw [hctorTailInst] at hr semanticSupport
                        refine (getSortLevel.WF htypeS).bind
                          fun sortLevel nextState _ _ => ?_
                        split
                        · exact invalidProj.WF
                        · rename_i hrecGate
                          have hstructBelow : c.FVarsBelow
                              (.proj familyName i e) e := by
                            intro P _ hproj
                            simpa [FVarsIn] using hproj
                          let fieldCount :=
                            (artifact.view.specializedFields levels' params').length
                          have hfieldCount : fieldCount =
                              artifact.view.fields.length := by
                            simp [fieldCount,
                              VRestoredBlockStructureView.specializedFields]
                          have semanticSupportFields : ProjectionSpineSupport
                              fieldCount r
                              (VExpr.forallN
                                (artifact.view.specializedFields levels' params')
                                tailResult) := by
                            simpa [fieldCount, hfieldCount] using semanticSupport
                          have hfieldsBound : i + 1 ≤ fieldCount := by
                            dsimp only [fieldCount]
                            omega
                          have semanticPrefix :=
                            semanticSupportFields.prefix hfieldsBound
                          have runtimeSupport :=
                            semanticSupportFields.retargetForallN
                          have majorSupportAll₀ := runtimeSupport.liftN
                            (amount := 1) (depth := 0)
                          have hmajorFields :=
                            artifact.parameterLayout.toLayoutWF
                              |>.specializedFields_liftN c.Ewf.ordered
                                levels' params' hparamsLength 1 0
                          rw [VExpr.liftN_forallN, ← hmajorFields] at majorSupportAll₀
                          have majorSupportAll : ProjectionSpineSupport
                              fieldCount r
                              (VExpr.forallN
                                (artifact.view.specializedFields levels'
                                  (params'.map (VExpr.liftN 1)))
                                (.sort .zero)) := by
                            simpa [fieldCount, VExpr.liftN] using majorSupportAll₀
                          have majorPrefix := majorSupportAll.prefix hfieldsBound
                          have constructorSupportAll₀ := runtimeSupport.liftN
                            (amount := fieldCount) (depth := 0)
                          rw [VExpr.liftN_forallN] at constructorSupportAll₀
                          have constructorSupportAll : ProjectionSpineSupport
                              fieldCount r
                              (VExpr.forallN
                                (VExpr.liftTelN fieldCount
                                  (artifact.view.specializedFields levels' params') 0)
                                (.sort .zero)) := by
                            simpa [fieldCount, VExpr.liftN] using
                              constructorSupportAll₀
                          have constructorPrefix :=
                            constructorSupportAll.prefix hfieldsBound
                          have hsmallMaybe : artifact.view.elimination = .small →
                              (!sortLevel.isNeverZero) = true := by
                            intro mode
                            have hrecEq : recInfo.levelParams.length =
                                info.levelParams.length := by
                              calc
                                recInfo.levelParams.length =
                                    artifact.view.recUvars := hrecLevelLength
                                _ = artifact.view.uvars := by
                                  have flatUvars :
                                      artifact.view.nested.elim.flat.uvars =
                                        artifact.view.uvars := by
                                    simpa using congrArg VInductDecl.uvars
                                      artifact.view.nested.elim.flat_eq
                                  simp [VRestoredBlockStructureView.recUvars,
                                    VRestoredBlockStructureView.elimination,
                                    VInductDecl.BlockGenerationChecked.recUvars,
                                    mode, flatUvars]
                                _ = info.levelParams.length :=
                                  artifact.levelParams_length.symm
                            cases hmaybe : (!sortLevel.isNeverZero) with
                            | true => rfl
                            | false => simp [hmaybe, hrecEq] at hrecGate
                          have hcursorZero :
                              (VExpr.forallN
                                (artifact.view.specializedFields levels' params')
                                tailResult).consumeForalls?
                                  (artifact.view.operationalProjectionArgs
                                    levels' params' 0 e') =
                                some (VExpr.forallN
                                  (artifact.view.specializedFields levels' params')
                                  tailResult) := by
                            rfl
                          have hmajorCursorZero :
                              (VExpr.forallN
                                (artifact.view.specializedFields levels'
                                  (params'.map (VExpr.liftN 1)))
                                (.sort .zero)).consumeForalls?
                                  (artifact.view.operationalProjectionArgs levels'
                                    (params'.map (VExpr.liftN 1)) 0 (.bvar 0)) =
                                some (VExpr.forallN
                                  (artifact.view.specializedFields levels'
                                    (params'.map (VExpr.liftN 1)))
                                  (.sort .zero)) := by
                            rfl
                          have hconstructorCursorZero :
                              (VExpr.forallN
                                (VExpr.liftTelN fieldCount
                                  (artifact.view.specializedFields levels' params') 0)
                                (.sort .zero)).consumeForalls? [] =
                                some (VExpr.forallN
                                  (VExpr.liftTelN fieldCount
                                    (artifact.view.specializedFields levels' params') 0)
                                  (.sort .zero)) := by
                            rfl
                          refine (inferProjFields.WF_runtimeRestored he
                            artifact.parameterLayout artifact.codeNaturality
                            artifact.recEntriesClosed hlevelsWF hlevelsLength'
                            hparamsLength hparamsSpine artifact.name_eq hmajorType
                            hrBelow hstructBelow (by simpa using hiFields) hr
                            hcursorZero
                            (VRestoredBlockStructureView.OperationalRuntimePrefix.zero
                              artifact.view c.venv c.lparams.length c.vlctx.toCtx
                              levels' params')
                            semanticPrefix majorPrefix hmajorCursorZero
                            constructorPrefix (by
                              simpa [fieldCount] using hconstructorCursorZero)
                            hsmallMaybe).bind fun r _ _ runtimeResult => ?_
                          obtain ⟨cursor, majorCursor, constructorCursor,
                            hcursor, hmajorCursor, hconstructorCursor, hrBelow, hr,
                            semanticOne, majorOne, constructorOne, runtime⟩ :=
                              runtimeResult
                          have hcursor' :
                              (VExpr.forallN
                                (artifact.view.specializedFields levels' params')
                                tailResult).consumeForalls?
                                  (artifact.view.operationalProjectionArgs
                                    levels' params' i e') = some cursor := by
                            simpa only [Nat.zero_add] using hcursor
                          have hmajorCursor' :
                              (VExpr.forallN
                                (artifact.view.specializedFields levels'
                                  (params'.map (VExpr.liftN 1)))
                                (.sort .zero)).consumeForalls?
                                  (artifact.view.operationalProjectionArgs levels'
                                    (params'.map (VExpr.liftN 1)) i (.bvar 0)) =
                                some majorCursor := by
                            simpa only [Nat.zero_add] using hmajorCursor
                          have hconstructorCursor' :
                              let fields :=
                                artifact.view.specializedFields levels' params'
                              let fieldCount := fields.length
                              (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
                                (.sort .zero)).consumeForalls?
                                  (((artifact.view.operationalProjectionCodes
                                    levels' params').take i).map fun prior =>
                                      .app (prior.projector.liftN fieldCount)
                                        (artifact.view.projectionConstructorApp
                                          levels' params' fields)) =
                                some constructorCursor := by
                            simpa only [Nat.zero_add] using hconstructorCursor
                          have runtime' :
                              artifact.view.OperationalRuntimePrefix c.venv
                                c.lparams.length c.vlctx.toCtx levels' params' i := by
                            simpa only [Nat.zero_add] using runtime
                          exact inferProjResult.WF_runtimeRestored
                            (typeName := familyName) (fieldIdx := i)
                            (struct := e) (major := e')
                            (tailResult := tailResult)
                            (maybePropType := !sortLevel.isNeverZero)
                            he artifact.parameterLayout artifact.codeNaturality
                            artifact.recEntriesClosed hlevelsWF hlevelsLength'
                            hparamsLength hparamsSpine artifact.name_eq hmajorType
                            hrBelow hiFields hr hcursor' runtime' semanticOne
                            majorOne hmajorCursor' constructorOne
                            hconstructorCursor' hsmallMaybe
                    | axiomInfo | defnInfo | thmInfo | opaqueInfo | quotInfo |
                        inductInfo | ctorInfo => exact invalidProj.WF
                  · exact invalidProj.WF
                | axiomInfo | defnInfo | thmInfo | opaqueInfo | quotInfo |
                    inductInfo | recInfo => exact invalidProj.WF
          · exact invalidProj.WF
        · exact invalidProj.WF
      · exact invalidProj.WF
    · have hnameTest : (st != familyName) = true := by simp [hname]
      rw [hnameTest]
      exact invalidProj.WF
  · exact invalidProj.WF

theorem literal_is_primitive (H : n = ``Nat ∨ n = ``Char.ofNat ∨ n = ``String.ofList)  :
    Environment.primitives.contains n := by
  simp [Environment.primitives, NameSet.ofList]
  obtain rfl|rfl|rfl := H <;> simp +decide [NameSet.contains]

theorem infer_literal {c : VContext} (H : c.venv.ContainsLits l) :
    c.TrTyping (.lit l) l.type (.trLiteral l) (.const l.typeName []) := by
  refine
    have := TrExprS.trLiteral c.Ewf c.hasPrimitives l H
    ⟨fun _ _ _ => .litType, this.1, ?_, this.2⟩
  rw [← Literal.mkConst_typeName]
  have ⟨_, h⟩ := this.2.isType c.Ewf c.Δwf
  have ⟨_, h1, _, h3⟩  := h.const_inv c.Ewf c.Δwf
  exact .const h1 rfl h3

theorem infer_sort {c : VContext} (H : VLevel.ofLevel c.lparams u = some u') :
    c.TrTyping (.sort u) (.sort u.succ) (.sort u') (.sort u'.succ) := by
  refine ⟨fun _ _ _ => (?a).fvarsIn, .sort H, ?a, .sort (.of_ofLevel H)⟩
  exact .sort <| by simpa [VLevel.ofLevel]

theorem inferType'.WF
    (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    (inferType' e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' := by
  unfold inferType'; lift_lets; intro F F1
  split <;> [exact .throw; refine .get <| .get ?_]
  split
  · rename_i h; refine .stateWF fun wf => .pure ?_
    generalize hic : cond .. = ic at h
    have : ic.WF c s := by
      subst ic; cases inferOnly <;> [exact wf.inferTypeC_wf; exact wf.inferTypeI_wf]
    exact (this h).2.2.2.2 h1
  generalize hP : (fun _ (_ : VState) => _) = P
  have hF {ty e' ty' s} (H : c.TrTyping e ty e' ty') : (F ty).WF c s P := by
    rintro _ mwf wf a s' ⟨⟩
    refine let s' := _; ⟨s', rfl, ?_⟩
    have hic {ic} (hic : InferCache.WF c s ic) : InferCache.WF c s (ic.insert e ty) := by
      intro _ _ h
      rw [Std.HashMap.getElem?_insert] at h; split at h <;> [cases h; exact hic h]
      rename_i eq
      refine .mk c.mlctx.noBV (.eqv H eq BEq.rfl) (.eqv eq ?_) ?_
      · exact H.2.1.fvarsIn.mono wf.ngen_wf
      · exact H.2.2.1.fvarsIn.mono wf.ngen_wf
    subst P; revert s'; cases inferOnly <;> (dsimp -zeta; intro s'; refine ⟨.rfl, ?_, _, _, H⟩)
    · exact { wf with inferTypeC_wf := hic wf.inferTypeC_wf }
    · exact { wf with inferTypeI_wf := hic wf.inferTypeI_wf }
  split
  · extract_lets G1; split <;> [split; skip]
    · refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ h => ?_
      have ⟨_, h, _⟩ := c.trenv.find? h <|
        (c.safePrimitives h (literal_is_primitive (.inl rfl))).1 ▸ DefinitionSafety.le_safe
      exact hF (infer_literal ⟨_, h⟩)
    · refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ h1 => ?_
      refine .getEnv <| (M.WF.liftExcept envGet.WF).lift.bind fun _ _ _ h2 => ?_
      have ⟨_, h1, _⟩ := c.trenv.find? h1 <|
        (c.safePrimitives h1 (literal_is_primitive (.inr (.inl rfl)))).1 ▸ DefinitionSafety.le_safe
      have ⟨_, h2, _⟩ := c.trenv.find? h2 <|
        (c.safePrimitives h2 (literal_is_primitive (.inr (.inr rfl)))).1 ▸ DefinitionSafety.le_safe
      exact hF (infer_literal ⟨⟨_, h1⟩, ⟨_, h2⟩⟩)
    · rename_i h; have ⟨_, h⟩ := hinf (by simpa using h)
      have := h.lit_has_type
      simp [G1]; exact hF (infer_literal this)
  · refine (inferType'.WF (by exact h1) ?_).bind fun _ _ _ ⟨_, _, hb, h1, h⟩ => ?_
    · exact fun h => let ⟨_, .mdata h⟩ := hinf h; ⟨_, h⟩
    exact hF ⟨hb, .mdata h1, h⟩
  · refine (inferType'.WF (by exact h1) ?_).bind fun _ _ _ ⟨_, _, hb, h1, h2, h3⟩ => ?_
    · exact fun h => let ⟨_, .proj h ..⟩ := hinf h; ⟨_, h⟩
    exact (inferProj.WF hb h1 h2 h3).bind fun ty _ _ ⟨_, ty', h⟩ => hF h
  · exact .readThe <| (M.WF.liftExcept inferFVar.WF).lift.bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · exact .throw
  · exact .throw
  · split <;> rename_i h
    · refine .readThe <| (M.WF.liftExcept (checkLevel.WF h1)).lift.bind fun _ _ _ ⟨_, h⟩ => ?_
      exact hF (infer_sort h)
    · let ⟨_, .sort h⟩ := hinf (by simpa using h)
      exact hF (infer_sort h)
  · refine .readThe <|
      (M.WF.liftExcept (inferConstant.WF h1 hinf)).lift.bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · exact (inferLambda.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · exact (inferForall.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h
  · split <;> rename_i h
    · let ⟨_, h⟩ := hinf h; exact (inferApp.WF h).bind fun _ _ _ ⟨_, h⟩ => hF h
    refine (inferType'.WF h1.1 ?_).bind fun _ _ _ ⟨_, _, hfb, hf1, hf2, hf3⟩ => ?_
    · exact fun h => let ⟨_, .app _ _ h _⟩ := hinf h; ⟨_, h⟩
    refine .stateWF fun wf => ?_
    refine (ensureForallCore.WF hf2).bind fun _ _ _ H => ?_
    obtain ⟨hb, h2, name, dType, body, bi, rfl⟩ := H
    let ⟨_, .forallE (ty' := dType') hl1 hl2 hl3 hl4, hl5⟩ := h2
    extract_lets _ G1
    refine (inferType'.WF h1.2 ?_).bind fun aType _ _ ⟨_, aType', hab, ha1, ha2, ha3⟩ => ?_
    · exact fun h => let ⟨_, .app _ _ _ h⟩ := hinf h; ⟨_, h⟩
    extract_lets G2
    suffices ∀ {s b} (H : b = true → c.IsDefEqU dType' aType'), RecM.WF c s (G2 b) P by
      split
      · refine .bind ?_ (Q := fun b _ => b = true → c.IsDefEqU dType' aType') fun b _ _ => this
        intro _ mwf wf _ _ eq
        let c' := { c with eagerReduce := true }
        have ⟨_, h1, h2, h3, h4⟩ := isDefEq.WF (c := c') hl3 ha2 _ mwf { wf with } _ _ eq
        exact ⟨_, h1, h2, { h3 with }, h4⟩
      · exact (isDefEq.WF hl3 ha2).bind fun b _ _ => this
    subst G2; dsimp; rintro s ⟨⟩ H
    · exact .getEnv <| .getLCtx .throw
    simp [G1, Expr.bindingBody!, Expr.instantiate1_eq]
    have hf3 := hf3.defeqU_r c.Ewf c.Δwf hl5.symm
    have ha3 := ha3.defeqU_r c.Ewf c.Δwf (H rfl).symm
    subst hP; refine hF ⟨?_, .app hf3 ha3 hf1 ha1, hl4.inst c.Ewf ha3 ha1, .app hf3 ha3⟩
    exact fun _ hP he => (hfb.trans hb _ hP he.1).2.instantiate1 he.2
  · exact (inferLet.WF h1 hinf).bind fun _ _ _ ⟨_, _, h⟩ => hF h

/--
info: 'Lean4Lean.TypeChecker.Inner.inferProj.WF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms inferProj.WF
