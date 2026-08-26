/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.ConditionSupport

/-!
# Verified reflected-condition checker evidence

This module verifies the bounded executable checker path that retains the
closed nondependent and dependent selector equations used by the Nat.mod/div
condition certificate. It is adapted from upstream lean4lean PR #32 at
\`6cfd43a48d17be85c76414638655c12ef9a7ee23\`.
-/

namespace Lean4Lean.Environment

open Lean hiding Environment Exception
open Kernel TypeChecker

theorem checkTypeIsDefEqGuard.bind_WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α} {next : M β} {Q : β → VState → Prop}
    (he : c.TrExprS e e') (he_unique : TrExprS.IsUnique e)
    (hA : c.TrExprS A A')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s', c.HasType e' A' → M.WF c s' next Q) :
    M.WF c s (do
      unless ← TypeChecker.isDefEq (← TypeChecker.checkType e) A do fail
      next) Q := by
  refine (checkType.WF he.fvarsIn).bind fun _ _ _ h => ?_
  let ⟨_, _, _, he'', hty, hhas⟩ := h
  refine (isDefEq.WF hty hA).bind fun b s' _ hEq => ?_
  split
  · have hEq := hEq (by assumption)
    cases he''.unique he_unique he
    exact hnext s' (VEnv.HasType.defeqU_r c.Ewf c.Δwf hEq hhas)
  · exact (hfail (s' := s')).bind nofun

theorem isDefEqGuard.bind_WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α} {next : M β} {Q : β → VState → Prop}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s', c.IsDefEqU e₁' e₂' → M.WF c s' next Q) :
    M.WF c s (do
      unless ← TypeChecker.isDefEq e₁ e₂ do fail
      next) Q := by
  refine (isDefEq.WF he₁ he₂).bind fun b s' _ hEq => ?_
  split
  · exact hnext s' (hEq (by assumption))
  · exact (hfail (s' := s')).bind nofun

theorem isDefEqGuard.WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (do unless ← TypeChecker.isDefEq e₁ e₂ do fail)
      fun _ _ => c.IsDefEqU e₁' e₂' := by
  refine (isDefEq.WF he₁ he₂).bind fun b s' _ hEq => ?_
  split
  · exact .pure (hEq (by assumption))
  · exact (hfail (s' := s')).mono nofun

theorem inferTypeIsDefEqGuard.bind_WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α} {next : M β} {Q : β → VState → Prop}
    (he : c.TrExprS e e') (hA : c.TrExprS A A')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s', c.HasType e' A' → M.WF c s' next Q) :
    M.WF c s (do
      unless ← TypeChecker.isDefEq (← TypeChecker.inferType e) A do fail
      next) Q := by
  refine (inferType.WF he).bind fun _ _ _ h => ?_
  let ⟨_, _, _, hty, hhas⟩ := h
  refine (isDefEq.WF hty hA).bind fun b s' _ hEq => ?_
  split
  · exact hnext s' (hhas.defeqU_r c.Ewf c.Δwf (hEq (by assumption)))
  · exact (hfail (s' := s')).bind nofun

theorem checkTypeDiscard.bind_WF {c : VContext} {s : VState}
    {next : M β} {Q : β → VState → Prop}
    (he : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hnext : ∀ s', M.WF c s' next Q) :
    M.WF c s (do _ ← TypeChecker.checkType e; next) Q :=
  (checkType.WF he).bind fun _ s' _ _ => hnext s'


theorem checkTypeList.WF {c : VContext} {s : VState} {es : List Expr}
    (hes : ∀ e ∈ es, e.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (checkExprTypes es)
      fun _ _ => ∀ e ∈ es, ∃ e' A', c.TrExprS e e' ∧ c.HasType e' A' := by
  induction es generalizing s with
  | nil =>
    simp only [checkExprTypes]
    exact .pure fun _ h => by simp at h
  | cons e es ih =>
    simp only [checkExprTypes]
    refine (checkType.WF (hes e (by simp))).bind fun _ _ _ h => ?_
    rcases h with ⟨e', A', _, he', _, hhas⟩
    refine (ih (fun x hx => hes x (by simp [hx]))).mono fun _ _ _ htail => ?_
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨e', A', he', hhas⟩
    · exact htail x hx

theorem inferTypeIsPropGuard.bind_WF {c : VContext} {s : VState}
    {fail : ∀ {α}, M α} {next : M β} {Q : β → VState → Prop}
    (he : c.TrExprS e e')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s',
      (∃ ty', c.HasType e' ty' ∧ c.HasType ty' (.sort .zero)) → M.WF c s' next Q) :
    M.WF c s (do
      unless ← TypeChecker.isProp (← TypeChecker.inferType e) do fail
      next) Q := by
  refine (inferType.WF he).bind fun _ _ _ h => ?_
  let ⟨ty', _, _, hty, hhas⟩ := h
  refine (isProp.WF hty).bind fun b s' _ hprop => ?_
  split
  · exact hnext s' ⟨ty', hhas, hprop (by assumption)⟩
  · exact (hfail (s' := s')).bind nofun

theorem Reflection.check.WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α}
    (hr : c.TrExprS r.type rtype) (hr_unique : TrExprS.IsUnique r.type)
    (hcanon : c.TrExprS q(Prop → Bool → Prop) canon)
    (hfail : ∀ {α} {s'}, s ≤ s' →
      M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (r.check fail) fun _ _ => c.HasType rtype canon := by
  simp only [Reflection.check]
  refine (checkType.WF hr.fvarsIn).bind fun _ _ le₁ h => ?_
  let ⟨_, _, _, hr', hty, hhas⟩ := h
  refine (isDefEq.WF hty hcanon).bind fun b s' le₂ hEq => ?_
  split
  · have hEq := hEq (by assumption)
    cases hr'.unique hr_unique hr
    exact .pure (VEnv.HasType.defeqU_r c.Ewf c.Δwf hEq hhas)
  · exact (hfail (le₁.trans le₂)).mono nofun

theorem Reflection.check.bind_WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α} {next : M β} {Q}
    (hr : c.TrExprS r.type rtype) (hr_unique : TrExprS.IsUnique r.type)
    (hcanon : c.TrExprS q(Prop → Bool → Prop) canon)
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s', M.WF c s' next Q) :
    M.WF c s (do r.check fail; next) Q := by
  exact (Reflection.check.WF hr hr_unique hcanon (fun _ => hfail)).bind
    fun _ s' _ _ => hnext s'

theorem Reflection.checkITE.WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α}
    (hite : c.TrExprS r.ite ite') (hite_unique : TrExprS.IsUnique r.ite)
    (hiteTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) q(∀ α : Type, α → α → α)) iteTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0) falseR')
    (hfail : ∀ {α} {s'}, s ≤ s' →
      M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (r.checkITE fail) fun _ _ =>
      c.HasType ite' iteTy' ∧ c.IsDefEqU trueL' trueR' ∧
        c.IsDefEqU falseL' falseR' := by
  simp only [Reflection.checkITE]
  refine (checkType.WF hite.fvarsIn).bind fun _ _ le₁ h => ?_
  let ⟨_, _, _, hite'', hty, hhas⟩ := h
  refine (isDefEq.WF hty hiteTy).bind fun b _ le₂ htyEq => ?_
  split
  · have htyEq := htyEq (by assumption)
    cases hite''.unique hite_unique hite
    have hiteHas := VEnv.HasType.defeqU_r c.Ewf c.Δwf htyEq hhas
    exact (isDefEq.WF htrueL htrueR).bind fun b _ le₃ htrueEq => by
      split
      · have htrueEq := htrueEq (by assumption)
        exact (isDefEq.WF hfalseL hfalseR).bind fun b _ le₄ hfalseEq => by
          split
          · exact .pure ⟨hiteHas, htrueEq, hfalseEq (by assumption)⟩
          · exact (hfail (((le₁.trans le₂).trans le₃).trans le₄)).mono nofun
      · exact (hfail ((le₁.trans le₂).trans le₃)).bind nofun
  · exact (hfail (le₁.trans le₂)).bind nofun

theorem Reflection.checkITE.bind_WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α} {next : M β} {Q}
    (hite : c.TrExprS r.ite ite') (hite_unique : TrExprS.IsUnique r.ite)
    (hiteTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) q(∀ α : Type, α → α → α)) iteTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0) falseR')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s',
      (c.HasType ite' iteTy' ∧ c.IsDefEqU trueL' trueR' ∧
        c.IsDefEqU falseL' falseR') → M.WF c s' next Q) :
    M.WF c s (do _ ← r.checkITE fail; next) Q := by
  exact (Reflection.checkITE.WF hite hite_unique hiteTy htrueL htrueR
    hfalseL hfalseR (fun _ => hfail)).bind fun _ s' _ h => hnext s' h


theorem Reflection.checkITE.WF.checked {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α}
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hite : c.TrExprS r.ite ite') (hite_unique : TrExprS.IsUnique r.ite)
    (hiteTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) q(∀ α : Type, α → α → α)) iteTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0) falseR')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (r.checkITE fail) fun _ _ =>
      c.HasType ite' iteTy' ∧ VEnv.ReflectionITEChecked c.venv r := by
  refine (Reflection.checkITE.WF hite hite_unique hiteTy htrueL htrueR
    hfalseL hfalseR (fun _ => hfail)).mono fun _ _ _ h => ?_
  rcases h with ⟨hiteHas, hteq, hfeq⟩
  change TrExprS c.venv c.lparams c.vlctx _ _ at htrueL htrueR hfalseL hfalseR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at hteq hfeq
  rw [hlparams, hvlctx] at htrueL htrueR hfalseL hfalseR hteq hfeq
  exact ⟨hiteHas, _, _, _, _, htrueL, htrueR, hteq,
    hfalseL, hfalseR, hfeq⟩

theorem Reflection.checkNatDITE.WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α}
    (hnot : c.TrExprS q(Not) not') (hnot_unique : TrExprS.IsUnique q(Not))
    (hnotTy : c.TrExprS q(Prop → Prop) notTy')
    (hdite : c.TrExprS r.natDITE dite') (hdite_unique : TrExprS.IsUnique r.natDITE)
    (hditeTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
      .arrow (.arrow (.bvar 2) q(Nat)) <|
      .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)) diteTy')
    (hofTrue : c.TrExprS r.ofTrue ofTrue')
    (hofTrue_unique : TrExprS.IsUnique r.ofTrue)
    (hofTrueTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)) ofTrueTy')
    (hofFalse : c.TrExprS r.ofFalse ofFalse')
    (hofFalse_unique : TrExprS.IsUnique r.ofFalse)
    (hofFalseTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))) ofFalseTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0) (.bvar 2) (.bvar 1)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0) (.bvar 2) (.bvar 1)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))) falseR')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (r.checkNatDITE fail) fun _ _ =>
      c.HasType dite' diteTy' ∧
      c.HasType ofTrue' ofTrueTy' ∧
      c.HasType ofFalse' ofFalseTy' ∧
      c.IsDefEqU trueL' trueR' ∧ c.IsDefEqU falseL' falseR' := by
  simp only [Reflection.checkNatDITE]
  refine checkTypeIsDefEqGuard.bind_WF hnot hnot_unique hnotTy hfail fun _ _ => ?_
  refine checkTypeIsDefEqGuard.bind_WF hdite hdite_unique hditeTy hfail fun _ hditeHas => ?_
  refine checkTypeIsDefEqGuard.bind_WF hofTrue hofTrue_unique hofTrueTy hfail fun _ hofTrueHas => ?_
  refine checkTypeIsDefEqGuard.bind_WF hofFalse hofFalse_unique hofFalseTy hfail fun _ hofFalseHas => ?_
  refine isDefEqGuard.bind_WF htrueL htrueR hfail fun _ htrueEq => ?_
  exact (isDefEqGuard.WF hfalseL hfalseR hfail).mono fun _ _ _ hfalseEq =>
    ⟨hditeHas, hofTrueHas, hofFalseHas, htrueEq, hfalseEq⟩


theorem Reflection.checkNatDITE.WF.checked {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α}
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hnot : c.TrExprS q(Not) not') (hnot_unique : TrExprS.IsUnique q(Not))
    (hnotTy : c.TrExprS q(Prop → Prop) notTy')
    (hdite : c.TrExprS r.natDITE dite') (hdite_unique : TrExprS.IsUnique r.natDITE)
    (hditeTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
      .arrow (.arrow (.bvar 2) q(Nat)) <|
      .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)) diteTy')
    (hofTrue : c.TrExprS r.ofTrue ofTrue')
    (hofTrue_unique : TrExprS.IsUnique r.ofTrue)
    (hofTrueTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)) ofTrueTy')
    (hofFalse : c.TrExprS r.ofFalse ofFalse')
    (hofFalse_unique : TrExprS.IsUnique r.ofFalse)
    (hofFalseTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))) ofFalseTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0) (.bvar 2) (.bvar 1)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0) (.bvar 2) (.bvar 1)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))) falseR')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (r.checkNatDITE fail) fun _ _ =>
      c.HasType dite' diteTy' ∧
      c.HasType ofTrue' ofTrueTy' ∧
      c.HasType ofFalse' ofFalseTy' ∧
      VEnv.ReflectionNatDITEChecked c.venv r := by
  refine (Reflection.checkNatDITE.WF hnot hnot_unique hnotTy hdite hdite_unique
    hditeTy hofTrue hofTrue_unique hofTrueTy hofFalse hofFalse_unique hofFalseTy
    htrueL htrueR hfalseL hfalseR hfail).mono fun _ _ _ h => ?_
  rcases h with ⟨hditeHas, hofTrueHas, hofFalseHas, hteq, hfeq⟩
  change TrExprS c.venv c.lparams c.vlctx _ _ at htrueL htrueR hfalseL hfalseR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at hteq hfeq
  rw [hlparams, hvlctx] at htrueL htrueR hfalseL hfalseR hteq hfeq
  exact ⟨hditeHas, hofTrueHas, hofFalseHas,
    _, _, _, _, htrueL, htrueR, hteq, hfalseL, hfalseR, hfeq⟩

theorem Reflection.checkNatDITE.bind_WF {c : VContext} {s : VState}
    {r : Reflection} {fail : ∀ {α}, M α} {next : M β} {Q}
    (hnot : c.TrExprS q(Not) not') (hnot_unique : TrExprS.IsUnique q(Not))
    (hnotTy : c.TrExprS q(Prop → Prop) notTy')
    (hdite : c.TrExprS r.natDITE dite') (hdite_unique : TrExprS.IsUnique r.natDITE)
    (hditeTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 r.type (.bvar 1) (.bvar 0)) <|
      .arrow (.arrow (.bvar 2) q(Nat)) <|
      .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)) diteTy')
    (hofTrue : c.TrExprS r.ofTrue ofTrue')
    (hofTrue_unique : TrExprS.IsUnique r.ofTrue)
    (hofTrueTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(true)) (.bvar 1)) ofTrueTy')
    (hofFalse : c.TrExprS r.ofFalse ofFalse')
    (hofFalse_unique : TrExprS.IsUnique r.ofFalse)
    (hofFalseTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 r.type (.bvar 0) q(false)) (mkApp q(Not) (.bvar 1))) ofFalseTy')
    (htrueL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0) (.bvar 2) (.bvar 1)) trueL')
    (htrueR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))) trueR')
    (hfalseL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0) (.bvar 2) (.bvar 1)) falseL')
    (hfalseR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))) falseR')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False)
    (hnext : ∀ s',
      (c.IsDefEqU trueL' trueR' ∧ c.IsDefEqU falseL' falseR') →
        M.WF c s' next Q) :
    M.WF c s (do _ ← r.checkNatDITE fail; next) Q := by
  exact (Reflection.checkNatDITE.WF hnot hnot_unique hnotTy hdite hdite_unique
    hditeTy hofTrue hofTrue_unique hofTrueTy hofFalse hofFalse_unique hofFalseTy
    htrueL htrueR hfalseL hfalseR hfail).bind fun _ s' _ h =>
      hnext s' ⟨h.2.2.2.1, h.2.2.2.2⟩

theorem Condition.check.reflectNatNat_ite.WF {c : VContext} {s : VState}
    {cond : Condition} {asBool : Expr} {reflect : Reflection} {proof : Expr}
    {fail : ∀ {α}, M α} {Rite : Prop}
    (himpl : cond.impl = .reflectNatNat asBool reflect proof)
    (hdec : c.TrExprS cond.dec dec')
    (hprop : c.TrExprS cond.prop prop')
    (hpropTy : c.TrExprS q(Nat → Nat → Prop) propTy')
    (hreflect : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', M.WF c s'' next Q) →
      M.WF c s' (do reflect.check fail; next) Q)
    (hcheckITE : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', Rite → M.WF c s'' next Q) →
      M.WF c s' (do _ ← reflect.checkITE fail; next) Q)
    (he : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 reflect.toDec
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 asBool (.bvar 1) (.bvar 0))
        (mkApp2 proof (.bvar 1) (.bvar 0))) e')
    (hdecide : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp5 q(@_root_.ite.{1}) q(Bool)
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 cond.dec (.bvar 1) (.bvar 0)) q(true) q(false)) decide')
    (hdecideTy : c.TrExprS q(Nat → Nat → Bool) decideTy')
    (hasBool : c.TrExprS asBool asBool')
    (hasBoolTy : c.TrExprS q(Nat → Nat → Bool) asBoolTy')
    (hproof : c.TrExprS proof proof')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (cond.check fail (ite := true)) fun _ _ =>
      Rite ∧ c.IsDefEqU e' dec' := by
  simp [Condition.check, himpl]
  refine checkTypeDiscard.bind_WF hdec.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hprop hpropTy hfail fun _ _ => ?_
  refine hreflect fun _ => ?_
  refine hcheckITE fun _ hite => ?_
  refine checkTypeDiscard.bind_WF he.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hdecide hdecideTy hfail fun _ _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hasBool hasBoolTy hfail fun _ _ => ?_
  refine inferTypeIsPropGuard.bind_WF hproof hfail fun _ _ => ?_
  exact (isDefEqGuard.WF he hdec hfail).mono fun _ _ _ heq => ⟨hite, heq⟩

theorem Condition.check.reflectNatNat_dite.WF {c : VContext} {s : VState}
    {cond : Condition} {asBool : Expr} {reflect : Reflection} {proof : Expr}
    {fail : ∀ {α}, M α} {Rdite : Prop}
    (himpl : cond.impl = .reflectNatNat asBool reflect proof)
    (hdec : c.TrExprS cond.dec dec')
    (hprop : c.TrExprS cond.prop prop')
    (hpropTy : c.TrExprS q(Nat → Nat → Prop) propTy')
    (hreflect : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', M.WF c s'' next Q) →
      M.WF c s' (do reflect.check fail; next) Q)
    (hcheckDITE : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', Rdite → M.WF c s'' next Q) →
      M.WF c s' (do _ ← reflect.checkNatDITE fail; next) Q)
    (he : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 reflect.toDec
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 asBool (.bvar 1) (.bvar 0))
        (mkApp2 proof (.bvar 1) (.bvar 0))) e')
    (hdecide : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp5 q(@_root_.ite.{1}) q(Bool)
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 cond.dec (.bvar 1) (.bvar 0)) q(true) q(false)) decide')
    (hdecideTy : c.TrExprS q(Nat → Nat → Bool) decideTy')
    (hasBool : c.TrExprS asBool asBool')
    (hasBoolTy : c.TrExprS q(Nat → Nat → Bool) asBoolTy')
    (hproof : c.TrExprS proof proof')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (cond.check fail (dite := true)) fun _ _ =>
      Rdite ∧ c.IsDefEqU e' dec' := by
  simp [Condition.check, himpl]
  refine checkTypeDiscard.bind_WF hdec.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hprop hpropTy hfail fun _ _ => ?_
  refine hreflect fun _ => ?_
  refine hcheckDITE fun _ hdite => ?_
  refine checkTypeDiscard.bind_WF he.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hdecide hdecideTy hfail fun _ _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hasBool hasBoolTy hfail fun _ _ => ?_
  refine inferTypeIsPropGuard.bind_WF hproof hfail fun _ _ => ?_
  exact (isDefEqGuard.WF he hdec hfail).mono fun _ _ _ heq => ⟨hdite, heq⟩

theorem Condition.check.reflectNatNat_ite_dite.WF {c : VContext} {s : VState}
    {cond : Condition} {asBool : Expr} {reflect : Reflection} {proof : Expr}
    {fail : ∀ {α}, M α} {Rreflect Rite Rdite : Prop}
    (himpl : cond.impl = .reflectNatNat asBool reflect proof)
    (hdec : c.TrExprS cond.dec dec')
    (hprop : c.TrExprS cond.prop prop')
    (hpropTy : c.TrExprS q(Nat → Nat → Prop) propTy')
    (hreflect : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', Rreflect → M.WF c s'' next Q) →
      M.WF c s' (do reflect.check fail; next) Q)
    (hcheckITE : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', Rite → M.WF c s'' next Q) →
      M.WF c s' (do _ ← reflect.checkITE fail; next) Q)
    (hcheckDITE : ∀ {β} {next : M β} {Q} {s'},
      (∀ s'', Rdite → M.WF c s'' next Q) →
      M.WF c s' (do _ ← reflect.checkNatDITE fail; next) Q)
    (he : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp3 reflect.toDec
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 asBool (.bvar 1) (.bvar 0))
        (mkApp2 proof (.bvar 1) (.bvar 0))) e')
    (hdecide : c.TrExprS
      (.lam0 q(Nat) <| .lam0 q(Nat) <| mkApp5 q(@_root_.ite.{1}) q(Bool)
        (mkApp2 cond.prop (.bvar 1) (.bvar 0))
        (mkApp2 cond.dec (.bvar 1) (.bvar 0)) q(true) q(false)) decide')
    (hdecideTy : c.TrExprS q(Nat → Nat → Bool) decideTy')
    (hasBool : c.TrExprS asBool asBool')
    (hasBoolTy : c.TrExprS q(Nat → Nat → Bool) asBoolTy')
    (hproof : c.TrExprS proof proof')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (cond.check fail (ite := true) (dite := true)) fun _ _ =>
      Rreflect ∧ Rite ∧ Rdite ∧ c.IsDefEqU e' dec' := by
  simp [Condition.check, himpl]
  refine checkTypeDiscard.bind_WF hdec.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hprop hpropTy hfail fun _ _ => ?_
  refine hreflect fun _ hreflect => ?_
  refine hcheckITE fun _ hite => ?_
  refine hcheckDITE fun _ hdite => ?_
  refine checkTypeDiscard.bind_WF he.fvarsIn fun _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hdecide hdecideTy hfail fun _ _ => ?_
  refine inferTypeIsDefEqGuard.bind_WF hasBool hasBoolTy hfail fun _ _ => ?_
  refine inferTypeIsPropGuard.bind_WF hproof hfail fun _ _ => ?_
  exact (isDefEqGuard.WF he hdec hfail).mono fun _ _ _ heq =>
    ⟨hreflect, hite, hdite, heq⟩

/-- A successful `Nat ≤` condition check retains both selector interfaces
needed by the `Nat.mod` checker and the dependent selector needed by
`Nat.div`. -/
theorem Condition.natLE.check.WF
    {c : VContext} {s : VState} {fail : ∀ {α}, M α}
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hdec : c.TrExprS Condition.natLE.dec dec')
    (hprop : c.TrExprS Condition.natLE.prop prop')
    (hpropTy : c.TrExprS q(Nat → Nat → Prop) propTy')
    (hrtype : c.TrExprS Reflection.defn₁.type rtype')
    (hrtypeUnique : TrExprS.IsUnique Reflection.defn₁.type)
    (hrtypeCanon : c.TrExprS q(Prop → Bool → Prop) rtypeCanon')
    (hite : c.TrExprS Reflection.defn₁.ite ite')
    (hiteUnique : TrExprS.IsUnique Reflection.defn₁.ite)
    (hiteTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 Reflection.defn₁.type (.bvar 1) (.bvar 0))
        q(∀ α : Type, α → α → α)) iteTy')
    (hiteTrueL : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₁.type (.bvar 0) q(true)) <|
          mkApp3 Reflection.defn₁.ite (.bvar 1) q(true) (.bvar 0)) iteTrueL')
    (hiteTrueR : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₁.type (.bvar 0) q(true)) <|
          .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <|
            .bvar 1) iteTrueR')
    (hiteFalseL : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₁.type (.bvar 0) q(false)) <|
          mkApp3 Reflection.defn₁.ite (.bvar 1) q(false) (.bvar 0)) iteFalseL')
    (hiteFalseR : c.TrExprS
      (.lam0 q(Prop) <|
        .lam0 (mkApp2 Reflection.defn₁.type (.bvar 0) q(false)) <|
          .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <|
            .bvar 0) iteFalseR')
    (hnot : c.TrExprS q(Not) not') (hnotUnique : TrExprS.IsUnique q(Not))
    (hnotTy : c.TrExprS q(Prop → Prop) notTy')
    (hdite : c.TrExprS Reflection.defn₁.natDITE dite')
    (hditeUnique : TrExprS.IsUnique Reflection.defn₁.natDITE)
    (hditeTy : c.TrExprS (.arrow q(Prop) <| .arrow q(Bool) <|
      .arrow (mkApp2 Reflection.defn₁.type (.bvar 1) (.bvar 0)) <|
      .arrow (.arrow (.bvar 2) q(Nat)) <|
      .arrow (.arrow (mkApp q(Not) (.bvar 3)) q(Nat)) q(Nat)) diteTy')
    (hofTrue : c.TrExprS Reflection.defn₁.ofTrue ofTrue')
    (hofTrueUnique : TrExprS.IsUnique Reflection.defn₁.ofTrue)
    (hofTrueTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 Reflection.defn₁.type (.bvar 0) q(true))
        (.bvar 1)) ofTrueTy')
    (hofFalse : c.TrExprS Reflection.defn₁.ofFalse ofFalse')
    (hofFalseUnique : TrExprS.IsUnique Reflection.defn₁.ofFalse)
    (hofFalseTy : c.TrExprS (.arrow q(Prop) <|
      .arrow (mkApp2 Reflection.defn₁.type (.bvar 0) q(false))
        (mkApp q(Not) (.bvar 1))) ofFalseTy')
    (hditeTrueL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 Reflection.defn₁.type (.bvar 2) q(true)) <|
       mkApp5 Reflection.defn₁.natDITE (.bvar 3) q(true) (.bvar 0)
         (.bvar 2) (.bvar 1)) diteTrueL')
    (hditeTrueR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 Reflection.defn₁.type (.bvar 2) q(true)) <|
       mkApp (.bvar 2)
         (mkApp2 Reflection.defn₁.ofTrue (.bvar 3) (.bvar 0))) diteTrueR')
    (hditeFalseL : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 Reflection.defn₁.type (.bvar 2) q(false)) <|
       mkApp5 Reflection.defn₁.natDITE (.bvar 3) q(false) (.bvar 0)
         (.bvar 2) (.bvar 1)) diteFalseL')
    (hditeFalseR : c.TrExprS
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 Reflection.defn₁.type (.bvar 2) q(false)) <|
       mkApp (.bvar 1)
         (mkApp2 Reflection.defn₁.ofFalse (.bvar 3) (.bvar 0))) diteFalseR')
    (hreflect : c.TrExprS Condition.natLEReflectedFn reflectFn')
    (hdecide : c.TrExprS Condition.natLEDecideFn decide')
    (hdecideTy : c.TrExprS q(Nat → Nat → Bool) decideTy')
    (hasBool : c.TrExprS q(Nat.ble) asBool')
    (hasBoolTy : c.TrExprS q(Nat → Nat → Bool) asBoolTy')
    (hproof : c.TrExprS Condition.natLEReflectProof proof')
    (hfail : ∀ {α} {s'}, M.WF c s' (fail : M α) fun _ _ => False) :
    M.WF c s (Condition.natLE.check fail (ite := true) (dite := true))
      fun _ _ =>
        c.HasType rtype' rtypeCanon' ∧
        (c.HasType ite' iteTy' ∧
          VEnv.ReflectionITEChecked c.venv Reflection.defn₁) ∧
        (c.HasType dite' diteTy' ∧
          c.HasType ofTrue' ofTrueTy' ∧
          c.HasType ofFalse' ofFalseTy' ∧
          VEnv.ReflectionNatDITEChecked c.venv Reflection.defn₁) ∧
        c.IsDefEqU reflectFn' dec' := by
  apply Condition.check.reflectNatNat_ite_dite.WF (cond := Condition.natLE)
    (asBool := q(Nat.ble)) (reflect := Reflection.defn₁)
    (proof := Condition.natLEReflectProof) (by rfl)
    hdec hprop hpropTy
  · intro β next Q s' hnext
    exact (Reflection.check.WF hrtype hrtypeUnique hrtypeCanon
      (fun _ => hfail)).bind fun _ s'' _ hrtypeHas =>
        hnext s'' hrtypeHas
  · intro β next Q s' hnext
    exact (Reflection.checkITE.WF.checked hlparams hvlctx hite hiteUnique
      hiteTy hiteTrueL hiteTrueR hiteFalseL hiteFalseR hfail).bind
        fun _ s'' _ hcert => hnext s'' hcert
  · intro β next Q s' hnext
    exact (Reflection.checkNatDITE.WF.checked hlparams hvlctx hnot hnotUnique
      hnotTy hdite hditeUnique hditeTy hofTrue hofTrueUnique hofTrueTy
      hofFalse hofFalseUnique hofFalseTy hditeTrueL hditeTrueR
      hditeFalseL hditeFalseR hfail).bind
        fun _ s'' _ hcert => hnext s'' hcert
  · exact hreflect
  · exact hdecide
  · exact hdecideTy
  · exact hasBool
  · exact hasBoolTy
  · exact hproof
  · exact hfail


end Lean4Lean.Environment
