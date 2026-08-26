/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.BitwiseReflect

/-!
# Verified Nat.bitwise specializations

This module certifies the finite `Nat.land`, `Nat.lor`, and `Nat.xor`
wrappers over the generic-state `Nat.bitwise` primitive. It manually adapts
the corresponding bounded slice of lean4lean PR #32 while retaining this
fork's readiness-aware environment transaction.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel TypeChecker

@[simp] private theorem mkApp2_eq_app (f a b : Expr) :
    mkApp2 f a b = (f.app a).app b := rfl

@[simp] private theorem Expr.lam0_eq_lam (ty body : Expr) :
    Expr.lam0 ty body = .lam `_ ty body .default := rfl

namespace Environment

/-- Recover the Nat and Bool declarations from the checked generic bitwise
reflection. This avoids treating source-level dependency membership as a
Theory typing fact. -/
theorem VEnv.HasPrimitives.nat_bool_of_bitwise_contains
    {env : VEnv} (h : env.HasPrimitives) (wf : env.WF)
    (hbitwise : env.contains ``Nat.bitwise) :
    env.contains ``Nat ∧ env.contains ``Bool := by
  have hfun := (h.natBitwise hbitwise).1 0 []
  have ⟨_, hfunType⟩ := hfun.isType wf trivial
  obtain ⟨⟨_, hopType⟩, ⟨_, hrestType⟩⟩ := hfunType.forallE_inv wf
  obtain ⟨⟨_, hboolType⟩, _⟩ := hopType.forallE_inv wf
  obtain ⟨_, hbool, _⟩ := hboolType.const_inv wf trivial
  obtain ⟨⟨_, hnatType⟩, _⟩ := hrestType.forallE_inv wf
  have hctx : OnCtx [(.forallE .bool <| .forallE .bool .bool)]
      (env.IsType 0) := ⟨trivial, ⟨_, hopType⟩⟩
  obtain ⟨_, hnat, _⟩ := hnatType.const_inv wf hctx
  exact ⟨⟨_, hnat⟩, ⟨_, hbool⟩⟩

/-- Decompose a translated `Nat.bitwise op` body and recover the translated
operator together with its canonical Boolean binary type. -/
theorem TrExprS.bitwise_op
    {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hbitwise : env.contains ``Nat.bitwise) (hΔ : Δ.WF env Us.length)
    (hvalue : TrExprS env Us Δ
      (.app (.const ``Nat.bitwise []) op) value') :
    ∃ op', value' = .app (.const ``Nat.bitwise []) op' ∧
      TrExprS env Us Δ op op' ∧
      env.HasType Us.length Δ.toCtx op'
        (.forallE .bool <| .forallE .bool .bool) := by
  cases hvalue with
  | app hfunT hopT hfunS hopS =>
    cases hfunS with
    | const hci hlevels hlen =>
      simp at hlevels
      subst hlevels
      have hcanonT := (hprim.natBitwise hbitwise).1 Us.length Δ.toCtx
      have hfunEq := hfunT.uniqU wf hΔ.toCtx hcanonT
      obtain ⟨⟨_, hdomEq⟩, _⟩ := hfunEq.forallE_inv wf hΔ.toCtx
      exact ⟨_, rfl, hopS,
        hopT.defeqU_r wf hΔ.toCtx ⟨_, hdomEq⟩⟩

/-- A globally closed translation can be reused under a fresh local Bool
binder without changing its translated expression. -/
private theorem TrExprS.closed_weak
    {env : VEnv} (wf : env.WF)
    {e : Expr} {eV : VExpr} {Δ : VLCtx} {dn n : Nat}
    (hglobal : TrExprS env Us [] e eV)
    (W : VLCtx.BVLift [] Δ dn 0 n 0) :
    TrExprS env Us Δ e eV := by
  obtain ⟨_, hglobalWF⟩ := hglobal.wf wf.ordered
    (Δ := []) trivial
  have heVClosed :=
    (hglobalWF.hasType.1.closedN' wf.ordered.closed trivial).1
  have hsourceClosed := hglobal.closed.looseBVarRange_zero
  have hsourceLift : e.liftLooseBVars' 0 dn = e :=
    Expr.liftLooseBVars_eq_self (by rw [hsourceClosed]; omega)
  have htargetLift : eV.liftN n 0 = eV :=
    heVClosed.liftN_eq (Nat.zero_le _)
  have hweak := hglobal.weakBV wf.ordered W
  rwa [hsourceLift, htargetLift] at hweak

/-- Translate the two left-fixed Boolean equations used by `land` and `lor`,
plus their constant and identity right-hand sides. -/
theorem TrExprS.boolLeftLamEvidence
    {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hbool : env.contains ``Bool) (hopS : TrExprS env Us [] op op')
    (hopT : env.HasType Us.length [] op'
      (.forallE .bool <| .forallE .bool .bool)) :
    TrExprS env Us []
        (.lam0 q(Bool) <| mkApp2 op q(false) (.bvar 0))
        (.lam .bool <| .app (.app op' .boolFalse) (.bvar 0)) ∧
      TrExprS env Us [] (.lam0 q(Bool) q(false))
        (.lam .bool .boolFalse) ∧
      TrExprS env Us []
        (.lam0 q(Bool) <| mkApp2 op q(true) (.bvar 0))
        (.lam .bool <| .app (.app op' .boolTrue) (.bvar 0)) ∧
      TrExprS env Us [] (.lam0 q(Bool) <| .bvar 0)
        (.lam .bool <| .bvar 0) ∧
      TrExprS env Us [] (.lam0 q(Bool) q(true))
        (.lam .bool .boolTrue) := by
  let Δ : VLCtx := [(none, .vlam .bool)]
  have hbool0 := TrExprS.boolType_of_contains wf hprim hbool Us []
  have hbool1 := TrExprS.boolType_of_contains wf hprim hbool Us Δ
  have hf := TrExprS.boolFalse (Us := Us) (Δ := Δ) hprim hbool
  have ht := TrExprS.boolTrue (Us := Us) (Δ := Δ) hprim hbool
  have hxS : TrExprS env Us Δ (.bvar 0) (.bvar 0) :=
    .bvar (e := .bvar 0) (A := .bool) (by
      simp [Δ, VLCtx.find?, VLCtx.next,
        VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN,
        VExpr.bool])
  have hxT : env.HasType Us.length [.bool] (.bvar 0) .bool :=
    .bvar .zero
  have hopS' : TrExprS env Us Δ op op' :=
    TrExprS.closed_weak wf hopS (.skip (.vlam .bool) .refl)
  have hopT' : env.HasType Us.length [.bool] op'
      (.forallE .bool <| .forallE .bool .bool) := hopT.weak0 wf
  have hfalseBody : TrExprS env Us Δ
      (mkApp2 op q(false) (.bvar 0))
      (.app (.app op' .boolFalse) (.bvar 0)) :=
    .app (.app hopT' hf.2) hxT (.app hopT' hf.2 hopS' hf.1) hxS
  have htrueBody : TrExprS env Us Δ
      (mkApp2 op q(true) (.bvar 0))
      (.app (.app op' .boolTrue) (.bvar 0)) :=
    .app (.app hopT' ht.2) hxT (.app hopT' ht.2 hopS' ht.1) hxS
  exact ⟨.lam hbool0.2 hbool0.1 hfalseBody,
    .lam hbool0.2 hbool0.1 hf.1,
    .lam hbool0.2 hbool0.1 htrueBody,
    .lam hbool0.2 hbool0.1 hxS,
    .lam hbool0.2 hbool0.1 ht.1⟩

set_option maxHeartbeats 800000 in
/-- Exact typed certificate for the finite `Nat.xor` recognizer branch. -/
theorem checkPrimitiveDef.natXor.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.xor)
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat ∧ c.venv.contains ``Bool ∧
      c.venv.contains ``Nat.bitwise ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      ∃ op', value' = .app (.const ``Nat.bitwise []) op' ∧
        c.HasType op' (.forallE .bool <| .forallE .bool .bool) ∧
        c.IsDefEqU (.app (.app op' .boolFalse) .boolFalse) .boolFalse ∧
        c.IsDefEqU (.app (.app op' .boolTrue) .boolFalse) .boolTrue ∧
        c.IsDefEqU (.app (.app op' .boolFalse) .boolTrue) .boolTrue ∧
        c.IsDefEqU (.app (.app op' .boolTrue) .boolTrue) .boolFalse := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  by_cases hdeps : (c.env.contains ``Nat.bitwise &&
      v.levelParams.isEmpty) = true
  · rw [if_pos hdeps]
    have hdeps' : c.env.contains ``Nat.bitwise = true ∧
        v.levelParams = [] := by simpa using hdeps
    have hlevels := hdeps'.2
    have hbitwise : c.venv.contains ``Nat.bitwise :=
      VContext.contains_safe_primitive c hdeps'.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    obtain ⟨hnat, hbool⟩ :=
      Environment.VEnv.HasPrimitives.nat_bool_of_bitwise_contains
        c.hasPrimitives c.Ewf hbitwise
    have hcanon := TrExprS.natBinaryType_of_contains
      c.Ewf c.hasPrimitives hnat c.lparams c.vlctx
    have hopCanon := TrExprS.boolBinaryType_of_contains
      c.Ewf c.hasPrimitives hbool c.lparams c.vlctx
    split
    all_goals try exact .throw
    rename_i op hshape
    have hvalue' := hvalue
    rw [hshape] at hvalue'
    obtain ⟨op', hvalueShape, hop, hopT⟩ :=
      TrExprS.bitwise_op c.Ewf c.hasPrimitives hbitwise c.Δwf hvalue'
    have hf := TrExprS.boolFalse (Us := c.lparams) (Δ := c.vlctx)
      c.hasPrimitives hbool
    have ht := TrExprS.boolTrue (Us := c.lparams) (Δ := c.vlctx)
      c.hasPrimitives hbool
    have hff₁ : c.TrExprS (mkApp2 op q(false) q(false))
        (.app (.app op' .boolFalse) .boolFalse) :=
      .app (.app hopT hf.2) hf.2 (.app hopT hf.2 hop hf.1) hf.1
    have htf₁ : c.TrExprS (mkApp2 op q(true) q(false))
        (.app (.app op' .boolTrue) .boolFalse) :=
      .app (.app hopT ht.2) hf.2 (.app hopT ht.2 hop ht.1) hf.1
    have hft₁ : c.TrExprS (mkApp2 op q(false) q(true))
        (.app (.app op' .boolFalse) .boolTrue) :=
      .app (.app hopT hf.2) ht.2 (.app hopT hf.2 hop hf.1) ht.1
    have htt₁ : c.TrExprS (mkApp2 op q(true) q(true))
        (.app (.app op' .boolTrue) .boolTrue) :=
      .app (.app hopT ht.2) ht.2 (.app hopT ht.2 hop ht.1) ht.1
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        refine (inferType.WF hop).bind fun _ _ _ hOpTy => ?_
        let ⟨_, _, _, hOpTyTr, hOpHas⟩ := hOpTy
        refine (isDefEq.WF hOpTyTr hopCanon).bind fun b _ _ hOpEq => ?_
        split
        · have hopTy := hOpHas.defeqU_r c.Ewf c.Δwf
            (hOpEq (by assumption))
          exact (isDefEq.WF hff₁ hf.1).bind fun b _ _ hffEq => by
            split
            · have hffEq := hffEq (by assumption)
              exact (isDefEq.WF htf₁ ht.1).bind fun b _ _ htfEq => by
                split
                · have htfEq := htfEq (by assumption)
                  exact (isDefEq.WF hft₁ ht.1).bind fun b _ _ hftEq => by
                    split
                    · have hftEq := hftEq (by assumption)
                      exact (isDefEq.WF htt₁ hf.1).bind fun b _ _ httEq => by
                        split
                        · exact .pure fun _ =>
                            ⟨hlevels, hnat, hbool, hbitwise, htyEq,
                              op', hvalueShape, hopTy, hffEq, htfEq,
                              hftEq, httEq (by assumption)⟩
                        · exact .throw
                    · exact .throw
                · exact .throw
            · exact .throw
        · exact .throw
      · exact .throw
  · rw [if_neg hdeps]
    exact .throw

set_option maxHeartbeats 800000 in
/-- Exact typed certificate for the finite `Nat.land` recognizer branch. -/
theorem checkPrimitiveDef.natLand.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.land)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat ∧ c.venv.contains ``Bool ∧
      c.venv.contains ``Nat.bitwise ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      ∃ op', value' = .app (.const ``Nat.bitwise []) op' ∧
        c.HasType op' (.forallE .bool <| .forallE .bool .bool) ∧
        c.IsDefEqU
          (.lam .bool <| .app (.app op' .boolFalse) (.bvar 0))
          (.lam .bool .boolFalse) ∧
        c.IsDefEqU
          (.lam .bool <| .app (.app op' .boolTrue) (.bvar 0))
          (.lam .bool <| .bvar 0) := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hdeps' : c.env.contains ``Nat.bitwise = true ∧
        v.levelParams = [] := by simpa using hdeps
    have hlevels := hdeps'.2
    have hbitwise : c.venv.contains ``Nat.bitwise :=
      VContext.contains_safe_primitive c hdeps'.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    obtain ⟨hnat, hbool⟩ :=
      Environment.VEnv.HasPrimitives.nat_bool_of_bitwise_contains
        c.hasPrimitives c.Ewf hbitwise
    have hcanon := TrExprS.natBinaryType_of_contains
      c.Ewf c.hasPrimitives hnat c.lparams c.vlctx
    have hopCanon := TrExprS.boolBinaryType_of_contains
      c.Ewf c.hasPrimitives hbool c.lparams c.vlctx
    split
    all_goals try exact .throw
    rename_i op hshape
    have hvalue' := hvalue
    rw [hshape] at hvalue'
    obtain ⟨op', hvalueShape, hopS, hopT⟩ :=
      TrExprS.bitwise_op c.Ewf c.hasPrimitives hbitwise c.Δwf hvalue'
    have hopS0 : TrExprS c.venv c.lparams [] op op' := by
      rw [← hvlctx]
      exact hopS
    have hopT0 : c.venv.HasType c.lparams.length [] op'
        (.forallE .bool <| .forallE .bool .bool) := by
      simpa [hvlctx, VLCtx.toCtx] using hopT
    obtain ⟨hf₁, hf₂, ht₁, htId, _⟩ :=
      TrExprS.boolLeftLamEvidence c.Ewf c.hasPrimitives hbool hopS0 hopT0
    have hf₁' : c.TrExprS
        (.lam0 q(Bool) <| mkApp2 op q(false) (.bvar 0))
        (.lam .bool <| .app (.app op' .boolFalse) (.bvar 0)) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact hf₁
    have hf₂' : c.TrExprS (.lam0 q(Bool) q(false))
        (.lam .bool .boolFalse) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact hf₂
    have ht₁' : c.TrExprS
        (.lam0 q(Bool) <| mkApp2 op q(true) (.bvar 0))
        (.lam .bool <| .app (.app op' .boolTrue) (.bvar 0)) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact ht₁
    have htId' : c.TrExprS (.lam0 q(Bool) <| .bvar 0)
        (.lam .bool <| .bvar 0) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact htId
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        refine (inferType.WF hopS).bind fun _ _ _ hOpTy => ?_
        let ⟨_, _, _, hOpTyTr, hOpHas⟩ := hOpTy
        refine (isDefEq.WF hOpTyTr hopCanon).bind fun b _ _ hOpEq => ?_
        split
        · have hopTy := hOpHas.defeqU_r c.Ewf c.Δwf
            (hOpEq (by assumption))
          exact (isDefEq.WF hf₁' hf₂').bind fun b _ _ hfEq => by
            split
            · have hfEq := hfEq (by assumption)
              exact (isDefEq.WF ht₁' htId').bind fun b _ _ htEq => by
                split
                · exact .pure fun _ =>
                    ⟨hlevels, hnat, hbool, hbitwise, htyEq,
                      op', hvalueShape, hopTy, hfEq, htEq (by assumption)⟩
                · exact .throw
            · exact .throw
        · exact .throw
      · exact .throw
  · exact .throw

set_option maxHeartbeats 800000 in
/-- Exact typed certificate for the finite `Nat.lor` recognizer branch. -/
theorem checkPrimitiveDef.natLor.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.lor)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat ∧ c.venv.contains ``Bool ∧
      c.venv.contains ``Nat.bitwise ∧
      c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
      ∃ op', value' = .app (.const ``Nat.bitwise []) op' ∧
        c.HasType op' (.forallE .bool <| .forallE .bool .bool) ∧
        c.IsDefEqU
          (.lam .bool <| .app (.app op' .boolFalse) (.bvar 0))
          (.lam .bool <| .bvar 0) ∧
        c.IsDefEqU
          (.lam .bool <| .app (.app op' .boolTrue) (.bvar 0))
          (.lam .bool .boolTrue) := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hdeps' : c.env.contains ``Nat.bitwise = true ∧
        v.levelParams = [] := by simpa using hdeps
    have hlevels := hdeps'.2
    have hbitwise : c.venv.contains ``Nat.bitwise :=
      VContext.contains_safe_primitive c hdeps'.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    obtain ⟨hnat, hbool⟩ :=
      Environment.VEnv.HasPrimitives.nat_bool_of_bitwise_contains
        c.hasPrimitives c.Ewf hbitwise
    have hcanon := TrExprS.natBinaryType_of_contains
      c.Ewf c.hasPrimitives hnat c.lparams c.vlctx
    have hopCanon := TrExprS.boolBinaryType_of_contains
      c.Ewf c.hasPrimitives hbool c.lparams c.vlctx
    split
    all_goals try exact .throw
    rename_i op hshape
    have hvalue' := hvalue
    rw [hshape] at hvalue'
    obtain ⟨op', hvalueShape, hopS, hopT⟩ :=
      TrExprS.bitwise_op c.Ewf c.hasPrimitives hbitwise c.Δwf hvalue'
    have hopS0 : TrExprS c.venv c.lparams [] op op' := by
      rw [← hvlctx]
      exact hopS
    have hopT0 : c.venv.HasType c.lparams.length [] op'
        (.forallE .bool <| .forallE .bool .bool) := by
      simpa [hvlctx, VLCtx.toCtx] using hopT
    obtain ⟨hf₁, _, ht₁, htId, htTrue⟩ :=
      TrExprS.boolLeftLamEvidence c.Ewf c.hasPrimitives hbool hopS0 hopT0
    have hf₁' : c.TrExprS
        (.lam0 q(Bool) <| mkApp2 op q(false) (.bvar 0))
        (.lam .bool <| .app (.app op' .boolFalse) (.bvar 0)) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact hf₁
    have hfId' : c.TrExprS (.lam0 q(Bool) <| .bvar 0)
        (.lam .bool <| .bvar 0) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact htId
    have ht₁' : c.TrExprS
        (.lam0 q(Bool) <| mkApp2 op q(true) (.bvar 0))
        (.lam .bool <| .app (.app op' .boolTrue) (.bvar 0)) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact ht₁
    have htTrue' : c.TrExprS (.lam0 q(Bool) q(true))
        (.lam .bool .boolTrue) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact htTrue
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      split
      · have htyEq := htyEq (by assumption)
        refine (inferType.WF hopS).bind fun _ _ _ hOpTy => ?_
        let ⟨_, _, _, hOpTyTr, hOpHas⟩ := hOpTy
        refine (isDefEq.WF hOpTyTr hopCanon).bind fun b _ _ hOpEq => ?_
        split
        · have hopTy := hOpHas.defeqU_r c.Ewf c.Δwf
            (hOpEq (by assumption))
          exact (isDefEq.WF hf₁' hfId').bind fun b _ _ hfEq => by
            split
            · have hfEq := hfEq (by assumption)
              exact (isDefEq.WF ht₁' htTrue').bind fun b _ _ htEq => by
                split
                · exact .pure fun _ =>
                    ⟨hlevels, hnat, hbool, hbitwise, htyEq,
                      op', hvalueShape, hopTy, hfEq, htEq (by assumption)⟩
                · exact .throw
            · exact .throw
        · exact .throw
      · exact .throw
  · exact .throw

end Environment

/-! ## Semantic specialization and primitive-contract conservation -/

/-- Environment extension preserves constant membership. -/
theorem VEnv.LE.contains {env env' : VEnv} (le : env ≤ env')
    (h : env.contains n) : env'.contains n := by
  obtain ⟨ci, hci⟩ := h
  exact ⟨ci, le.constants hci⟩

/-- Specialize the Kripke generic bitwise reflection at a checked Boolean
operator and transport it across the wrapper's definitional equality. -/
theorem VEnv.ReflectsNatNatNat.of_bitwise_specialization
    (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hbitwise : env.ReflectsNatBitwise ``Nat.bitwise)
    (hbitwiseC : env.contains ``Nat.bitwise)
    (hf : ∀ U Γ, env.HasType U Γ (.const fc [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const fc [])
      (.app (.const ``Nat.bitwise []) op))
    (hop : env.ReflectsBoolBin op f)
    (hg : g = Nat.bitwise f) : env.ReflectsNatNatNat fc g := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
  have h₂ := h₁.app_same henv trivial (.app (hf 0 []) (hlit a []))
    (hlit b [])
  have heval := (hbitwise hbitwiseC).2 env .rfl henv op f hop a b
  exact h₂.trans henv trivial <| by simpa [hg] using heval

/-- A complete Boolean truth table is a reflection certificate. -/
theorem VEnv.ReflectsBoolBin.of_table {env : VEnv}
    (hop : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hff : env.IsDefEqU 0 []
      (.app (.app op .boolFalse) .boolFalse) (.boolLit (f false false)))
    (hft : env.IsDefEqU 0 []
      (.app (.app op .boolFalse) .boolTrue) (.boolLit (f false true)))
    (htf : env.IsDefEqU 0 []
      (.app (.app op .boolTrue) .boolFalse) (.boolLit (f true false)))
    (htt : env.IsDefEqU 0 []
      (.app (.app op .boolTrue) .boolTrue) (.boolLit (f true true))) :
    env.ReflectsBoolBin op f := by
  refine ⟨hop, fun a b => ?_⟩
  cases a <;> cases b <;> assumption

/-- The two left-fixed equations checked for `Nat.land` imply the complete
Boolean conjunction table. -/
theorem VEnv.ReflectsBoolBin.of_and_equations {env : VEnv} (henv : env.WF)
    (hboolT : ∀ b Γ, env.HasType 0 Γ (.boolLit b) .bool)
    (hop : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hf : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolFalse) (.bvar 0))
      (.lam .bool .boolFalse))
    (ht : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolTrue) (.bvar 0))
      (.lam .bool <| .bvar 0)) : env.ReflectsBoolBin op and := by
  have ⟨_, hBoolSort⟩ := (hboolT false []).isType henv trivial
  have hopClosed : op.ClosedN :=
    (hop.closedN' henv.ordered.closed trivial).2.1
  have hfalseL : env.HasType 0 [.bool]
      (.app (.app op .boolFalse) (.bvar 0)) .bool :=
    .app (.app (hop.weak0 henv) (hboolT false _)) (.bvar .zero)
  have htrueL : env.HasType 0 [.bool]
      (.app (.app op .boolTrue) (.bvar 0)) .bool :=
    .app (.app (hop.weak0 henv) (hboolT true _)) (.bvar .zero)
  have hfalse (b) := hf.lam_inst henv trivial hBoolSort hfalseL
    (hboolT false _) (hboolT b [])
  have htrue (b) := ht.lam_inst henv trivial hBoolSort htrueL
    (.bvar .zero) (hboolT b [])
  have hff := hfalse false
  have hft := hfalse true
  have htf := htrue false
  have htt := htrue true
  simp [VExpr.inst, hopClosed.instN_eq] at hff hft htf htt
  exact .of_table hop hff hft htf htt

/-- The two left-fixed equations checked for `Nat.lor` imply the complete
Boolean disjunction table. -/
theorem VEnv.ReflectsBoolBin.of_or_equations {env : VEnv} (henv : env.WF)
    (hboolT : ∀ b Γ, env.HasType 0 Γ (.boolLit b) .bool)
    (hop : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hf : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolFalse) (.bvar 0))
      (.lam .bool <| .bvar 0))
    (ht : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolTrue) (.bvar 0))
      (.lam .bool .boolTrue)) : env.ReflectsBoolBin op or := by
  have ⟨_, hBoolSort⟩ := (hboolT false []).isType henv trivial
  have hopClosed : op.ClosedN :=
    (hop.closedN' henv.ordered.closed trivial).2.1
  have hfalseL : env.HasType 0 [.bool]
      (.app (.app op .boolFalse) (.bvar 0)) .bool :=
    .app (.app (hop.weak0 henv) (hboolT false _)) (.bvar .zero)
  have htrueL : env.HasType 0 [.bool]
      (.app (.app op .boolTrue) (.bvar 0)) .bool :=
    .app (.app (hop.weak0 henv) (hboolT true _)) (.bvar .zero)
  have hfalse (b) := hf.lam_inst henv trivial hBoolSort hfalseL
    (.bvar .zero) (hboolT b [])
  have htrue (b) := ht.lam_inst henv trivial hBoolSort htrueL
    (hboolT true _) (hboolT b [])
  have hff := hfalse false
  have hft := hfalse true
  have htf := htrue false
  have htt := htrue true
  simp [VExpr.inst, hopClosed.instN_eq] at hff hft htf htt
  exact .of_table hop hff hft htf htt

/-- Common bookkeeping for adding a reflected primitive definition whose
name is not one of the syntactically stored type or constructor fields. -/
theorem VEnv.HasPrimitives.addPrimitiveDefEq {env env' : VEnv}
    (h : env.HasPrimitives) (hadd : env.addConst n ci = some env')
    (hneBool : n ≠ ``Bool) (hneFalse : n ≠ ``Bool.false)
    (hneTrue : n ≠ ``Bool.true) (hneNat : n ≠ ``Nat)
    (hneZero : n ≠ ``Nat.zero) (hneSucc : n ≠ ``Nat.succ)
    (hneChar : n ≠ ``Char.ofNat) (hneString : n ≠ ``String.ofList)
    (natPred : (env'.addDefEq df).ReflectsNatNat ``Nat.pred Nat.pred)
    (natAdd : (env'.addDefEq df).ReflectsNatNatNat ``Nat.add Nat.add)
    (natSub : (env'.addDefEq df).ReflectsNatNatNat ``Nat.sub Nat.sub)
    (natMul : (env'.addDefEq df).ReflectsNatNatNat ``Nat.mul Nat.mul)
    (natPow : (env'.addDefEq df).ReflectsNatNatNat ``Nat.pow Nat.pow)
    (natGcd : (env'.addDefEq df).ReflectsNatNatNat ``Nat.gcd Nat.gcd)
    (natMod : (env'.addDefEq df).ReflectsNatNatNat ``Nat.mod Nat.mod)
    (natDiv : (env'.addDefEq df).ReflectsNatNatNat ``Nat.div Nat.div)
    (natBEq : (env'.addDefEq df).ReflectsNatNatBool ``Nat.beq Nat.beq)
    (natBLE : (env'.addDefEq df).ReflectsNatNatBool ``Nat.ble Nat.ble)
    (natBitwise : (env'.addDefEq df).ReflectsNatBitwise ``Nat.bitwise)
    (natLAnd : (env'.addDefEq df).ReflectsNatNatNat ``Nat.land Nat.land)
    (natLOr : (env'.addDefEq df).ReflectsNatNatNat ``Nat.lor Nat.lor)
    (natXor : (env'.addDefEq df).ReflectsNatNatNat ``Nat.xor Nat.xor)
    (natShiftLeft : (env'.addDefEq df).ReflectsNatNatNat
      ``Nat.shiftLeft Nat.shiftLeft)
    (natShiftRight : (env'.addDefEq df).ReflectsNatNatNat
      ``Nat.shiftRight Nat.shiftRight) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : n ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : n ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains hneBool H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolType := fun H => h.boolType (by rwa [same ``Bool hneBool] at H)
    boolFalse := fun H => h.boolFalse (by
      rwa [same ``Bool.false hneFalse] at H)
    boolTrue := fun H => h.boolTrue (by
      rwa [same ``Bool.true hneTrue] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains hneNat H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      rwa [same ``Nat.zero hneZero] at H)
    natSucc := fun H => h.natSucc (by
      rwa [same ``Nat.succ hneSucc] at H)
    natPred := natPred
    natAdd := natAdd
    natSub := natSub
    natMul := natMul
    natPow := natPow
    natGcd := natGcd
    natMod := natMod
    natDiv := natDiv
    natBEq := natBEq
    natBLE := natBLE
    natBitwise := natBitwise
    natLAnd := natLAnd
    natLOr := natLOr
    natXor := natXor
    natShiftLeft := natShiftLeft
    natShiftRight := natShiftRight
    charOfNat := fun H => by
      obtain ⟨hu, hty⟩ := h.charOfNat (by
        rwa [same ``Char.ofNat hneChar] at H)
      exact ⟨hu, fun U Γ => (hty U Γ).mono le⟩
    stringOfList := fun H => by
      obtain ⟨hu, hty, hnil, hcons⟩ := h.stringOfList (by
        rwa [same ``String.ofList hneString] at H)
      exact ⟨hu, fun U Γ => (hty U Γ).mono le,
        hnil.mono le, hcons.mono le⟩ }

/-- Install a checked `Nat.xor` specialization and its literal reflection. -/
theorem VEnv.HasPrimitives.addNatXorDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives)
    (hnat : env.contains ``Nat) (hbitwiseC : env.contains ``Nat.bitwise)
    (hname : v.name = ``Nat.xor)
    (hadd : env.addConst ``Nat.xor v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF) (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hvalue : v.value = .app (.const ``Nat.bitwise []) op)
    (hopTy : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hff : env.IsDefEqU 0 []
      (.app (.app op .boolFalse) .boolFalse) .boolFalse)
    (htf : env.IsDefEqU 0 []
      (.app (.app op .boolTrue) .boolFalse) .boolTrue)
    (hft : env.IsDefEqU 0 []
      (.app (.app op .boolFalse) .boolTrue) .boolTrue)
    (htt : env.IsDefEqU 0 []
      (.app (.app op .boolTrue) .boolTrue) .boolFalse) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  refine h.natDefKit hnat hname hadd hwf hu hty ?_
  intro le hf hcf hzero hsucc
  rw [hvalue] at hcf
  have hbitwise' :=
    (h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hbitwiseC' : (env'.addDefEq v.toDefEq).contains ``Nat.bitwise := by
    obtain ⟨ci, hci⟩ := hbitwiseC
    exact ⟨ci, le.constants hci⟩
  have hop : env.ReflectsBoolBin op bne :=
    VEnv.ReflectsBoolBin.of_table hopTy hff hft htf htt
  have href := VEnv.ReflectsNatNatNat.of_bitwise_specialization hwf hzero hsucc
    hbitwise' hbitwiseC' hf hcf (hop.mono le) (g := Nat.xor) rfl
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    hbitwise'
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

/-- Install a checked `Nat.land` specialization and its literal reflection. -/
theorem VEnv.HasPrimitives.addNatLandDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF)
    (hnat : env.contains ``Nat) (hbool : env.contains ``Bool)
    (hbitwiseC : env.contains ``Nat.bitwise)
    (hname : v.name = ``Nat.land)
    (hadd : env.addConst ``Nat.land v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF) (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hvalue : v.value = .app (.const ``Nat.bitwise []) op)
    (hopTy : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hf : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolFalse) (.bvar 0))
      (.lam .bool .boolFalse))
    (ht : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolTrue) (.bvar 0))
      (.lam .bool <| .bvar 0)) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  refine h.natDefKit hnat hname hadd hwf hu hty ?_
  intro le hfun hcf hzero hsucc
  rw [hvalue] at hcf
  have hboolT (b) (Γ) : env.HasType 0 Γ (.boolLit b) .bool :=
    (TrExprS.boolLit (Us := []) (Δ := []) h hbool b).2.weak0 henv
  have hop := VEnv.ReflectsBoolBin.of_and_equations henv hboolT hopTy hf ht
  have hbitwise' :=
    (h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hbitwiseC' : (env'.addDefEq v.toDefEq).contains ``Nat.bitwise := by
    obtain ⟨ci, hci⟩ := hbitwiseC
    exact ⟨ci, le.constants hci⟩
  have href := VEnv.ReflectsNatNatNat.of_bitwise_specialization hwf hzero hsucc
    hbitwise' hbitwiseC' hfun hcf (hop.mono le) (g := Nat.land) rfl
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    hbitwise' href
    ((h.natLOr.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

/-- Install a checked `Nat.lor` specialization and its literal reflection. -/
theorem VEnv.HasPrimitives.addNatLorDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF)
    (hnat : env.contains ``Nat) (hbool : env.contains ``Bool)
    (hbitwiseC : env.contains ``Nat.bitwise)
    (hname : v.name = ``Nat.lor)
    (hadd : env.addConst ``Nat.lor v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF) (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hvalue : v.value = .app (.const ``Nat.bitwise []) op)
    (hopTy : env.HasType 0 [] op (.forallE .bool <| .forallE .bool .bool))
    (hf : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolFalse) (.bvar 0))
      (.lam .bool <| .bvar 0))
    (ht : env.IsDefEqU 0 []
      (.lam .bool <| .app (.app op .boolTrue) (.bvar 0))
      (.lam .bool .boolTrue)) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  refine h.natDefKit hnat hname hadd hwf hu hty ?_
  intro le hfun hcf hzero hsucc
  rw [hvalue] at hcf
  have hboolT (b) (Γ) : env.HasType 0 Γ (.boolLit b) .bool :=
    (TrExprS.boolLit (Us := []) (Δ := []) h hbool b).2.weak0 henv
  have hop := VEnv.ReflectsBoolBin.of_or_equations henv hboolT hopTy hf ht
  have hbitwise' :=
    (h.natBitwise.addConst hadd (by decide)).addDefEq (df := v.toDefEq)
  have hbitwiseC' : (env'.addDefEq v.toDefEq).contains ``Nat.bitwise := by
    obtain ⟨ci, hci⟩ := hbitwiseC
    exact ⟨ci, le.constants hci⟩
  have href := VEnv.ReflectsNatNatNat.of_bitwise_specialization hwf hzero hsucc
    hbitwise' hbitwiseC' hfun hcf (hop.mono le) (g := Nat.lor) rfl
  exact h.addPrimitiveDefEq hadd (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ((h.natPred.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natAdd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natSub.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMul.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natPow.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natGcd.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natMod.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natDiv.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBEq.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natBLE.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    hbitwise'
    ((h.natLAnd.addConst hadd (by decide)).addDefEq (df := v.toDefEq)) href
    ((h.natXor.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftLeft.addConst hadd (by decide)).addDefEq (df := v.toDefEq))
    ((h.natShiftRight.addConst hadd (by decide)).addDefEq (df := v.toDefEq))

end Lean4Lean
