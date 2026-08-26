/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Primitive

/-!
# Shared reflected-condition support

This module isolates the generic proof utilities and semantic data retained by
checked Boolean selectors. It is the common dependency for the Nat.mod/div
condition track and the later bitwise track; it does not certify either
primitive family on its own.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel TypeChecker

theorem VEnv.IsDefEqU.app_both (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.IsDefEqU U Γ f g)
    (ha : env.IsDefEqU U Γ a b)
    (hft : env.HasType U Γ f (.forallE A B))
    (hat : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (.app f a) (.app g b) :=
  ⟨_, .appDF (hf.of_l henv hΓ hft) (ha.of_l henv hΓ hat)⟩


theorem VEnv.IsDefEqU.lam_instU (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqU U Γ (.lam A e₁) (.lam A e₂))
    (hA : env.HasType U Γ A (.sort u))
    (h₁ : env.HasType U (A :: Γ) e₁ B₁)
    (h₂ : env.HasType U (A :: Γ) e₂ B₂)
    (ha : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (e₁.inst a) (e₂.inst a) := by
  have happ := h.app_same henv hΓ (.lam hA h₁) ha
  have hbeta₁ : env.IsDefEqU U Γ (.app (.lam A e₁) a) (e₁.inst a) :=
    ⟨_, .beta h₁ ha⟩
  have hbeta₂ : env.IsDefEqU U Γ (.app (.lam A e₂) a) (e₂.inst a) :=
    ⟨_, .beta h₂ ha⟩
  exact hbeta₁.symm.trans henv hΓ happ |>.trans henv hΓ hbeta₂

theorem VEnv.IsDefEqU.lam_instU₂ (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqU U Γ (.lam A₁ e₁) (.lam A₂ e₂))
    (hA₁ : env.HasType U Γ A₁ (.sort u₁))
    (hbody₁ : env.HasType U (A₁ :: Γ) e₁ B₁)
    (hbody₂ : env.HasType U (A₂ :: Γ) e₂ B₂)
    (hA : env.IsDefEqU U Γ A₁ A₂)
    (ha : env.HasType U Γ a A₁) :
    env.IsDefEqU U Γ (e₁.inst a) (e₂.inst a) := by
  have happ := h.app_same henv hΓ (.lam hA₁ hbody₁) ha
  have ha₂ := ha.defeqU_r henv hΓ hA
  have hbeta₁ : env.IsDefEqU U Γ (.app (.lam A₁ e₁) a) (e₁.inst a) :=
    ⟨_, .beta hbody₁ ha⟩
  have hbeta₂ : env.IsDefEqU U Γ (.app (.lam A₂ e₂) a) (e₂.inst a) :=
    ⟨_, .beta hbody₂ ha₂⟩
  exact hbeta₁.symm.trans henv hΓ happ |>.trans henv hΓ hbeta₂

/-- Instantiate definitionally equal lambdas when the same argument is known
to inhabit both (possibly only definitionally equal) binder domains. -/
theorem VEnv.IsDefEqU.lam_instU_hetero (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqU U Γ (.lam A₁ e₁) (.lam A₂ e₂))
    (hA₁ : env.HasType U Γ A₁ (.sort u₁))
    (hbody₁ : env.HasType U (A₁ :: Γ) e₁ B₁)
    (hbody₂ : env.HasType U (A₂ :: Γ) e₂ B₂)
    (ha₁ : env.HasType U Γ a A₁)
    (ha₂ : env.HasType U Γ a A₂) :
    env.IsDefEqU U Γ (e₁.inst a) (e₂.inst a) := by
  have happ := h.app_same henv hΓ (.lam hA₁ hbody₁) ha₁
  have hbeta₁ : env.IsDefEqU U Γ (.app (.lam A₁ e₁) a) (e₁.inst a) :=
    ⟨_, .beta hbody₁ ha₁⟩
  have hbeta₂ : env.IsDefEqU U Γ (.app (.lam A₂ e₂) a) (e₂.inst a) :=
    ⟨_, .beta hbody₂ ha₂⟩
  exact hbeta₁.symm.trans henv hΓ happ |>.trans henv hΓ hbeta₂

namespace Environment

/-- The natural-number constructor fragment of `HasPrimitives` shared by
reflected-condition and recursive-primitive semantics. -/
structure VEnv.HasNatConstructors (env : VEnv) : Prop where
  nat : env.contains ``Nat
  natZero : env.constants ``Nat.zero =
    some { uvars := 0, type := .nat }
  natSucc : env.constants ``Nat.succ =
    some { uvars := 0, type := .forallE .nat .nat }

/-- The Nat/Bool constructor fragment needed by reflected-condition
certificates and their later arithmetic consumers. -/
structure VEnv.HasNatBoolConstructors (env : VEnv) : Prop
    extends VEnv.HasNatConstructors env where
  bool : env.contains ``Bool
  boolFalse : env.constants ``Bool.false =
    some { uvars := 0, type := .bool }
  boolTrue : env.constants ``Bool.true =
    some { uvars := 0, type := .bool }

theorem VEnv.HasNatConstructors.of_primitives {env : VEnv}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat) :
    VEnv.HasNatConstructors env := by
  obtain ⟨hzero, hsucc⟩ := h.nat hnat
  rcases hzero with ⟨zeroCi, hzeroCi⟩
  rcases hsucc with ⟨succCi, hsuccCi⟩
  exact {
    nat := hnat
    natZero := by simpa [h.natZero hzeroCi] using hzeroCi
    natSucc := by simpa [h.natSucc hsuccCi] using hsuccCi }

theorem VEnv.HasNatConstructors.mono {env env' : VEnv}
    (h : VEnv.HasNatConstructors env) (le : env ≤ env') :
    VEnv.HasNatConstructors env' where
  nat := let ⟨ci, hci⟩ := h.nat; ⟨ci, le.constants hci⟩
  natZero := le.constants h.natZero
  natSucc := le.constants h.natSucc

theorem VEnv.HasNatBoolConstructors.of_primitives {env : VEnv}
    (h : env.HasPrimitives) (hbool : env.contains ``Bool)
    (hnat : env.contains ``Nat) : VEnv.HasNatBoolConstructors env := by
  obtain ⟨hfalse, htrue⟩ := h.bool hbool
  rcases hfalse with ⟨falseCi, hfalseCi⟩
  rcases htrue with ⟨trueCi, htrueCi⟩
  exact {
    bool := hbool
    boolFalse := by simpa [h.boolFalse hfalseCi] using hfalseCi
    boolTrue := by simpa [h.boolTrue htrueCi] using htrueCi
    toHasNatConstructors := VEnv.HasNatConstructors.of_primitives h hnat }

theorem VEnv.HasNatBoolConstructors.mono {env env' : VEnv}
    (h : VEnv.HasNatBoolConstructors env) (le : env ≤ env') :
    VEnv.HasNatBoolConstructors env' where
  bool := let ⟨ci, hci⟩ := h.bool; ⟨ci, le.constants hci⟩
  boolFalse := le.constants h.boolFalse
  boolTrue := le.constants h.boolTrue
  toHasNatConstructors := h.toHasNatConstructors.mono le

theorem VEnv.HasNatBoolConstructors.boolFalseS
    (h : VEnv.HasNatBoolConstructors env) :
    TrExprS env Us Δ (toExpr false) .boolFalse ∧
      env.HasType Us.length Δ.toCtx .boolFalse .bool :=
  ⟨.const h.boolFalse rfl rfl, .const h.boolFalse nofun rfl⟩

theorem VEnv.HasNatBoolConstructors.boolTrueS
    (h : VEnv.HasNatBoolConstructors env) :
    TrExprS env Us Δ (toExpr true) .boolTrue ∧
      env.HasType Us.length Δ.toCtx .boolTrue .bool :=
  ⟨.const h.boolTrue rfl rfl, .const h.boolTrue nofun rfl⟩

theorem VEnv.HasNatBoolConstructors.boolLitS
    (h : VEnv.HasNatBoolConstructors env) (b : Bool) :
    TrExprS env Us Δ (toExpr b) (.boolLit b) ∧
      env.HasType Us.length Δ.toCtx (.boolLit b) .bool := by
  cases b <;> first | exact h.boolFalseS | exact h.boolTrueS

theorem VEnv.HasNatConstructors.natZeroS
    (h : VEnv.HasNatConstructors env) :
    TrExprS env Us Δ .natZero .natZero ∧
      env.HasType Us.length Δ.toCtx .natZero .nat :=
  ⟨.const h.natZero rfl rfl, .const h.natZero nofun rfl⟩

theorem VEnv.HasNatConstructors.natSuccS
    (h : VEnv.HasNatConstructors env) :
    TrExprS env Us Δ .natSucc .natSucc ∧
      env.HasType Us.length Δ.toCtx .natSucc (.forallE .nat .nat) :=
  ⟨.const h.natSucc rfl rfl, .const h.natSucc nofun rfl⟩

theorem VEnv.HasNatConstructors.natLitS
    (h : VEnv.HasNatConstructors env) (n : Nat) :
    TrExprS env Us Δ (.lit (.natVal n)) (.natLit n) ∧
      env.HasType Us.length Δ.toCtx (.natLit n) .nat := by
  induction n with
  | zero => exact ⟨.lit h.nat h.natZeroS.1, h.natZeroS.2⟩
  | succ n ih =>
    exact ⟨.lit h.nat (.app h.natSuccS.2 ih.2 h.natSuccS.1 ih.1),
      .app h.natSuccS.2 ih.2⟩

theorem VEnv.HasNatBoolConstructors.natZeroS
    (h : VEnv.HasNatBoolConstructors env) :
    TrExprS env Us Δ .natZero .natZero ∧
      env.HasType Us.length Δ.toCtx .natZero .nat :=
  h.toHasNatConstructors.natZeroS

theorem VEnv.HasNatBoolConstructors.natSuccS
    (h : VEnv.HasNatBoolConstructors env) :
    TrExprS env Us Δ .natSucc .natSucc ∧
      env.HasType Us.length Δ.toCtx .natSucc (.forallE .nat .nat) :=
  h.toHasNatConstructors.natSuccS

theorem VEnv.HasNatBoolConstructors.natLitS
    (h : VEnv.HasNatBoolConstructors env) (n : Nat) :
    TrExprS env Us Δ (.lit (.natVal n)) (.natLit n) ∧
      env.HasType Us.length Δ.toCtx (.natLit n) .nat :=
  h.toHasNatConstructors.natLitS n


def VEnv.ReflectionITEChecked (env : VEnv) (r : Reflection) : Prop :=
  ∃ trueL trueR falseL falseR,
    TrExprS env [] []
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        mkApp3 r.ite (.bvar 1) q(true) (.bvar 0)) trueL ∧
    TrExprS env [] []
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(true)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 1) trueR ∧
    env.IsDefEqU 0 [] trueL trueR ∧
    TrExprS env [] []
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        mkApp3 r.ite (.bvar 1) q(false) (.bvar 0)) falseL ∧
    TrExprS env [] []
      (.lam0 q(Prop) <| .lam0 (mkApp2 r.type (.bvar 0) q(false)) <|
        .lam0 q(Type) <| .lam0 (.bvar 0) <| .lam0 (.bvar 1) <| .bvar 0) falseR ∧
    env.IsDefEqU 0 [] falseL falseR

theorem VEnv.ReflectionITEChecked.mono {env env' : VEnv} (hle : env ≤ env')
    (h : VEnv.ReflectionITEChecked env r) : VEnv.ReflectionITEChecked env' r := by
  rcases h with ⟨tl, tr, fl, fr, htl, htr, hteq, hfl, hfr, hfeq⟩
  exact ⟨tl, tr, fl, fr, htl.mono hle, htr.mono hle, hteq.mono hle,
    hfl.mono hle, hfr.mono hle, hfeq.mono hle⟩


def VEnv.ReflectionNatDITEChecked (env : VEnv) (r : Reflection) : Prop :=
  ∃ trueL trueR falseL falseR,
    TrExprS env [] []
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp5 r.natDITE (.bvar 3) q(true) (.bvar 0) (.bvar 2) (.bvar 1)) trueL ∧
    TrExprS env [] []
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(true)) <|
       mkApp (.bvar 2) (mkApp2 r.ofTrue (.bvar 3) (.bvar 0))) trueR ∧
    env.IsDefEqU 0 [] trueL trueR ∧
    TrExprS env [] []
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp5 r.natDITE (.bvar 3) q(false) (.bvar 0) (.bvar 2) (.bvar 1)) falseL ∧
    TrExprS env [] []
      (.lam0 q(Prop) <|
       .lam0 (.arrow (.bvar 0) q(Nat)) <|
       .lam0 (.arrow (mkApp q(Not) (.bvar 1)) q(Nat)) <|
       .lam0 (mkApp2 r.type (.bvar 2) q(false)) <|
       mkApp (.bvar 1) (mkApp2 r.ofFalse (.bvar 3) (.bvar 0))) falseR ∧
    env.IsDefEqU 0 [] falseL falseR

theorem VEnv.ReflectionNatDITEChecked.mono {env env' : VEnv}
    (hle : env ≤ env') (h : VEnv.ReflectionNatDITEChecked env r) :
    VEnv.ReflectionNatDITEChecked env' r := by
  rcases h with ⟨tl, tr, fl, fr, htl, htr, hteq, hfl, hfr, hfeq⟩
  exact ⟨tl, tr, fl, fr, htl.mono hle, htr.mono hle, hteq.mono hle,
    hfl.mono hle, hfr.mono hle, hfeq.mono hle⟩


end Environment
end Lean4Lean
