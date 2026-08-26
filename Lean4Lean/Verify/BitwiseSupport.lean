/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.NatWellFoundedChecker

namespace Lean4Lean.Environment
open Lean

def _root_.Lean4Lean.VEnv.ReflectsBoolNatITE (env : VEnv) (ite : VExpr) :=
  env.HasType 0 [] ite
    (.forallE .bool <| .forallE .nat <| .forallE .nat .nat) ∧
  ∀ b x y, env.IsDefEqU 0 []
    (.app (.app (.app ite (.boolLit b)) (.natLit x)) (.natLit y))
    (.natLit (if b then x else y))

theorem _root_.Lean4Lean.VEnv.ReflectsBoolNatITE.of_equations
    {env : VEnv} {ite : VExpr}
    (henv : env.WF)
    (hboolT : ∀ b, env.HasType 0 [] (.boolLit b) .bool)
    (hnatTy₀ : env.IsType 0 [] .nat)
    (hnatTy₁ : env.IsType 0 [.nat] .nat)
    (hnatT : ∀ n Γ, env.HasType 0 Γ (.natLit n) .nat)
    (hite : env.HasType 0 [] ite
      (.forallE .bool <| .forallE .nat <| .forallE .nat .nat))
    (htrue : env.IsDefEqU 0 [] (.app ite .boolTrue)
      (.lam .nat <| .lam .nat <| .bvar 1))
    (hfalse : env.IsDefEqU 0 [] (.app ite .boolFalse)
      (.lam .nat <| .lam .nat <| .bvar 0)) :
    env.ReflectsBoolNatITE ite := by
  refine ⟨hite, fun b x y => ?_⟩
  have app_same {f g a A B}
      (hf : env.IsDefEqU 0 [] f g)
      (hft : env.HasType 0 [] f (.forallE A B))
      (ha : env.HasType 0 [] a A) :
      env.IsDefEqU 0 [] (.app f a) (.app g a) :=
    ⟨_, .appDF (hf.of_l henv trivial hft) ha⟩
  have hnatClosed : VExpr.nat.ClosedN := by
    exact ((hnatT 0 []).closedN' henv.ordered.closed trivial).2.2
  have hnatLitClosed (n) : (VExpr.natLit n).ClosedN := by
    exact ((hnatT n []).closedN' henv.ordered.closed trivial).1
  have hiteB : env.HasType 0 [] (.app ite (.boolLit b))
      (.forallE .nat <| .forallE .nat .nat) := .app hite (hboolT b)
  have hiteBX : env.HasType 0 [] (.app (.app ite (.boolLit b)) (.natLit x))
      (.forallE .nat .nat) := .app hiteB (hnatT x [])
  have hbranch : env.IsDefEqU 0 [] (ite.app (.boolLit b))
      (if b then (.lam .nat <| .lam .nat <| .bvar 1)
        else (.lam .nat <| .lam .nat <| .bvar 0)) := by
    cases b with
    | false => simpa [VExpr.boolLit] using hfalse
    | true => simpa [VExpr.boolLit] using htrue
  have happ₁ := app_same hbranch hiteB (hnatT x [])
  have happ₂ := app_same happ₁ hiteBX (hnatT y [])
  cases b with
  | false =>
    have hinner : env.HasType 0 [.nat] (.lam .nat <| .bvar 0)
        (.forallE .nat .nat) := by
      let ⟨_, hnatSort⟩ := hnatTy₁
      exact .lam hnatSort (.bvar .zero)
    have houter : env.HasType 0 [] (.lam .nat <| .lam .nat <| .bvar 0)
        (.forallE .nat <| .forallE .nat .nat) := by
      let ⟨_, hnatSort⟩ := hnatTy₀
      exact .lam hnatSort hinner
    have houterApp : env.HasType 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 0) (.natLit x))
        (.forallE .nat .nat) := .app houter (hnatT x [])
    have hbeta₁ : env.IsDefEqU 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 0) (.natLit x))
        (.lam .nat <| .bvar 0) :=
      ⟨_, VEnv.IsDefEq.beta hinner (hnatT x [])⟩
    have hbeta₂ : env.IsDefEqU 0 []
        (.app (.lam .nat <| .bvar 0) (.natLit y)) (.natLit y) :=
      by simpa [VExpr.inst] using
        (show env.IsDefEqU 0 []
          (.app (.lam .nat <| .bvar 0) (.natLit y))
          ((VExpr.bvar 0).inst (.natLit y)) from
            ⟨_, VEnv.IsDefEq.beta (.bvar (.zero)) (hnatT y [])⟩)
    have hbeta₁App := app_same hbeta₁ houterApp (hnatT y [])
    exact happ₂.trans henv trivial (hbeta₁App.trans henv trivial hbeta₂)
  | true =>
    have hinner : env.HasType 0 [.nat] (.lam .nat <| .bvar 1)
        (.forallE .nat .nat) := by
      let ⟨_, hnatSort⟩ := hnatTy₁
      exact .lam hnatSort (.bvar (.succ .zero))
    have houter : env.HasType 0 [] (.lam .nat <| .lam .nat <| .bvar 1)
        (.forallE .nat <| .forallE .nat .nat) := by
      let ⟨_, hnatSort⟩ := hnatTy₀
      exact .lam hnatSort hinner
    have houterApp : env.HasType 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit x))
        (.forallE .nat .nat) := .app houter (hnatT x [])
    have hbeta₁ : env.IsDefEqU 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit x))
        (.lam .nat <| .natLit x) := by
      simpa [VExpr.inst, VExpr.inst_lift,
        hnatClosed.instN_eq, (hnatLitClosed x).lift_eq,
        (hnatLitClosed x).instN_eq] using (show env.IsDefEqU 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit x))
        ((VExpr.lam .nat <| .bvar 1).inst (.natLit x)) from
          ⟨_, VEnv.IsDefEq.beta hinner (hnatT x [])⟩)
    have hbody : env.HasType 0 [.nat] (.natLit x) .nat := hnatT x [.nat]
    have hbeta₂ : env.IsDefEqU 0 []
        (.app (.lam .nat <| .natLit x) (.natLit y)) (.natLit x) :=
      by simpa [VExpr.inst, hnatClosed.instN_eq,
          (hnatLitClosed x).instN_eq] using
        (show env.IsDefEqU 0 []
          (.app (.lam .nat <| .natLit x) (.natLit y))
          ((VExpr.natLit x).inst (.natLit y)) from
            ⟨_, VEnv.IsDefEq.beta hbody (hnatT y [])⟩)
    have hbeta₁App := app_same hbeta₁ houterApp (hnatT y [])
    exact happ₂.trans henv trivial (hbeta₁App.trans henv trivial hbeta₂)

/-- Semantic relation represented by the translated recursive calls retained
in a bitwise fixpoint certificate. -/
def _root_.Lean4Lean.VEnv.BitwiseGoCall (env : VEnv)
    (r : NatBitwiseFixCertificate) (op : VExpr)
    (fuel a b : Nat) (e : VExpr) : Prop :=
  ∃ callV fuelV hpV,
    TrExprS env [] [] r.callFn callV ∧
    env.IsDefEqU 0 [] fuelV (.natLit fuel) ∧
    env.IsDefEqU 0 [] e
      (.app (.app (.app (.app (.app callV op) fuelV)
        (.natLit a)) (.natLit b)) hpV)

theorem _root_.Lean4Lean.VEnv.BitwiseGoCall.mono {env env' : VEnv}
    (h : VEnv.BitwiseGoCall env r op fuel a b e) (le : env ≤ env') :
    VEnv.BitwiseGoCall env' r op fuel a b e := by
  rcases h with ⟨callV, fuelV, hpV, hcall, hfuel, he⟩
  exact ⟨callV, fuelV, hpV, hcall.mono le, hfuel.mono le, he.mono le⟩

/-- Fuel adequacy for the relational presentation of the compiled
`Nat.bitwise` fixpoint. -/
theorem _root_.Lean4Lean.VEnv.evalNatBitwise_of_fix_relation
    (henv : VEnv.WF env)
    (G : Nat → Nat → Nat → VExpr → Prop)
    (htop : ∀ a b, ∃ e, G (a + 1) a b e ∧ env.IsDefEqU 0 []
      (.app (.app (.app g op) (.natLit a)) (.natLit b)) e)
    (hgo : ∀ fuel a b e, G (fuel + 1) a b e →
      env.IsDefEqU 0 [] e e →
      if a = 0 then
        env.IsDefEqU 0 [] e (.natLit (if f false true then b else 0))
      else if b = 0 then
        env.IsDefEqU 0 [] e (.natLit (if f true false then a else 0))
      else ∃ e', G fuel (a / 2) (b / 2) e' ∧
        env.IsDefEqU 0 [] e' e' ∧
        ∀ q, env.IsDefEqU 0 [] e' (.natLit q) →
          env.IsDefEqU 0 [] e
            (.natLit (if f (a % 2 = 1) (b % 2 = 1)
              then q + q + 1 else q + q))) :
    ∀ a b, env.IsDefEqU 0 []
      (.app (.app (.app g op) (.natLit a)) (.natLit b))
      (.natLit (Nat.bitwise f a b)) := by
  have goEval : ∀ fuel a b e, G fuel a b e →
      env.IsDefEqU 0 [] e e → a < fuel →
      env.IsDefEqU 0 [] e (.natLit (Nat.bitwise f a b)) := by
    intro fuel a b e hG hWT hlt
    refine VEnv.natLit_defeq_of_fuel_relation henv
      (G := fun fuel p e => G fuel p.1 p.2 e)
      (WT := fun e => env.IsDefEqU 0 [] e e)
      (fun p => p.1) (fun p => Nat.bitwise f p.1 p.2)
      (fun p => match p with
        | (0, b) => .done (if f false true then b else 0)
        | (a + 1, 0) => .done (if f true false then a + 1 else 0)
        | (a + 1, b + 1) => .recur ((a + 1) / 2, (b + 1) / 2)
            (fun q => if f ((a + 1) % 2 = 1) ((b + 1) % 2 = 1)
              then q + q + 1 else q + q))
      ?_ ?_ ?_ fuel (a, b) e hG hWT hlt
    · rintro ⟨a, b⟩
      cases a with
      | zero => rw [Nat.bitwise]; simp [FuelStep.out]
      | succ a =>
        cases b with
        | zero => rw [Nat.bitwise]; simp [FuelStep.out]
        | succ b =>
          show Nat.bitwise f (a + 1) (b + 1) = _
          rw [Nat.bitwise]
          simp [FuelStep.out]
    · rintro ⟨a, b⟩ next post hs
      cases a with
      | zero => cases hs
      | succ a =>
        cases b with
        | zero => cases hs
        | succ b =>
          cases hs
          exact Nat.bitwise_rec_lemma (Nat.succ_ne_zero a)
    · rintro fuel ⟨a, b⟩ e hG hWT
      cases a with
      | zero => simpa using hgo fuel 0 b e hG hWT
      | succ a =>
        cases b with
        | zero => simpa using hgo fuel (a + 1) 0 e hG hWT
        | succ b =>
          obtain ⟨e', hG', he'Ty, hfinish⟩ := by
            simpa using hgo fuel (a + 1) (b + 1) e hG hWT
          exact ⟨e', hG', he'Ty, hfinish⟩
  intro a b
  obtain ⟨e, hG, ht⟩ := htop a b
  exact ht.trans henv trivial <| goEval (a + 1) a b e hG
    (ht.symm.trans henv trivial ht) (by omega)

theorem _root_.Lean4Lean.TrExprS.boolBinaryType_of_contains
    {env : VEnv} (wf : env.WF) (h : env.HasPrimitives)
    (hbool : env.contains ``Bool) (Us : List Name) (Δ : VLCtx) :
    TrExprS env Us Δ q(Bool → Bool → Bool)
      (.forallE .bool <| .forallE .bool .bool) := by
  let Δ1 : VLCtx := (none, .vlam .bool) :: Δ
  let Δ2 : VLCtx := (none, .vlam .bool) :: Δ1
  have hbool0 := TrExprS.boolType_of_contains wf h hbool Us Δ
  have hbool1 := TrExprS.boolType_of_contains wf h hbool Us Δ1
  have hbool2 := TrExprS.boolType_of_contains wf h hbool Us Δ2
  have hinnerS : TrExprS env Us Δ1 q(Bool → Bool)
      (.forallE .bool .bool) :=
    .forallE hbool1.2 hbool2.2 hbool1.1 hbool2.1
  have hinnerT : env.IsType Us.length Δ1.toCtx
      (.forallE .bool .bool) := by
    obtain ⟨u, hA⟩ := hbool1.2
    obtain ⟨w, hB⟩ := hbool2.2
    exact ⟨_, .forallEDF hA hB⟩
  exact .forallE hbool0.2 hinnerT hbool0.1 hinnerS

theorem _root_.Lean4Lean.VEnv.boolBinaryType_isType_of_contains
    {env : VEnv} (wf : env.WF) (h : env.HasPrimitives)
    (hbool : env.contains ``Bool) (Us : List Name) (Δ : VLCtx) :
    env.IsType Us.length Δ.toCtx
      (.forallE .bool <| .forallE .bool .bool) := by
  let Δ1 : VLCtx := (none, .vlam .bool) :: Δ
  let Δ2 : VLCtx := (none, .vlam .bool) :: Δ1
  have hbool0 := TrExprS.boolType_of_contains wf h hbool Us Δ
  have hbool1 := TrExprS.boolType_of_contains wf h hbool Us Δ1
  have hbool2 := TrExprS.boolType_of_contains wf h hbool Us Δ2
  have hinnerT : env.IsType Us.length Δ1.toCtx
      (.forallE .bool .bool) := by
    obtain ⟨u, hA⟩ := hbool1.2
    obtain ⟨w, hB⟩ := hbool2.2
    exact ⟨_, .forallEDF hA hB⟩
  obtain ⟨u, hA⟩ := hbool0.2
  obtain ⟨w, hB⟩ := hinnerT
  exact ⟨_, .forallEDF hA hB⟩

theorem _root_.Lean4Lean.TrExprS.natBinaryBoolType_of_contains
    {env : VEnv} (wf : env.WF) (h : env.HasPrimitives)
    (hnat : env.contains ``Nat) (hbool : env.contains ``Bool)
    (Us : List Name) (Δ : VLCtx) :
    TrExprS env Us Δ q(Nat → Nat → Bool)
      (.forallE .nat <| .forallE .nat .bool) := by
  let Δ1 : VLCtx := (none, .vlam .nat) :: Δ
  let Δ2 : VLCtx := (none, .vlam .nat) :: Δ1
  have hnat0 := TrExprS.natType_of_contains wf h hnat Us Δ
  have hnat1 := TrExprS.natType_of_contains wf h hnat Us Δ1
  have hnat2 := TrExprS.natType_of_contains wf h hnat Us Δ2
  have hbool2 := TrExprS.boolType_of_contains wf h hbool Us Δ2
  have hinnerS : TrExprS env Us Δ1 q(Nat → Bool)
      (.forallE .nat .bool) :=
    .forallE hnat1.2 hbool2.2 hnat1.1 hbool2.1
  have hinnerT : env.IsType Us.length Δ1.toCtx
      (.forallE .nat .bool) := by
    obtain ⟨u, hA⟩ := hnat1.2
    obtain ⟨w, hB⟩ := hbool2.2
    exact ⟨_, .forallEDF hA hB⟩
  exact .forallE hnat0.2 hinnerT hnat0.1 hinnerS

theorem _root_.Lean4Lean.TrExprS.boolNatBinaryType_of_contains
    {env : VEnv} (wf : env.WF) (h : env.HasPrimitives)
    (hbool : env.contains ``Bool) (hnat : env.contains ``Nat)
    (Us : List Name) (Δ : VLCtx) :
    TrExprS env Us Δ q(Bool → Nat → Nat → Nat)
      (.forallE .bool <| .forallE .nat <| .forallE .nat .nat) := by
  let Δ1 : VLCtx := (none, .vlam .bool) :: Δ
  let Δ2 : VLCtx := (none, .vlam .nat) :: Δ1
  let Δ3 : VLCtx := (none, .vlam .nat) :: Δ2
  have hbool0 := TrExprS.boolType_of_contains wf h hbool Us Δ
  have hnat1 := TrExprS.natType_of_contains wf h hnat Us Δ1
  have hnat2 := TrExprS.natType_of_contains wf h hnat Us Δ2
  have hnat3 := TrExprS.natType_of_contains wf h hnat Us Δ3
  have htailS : TrExprS env Us Δ2 q(Nat → Nat)
      (.forallE .nat .nat) :=
    .forallE hnat2.2 hnat3.2 hnat2.1 hnat3.1
  have htailT : env.IsType Us.length Δ2.toCtx
      (.forallE .nat .nat) := by
    obtain ⟨u, hA⟩ := hnat2.2
    obtain ⟨w, hB⟩ := hnat3.2
    exact ⟨_, .forallEDF hA hB⟩
  have hinnerS : TrExprS env Us Δ1 q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat) :=
    .forallE hnat1.2 htailT hnat1.1 htailS
  have hinnerT : env.IsType Us.length Δ1.toCtx
      (.forallE .nat <| .forallE .nat .nat) := by
    obtain ⟨u, hA⟩ := hnat1.2
    obtain ⟨w, hB⟩ := htailT
    exact ⟨_, .forallEDF hA hB⟩
  exact .forallE hbool0.2 hinnerT hbool0.1 hinnerS

theorem _root_.Lean4Lean.TrExprS.propBoolPropType_of_contains
    {env : VEnv} (wf : env.WF) (h : env.HasPrimitives)
    (hbool : env.contains ``Bool) (Us : List Name) (Δ : VLCtx) :
    TrExprS env Us Δ q(Prop → Bool → Prop)
      (.forallE (.sort .zero) <| .forallE .bool (.sort .zero)) := by
  let Δ1 : VLCtx := (none, .vlam (.sort .zero)) :: Δ
  let Δ2 : VLCtx := (none, .vlam .bool) :: Δ1
  have hprop0 : TrExprS env Us Δ q(Prop) (.sort .zero) := .sort rfl
  have hprop2 : TrExprS env Us Δ2 q(Prop) (.sort .zero) := .sort rfl
  have hpropTy0 : env.IsType Us.length Δ.toCtx (.sort .zero) :=
    ⟨.succ .zero, .sortDF trivial trivial rfl⟩
  have hpropTy2 : env.IsType Us.length Δ2.toCtx (.sort .zero) :=
    ⟨.succ .zero, .sortDF trivial trivial rfl⟩
  have hbool1 := TrExprS.boolType_of_contains wf h hbool Us Δ1
  have hinnerS : TrExprS env Us Δ1 q(Bool → Prop)
      (.forallE .bool (.sort .zero)) :=
    .forallE hbool1.2 hpropTy2 hbool1.1 hprop2
  have hinnerT : env.IsType Us.length Δ1.toCtx
      (.forallE .bool (.sort .zero)) := by
    obtain ⟨u, hA⟩ := hbool1.2
    obtain ⟨w, hB⟩ := hpropTy2
    exact ⟨_, .forallEDF hA hB⟩
  exact .forallE hpropTy0 hinnerT hprop0 hinnerS

theorem _root_.Lean4Lean.TrExprS.bitwiseType_of_contains
    {env : VEnv} (wf : env.WF) (h : env.HasPrimitives)
    (hbool : env.contains ``Bool) (hnat : env.contains ``Nat)
    (Us : List Name) (Δ : VLCtx) :
    TrExprS env Us Δ q((Bool → Bool → Bool) → Nat → Nat → Nat)
      (.forallE (.forallE .bool <| .forallE .bool .bool) <|
        .forallE .nat <| .forallE .nat .nat) := by
  let fTy : VExpr := .forallE .bool <| .forallE .bool .bool
  let Δf : VLCtx := (none, .vlam fTy) :: Δ
  have hfunS := TrExprS.boolBinaryType_of_contains wf h hbool Us Δ
  have hfunT := VEnv.boolBinaryType_isType_of_contains wf h hbool Us Δ
  let Δn1 : VLCtx := (none, .vlam .nat) :: Δf
  let Δn2 : VLCtx := (none, .vlam .nat) :: Δn1
  have hnat1 := TrExprS.natType_of_contains wf h hnat Us Δf
  have hnat2 := TrExprS.natType_of_contains wf h hnat Us Δn1
  have hnat3 := TrExprS.natType_of_contains wf h hnat Us Δn2
  have htailS : TrExprS env Us Δn1 q(Nat → Nat)
      (.forallE .nat .nat) :=
    .forallE hnat2.2 hnat3.2 hnat2.1 hnat3.1
  have htailT : env.IsType Us.length Δn1.toCtx
      (.forallE .nat .nat) := by
    obtain ⟨u, hA⟩ := hnat2.2
    obtain ⟨w, hB⟩ := hnat3.2
    exact ⟨_, .forallEDF hA hB⟩
  have hnatS : TrExprS env Us Δf q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat) :=
    .forallE hnat1.2 htailT hnat1.1 htailS
  have hnatT : env.IsType Us.length Δf.toCtx
      (.forallE .nat <| .forallE .nat .nat) := by
    obtain ⟨u, hA⟩ := hnat1.2
    obtain ⟨w, hB⟩ := htailT
    exact ⟨_, .forallEDF hA hB⟩
  exact .forallE hfunT hnatT hfunS hnatS

/-- Semantic interface exported by the checked `Condition.natEq`
implementation.  Keeping the function expression explicit lets certificate
translations be related to calls occurring below unrelated local binders. -/
def VEnv.ReflectsNatEqDecide (env : VEnv) (decide : VExpr) : Prop :=
  env.HasType 0 [] decide (.forallE .nat <| .forallE .nat .bool) ∧
  ∀ a b, env.IsDefEqU 0 []
    (.app (.app decide (.natLit a)) (.natLit b))
    (.boolLit (a == b))

theorem VEnv.ReflectsNatEqDecide.mono {env env' : VEnv} {decide : VExpr}
    (h : Lean4Lean.Environment.VEnv.ReflectsNatEqDecide env decide)
    (le : env ≤ env') :
    Lean4Lean.Environment.VEnv.ReflectsNatEqDecide env' decide :=
  ⟨h.1.mono le, fun a b => (h.2 a b).mono le⟩

/-- Relate a translated occurrence of `Condition.natEq.decide` to an
application of the translated closed decision function.  This is the bridge
between occurrences embedded under certificate binders and the closed
semantic interface above. -/
theorem Condition.natEqDecideFn.call_eq {env : VEnv} (wf : env.WF)
    {Δ : VLCtx} (hΔ : Δ.WF env 0)
    {x y : Expr} {x' y' out decide : VExpr}
    (hdecide : TrExprS env [] Δ Condition.natEqDecideFn decide)
    (hx : TrExprS env [] Δ x x') (hy : TrExprS env [] Δ y y')
    (hxT : env.HasType 0 Δ.toCtx x' .nat)
    (hyT : env.HasType 0 Δ.toCtx y' .nat)
    (hcall : TrExprS env [] Δ (Condition.natEq.decide #[x, y]) out) :
    env.IsDefEqU 0 Δ.toCtx out (.app (.app decide x') y') := by
  unfold Condition.natEqDecideFn at hdecide
  cases hdecide with
  | lam hnatTy₁ hnatS₁ hinnerS =>
    cases hinnerS with
    | lam hnatTy₂ hnatS₂ hbodyS =>
      rename_i natTy₁ natTy₂ body
      have hnatCanon (Δ' : VLCtx) : TrExprS env [] Δ' q(Nat) .nat := by
        obtain ⟨_, hnatCi, _, hnatLen⟩ :=
          (hxT.isType wf hΔ.toCtx).choose_spec.const_inv wf hΔ.toCtx
        exact .const hnatCi rfl (by simpa using hnatLen)
      have hctx : VLCtx.IsDefEq env 0 Δ Δ := .refl wf hΔ
      have hnatEq₁ := TrExprS.uniq (Us := []) wf hctx hnatS₁ (hnatCanon Δ)
      have hxT' := hxT.defeqU_r wf hΔ.toCtx hnatEq₁.symm
      have hinnerS' : TrExprS env []
          ((none, .vlam natTy₁) :: Δ)
          (.lam0 q(Nat) <|
            Condition.natEq.decide #[.bvar 1, .bvar 0])
          (.lam natTy₂ body) := .lam hnatTy₂ hnatS₂ hbodyS
      have hinnerInst := TrExprS.inst (env := env) (Us := []) (Δ := Δ)
        (e₀' := x') (A₀ := natTy₁) wf.ordered hxT' hinnerS' hx
      cases hinnerInst with
      | lam hnatTy₂' hnatS₂' hbodyInstS =>
        have hnatEq₂ := TrExprS.uniq (Us := []) wf hctx hnatS₂'
          (hnatCanon Δ)
        have hyT' := hyT.defeqU_r wf hΔ.toCtx hnatEq₂.symm
        have hbodyInst₂ := TrExprS.inst (env := env) (Us := []) (Δ := Δ)
          (e₀' := y') wf.ordered hyT' hbodyInstS hy
        have hbodyInst₂' : TrExprS env [] Δ
            (Condition.natEq.decide #[x, y])
            ((body.inst x' 1).inst y') := by
          simpa [Condition.natEqDecideFn, Condition.decide,
            Condition.ite, Condition.natEq, VExpr.inst,
            Lean.mkAppN, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp,
            Expr.instantiate1', Expr.instantiate1'_instantiate1',
            Expr.instantiate1'_liftLooseBVars_0] using hbodyInst₂
        have houtEq := TrExprS.uniq (Us := []) wf hctx hcall hbodyInst₂'
        obtain ⟨_, hfnT⟩ :=
          (show TrExprS env [] Δ
            (.lam0 q(Nat) <| .lam0 q(Nat) <|
              Condition.natEq.decide #[.bvar 1, .bvar 0])
            (.lam natTy₁ <| .lam natTy₂ body) from
              .lam hnatTy₁ hnatS₁ (.lam hnatTy₂ hnatS₂ hbodyS)).wf
            wf.ordered (Us := []) (Δ := Δ) hΔ
        obtain ⟨⟨_, hnatSort₁⟩, _, hinnerT⟩ :=
          hfnT.hasType.1.lam_inv wf hΔ.toCtx
        have hbeta₁ : env.IsDefEqU 0 Δ.toCtx
            (.app (VExpr.lam natTy₁ (VExpr.lam natTy₂ body)) x')
            ((VExpr.lam natTy₂ body).inst x') :=
          ⟨_, .beta hinnerT hxT'⟩
        have hinnerInstT := hinnerT.instN wf.ordered hxT'
          (.zero : Ctx.InstN Δ.toCtx x' natTy₁ 0
            (natTy₁ :: Δ.toCtx) Δ.toCtx)
        have hΔ₂ : VLCtx.WF env 0
            ((none, .vlam (natTy₂.inst x')) :: Δ) :=
          ⟨hΔ, nofun, hnatTy₂'⟩
        obtain ⟨_, hbodyInstWF⟩ := hbodyInstS.wf wf.ordered
          (Us := []) (Δ := ((none, .vlam (natTy₂.inst x')) :: Δ)) hΔ₂
        obtain ⟨_, hnatSort₂⟩ := hnatTy₂'
        have hrightPrefixT := VEnv.HasType.lam hnatSort₂
          hbodyInstWF.hasType.1
        have hbeta₂ : env.IsDefEqU 0 Δ.toCtx
            (.app ((VExpr.lam natTy₂ body).inst x') y')
            ((body.inst x' 1).inst y') := by
          exact ⟨_, .beta hbodyInstWF.hasType.1 hyT'⟩
        have hprefixT :=
          (hbeta₁.of_r wf hΔ.toCtx hrightPrefixT).hasType.1
        have happ := hbeta₁.app_same wf hΔ.toCtx hprefixT hyT'
        exact houtEq.trans wf hΔ.toCtx (happ.trans wf hΔ.toCtx hbeta₂).symm

/- The shared lambda-instantiation and dependent-proof-binder helpers come
from `NatModReflect`; bitwise reuses the same verified telescope machinery. -/

/-- The semantic result of instantiating the common `(Bool → Bool → Bool) →
Nat → Nat →` prefix of a checked bitwise equation.  The translated source
bodies and their original local contexts are retained for subsequent
constructor-specific reasoning. -/
inductive VEnv.BitwiseLam3Instantiation (env : VEnv)
    (leftBody rightBody : Expr) (op : VExpr) (a b : Nat) : Prop where
  | intro (funTyL natTyL₁ natTyL₂ bodyL : VExpr)
      (funTyR natTyR₁ natTyR₂ bodyR : VExpr)
      (hfunTyL : env.IsType 0 [] funTyL)
      (hnatTyL₁ : env.IsType 0 [funTyL] natTyL₁)
      (hnatTyL₂ : env.IsType 0 [natTyL₁, funTyL] natTyL₂)
      (hfunTyR : env.IsType 0 [] funTyR)
      (hnatTyR₁ : env.IsType 0 [funTyR] natTyR₁)
      (hnatTyR₂ : env.IsType 0 [natTyR₁, funTyR] natTyR₂)
      (hnatEqL₁ : env.IsDefEqU 0 [funTyL] natTyL₁ .nat)
      (hnatEqL₂ : env.IsDefEqU 0 [natTyL₁, funTyL] natTyL₂ .nat)
      (hnatEqR₁ : env.IsDefEqU 0 [funTyR] natTyR₁ .nat)
      (hnatEqR₂ : env.IsDefEqU 0 [natTyR₁, funTyR] natTyR₂ .nat)
      (hopL : env.HasType 0 [] op funTyL)
      (hopR : env.HasType 0 [] op funTyR)
      (haT : env.HasType 0 [] (.natLit a) .nat)
      (hbT : env.HasType 0 [] (.natLit b) .nat)
      (haL : env.HasType 0 [] (.natLit a) (natTyL₁.inst op))
      (haR : env.HasType 0 [] (.natLit a) (natTyR₁.inst op))
      (hbL : env.HasType 0 [] (.natLit b)
        ((natTyL₂.inst op 1).inst (.natLit a)))
      (hbR : env.HasType 0 [] (.natLit b)
        ((natTyR₂.inst op 1).inst (.natLit a)))
      (leftS : TrExprS env []
        [(none, .vlam natTyL₂), (none, .vlam natTyL₁),
          (none, .vlam funTyL)] leftBody bodyL)
      (rightS : TrExprS env []
        [(none, .vlam natTyR₂), (none, .vlam natTyR₁),
          (none, .vlam funTyR)] rightBody bodyR)
      (eq : env.IsDefEqU 0 []
        (((bodyL.inst op 2).inst (.natLit a) 1).inst (.natLit b))
        (((bodyR.inst op 2).inst (.natLit a) 1).inst (.natLit b))) :
      BitwiseLam3Instantiation env leftBody rightBody op a b

/-- Instantiate the common three-lambda prefix of a checked bitwise equation
with an arbitrary semantic Boolean operation and two concrete naturals. -/
theorem VEnv.instantiate_bitwise_lam3_equation {env : VEnv}
    (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {leftBody rightBody : Expr} {l r : VExpr}
    (hl : TrExprS env [] []
      (.lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <|
        .lam0 q(Nat) leftBody) l)
    (hr : TrExprS env [] []
      (.lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <|
        .lam0 q(Nat) rightBody) r)
    (heq : env.IsDefEqU 0 [] l r)
    (hop : env.HasType 0 [] op
      (.forallE .bool <| .forallE .bool .bool)) :
    VEnv.BitwiseLam3Instantiation env leftBody rightBody op a b := by
  cases hl with
  | lam hfunTyL hfunSL hl₁ =>
    cases hl₁ with
    | lam hnatTyL₁ hnatSL₁ hl₂ =>
      cases hl₂ with
      | lam hnatTyL₂ hnatSL₂ hl₃ =>
        cases hr with
        | lam hfunTyR hfunSR hr₁ =>
          cases hr₁ with
          | lam hnatTyR₁ hnatSR₁ hr₂ =>
            cases hr₂ with
            | lam hnatTyR₂ hnatSR₂ hr₃ =>
              rename_i funTyL natTyL₁ natTyL₂ bodyL
                funTyR natTyR₁ natTyR₂ bodyR
              obtain ⟨_, hopSort⟩ := hop.isType wf trivial
              obtain ⟨hboolTy, hboolRestTy⟩ := hopSort.forallE_inv wf
              obtain ⟨hboolTy₁, hboolTy₂⟩ :=
                hboolRestTy.forallE_inv wf
              let ⟨_, hboolSort⟩ := hboolTy
              obtain ⟨_, hboolCi, _, hboolLen⟩ :=
                hboolSort.const_inv wf trivial
              have hboolS (Δ : VLCtx) :
                  TrExprS env [] Δ q(Bool) .bool :=
                .const hboolCi rfl (by simpa using hboolLen)
              have hboolBinS : TrExprS env [] []
                  q(Bool → Bool → Bool)
                  (.forallE .bool <| .forallE .bool .bool) :=
                .forallE hboolTy hboolRestTy (hboolS []) <|
                  .forallE hboolTy₁ hboolTy₂
                    (hboolS [(none, .vlam .bool)])
                    (hboolS [(none, .vlam .bool), (none, .vlam .bool)])
              have hfunEqL := hfunSL.uniq wf
                (.refl wf (U := 0) (Δ := []) (by trivial)) hboolBinS
              have hfunEqR := hfunSR.uniq wf
                (.refl wf (U := 0) (Δ := []) (by trivial)) hboolBinS
              obtain ⟨hopL, hopR, houter⟩ :=
                VEnv.instantiate_lamU_step wf heq hfunEqL hfunEqR hop
              simp only [VExpr.inst] at houter
              have hzT :=
                (hctors.natZeroS (Us := []) (Δ := [])).2
              obtain ⟨_, hnatSort⟩ := hzT.isType wf trivial
              obtain ⟨_, hnatCi, _, hnatLen⟩ :=
                hnatSort.const_inv wf trivial
              have hnatS (Δ : VLCtx) : TrExprS env [] Δ q(Nat) .nat :=
                .const hnatCi rfl (by simpa using hnatLen)
              have hctxL : VLCtx.IsDefEq env 0
                  [(none, .vlam funTyL)] [(none, .vlam funTyL)] :=
                .refl wf ⟨trivial, nofun, hfunTyL⟩
              have hctxR : VLCtx.IsDefEq env 0
                  [(none, .vlam funTyR)] [(none, .vlam funTyR)] :=
                .refl wf ⟨trivial, nofun, hfunTyR⟩
              have hnatEqLCtx := TrExprS.uniq (Us := []) wf hctxL hnatSL₁
                (hnatS [(none, .vlam funTyL)])
              have hnatEqRCtx := TrExprS.uniq (Us := []) wf hctxR hnatSR₁
                (hnatS [(none, .vlam funTyR)])
              have hnatEqL := hnatEqLCtx.instN wf.ordered
                (.zero : Ctx.InstN [] op funTyL 0 [funTyL] []) hopL
              have hnatEqR := hnatEqRCtx.instN wf.ordered
                (.zero : Ctx.InstN [] op funTyR 0 [funTyR] []) hopR
              have hnatEqL' : env.IsDefEqU 0 [] (natTyL₁.inst op) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqL
              have hnatEqR' : env.IsDefEqU 0 [] (natTyR₁.inst op) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqR
              have haT :=
                (hctors.natLitS a (Us := []) (Δ := [])).2
              obtain ⟨haL, haR, hmiddle⟩ :=
                VEnv.instantiate_lamU_step wf houter hnatEqL' hnatEqR' haT
              simp only [VExpr.inst] at hmiddle
              have hctxL₂ : VLCtx.IsDefEq env 0
                  [(none, .vlam natTyL₁), (none, .vlam funTyL)]
                  [(none, .vlam natTyL₁), (none, .vlam funTyL)] :=
                .refl wf ⟨⟨trivial, nofun, hfunTyL⟩, nofun, hnatTyL₁⟩
              have hctxR₂ : VLCtx.IsDefEq env 0
                  [(none, .vlam natTyR₁), (none, .vlam funTyR)]
                  [(none, .vlam natTyR₁), (none, .vlam funTyR)] :=
                .refl wf ⟨⟨trivial, nofun, hfunTyR⟩, nofun, hnatTyR₁⟩
              have hnatEqL₂Ctx := TrExprS.uniq (Us := []) wf hctxL₂
                hnatSL₂ (hnatS [(none, .vlam natTyL₁),
                  (none, .vlam funTyL)])
              have hnatEqR₂Ctx := TrExprS.uniq (Us := []) wf hctxR₂
                hnatSR₂ (hnatS [(none, .vlam natTyR₁),
                  (none, .vlam funTyR)])
              have hnatEqL₂Op := hnatEqL₂Ctx.instN wf.ordered
                (.succ (.zero : Ctx.InstN [] op funTyL 0 [funTyL] [])) hopL
              have hnatEqR₂Op := hnatEqR₂Ctx.instN wf.ordered
                (.succ (.zero : Ctx.InstN [] op funTyR 0 [funTyR] [])) hopR
              have hnatEqL₂ := hnatEqL₂Op.instN wf.ordered
                (.zero : Ctx.InstN [] (.natLit a) (natTyL₁.inst op) 0
                  [natTyL₁.inst op] []) haL
              have hnatEqR₂ := hnatEqR₂Op.instN wf.ordered
                (.zero : Ctx.InstN [] (.natLit a) (natTyR₁.inst op) 0
                  [natTyR₁.inst op] []) haR
              have hnatEqL₂' : env.IsDefEqU 0 []
                  ((natTyL₂.inst op 1).inst (.natLit a)) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqL₂
              have hnatEqR₂' : env.IsDefEqU 0 []
                  ((natTyR₂.inst op 1).inst (.natLit a)) .nat := by
                simpa [VExpr.nat, VExpr.inst] using hnatEqR₂
              have hbT :=
                (hctors.natLitS b (Us := []) (Δ := [])).2
              obtain ⟨hbL, hbR, hfinal⟩ :=
                VEnv.instantiate_lamU_step wf hmiddle hnatEqL₂' hnatEqR₂' hbT
              exact .intro funTyL natTyL₁ natTyL₂ bodyL
                funTyR natTyR₁ natTyR₂ bodyR
                hfunTyL hnatTyL₁ hnatTyL₂ hfunTyR hnatTyR₁ hnatTyR₂
                hnatEqLCtx hnatEqL₂Ctx hnatEqRCtx hnatEqR₂Ctx
                hopL hopR haT hbT haL haR hbL hbR hl₃ hr₃ hfinal

/-- Substitute the semantic bitwise prefix while preserving one dependent
local binder at the head of the context. -/
theorem VEnv.IsDefEqU.inst_bitwise_outer3 {env : VEnv}
    (wf : env.WF)
    {funTy natTy₁ natTy₂ proofTy op x y : VExpr} {a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (ha : env.HasType 0 [] (.natLit a) (natTy₁.inst op))
    (hb : env.HasType 0 [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)))
    (h : env.IsDefEqU 0 [proofTy, natTy₂, natTy₁, funTy] x y) :
    env.IsDefEqU 0
      [((proofTy.inst op 2).inst (.natLit a) 1).inst (.natLit b)]
      (((x.inst op 3).inst (.natLit a) 2).inst (.natLit b) 1)
      (((y.inst op 3).inst (.natLit a) 2).inst (.natLit b) 1) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.succ (.zero : Ctx.InstN [] op funTy 0
      [funTy] [])))) hop
  have h₂ := h₁.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] (.natLit a)
      (natTy₁.inst op) 0 [natTy₁.inst op] []))) ha
  exact h₂.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)) 0
      [((natTy₂.inst op 1).inst (.natLit a))] [])) hb

/-- Typing counterpart of `IsDefEqU.inst_bitwise_outer3`. -/
theorem VEnv.HasType.inst_bitwise_outer3 {env : VEnv}
    (wf : env.WF)
    {funTy natTy₁ natTy₂ proofTy op x A : VExpr} {a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (ha : env.HasType 0 [] (.natLit a) (natTy₁.inst op))
    (hb : env.HasType 0 [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)))
    (h : env.HasType 0 [proofTy, natTy₂, natTy₁, funTy] x A) :
    env.HasType 0
      [((proofTy.inst op 2).inst (.natLit a) 1).inst (.natLit b)]
      (((x.inst op 3).inst (.natLit a) 2).inst (.natLit b) 1)
      (((A.inst op 3).inst (.natLit a) 2).inst (.natLit b) 1) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.succ (.zero : Ctx.InstN [] op funTy 0
      [funTy] [])))) hop
  have h₂ := h₁.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] (.natLit a)
      (natTy₁.inst op) 0 [natTy₁.inst op] []))) ha
  exact h₂.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)) 0
      [((natTy₂.inst op 1).inst (.natLit a))] [])) hb

/-- Substitute the three semantic bitwise arguments from a three-entry local
context, discharging the context completely. -/
theorem VEnv.IsDefEqU.inst_bitwise3 {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ op x y : VExpr} {a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (ha : env.HasType 0 [] (.natLit a) (natTy₁.inst op))
    (hb : env.HasType 0 [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)))
    (h : env.IsDefEqU 0 [natTy₂, natTy₁, funTy] x y) :
    env.IsDefEqU 0 []
      (((x.inst op 2).inst (.natLit a) 1).inst (.natLit b))
      (((y.inst op 2).inst (.natLit a) 1).inst (.natLit b)) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] op funTy 0 [funTy] []))) hop
  have h₂ := h₁.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] (.natLit a)
      (natTy₁.inst op) 0 [natTy₁.inst op] [])) ha
  exact h₂.instN wf.ordered
    (.zero : Ctx.InstN [] (.natLit b)
      ((natTy₂.inst op 1).inst (.natLit a)) 0
      [((natTy₂.inst op 1).inst (.natLit a))] []) hb

/-- Substitute the four semantic successor-equation binders while preserving
the dependent proof binder at the head of the context. -/
theorem VEnv.IsDefEqU.inst_bitwise_outer4 {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ natTy₃ proofTy op x y : VExpr}
    {fuel a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (hf : env.HasType 0 [] (.natLit fuel) (natTy₁.inst op))
    (ha : env.HasType 0 [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)))
    (hb : env.HasType 0 [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (h : env.IsDefEqU 0
      [proofTy, natTy₃, natTy₂, natTy₁, funTy] x y) :
    env.IsDefEqU 0
      [(((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)]
      ((((x.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1)
      ((((y.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.succ (.succ (.zero : Ctx.InstN [] op funTy 0
      [funTy] []))))) hop
  have h₂ := h₁.instN wf.ordered
    (.succ (.succ (.succ (.zero : Ctx.InstN [] (.natLit fuel)
      (natTy₁.inst op) 0 [natTy₁.inst op] [])))) hf
  have h₃ := h₂.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)) 0
      [((natTy₂.inst op 1).inst (.natLit fuel))] []))) ha
  exact h₃.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)) 0
      [(((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a))] [])) hb

theorem VEnv.HasType.inst_bitwise_outer4 {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ natTy₃ proofTy op x A : VExpr}
    {fuel a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (hf : env.HasType 0 [] (.natLit fuel) (natTy₁.inst op))
    (ha : env.HasType 0 [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)))
    (hb : env.HasType 0 [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (h : env.HasType 0
      [proofTy, natTy₃, natTy₂, natTy₁, funTy] x A) :
    env.HasType 0
      [(((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)]
      ((((x.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1)
      ((((A.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1) := by
  have h₁ := h.instN wf.ordered
    (.succ (.succ (.succ (.succ (.zero : Ctx.InstN [] op funTy 0
      [funTy] []))))) hop
  have h₂ := h₁.instN wf.ordered
    (.succ (.succ (.succ (.zero : Ctx.InstN [] (.natLit fuel)
      (natTy₁.inst op) 0 [natTy₁.inst op] [])))) hf
  have h₃ := h₂.instN wf.ordered
    (.succ (.succ (.zero : Ctx.InstN [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)) 0
      [((natTy₂.inst op 1).inst (.natLit fuel))] []))) ha
  exact h₃.instN wf.ordered
    (.succ (.zero : Ctx.InstN [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)) 0
      [(((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a))] [])) hb

/-- Semantic instantiation of the four ordinary binders of a certified
successor/successor bitwise equation. -/
inductive VEnv.BitwiseLam4Instantiation (env : VEnv)
    (leftBody rightBody : Expr) (op : VExpr)
    (fuel a b : Nat) : Prop where
  | intro (funTyL natTyL₁ natTyL₂ natTyL₃ bodyL : VExpr)
      (funTyR natTyR₁ natTyR₂ natTyR₃ bodyR : VExpr)
      (hfunTyL : env.IsType 0 [] funTyL)
      (hnatTyL₁ : env.IsType 0 [funTyL] natTyL₁)
      (hnatTyL₂ : env.IsType 0 [natTyL₁, funTyL] natTyL₂)
      (hnatTyL₃ : env.IsType 0 [natTyL₂, natTyL₁, funTyL] natTyL₃)
      (hfunTyR : env.IsType 0 [] funTyR)
      (hnatTyR₁ : env.IsType 0 [funTyR] natTyR₁)
      (hnatTyR₂ : env.IsType 0 [natTyR₁, funTyR] natTyR₂)
      (hnatTyR₃ : env.IsType 0 [natTyR₂, natTyR₁, funTyR] natTyR₃)
      (hnatEqL₁ : env.IsDefEqU 0 [funTyL] natTyL₁ .nat)
      (hnatEqL₂ : env.IsDefEqU 0 [natTyL₁, funTyL] natTyL₂ .nat)
      (hnatEqL₃ : env.IsDefEqU 0 [natTyL₂, natTyL₁, funTyL]
        natTyL₃ .nat)
      (hnatEqR₁ : env.IsDefEqU 0 [funTyR] natTyR₁ .nat)
      (hnatEqR₂ : env.IsDefEqU 0 [natTyR₁, funTyR] natTyR₂ .nat)
      (hnatEqR₃ : env.IsDefEqU 0 [natTyR₂, natTyR₁, funTyR]
        natTyR₃ .nat)
      (hopL : env.HasType 0 [] op funTyL)
      (hopR : env.HasType 0 [] op funTyR)
      (hfT : env.HasType 0 [] (.natLit fuel) .nat)
      (haT : env.HasType 0 [] (.natLit a) .nat)
      (hbT : env.HasType 0 [] (.natLit b) .nat)
      (hfL : env.HasType 0 [] (.natLit fuel) (natTyL₁.inst op))
      (hfR : env.HasType 0 [] (.natLit fuel) (natTyR₁.inst op))
      (haL : env.HasType 0 [] (.natLit a)
        ((natTyL₂.inst op 1).inst (.natLit fuel)))
      (haR : env.HasType 0 [] (.natLit a)
        ((natTyR₂.inst op 1).inst (.natLit fuel)))
      (hbL : env.HasType 0 [] (.natLit b)
        (((natTyL₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
      (hbR : env.HasType 0 [] (.natLit b)
        (((natTyR₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
      (leftS : TrExprS env []
        [(none, .vlam natTyL₃), (none, .vlam natTyL₂),
          (none, .vlam natTyL₁), (none, .vlam funTyL)] leftBody bodyL)
      (rightS : TrExprS env []
        [(none, .vlam natTyR₃), (none, .vlam natTyR₂),
          (none, .vlam natTyR₁), (none, .vlam funTyR)] rightBody bodyR)
      (eq : env.IsDefEqU 0 []
        ((((bodyL.inst op 3).inst (.natLit fuel) 2).inst
          (.natLit a) 1).inst (.natLit b))
        ((((bodyR.inst op 3).inst (.natLit fuel) 2).inst
          (.natLit a) 1).inst (.natLit b))) :
      BitwiseLam4Instantiation env leftBody rightBody op fuel a b

theorem VEnv.instantiate_bitwise_lam4_equation {env : VEnv}
    (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {leftBody rightBody : Expr} {l r : VExpr}
    (hl : TrExprS env [] []
      (.lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <|
        .lam0 q(Nat) <| .lam0 q(Nat) leftBody) l)
    (hr : TrExprS env [] []
      (.lam0 q(Bool → Bool → Bool) <| .lam0 q(Nat) <|
        .lam0 q(Nat) <| .lam0 q(Nat) rightBody) r)
    (heq : env.IsDefEqU 0 [] l r)
    (hop : env.HasType 0 [] op
      (.forallE .bool <| .forallE .bool .bool)) :
    VEnv.BitwiseLam4Instantiation env leftBody rightBody op fuel a b := by
  have h₃ := VEnv.instantiate_bitwise_lam3_equation wf hctors
    (a := fuel) (b := a) hl hr heq hop
  cases h₃ with
  | intro funTyL natTyL₁ natTyL₂ bodyL
      funTyR natTyR₁ natTyR₂ bodyR
      hfunTyL hnatTyL₁ hnatTyL₂ hfunTyR hnatTyR₁ hnatTyR₂
      hnatEqL₁ hnatEqL₂ hnatEqR₁ hnatEqR₂
      hopL hopR hfT haT hfL hfR haL haR hleftS hrightS hmiddle =>
    cases hleftS with
    | lam hnatTyL₃ hnatSL₃ hbodyL =>
      cases hrightS with
      | lam hnatTyR₃ hnatSR₃ hbodyR =>
        rename_i natTyL₃ bodyLFinal natTyR₃ bodyRFinal
        have hnatZeroT :=
          (hctors.natZeroS (Us := []) (Δ := [])).2
        obtain ⟨_, hnatSort⟩ := hnatZeroT.isType wf trivial
        obtain ⟨_, hnatCi, _, hnatLen⟩ :=
          hnatSort.const_inv wf trivial
        have hnatS (Δ : VLCtx) : TrExprS env [] Δ q(Nat) .nat :=
          .const hnatCi rfl (by simpa using hnatLen)
        have hctxL : VLCtx.IsDefEq env 0
            [(none, .vlam natTyL₂), (none, .vlam natTyL₁),
              (none, .vlam funTyL)]
            [(none, .vlam natTyL₂), (none, .vlam natTyL₁),
              (none, .vlam funTyL)] :=
          .refl wf ⟨⟨⟨trivial, nofun, hfunTyL⟩, nofun, hnatTyL₁⟩,
            nofun, hnatTyL₂⟩
        have hctxR : VLCtx.IsDefEq env 0
            [(none, .vlam natTyR₂), (none, .vlam natTyR₁),
              (none, .vlam funTyR)]
            [(none, .vlam natTyR₂), (none, .vlam natTyR₁),
              (none, .vlam funTyR)] :=
          .refl wf ⟨⟨⟨trivial, nofun, hfunTyR⟩, nofun, hnatTyR₁⟩,
            nofun, hnatTyR₂⟩
        have hnatSLCtx := TrExprS.uniq (Us := []) wf hctxL hnatSL₃
          (hnatS [(none, .vlam natTyL₂), (none, .vlam natTyL₁),
            (none, .vlam funTyL)])
        have hnatSRCtx := TrExprS.uniq (Us := []) wf hctxR hnatSR₃
          (hnatS [(none, .vlam natTyR₂), (none, .vlam natTyR₁),
            (none, .vlam funTyR)])
        have hnatEqL := VEnv.IsDefEqU.inst_bitwise3 wf hopL hfL haL
          hnatSLCtx
        have hnatEqR := VEnv.IsDefEqU.inst_bitwise3 wf hopR hfR haR
          hnatSRCtx
        have hnatEqL' : env.IsDefEqU 0 []
            (((natTyL₃.inst op 2).inst (.natLit fuel) 1).inst
              (.natLit a)) .nat := by
          simpa [VExpr.nat, VExpr.inst] using hnatEqL
        have hnatEqR' : env.IsDefEqU 0 []
            (((natTyR₃.inst op 2).inst (.natLit fuel) 1).inst
              (.natLit a)) .nat := by
          simpa [VExpr.nat, VExpr.inst] using hnatEqR
        have hbT :=
          (hctors.natLitS b (Us := []) (Δ := [])).2
        obtain ⟨hbL, hbR, hfinal⟩ :=
          VEnv.instantiate_lamU_step wf hmiddle hnatEqL' hnatEqR' hbT
        exact .intro funTyL natTyL₁ natTyL₂ natTyL₃ bodyLFinal
          funTyR natTyR₁ natTyR₂ natTyR₃ bodyRFinal
          hfunTyL hnatTyL₁ hnatTyL₂ hnatTyL₃
          hfunTyR hnatTyR₁ hnatTyR₂ hnatTyR₃
          hnatEqL₁ hnatEqL₂ hnatSLCtx
          hnatEqR₁ hnatEqR₂ hnatSRCtx
          hopL hopR hfT haT hbT hfL hfR haL haR hbL hbR
          hbodyL hbodyR hfinal

/-- Weaken a closed translation under the four bitwise equation binders. -/
theorem bitwise_weak4
    {env : VEnv} (wf : env.WF) {src : Expr}
    {closedV funTy natTy₁ natTy₂ proofTy : VExpr}
    (hS : TrExprS env [] [] src closedV) :
    TrExprS env []
      [(none, .vlam proofTy), (none, .vlam natTy₂),
        (none, .vlam natTy₁), (none, .vlam funTy)] src
      (closedV.liftN 4) := by
  have hlift : src.liftLooseBVars' 0 4 = src :=
    Expr.liftLooseBVars_eq_self hS.closed.looseBVarRange_le
  simpa [VLocalDecl.depth, hlift] using hS.weakBV wf.ordered
    (.skip (.vlam proofTy) <| .skip (.vlam natTy₂) <|
      .skip (.vlam natTy₁) <| .skip (.vlam funTy) <|
        (.refl : VLCtx.BVLift [] [] 0 0 0 0))

/-- Weaken a closed translation under the five successor-equation binders. -/
theorem bitwise_weak5
    {env : VEnv} (wf : env.WF) {src : Expr}
    {closedV funTy natTy₁ natTy₂ natTy₃ proofTy : VExpr}
    (hS : TrExprS env [] [] src closedV) :
    TrExprS env []
      [(none, .vlam proofTy), (none, .vlam natTy₃),
        (none, .vlam natTy₂), (none, .vlam natTy₁),
        (none, .vlam funTy)] src
      (closedV.liftN 5) := by
  have hlift : src.liftLooseBVars' 0 5 = src :=
    Expr.liftLooseBVars_eq_self hS.closed.looseBVarRange_le
  simpa [VLocalDecl.depth, hlift] using hS.weakBV wf.ordered
    (.skip (.vlam proofTy) <| .skip (.vlam natTy₃) <|
      .skip (.vlam natTy₂) <| .skip (.vlam natTy₁) <|
        .skip (.vlam funTy) <|
          (.refl : VLCtx.BVLift [] [] 0 0 0 0))

/-- Instantiate a local occurrence of a closed expression under the three
semantic bitwise binders, discarding the vanishing instantiations on the
closed side. -/
theorem bitwise_local_closed_eq
    {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ proofTy op localV closedV : VExpr} {n₁ n₂ : Nat}
    (hop : env.HasType 0 [] op funTy)
    (h₁ : env.HasType 0 [] (.natLit n₁) (natTy₁.inst op))
    (h₂ : env.HasType 0 [] (.natLit n₂)
      ((natTy₂.inst op 1).inst (.natLit n₁)))
    (hclosed : closedV.ClosedN)
    (hctxEq : env.IsDefEqU 0 [proofTy, natTy₂, natTy₁, funTy]
      localV (closedV.liftN 4)) :
    env.IsDefEqU 0
      [((proofTy.inst op 2).inst (.natLit n₁) 1).inst (.natLit n₂)]
      (((localV.inst op 3).inst (.natLit n₁) 2).inst (.natLit n₂) 1)
      closedV := by
  simpa [hclosed.liftN_eq (Nat.zero_le _),
    hclosed.instN_eq (Nat.zero_le _)] using
    VEnv.IsDefEqU.inst_bitwise_outer3 wf hop h₁ h₂ hctxEq

/-- Instantiate a local occurrence of a closed expression under the four
semantic successor-equation binders, discarding the vanishing
instantiations on the closed side. -/
theorem bitwise_local_closed_eq4
    {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ natTy₃ proofTy op localV closedV : VExpr}
    {fuel a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (hf : env.HasType 0 [] (.natLit fuel) (natTy₁.inst op))
    (ha : env.HasType 0 [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)))
    (hb : env.HasType 0 [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (hclosed : closedV.ClosedN)
    (hctxEq : env.IsDefEqU 0 [proofTy, natTy₃, natTy₂, natTy₁, funTy]
      localV (closedV.liftN 5)) :
    env.IsDefEqU 0
      [(((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)]
      ((((localV.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1)
      closedV := by
  simpa [hclosed.liftN_eq (Nat.zero_le _),
    hclosed.instN_eq (Nat.zero_le _)] using
    VEnv.IsDefEqU.inst_bitwise_outer4 wf hop hf ha hb hctxEq

/-- Substitute the four semantic successor-equation binders and the
dependent proof value, discharging the local context completely. -/
theorem bitwise_root_eq {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ natTy₃ proofTy op hpV x y : VExpr}
    {fuel a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (hf : env.HasType 0 [] (.natLit fuel) (natTy₁.inst op))
    (ha : env.HasType 0 [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)))
    (hb : env.HasType 0 [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (hp : env.HasType 0 [] hpV
      ((((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)))
    (h : env.IsDefEqU 0 [proofTy, natTy₃, natTy₂, natTy₁, funTy] x y) :
    env.IsDefEqU 0 []
      (((((x.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1).inst hpV)
      (((((y.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1).inst hpV) :=
  (VEnv.IsDefEqU.inst_bitwise_outer4 wf hop hf ha hb h).instN wf.ordered
    (.zero : Ctx.InstN [] hpV
      ((((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)) 0
      [(((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)] []) hp

/-- `bitwise_root_eq` against a weakened closed expression, discarding the
vanishing instantiations on the closed side. -/
theorem bitwise_root_closed_eq {env : VEnv} (wf : env.WF)
    {funTy natTy₁ natTy₂ natTy₃ proofTy op hpV localV closedV : VExpr}
    {fuel a b : Nat}
    (hop : env.HasType 0 [] op funTy)
    (hf : env.HasType 0 [] (.natLit fuel) (natTy₁.inst op))
    (ha : env.HasType 0 [] (.natLit a)
      ((natTy₂.inst op 1).inst (.natLit fuel)))
    (hb : env.HasType 0 [] (.natLit b)
      (((natTy₃.inst op 2).inst (.natLit fuel) 1).inst (.natLit a)))
    (hp : env.HasType 0 [] hpV
      ((((proofTy.inst op 3).inst (.natLit fuel) 2).inst
        (.natLit a) 1).inst (.natLit b)))
    (hclosed : closedV.ClosedN)
    (hctxEq : env.IsDefEqU 0 [proofTy, natTy₃, natTy₂, natTy₁, funTy]
      localV (closedV.liftN 5)) :
    env.IsDefEqU 0 []
      (((((localV.inst op 4).inst (.natLit fuel) 3).inst
        (.natLit a) 2).inst (.natLit b) 1).inst hpV)
      closedV := by
  simpa [hclosed.liftN_eq (Nat.zero_le _),
    hclosed.instN_eq (Nat.zero_le _)] using
    bitwise_root_eq wf hop hf ha hb hp hctxEq

/-- Evaluate a fully decomposed `boolNatITE` structure against reflected
condition and branch values. -/
theorem bitwise_struct_eval
    {env : VEnv} (wf : env.WF)
    {e iteV iteFinal condFinal thenFinal zeroFinal A : VExpr}
    {c : Bool} {t z : Nat}
    (hite : env.ReflectsBoolNatITE iteV)
    (heT : env.HasType 0 [] e A)
    (he : env.IsDefEqU 0 [] e
      (.app (.app (.app iteFinal condFinal) thenFinal) zeroFinal))
    (hiteEq : env.IsDefEqU 0 [] iteFinal iteV)
    (hcond : env.IsDefEqU 0 [] condFinal (.boolLit c))
    (hthen : env.IsDefEqU 0 [] thenFinal (.natLit t))
    (hzeroEq : env.IsDefEqU 0 [] zeroFinal (.natLit z)) :
    env.IsDefEqU 0 [] e (.natLit (if c then t else z)) := by
  have hstructT := (he.of_l wf trivial heT).hasType.2
  obtain ⟨_, _, hTwoT, hzT⟩ := hstructT.app_inv wf.ordered trivial
  obtain ⟨_, _, hOneT, hthenT⟩ := hTwoT.app_inv wf.ordered trivial
  obtain ⟨_, _, hiteT, hcondT⟩ := hOneT.app_inv wf.ordered trivial
  have h₁ := hiteEq.app_both wf trivial hcond hiteT hcondT
  have h₂ := h₁.app_both wf trivial hthen hOneT hthenT
  have h₃ := h₂.app_both wf trivial hzeroEq hTwoT hzT
  exact he.trans wf trivial (h₃.trans wf trivial (hite.2 c t z))

/-- Canonical translation and typing of a `g (Nat.succ x) 2` call for a
reflected binary `Nat` primitive, from a translated `Nat`-typed argument.
The successor-transition semantics uses this for its `Nat.mod` bit tests
and its `Nat.div` recursion arguments. -/
theorem VEnv.ReflectsNatNatNat.succ_two_canonS
    {env : VEnv} (wf : env.WF)
    (hctors : Lean4Lean.Environment.VEnv.HasNatBoolConstructors env)
    {g : Name} {G : Nat → Nat → Nat}
    (hg : env.ReflectsNatNatNat g G) (hgC : env.contains g)
    {Δ : VLCtx} {x : Expr} {x' : VExpr}
    (hx : TrExprS env [] Δ x x')
    (hxT : env.HasType 0 Δ.toCtx x' .nat) :
    TrExprS env [] Δ
      (mkApp2 (.const g []) (mkApp q(Nat.succ) x)
        (mkApp q(Nat.succ) (mkApp q(Nat.succ) q(Nat.zero))))
      (.app (.app (.const g []) (.app .natSucc x')) (.natLit 2)) ∧
    env.HasType 0 Δ.toCtx
      (.app (.app (.const g []) (.app .natSucc x')) (.natLit 2)) .nat := by
  have ⟨hgT, _⟩ := hg hgC
  obtain ⟨_, hgCi, _, hgLen⟩ := (hgT 0 []).const_inv wf trivial
  have hgS : TrExprS env [] Δ (.const g []) (.const g []) :=
    .const hgCi rfl (by simpa using hgLen)
  have hsuccS := (hctors.natSuccS (Us := []) (Δ := Δ)).1
  have hsuccT := (hctors.natSuccS (Us := []) (Δ := Δ)).2
  have hzeroS := (hctors.natZeroS (Us := []) (Δ := Δ)).1
  have hzeroT := (hctors.natZeroS (Us := []) (Δ := Δ)).2
  have hsxS : TrExprS env [] Δ (mkApp q(Nat.succ) x)
      (.app .natSucc x') := .app hsuccT hxT hsuccS hx
  have hsxT := VEnv.HasType.app hsuccT hxT
  have honeS : TrExprS env [] Δ (mkApp q(Nat.succ) q(Nat.zero))
      (.natLit 1) := .app hsuccT hzeroT hsuccS hzeroS
  have htwoS : TrExprS env [] Δ
      (mkApp q(Nat.succ) (mkApp q(Nat.succ) q(Nat.zero)))
      (.natLit 2) :=
    .app hsuccT (VEnv.HasType.app hsuccT hzeroT) hsuccS honeS
  have htwoT := (hctors.natLitS 2 (Us := []) (Δ := Δ)).2
  exact ⟨.app (VEnv.HasType.app (hgT 0 Δ.toCtx) hsxT) htwoT
      (.app (hgT 0 Δ.toCtx) hsxT hgS hsxS) htwoS,
    .app (.app (hgT 0 Δ.toCtx) hsxT) htwoT⟩

/-- Normalize the checked `Bool.true` selector equation to the particular
translation of `boolNatITE` used by a certified bitwise equation. -/
theorem VEnv.bitwiseBoolNatITE_true_of_equation {env : VEnv}
    (wf : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat)
    {l r ite : VExpr}
    (hl : TrExprS env [] []
      (mkApp Condition.bool.boolNatITE q(true)) l)
    (hr : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1) r)
    (heq : env.IsDefEqU 0 [] l r)
    (hite : TrExprS env [] [] Condition.bool.boolNatITE ite) :
    ∃ A B, env.HasType 0 [] ite (.forallE A B) ∧
      env.HasType 0 [] .boolTrue A ∧
      env.IsDefEqU 0 [] (.app ite .boolTrue)
        (.lam .nat <| .lam .nat <| .bvar 1) := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    refine ⟨?_, ⟨u, hnatTy⟩⟩
    exact .const hci rfl (by simpa using hlen)
  have hnatS' (Δ : VLCtx) : TrExprS env [] Δ q(Nat) .nat := by
    cases hnatS with
    | const hci hus hlen => exact .const hci hus hlen
  have hselector : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1)
      (.lam .nat <| .lam .nat <| .bvar 1) := by
    obtain ⟨u, hNatSort⟩ := hnatTy
    apply TrExprS.lam ⟨u, hNatSort⟩ (hnatS' [])
    apply TrExprS.lam ⟨u, hNatSort.weak0 wf⟩ (hnatS' _)
    exact TrExprS.bvar (A := .nat) (by
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.depth, VLocalDecl.value,
        VLocalDecl.type, VExpr.lift, VExpr.liftN, VExpr.nat, liftVar])
  have hrEq := hr.uniq wf
    (.refl wf (U := 0) (Δ := []) (by trivial)) hselector
  cases hl with
  | app hiteT htrueT hite' htrue =>
    rename_i iteCert iteA iteB trueCert
    cases htrue with
    | const hci hus hlen =>
      rename_i ci us
      simp at hus
      subst us
      have hciEq := hprim.boolTrue hci
      subst ci
      have hiteEq := hite.uniq wf
        (.refl wf (U := 0) (Δ := []) (by trivial)) hite'
      have hlTrue : env.IsDefEqU 0 [] (.app ite .boolTrue)
          (.app iteCert .boolTrue) := by
        have hi := hiteEq.of_r wf trivial hiteT
        exact ⟨_, .appDF hi htrueT⟩
      refine ⟨iteA, iteB, ?_, ?_, ?_⟩
      · exact (hiteEq.of_r wf trivial hiteT).hasType.1
      · exact htrueT
      · exact hlTrue.trans wf trivial <| heq.trans wf trivial hrEq

/-- Normalize the checked `Bool.false` selector equation to the particular
translation of `boolNatITE` used by a certified bitwise equation. -/
theorem VEnv.boolNatITE_false_of_equation {env : VEnv}
    (wf : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat)
    {l r ite : VExpr}
    (hl : TrExprS env [] []
      (mkApp Condition.bool.boolNatITE q(false)) l)
    (hr : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0) r)
    (heq : env.IsDefEqU 0 [] l r)
    (hite : TrExprS env [] [] Condition.bool.boolNatITE ite) :
    ∃ A B, env.HasType 0 [] ite (.forallE A B) ∧
      env.HasType 0 [] .boolFalse A ∧
      env.IsDefEqU 0 [] (.app ite .boolFalse)
        (.lam .nat <| .lam .nat <| .bvar 0) := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (TrExprS.natZero hprim hnat (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    refine ⟨?_, ⟨u, hnatTy⟩⟩
    exact .const hci rfl (by simpa using hlen)
  have hnatS' (Δ : VLCtx) : TrExprS env [] Δ q(Nat) .nat := by
    cases hnatS with
    | const hci hus hlen => exact .const hci hus hlen
  have hselector : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0)
      (.lam .nat <| .lam .nat <| .bvar 0) := by
    obtain ⟨u, hNatSort⟩ := hnatTy
    apply TrExprS.lam ⟨u, hNatSort⟩ (hnatS' [])
    apply TrExprS.lam ⟨u, hNatSort.weak0 wf⟩ (hnatS' _)
    exact TrExprS.bvar (A := .nat) (by
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type,
        VExpr.lift, VExpr.liftN, VExpr.nat])
  have hrEq := hr.uniq wf
    (.refl wf (U := 0) (Δ := []) (by trivial)) hselector
  cases hl with
  | app hiteT hfalseT hite' hfalse =>
    rename_i iteCert iteA iteB falseCert
    cases hfalse with
    | const hci hus hlen =>
      rename_i ci us
      simp at hus
      subst us
      have hciEq := hprim.boolFalse hci
      subst ci
      have hiteEq := hite.uniq wf
        (.refl wf (U := 0) (Δ := []) (by trivial)) hite'
      have hlFalse : env.IsDefEqU 0 [] (.app ite .boolFalse)
          (.app iteCert .boolFalse) := by
        have hi := hiteEq.of_r wf trivial hiteT
        exact ⟨_, .appDF hi hfalseT⟩
      refine ⟨iteA, iteB, ?_, ?_, ?_⟩
      · exact (hiteEq.of_r wf trivial hiteT).hasType.1
      · exact hfalseT
      · exact hlFalse.trans wf trivial <| heq.trans wf trivial hrEq

/-- The two equations emitted by `Condition.bool.check` give the reusable
semantic Boolean selector needed by certified bitwise transitions. -/
theorem VEnv.reflectsBoolNatITE_of_equations {env : VEnv}
    (wf : env.WF) (hprim : env.HasPrimitives)
    (hbool : env.contains ``Bool) (hnat : env.contains ``Nat)
    {ite tl tr fl fr : VExpr}
    (hiteS : TrExprS env [] [] Condition.bool.boolNatITE ite)
    (hiteT : env.HasType 0 [] ite
      (.forallE .bool <| .forallE .nat <| .forallE .nat .nat))
    (htl : TrExprS env [] []
      (mkApp Condition.bool.boolNatITE q(true)) tl)
    (htr : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 1) tr)
    (hteq : env.IsDefEqU 0 [] tl tr)
    (hfl : TrExprS env [] []
      (mkApp Condition.bool.boolNatITE q(false)) fl)
    (hfr : TrExprS env [] []
      (.lam0 q(Nat) <| .lam0 q(Nat) <| .bvar 0) fr)
    (hfeq : env.IsDefEqU 0 [] fl fr) :
    env.ReflectsBoolNatITE ite := by
  obtain ⟨_, _, _, _, htrue⟩ :=
    VEnv.bitwiseBoolNatITE_true_of_equation
      wf hprim hnat htl htr hteq hiteS
  obtain ⟨_, _, _, _, hfalse⟩ :=
    VEnv.boolNatITE_false_of_equation wf hprim hnat hfl hfr hfeq hiteS
  have hnatT (n Γ) : env.HasType 0 Γ (.natLit n) .nat :=
    (TrExprS.natLit hprim hnat n (Us := []) (Δ := [])).2.weak0 wf
  have hnatTy₀ := (hnatT 0 []).isType wf trivial
  obtain ⟨u, hnatSort⟩ := hnatTy₀
  have hnatTy₁ : env.IsType 0 [.nat] .nat :=
    ⟨u, hnatSort.weak0 wf⟩
  exact VEnv.ReflectsBoolNatITE.of_equations wf
    (fun b => (TrExprS.boolLit hprim hbool b (Us := []) (Δ := [])).2)
    ⟨u, hnatSort⟩ hnatTy₁ hnatT hiteT htrue hfalse

end Lean4Lean.Environment
