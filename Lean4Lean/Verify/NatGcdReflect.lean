/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.NatWellFoundedChecker

/-!
# Verified Nat.gcd reflection

This module connects the generic-state well-founded certificate to Euclid's
algorithm. It adapts upstream lean4lean PR #32 while deliberately treating
the compiler-selected state constructor as an opaque, typed binary packer.
-/

namespace Lean4Lean.Environment

open Lean hiding Environment Exception
open Kernel TypeChecker

theorem VEnv.ReflectsNatNatNat.nat_of_contains (henv : VEnv.WF env)
    (h : env.ReflectsNatNatNat fc f) (hc : env.contains fc) :
    env.contains ``Nat := by
  have hfun := (h hc).1 0 []
  have ⟨_, H⟩ := hfun.isType henv trivial
  let ⟨⟨_, H⟩, _⟩ := H.forallE_inv henv
  let ⟨_, H, _⟩ := H.const_inv henv trivial
  exact ⟨_, H⟩

/-- Relational form of the fuel-level gcd argument. Independently translated
recursive calls need only inhabit one semantic call relation. -/
theorem VEnv.ReflectsNatNatNat.of_gcd_fix_relation (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.gcd [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.gcd []) f)
    (G : Nat → Nat → Nat → VExpr → Prop)
    (htop : ∀ a b, ∃ e, G (a + 1) a b e ∧ env.IsDefEqU 0 []
      (.app (.app f (.natLit a)) (.natLit b)) e)
    (hgo : ∀ fuel a b e, G (fuel + 1) a b e →
      env.IsDefEqU 0 [] e e →
      if a = 0 then env.IsDefEqU 0 [] e (.natLit b)
      else ∃ e', G fuel (b % a) a e' ∧ env.IsDefEqU 0 [] e e') :
    env.ReflectsNatNatNat ``Nat.gcd Nat.gcd := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hcfApp (x y) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.gcd []) (.natLit x)) (.natLit y))
      (.app (.app f (.natLit x)) (.natLit y)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit x [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit x []))
      (hlit y [])
  have goEval : ∀ fuel a b e, G fuel a b e →
      env.IsDefEqU 0 [] e e → a < fuel →
      env.IsDefEqU 0 [] e (.natLit (Nat.gcd a b)) := by
    intro fuel a b e hG hWT hlt
    refine VEnv.natLit_defeq_of_fuel_relation henv
      (G := fun fuel p e => G fuel p.1 p.2 e)
      (WT := fun e => env.IsDefEqU 0 [] e e)
      (fun p => p.1) (fun p => Nat.gcd p.1 p.2)
      (fun p => match p with
        | (0, b) => .done b
        | (a + 1, b) => .recur (b % (a + 1), a + 1) id)
      ?_ ?_ ?_ fuel (a, b) e hG hWT hlt
    · rintro ⟨a, b⟩
      cases a with
      | zero => simp [FuelStep.out]
      | succ a => simp [FuelStep.out, Nat.gcd_succ]
    · rintro ⟨a, b⟩ next post hs
      cases a with
      | zero => cases hs
      | succ a =>
        cases hs
        exact Nat.mod_lt b (Nat.succ_pos a)
    · rintro fuel ⟨a, b⟩ e hG hWT
      cases a with
      | zero => simpa using hgo fuel 0 b e hG hWT
      | succ a =>
        obtain ⟨e', hG', hstep⟩ := by
          simpa using hgo fuel (a + 1) b e hG hWT
        exact ⟨e', hG', hstep.symm.trans henv trivial hstep,
          fun q hq => hstep.trans henv trivial hq⟩
  obtain ⟨e, hG, htop⟩ := htop a b
  exact (hcfApp a b).trans henv trivial <|
    htop.trans henv trivial (goEval (a + 1) a b e hG
      (htop.symm.trans henv trivial htop) (by omega))

theorem VEnv.boolNatITE_same_of_true_equation {env : VEnv}
    {ite cond A B : VExpr} {n : Nat} (henv : env.WF)
    (hnatTy₀ : env.IsType 0 [] .nat)
    (hnatTy₁ : env.IsType 0 [.nat] .nat)
    (hnatT : ∀ n Γ, env.HasType 0 Γ (.natLit n) .nat)
    (hiteT : env.HasType 0 [] ite (.forallE A B))
    (htrueT : env.HasType 0 [] .boolTrue A)
    (hcond : env.IsDefEqU 0 [] cond .boolTrue)
    (htrue : env.IsDefEqU 0 [] (.app ite .boolTrue)
      (.lam .nat <| .lam .nat <| .bvar 1)) :
    env.IsDefEqU 0 []
      (.app (.app (.app ite cond) (.natLit n)) (.natLit n))
      (.natLit n) := by
  have hcond' := hcond.of_r henv trivial htrueT
  have hiteCond : env.IsDefEqU 0 []
      (.app ite cond) (.app ite .boolTrue) :=
    ⟨_, .appDF hiteT hcond'⟩
  have hselect := hiteCond.trans henv trivial htrue
  have ⟨_, hnatSort⟩ := hnatTy₀
  have ⟨_, hnatSort₁⟩ := hnatTy₁
  have hinner : env.HasType 0 [.nat] (.lam .nat <| .bvar 1)
      (.forallE .nat .nat) := .lam hnatSort₁ (.bvar (.succ .zero))
  have hselector : env.HasType 0 []
      (.lam .nat <| .lam .nat <| .bvar 1)
      (.forallE .nat <| .forallE .nat .nat) :=
    .lam hnatSort hinner
  have hselectT := hselect.of_r henv trivial hselector
  have hnatClosed : VExpr.nat.ClosedN :=
    ((hnatT 0 []).closedN' henv.ordered.closed trivial).2.2
  have hnatLitClosed : (VExpr.natLit n).ClosedN :=
    ((hnatT n []).closedN' henv.ordered.closed trivial).1
  have h₁ : env.IsDefEq 0 []
      (.app (.app ite cond) (.natLit n))
      (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit n))
      (.forallE .nat .nat) := by
    simpa [VExpr.inst, hnatClosed.instN_eq] using
      (VEnv.IsDefEq.appDF hselectT (hnatT n []))
  have h₂ : env.IsDefEqU 0 []
      (.app (.app (.app ite cond) (.natLit n)) (.natLit n))
      (.app (.app (.lam .nat <| .lam .nat <| .bvar 1)
        (.natLit n)) (.natLit n)) :=
    ⟨_, .appDF h₁ (hnatT n [])⟩
  have hbeta₁ : env.IsDefEqU 0 []
      (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit n))
      (.lam .nat <| .natLit n) := by
    simpa [VExpr.inst, VExpr.inst_lift, hnatClosed.instN_eq,
      hnatLitClosed.lift_eq, hnatLitClosed.instN_eq] using
      (show env.IsDefEqU 0 []
        (.app (.lam .nat <| .lam .nat <| .bvar 1) (.natLit n))
        ((VExpr.lam .nat <| .bvar 1).inst (.natLit n)) from
          ⟨_, VEnv.IsDefEq.beta hinner (hnatT n [])⟩)
  have hbeta₁App := hbeta₁.app_same henv trivial
    (.app hselector (hnatT n [])) (hnatT n [])
  have hbody : env.HasType 0 [.nat] (.natLit n) .nat :=
    hnatT n [.nat]
  have hbeta₂ : env.IsDefEqU 0 []
      (.app (.lam .nat <| .natLit n) (.natLit n)) (.natLit n) := by
    simpa [VExpr.inst, hnatClosed.instN_eq,
      hnatLitClosed.instN_eq] using
      (show env.IsDefEqU 0 []
        (.app (.lam .nat <| .natLit n) (.natLit n))
        ((VExpr.natLit n).inst (.natLit n)) from
          ⟨_, VEnv.IsDefEq.beta hbody (hnatT n [])⟩)
  exact h₂.trans henv trivial <|
    hbeta₁App.trans henv trivial hbeta₂

/-- Instantiate the certified eager-fuel equation at a concrete numeral. -/
theorem VEnv.instantiate_eager_natLit_equation {env : VEnv}
    {r : NatWellFoundedCoreResult} {l rr : VExpr}
    (henv : env.WF)
    (hl : TrExprS env [] [] r.expectedEagerLhs l)
    (hr : TrExprS env [] [] r.expectedEagerRhs rr)
    (heq : env.IsDefEqU 0 [] l rr)
    (hnatS : TrExprS env [] [] (.natLitToConstructor n) (.natLit n))
    (hnatT : ∀ n Γ, env.HasType 0 Γ (.natLit n) .nat) :
    ∃ eager ite cond A B,
      TrExprS env [] []
        (r.eagerFn.instantiate1' (.natLitToConstructor n)) eager ∧
      TrExprS env [] [] Condition.bool.boolNatITE ite ∧
      TrExprS env [] []
        (mkApp2 (.const ``Nat.beq []) (.natLitToConstructor n)
          (.natLitToConstructor n)) cond ∧
      env.HasType 0 [] ite (.forallE A B) ∧
      env.HasType 0 [] cond A ∧
      env.IsDefEqU 0 [] (.app eager (.natLit n))
        (.app (.app (.app ite cond) (.natLit n)) (.natLit n)) := by
  unfold NatWellFoundedCoreResult.expectedEagerLhs at hl
  unfold NatWellFoundedCoreResult.expectedEagerRhs at hr
  cases hl with
  | lam hnatTy hnat hbodyL =>
    cases hr with
    | lam _ hnat' hbodyR =>
      cases hnat
      case const =>
       rename_i ci us hc hus hlen
       simp at hus
       subst us
       have hu : ci.uvars = 0 := hlen.symm
       cases hnat'
       case const =>
        rename_i ci' us' hc' hus' hlen' htype
        simp at hus'
        subst us'
        have hu' : ci'.uvars = 0 := hlen'.symm
        cases hbodyL with
      | app heagerT hbvarT heager hbvar =>
        cases hbvar with
        | bvar hb =>
          simp [VLCtx.find?, VLCtx.next] at hb
          rcases hb with ⟨rfl, rfl⟩
          cases hbodyR with
          | app hR2T hbvar2T hR2 hbvar2 =>
            cases hbvar2 with
            | bvar hb2 =>
              simp [VLCtx.find?, VLCtx.next] at hb2
              rcases hb2 with ⟨rfl, rfl⟩
              cases hR2 with
              | app _ _ hR1 hbvar1 =>
                cases hbvar1 with
                | bvar hb1 =>
                  simp [VLCtx.find?, VLCtx.next] at hb1
                  rcases hb1 with ⟨rfl, rfl⟩
                  cases hR1 with
                  | app hiteT hcondT hite hcond =>
                    rename_i eagerV eagerA eagerB outerA outerB midA midB
                      midArgT iteV iteA iteB condV innerAppT
                    have ⟨_, hnatSort⟩ :=
                      (hnatT 0 []).isType henv trivial
                    have hbodyLT := VEnv.HasType.app heagerT hbvarT
                    have hbodyRT := VEnv.HasType.app hR2T hbvar2T
                    have happ := heq.app_same henv trivial
                      (.lam hnatSort hbodyLT) (hnatT n [])
                    have hbetaL : env.IsDefEqU 0 []
                        (.app (.lam .nat (.app eagerV (.bvar 0)))
                          (.natLit n))
                        ((VExpr.app eagerV (.bvar 0)).inst (.natLit n)) :=
                      ⟨_, .beta hbodyLT (hnatT n [])⟩
                    have hbetaR : env.IsDefEqU 0 []
                        (.app (.lam .nat
                          (.app (.app (.app iteV condV) (.bvar 0))
                            (.bvar 0))) (.natLit n))
                        ((VExpr.app (.app (.app iteV condV) (.bvar 0))
                          (.bvar 0)).inst (.natLit n)) :=
                      ⟨_, .beta hbodyRT (hnatT n [])⟩
                    have hi := hbetaL.symm.trans henv trivial happ
                      |>.trans henv trivial hbetaR
                    have heager' := TrExprS.inst (Us := []) (Δ := [])
                      (A₀ := .nat) (e₀' := .natLit n) henv.ordered
                      (hnatT n []) heager hnatS
                    have hite' := TrExprS.inst (Us := []) (Δ := [])
                      (A₀ := .nat) (e₀' := .natLit n) henv.ordered
                      (hnatT n []) hite hnatS
                    have hcond' := TrExprS.inst (Us := []) (Δ := [])
                      (A₀ := .nat) (e₀' := .natLit n) henv.ordered
                      (hnatT n []) hcond hnatS
                    have hiteT' :=
                      hiteT.instN henv.ordered .zero (hnatT n [])
                    have hcondT' :=
                      hcondT.instN henv.ordered .zero (hnatT n [])
                    refine ⟨eagerV.inst (.natLit n),
                      iteV.inst (.natLit n), condV.inst (.natLit n),
                      iteA.inst (.natLit n), iteB.inst (.natLit n) 1,
                      ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · exact heager'
                    · simpa [Condition.boolNatITE, Condition.bool,
                        Expr.instantiate1', Expr.looseBVarRange'] using hite'
                    · simpa [mkApp2, mkApp, mkAppB, Expr.instantiate1',
                        Expr.looseBVarRange'] using hcond'
                    · simpa [VLCtx.toCtx, VExpr.inst] using hiteT'
                    · simpa [VLCtx.toCtx, VExpr.inst] using hcondT'
                    · simpa [VExpr.inst, VExpr.inst_lift] using hi

/-- Normalize the checked `Bool.true` selector equation to the translation
of `boolNatITE` used by the eager-fuel equation. -/
theorem VEnv.boolNatITE_true_of_equation {env : VEnv}
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
    have hzT := (TrExprS.natZero hprim hnat
      (Us := []) (Δ := [])).2
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
      simp [VLCtx.find?, VLCtx.next, VLocalDecl.depth,
        VLocalDecl.value, VLocalDecl.type, VExpr.lift, VExpr.liftN,
        VExpr.nat, liftVar])
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

/-- The eager fuel retained by a normalized auxiliary certificate evaluates
to every concrete numeral. -/
theorem VEnv.eager_natLit_of_aux_equations {env : VEnv}
    (wf : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) (hbeqC : env.contains ``Nat.beq)
    {r : NatWellFoundedCoreResult} {el er tl tr : VExpr}
    (hel : TrExprS env [] [] r.expectedEagerLhs el)
    (her : TrExprS env [] [] r.expectedEagerRhs er)
    (heeq : env.IsDefEqU 0 [] el er)
    (htl : TrExprS env [] [] r.expectedBoolTrueLhs tl)
    (htr : TrExprS env [] [] r.expectedBoolTrueRhs tr)
    (hteq : env.IsDefEqU 0 [] tl tr) :
    ∃ eager,
      TrExprS env [] [] (r.eagerFn.instantiate1'
        (.natLitToConstructor n)) eager ∧
      env.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n) := by
  have ⟨hnatLitS, _hnatT0⟩ :=
    TrExprS.natLit hprim hnat n (Us := []) (Δ := [])
  cases hnatLitS with
  | lit _ hnatS =>
    have hnatT (n Γ) : env.HasType 0 Γ (.natLit n) .nat :=
      (TrExprS.natLit hprim hnat n
        (Us := []) (Δ := [])).2.weak0 wf
    obtain ⟨eager, ite, cond, A, B, heagerS, hiteS, hcondS,
      hiteT, hcondT, heagerEq⟩ :=
      VEnv.instantiate_eager_natLit_equation wf hel her heeq hnatS hnatT
    obtain ⟨A', B', hiteT', htrueT, htrueEq⟩ :=
      VEnv.boolNatITE_true_of_equation wf hprim hnat
        htl htr hteq hiteS
    have ⟨hbeqT, hbeqEval⟩ := hprim.natBEq hbeqC
    obtain ⟨ci, hci, _, hlen⟩ :=
      (hbeqT 0 []).const_inv wf trivial
    have hbeqS : TrExprS env [] [] (.const ``Nat.beq [])
        (.const ``Nat.beq []) := .const hci rfl hlen
    have hbeqNS : TrExprS env [] []
        (mkApp (.const ``Nat.beq []) (.natLitToConstructor n))
        (.app (.const ``Nat.beq []) (.natLit n)) :=
      .app (hbeqT 0 []) (hnatT n []) hbeqS hnatS
    have hbeqNT := VEnv.HasType.app (hbeqT 0 []) (hnatT n [])
    have hcondCanon : TrExprS env [] []
        (mkApp2 (.const ``Nat.beq []) (.natLitToConstructor n)
          (.natLitToConstructor n))
        (.app (.app (.const ``Nat.beq []) (.natLit n)) (.natLit n)) :=
      .app hbeqNT (hnatT n []) hbeqNS hnatS
    have hcondEq := hcondS.uniq wf
      (.refl wf (U := 0) (Δ := []) (by trivial)) hcondCanon
    have hcondTrue := hcondEq.trans wf trivial
      (by simpa [VLCtx.toCtx] using hbeqEval n n)
    have hnatTy₀ := (hnatT 0 []).isType wf trivial
    obtain ⟨u, hNatSort⟩ := hnatTy₀
    have hnatTy₁ : env.IsType 0 [.nat] .nat :=
      ⟨u, hNatSort.weak0 wf⟩
    have hselected := VEnv.boolNatITE_same_of_true_equation
      (n := n) wf ⟨u, hNatSort⟩ hnatTy₁ hnatT hiteT' htrueT
      hcondTrue htrueEq
    exact ⟨eager, heagerS, heagerEq.trans wf trivial hselected⟩

private theorem Expr.natLitToConstructor_lift {n s d : Nat} :
    (Expr.natLitToConstructor n).liftLooseBVars' s d =
      .natLitToConstructor n :=
  Expr.liftLooseBVars_eq_self
    (Nat.le_trans
      (Closed.natLitToConstructor (k := 0)).looseBVarRange_le
      (Nat.zero_le s))

private theorem Expr.natLitToConstructor_inst {n : Nat} {a : Expr}
    {d : Nat} :
    (Expr.natLitToConstructor n).instantiate1' a d =
      .natLitToConstructor n :=
  Expr.instantiate1'_eq_self
    (Nat.le_trans
      (Closed.natLitToConstructor (k := 0)).looseBVarRange_le
      (Nat.zero_le d))

private theorem Expr.instantiate1'_closed {e a : Expr} {d : Nat}
    (h : e.looseBVarRange' = 0) : e.instantiate1' a d = e :=
  Expr.instantiate1'_eq_self (h ▸ Nat.zero_le d)

/-- Weaken a closed translation into a context extended by one lambda. -/
private theorem TrExprS.weak0_vlam {env : VEnv} (wf : env.WF)
    {e : Expr} {v A : VExpr}
    (h : TrExprS env [] [] e v) (hv : v.ClosedN) :
    TrExprS env [] [(none, .vlam A)] e v := by
  have hw := h.weakBV wf.ordered
    (.skip (.vlam A) (.refl : VLCtx.BVLift [] [] 0 0 0 0))
  simp only [Nat.zero_add, VLocalDecl.depth] at hw
  have hlift : e.liftLooseBVars' 0 1 = e :=
    Expr.liftLooseBVars_eq_self h.closed.looseBVarRange_le
  rw [hlift] at hw
  simpa [hv.lift_eq] using hw

/-- Renormalize both components of a translated compiler-selected state. -/
private theorem NatGcdFixCertificate.stateExpr_canon {env : VEnv}
    (wf : env.WF) {r : NatGcdFixCertificate} {ea eb ea' eb' : Expr}
    {stateV A aCanon bCanon aV' bV' : VExpr}
    (hstate : TrExprS env [] [] (r.stateExpr ea eb) stateV)
    (hstateT : env.HasType 0 [] stateV A)
    (haCanon : TrExprS env [] [] ea aCanon)
    (hbCanon : TrExprS env [] [] eb bCanon)
    (haEq : env.IsDefEqU 0 [] aCanon aV')
    (hbEq : env.IsDefEqU 0 [] bCanon bV')
    (haS' : TrExprS env [] [] ea' aV')
    (hbS' : TrExprS env [] [] eb' bV') :
    ∃ stateV', TrExprS env [] [] (r.stateExpr ea' eb') stateV' ∧
      env.IsDefEqU 0 [] stateV stateV' ∧
      env.HasType 0 [] stateV' A := by
  cases hstate with
  | app hmkAT hbT hmkA hbS =>
    cases hmkA with
    | app hmkT haT hmk haS =>
      have haEqC := (haS.uniq wf
        (.refl wf (U := 0) (Δ := []) (by trivial)) haCanon).trans wf
        trivial haEq
      have hbEqC := (hbS.uniq wf
        (.refl wf (U := 0) (Δ := []) (by trivial)) hbCanon).trans wf
        trivial hbEq
      have hmkAEq := haEqC.app_arg wf trivial hmkT haT
      have hstateEq := hmkAEq.app_both wf trivial hbEqC hmkAT hbT
      have haV'T := (haEqC.of_l wf trivial haT).hasType.2
      have hbV'T := (hbEqC.of_l wf trivial hbT).hasType.2
      have hmkA'T := (hmkAEq.of_l wf trivial hmkAT).hasType.2
      exact ⟨_, .app hmkA'T hbV'T (.app hmkT haV'T hmk haS') hbS',
        hstateEq, (hstateEq.of_l wf trivial hstateT).hasType.2⟩

/-- Canonicalize the closed prefix of a semantic gcd call. -/
private theorem VEnv.gcdGo_call_canon {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatConstructors env)
    {r : NatGcdFixCertificate}
    {goV fuelV stateV hpV fuelLit stateCanon A : VExpr}
    {fuelSrc stateSrc : Expr}
    (hgo : TrExprS env [] [] r.core.goFn goV)
    (hfuelSrcS : TrExprS env [] [] fuelSrc fuelLit)
    (hstateSrcS : TrExprS env [] [] stateSrc stateCanon)
    (hfuelEq : env.IsDefEqU 0 [] fuelV fuelLit)
    (hstateEq : env.IsDefEqU 0 [] stateV stateCanon)
    (heT : env.HasType 0 []
      (.app (.app (.app (.app (.app goV .natZero) .natZero) fuelV)
        stateV) hpV) A) :
    ∃ hpTy hpBodyTy,
      TrExprS env [] []
        (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
          fuelSrc stateSrc)
        (.app (.app (.app (.app goV .natZero) .natZero) fuelLit)
          stateCanon) ∧
      env.HasType 0 [] hpV hpTy ∧
      env.HasType 0 []
        (.app (.app (.app (.app goV .natZero) .natZero) fuelLit)
          stateCanon) (.forallE hpTy hpBodyTy) ∧
      env.IsDefEqU 0 []
        (.app (.app (.app (.app (.app goV .natZero) .natZero) fuelV)
          stateV) hpV)
        (.app (.app (.app (.app (.app goV .natZero) .natZero) fuelLit)
          stateCanon) hpV) := by
  obtain ⟨hpA, hpB, hprefixT, hpT⟩ := heT.app_inv wf.ordered trivial
  obtain ⟨stateA, stateB, hfuelPrefixT, hstateT⟩ :=
    hprefixT.app_inv wf.ordered trivial
  obtain ⟨fuelA, fuelB, hgoZerosT, hfuelT⟩ :=
    hfuelPrefixT.app_inv wf.ordered trivial
  obtain ⟨z2A, z2B, hgoZ1T, hz2T⟩ :=
    hgoZerosT.app_inv wf.ordered trivial
  obtain ⟨z1A, z1B, hgoT, hz1T⟩ :=
    hgoZ1T.app_inv wf.ordered trivial
  have hzS := (hctors.natZeroS (Us := []) (Δ := [])).1
  have hlitFuelT := (hfuelEq.of_l wf trivial hfuelT).hasType.2
  have hfuelPrefixEq := hfuelEq.app_arg wf trivial hgoZerosT hfuelT
  have hcanonFuelPrefixT :=
    (hfuelPrefixEq.of_l wf trivial hfuelPrefixT).hasType.2
  have hstateCanonT := (hstateEq.of_l wf trivial hstateT).hasType.2
  have hcanonPrefixEq := hfuelPrefixEq.app_both wf trivial hstateEq
    hfuelPrefixT hstateT
  have hcanonPrefixT :=
    (hcanonPrefixEq.of_l wf trivial hprefixT).hasType.2
  refine ⟨hpA, hpB, ?_, hpT, hcanonPrefixT,
    hcanonPrefixEq.app_same wf trivial hprefixT hpT⟩
  exact .app hcanonFuelPrefixT hstateCanonT
    (.app hgoZerosT hlitFuelT
      (.app hgoZ1T hz2T (.app hgoT hz1T hgo hzS) hzS) hfuelSrcS)
    hstateSrcS

/-- Semantic relation represented by the translated recursive calls retained
in a gcd fixpoint certificate. -/
def VEnv.GcdGoCall (env : VEnv) (r : NatGcdFixCertificate)
    (fuel a b : Nat) (e : VExpr) : Prop :=
  ∃ goV fuelV stateV hpE hpV,
    TrExprS env [] [] r.core.goFn goV ∧
    TrExprS env [] []
      (r.stateExpr (.natLitToConstructor a) (.natLitToConstructor b))
      stateV ∧
    TrExprS env [] [] hpE hpV ∧
    env.IsDefEqU 0 [] fuelV (.natLit fuel) ∧
    e = .app (.app (.app (.app (.app goV .natZero) .natZero) fuelV)
      stateV) hpV

/-- The normalized top equation places each gcd application in the semantic
recursive-call relation at fuel `a + 1`. -/
theorem NatGcdFixCertificate.top_semantics {env : VEnv}
    (wf : env.WF) (hctors : VEnv.HasNatConstructors env)
    {r : NatGcdFixCertificate} {gcd : Expr}
    (hgoClosed : r.core.goFn.looseBVarRange' = 0)
    (hstateClosed : r.core.stateFn.looseBVarRange' = 0) {l rr f : VExpr}
    (hl : TrExprS env [] [] (r.expectedTopLhs gcd) l)
    (hr : TrExprS env [] [] r.expectedTopRhs rr)
    (heq : env.IsDefEqU 0 [] l rr)
    (hgcd : TrExprS env [] [] gcd f)
    (hf : env.HasType 0 [] f (.forallE .nat <| .forallE .nat .nat))
    (heager : ∀ n, ∃ eager,
      TrExprS env [] [] q(WellFounded.Nat.eager) eager ∧
      env.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n)) :
    ∀ a b, ∃ e, VEnv.GcdGoCall env r (a+1) a b e ∧
      env.IsDefEqU 0 [] (.app (.app f (.natLit a)) (.natLit b)) e := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (hctors.natZeroS (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    refine ⟨?_, ⟨u, hnatTy⟩⟩
    exact .const hci rfl (by simpa using hlen)
  have lit (n) := hctors.natLitS n (Us := []) (Δ := [])
  intro a b
  have haT := (lit a).2
  have hbT := (lit b).2
  have haLitS := (lit a).1
  have hbLitS := (lit b).1
  cases haLitS with
  | lit _ haS =>
   cases hbLitS with
   | lit _ hbS =>
    simp only [NatGcdFixCertificate.expectedTopLhs] at hl
    unfold NatGcdFixCertificate.expectedTopRhs at hr
    obtain ⟨l₁, r₁, hl₁, hr₁, heq₁⟩ :=
      VEnv.instantiate_lam_equation wf (ty := q(Nat))
        (by trivial) hl hr heq hnatS haS haT (by trivial)
    obtain ⟨l₂, r₂, hl₂, hr₂, heq₂⟩ :=
      VEnv.instantiate_lam_equation wf (ty := q(Nat))
        (by trivial) hl₁ hr₁ heq₁ hnatS hbS hbT (by trivial)
    cases hr₂ with
    | app h4T hpT h4 hp =>
      cases h4 with
      | app h3T stateT h3 state =>
        cases h3 with
        | app h2T fuelT h2 fuel =>
          cases h2 with
          | app h1T hz2T h1 hz2 =>
            cases h1 with
            | app hgoT hz1T hgo hz1 =>
              rename_i hpA hpB hpV stateA stateB stateV fuelA fuelB fuelV
                z2A z2B z2V goV goA goB z1V
              simp only [Expr.instantiate1'_closed hgoClosed] at hgo
              have hzCanon :=
                (hctors.natZeroS (Us := []) (Δ := [])).1
              have hz1' : TrExprS env [] [] q(Nat.zero) z1V := by
                simpa [Expr.instantiate1',
                  Expr.instantiate1'_closed (e := q(Nat.zero)) (by rfl)]
                  using hz1
              have hz2' : TrExprS env [] [] q(Nat.zero) z2V := by
                simpa [Expr.instantiate1',
                  Expr.instantiate1'_closed (e := q(Nat.zero)) (by rfl)]
                  using hz2
              cases hz1'.unique (by trivial) hzCanon
              cases hz2'.unique (by trivial) hzCanon
              have hstate : TrExprS env [] []
                  (r.stateExpr (.natLitToConstructor a)
                    (.natLitToConstructor b)) stateV := by
                simpa [Literal.toConstructor,
                  Expr.natLitToConstructor_lift,
                  Expr.natLitToConstructor_inst, Expr.instantiate1',
                  Expr.looseBVarRange', NatGcdFixCertificate.stateExpr,
                  Expr.instantiate1'_closed hstateClosed,
                  mkApp2, mkApp, mkAppB] using state
              obtain ⟨eager, heagerS, heagerEq⟩ := heager (a+1)
              have hsuccS :=
                (hctors.natSuccS (Us := []) (Δ := [])).1
              have hsuccT :=
                (hctors.natSuccS (Us := []) (Δ := [])).2
              have hsaS : TrExprS env [] []
                  (mkApp q(Nat.succ) (.natLitToConstructor a))
                  (.natLit (a+1)) := .app hsuccT haT hsuccS haS
              have hfuelCanon : TrExprS env [] []
                  (mkApp q(WellFounded.Nat.eager)
                    (mkApp q(Nat.succ) (.natLitToConstructor a)))
                  (.app eager (.natLit (a+1))) := by
                obtain ⟨_, heagerAppEq⟩ := heagerEq
                obtain ⟨_, _, heagerT, heagerArgT⟩ :=
                  heagerAppEq.hasType.1.app_inv wf.ordered trivial
                exact .app heagerT heagerArgT heagerS hsaS
              have hfuel : TrExprS env [] []
                  (mkApp q(WellFounded.Nat.eager)
                    (mkApp q(Nat.succ) (.natLitToConstructor a)))
                  fuelV := by
                simpa [Literal.toConstructor,
                  Expr.natLitToConstructor_lift,
                  Expr.natLitToConstructor_inst, Expr.instantiate1',
                  Expr.looseBVarRange', mkApp, mkAppB] using fuel
              have hfuelEq := hfuel.uniq wf
                (.refl wf (U := 0) (Δ := []) (by trivial)) hfuelCanon
              have hfuelEval := hfuelEq.trans wf trivial heagerEq
              refine ⟨.app (.app (.app (.app (.app goV .natZero)
                .natZero) fuelV) stateV) hpV, ?_, ?_⟩
              · refine ⟨goV, fuelV, stateV, _, hpV, hgo, hstate, hp,
                  hfuelEval, rfl⟩
              · have hgcdClosed := hgcd.closed.looseBVarRange_zero
                have hcall : TrExprS env [] []
                    (mkApp2 gcd (.natLitToConstructor a)
                      (.natLitToConstructor b))
                    (.app (.app f (.natLit a)) (.natLit b)) := by
                  have hfaS : TrExprS env [] []
                      (mkApp gcd (.natLitToConstructor a))
                      (.app f (.natLit a)) := .app hf haT hgcd haS
                  exact .app (VEnv.HasType.app hf haT) hbT hfaS hbS
                have hl₂' : TrExprS env [] []
                    (mkApp2 gcd (.natLitToConstructor a)
                      (.natLitToConstructor b)) l₂ := by
                  simpa [Literal.toConstructor,
                    Expr.natLitToConstructor_lift,
                    Expr.natLitToConstructor_inst, Expr.instantiate1',
                    Expr.looseBVarRange',
                    Expr.instantiate1'_closed hgcdClosed,
                    mkApp2, mkApp, mkAppB] using hl₂
                have hcallEq := hcall.uniq wf
                  (.refl wf (U := 0) (Δ := []) (by trivial)) hl₂'
                exact hcallEq.trans wf trivial heq₂

/-- A certified zero equation reduces a well-typed gcd call whose first
state component is zero to its second component. -/
theorem NatGcdFixCertificate.zero_semantics {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatConstructors env)
    {r : NatGcdFixCertificate}
    (hstateClosed : r.core.stateFn.looseBVarRange' = 0)
    {l rr : VExpr}
    (hl : TrExprS env [] [] r.expectedZeroLhs l)
    (hr : TrExprS env [] [] r.expectedZeroRhs rr)
    (heq : env.IsDefEqU 0 [] l rr) :
    ∀ fuel b e, VEnv.GcdGoCall env r (fuel+1) 0 b e →
      env.IsDefEqU 0 [] e e → env.IsDefEqU 0 [] e (.natLit b) := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (hctors.natZeroS (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    refine ⟨?_, ⟨u, hnatTy⟩⟩
    exact .const hci rfl (by simpa using hlen)
  have lit (n) := hctors.natLitS n (Us := []) (Δ := [])
  intro fuel b e hG heSelf
  rcases hG with ⟨goV, fuelV, stateV, hpE, hpV, hgo, hstate, hpS,
    hfuelEq, rfl⟩
  have hfT := (lit fuel).2
  have hbT := (lit b).2
  cases (lit fuel).1 with
  | lit _ hfS =>
   cases (lit b).1 with
   | lit _ hbS =>
    unfold NatGcdFixCertificate.expectedZeroLhs at hl
    unfold NatGcdFixCertificate.expectedZeroRhs at hr
    obtain ⟨l₁, r₁, hl₁, hr₁, heq₁⟩ :=
      VEnv.instantiate_lam_equation wf (ty := q(Nat))
        (by trivial) hl hr heq hnatS hfS hfT (by trivial)
    obtain ⟨l₂, r₂, hl₂, hr₂, heq₂⟩ :=
      VEnv.instantiate_lam_equation wf (ty := q(Nat))
        (by trivial) hl₁ hr₁ heq₁ hnatS hbS hbT (by trivial)
    cases hl₂ with
    | lam hptyL hptySL hbodyL =>
      cases hr₂ with
      | lam hptyR hptySR hbodyR =>
        cases hbodyL with
        | app hprefixCertT hbvarT hprefixCert hbvar =>
          cases hbvar with
          | bvar hb =>
            simp [VLCtx.find?, VLCtx.next] at hb
            rcases hb with ⟨rfl, rfl⟩
            rename_i proofTyL bodyL proofTyR bodyR prefixCert certA certB
            obtain ⟨_, heSelfD⟩ := heSelf
            have heT := heSelfD.hasType.1
            have hsuccS := (hctors.natSuccS (Us := []) (Δ := [])).1
            have hsuccT := (hctors.natSuccS (Us := []) (Δ := [])).2
            have hsfS : TrExprS env [] []
                (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                (.natLit (fuel+1)) := .app hsuccT hfT hsuccS hfS
            obtain ⟨_, hstateT₀⟩ := hstate.wf wf.ordered
              (Us := []) (Δ := []) trivial
            have hzeroRefl : env.IsDefEqU 0 [] .natZero .natZero :=
              .refl ⟨_, (lit 0).2⟩
            have hbRefl : env.IsDefEqU 0 []
                (.natLit b) (.natLit b) := .refl ⟨_, hbT⟩
            have hzeroCtorS : TrExprS env [] []
                (.natLitToConstructor 0) (.natLit 0) := by
              cases (lit 0).1 with
              | lit _ h => exact h
            obtain ⟨stateCanon, hstateZero, hstateEq, -⟩ :=
              NatGcdFixCertificate.stateExpr_canon wf hstate hstateT₀
                hzeroCtorS hbS hzeroRefl hbRefl
                (hctors.natZeroS (Us := []) (Δ := [])).1 hbS
            obtain ⟨hpA, hpB, hprefixS, hpT, hprefixCallT, hcallEq⟩ :=
              VEnv.gcdGo_call_canon wf hctors hgo hsfS hstateZero
                hfuelEq hstateEq heT
            have hprefixWeak := TrExprS.weak0_vlam wf (A := bodyL)
              hprefixS
              (hprefixCallT.closedN' wf.ordered.closed trivial).1
            have hprefixCert' : TrExprS env [] [(none, .vlam bodyL)]
                (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                  (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                  (r.stateExpr q(Nat.zero)
                    (.natLitToConstructor b))) prefixCert := by
              have hgoClosed := hgo.closed.looseBVarRange_zero
              simpa [pure, Literal.toConstructor,
                Expr.natLitToConstructor_lift,
                Expr.natLitToConstructor_inst, Expr.instantiate1',
                Expr.instantiate1'_closed hgoClosed,
                Expr.instantiate1'_closed hstateClosed,
                Expr.looseBVarRange', NatGcdFixCertificate.stateExpr,
                mkApp2, mkApp, mkAppB] using hprefixCert
            have hprefixEq := TrExprS.uniq (Us := []) wf
              (.refl wf (U := 0) (Δ := [(none, .vlam bodyL)])
                ⟨trivial, nofun, hptyL⟩) hprefixCert' hprefixWeak
            obtain ⟨hpTR, hinst⟩ :=
              VEnv.finish_bitwise_proof_equation wf hptyL hprefixCertT
                hbvarT hprefixCallT hpT hprefixEq heq₂
            have hrightInstS := TrExprS.inst (Us := []) (Δ := [])
              wf.ordered hpTR hbodyR hpS
            have hrightS : TrExprS env [] []
                (.natLitToConstructor b) (bodyR.inst hpV) := by
              simpa [Literal.toConstructor,
                Expr.natLitToConstructor_lift,
                Expr.natLitToConstructor_inst, Expr.instantiate1',
                Expr.looseBVarRange'] using hrightInstS
            have hrightEq := hrightS.uniq wf
              (.refl wf (U := 0) (Δ := []) (by trivial)) hbS
            exact hcallEq.trans wf trivial hinst
              |>.trans wf trivial hrightEq

/-- A certified successor equation produces the Euclidean recursive call at
one less unit of fuel. -/
theorem NatGcdFixCertificate.succ_semantics {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatConstructors env)
    (hmodC : env.contains ``Nat.mod)
    (hmod : env.ReflectsNatNatNat ``Nat.mod Nat.mod)
    {r : NatGcdFixCertificate}
    (hstateClosed : r.core.stateFn.looseBVarRange' = 0)
    {l rr : VExpr}
    (hl : TrExprS env [] [] r.expectedSuccLhs l)
    (hr : TrExprS env [] [] r.expectedSuccRhs rr)
    (heq : env.IsDefEqU 0 [] l rr) :
    ∀ fuel a b e, VEnv.GcdGoCall env r (fuel+1) (a+1) b e →
      env.IsDefEqU 0 [] e e →
      ∃ e', VEnv.GcdGoCall env r fuel (b % (a+1)) (a+1) e' ∧
        env.IsDefEqU 0 [] e e' := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (hctors.natZeroS (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    refine ⟨?_, ⟨u, hnatTy⟩⟩
    exact .const hci rfl (by simpa using hlen)
  have lit (n) := hctors.natLitS n (Us := []) (Δ := [])
  intro fuel a b e hG heSelf
  rcases hG with ⟨goV, fuelV, stateV, hpE, hpV, hgo, hstate, hpS,
    hfuelEq, rfl⟩
  have hfT := (lit fuel).2
  have haT := (lit a).2
  have hbT := (lit b).2
  cases (lit fuel).1 with
  | lit _ hfS =>
   cases (lit a).1 with
   | lit _ haS =>
    cases (lit b).1 with
    | lit _ hbS =>
     cases (lit (a+1)).1 with
     | lit _ hsaCtorS =>
      cases (lit (b % (a+1))).1 with
      | lit _ hremS =>
       unfold NatGcdFixCertificate.expectedSuccLhs at hl
       unfold NatGcdFixCertificate.expectedSuccRhs at hr
       obtain ⟨l₁, r₁, hl₁, hr₁, heq₁⟩ :=
         VEnv.instantiate_lam_equation wf (ty := q(Nat))
           (by trivial) hl hr heq hnatS hfS hfT (by trivial)
       obtain ⟨l₂, r₂, hl₂, hr₂, heq₂⟩ :=
         VEnv.instantiate_lam_equation wf (ty := q(Nat))
           (by trivial) hl₁ hr₁ heq₁ hnatS haS haT (by trivial)
       obtain ⟨l₃, r₃, hl₃, hr₃, heq₃⟩ :=
         VEnv.instantiate_lam_equation wf (ty := q(Nat))
           (by trivial) hl₂ hr₂ heq₂ hnatS hbS hbT (by trivial)
       cases hl₃ with
       | lam hptyL hptySL hbodyL =>
        cases hr₃ with
        | lam hptyR hptySR hbodyR =>
         cases hbodyL with
         | app hprefixCertT hbvarT hprefixCert hbvar =>
          cases hbvar with
          | bvar hb =>
            simp [VLCtx.find?, VLCtx.next] at hb
            rcases hb with ⟨rfl, rfl⟩
            rename_i bodyL proofTyR bodyR prefixCert certA certB
            obtain ⟨_, heSelfD⟩ := heSelf
            have heT := heSelfD.hasType.1
            have hsuccS := (hctors.natSuccS (Us := []) (Δ := [])).1
            have hsuccT := (hctors.natSuccS (Us := []) (Δ := [])).2
            have hsfS : TrExprS env [] []
                (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                (.natLit (fuel+1)) := .app hsuccT hfT hsuccS hfS
            have hsaS : TrExprS env [] []
                (mkApp q(Nat.succ) (.natLitToConstructor a))
                (.natLit (a+1)) := .app hsuccT haT hsuccS haS
            obtain ⟨_, hstateT₀⟩ := hstate.wf wf.ordered
              (Us := []) (Δ := []) trivial
            have hsaRefl : env.IsDefEqU 0 []
                (.natLit (a+1)) (.natLit (a+1)) :=
              .refl ⟨_, (lit (a+1)).2⟩
            have hbRefl : env.IsDefEqU 0 []
                (.natLit b) (.natLit b) := .refl ⟨_, hbT⟩
            obtain ⟨stateCanon, hstateSucc, hstateEq, -⟩ :=
              NatGcdFixCertificate.stateExpr_canon wf hstate hstateT₀
                hsaCtorS hbS hsaRefl hbRefl hsaS hbS
            obtain ⟨hpA, hpB, hprefixS, hpT, hprefixCallT, hcallEq⟩ :=
              VEnv.gcdGo_call_canon wf hctors hgo hsfS hstateSucc
                hfuelEq hstateEq heT
            have hprefixWeak := TrExprS.weak0_vlam wf (A := bodyL)
              hprefixS
              (hprefixCallT.closedN' wf.ordered.closed trivial).1
            have hprefixCert' : TrExprS env [] [(none, .vlam bodyL)]
                (mkApp2 (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                  (mkApp q(Nat.succ) (.natLitToConstructor fuel))
                  (r.stateExpr
                    (mkApp q(Nat.succ) (.natLitToConstructor a))
                    (.natLitToConstructor b))) prefixCert := by
              have hgoClosed := hgo.closed.looseBVarRange_zero
              simpa [pure, Literal.toConstructor,
                Expr.natLitToConstructor_lift,
                Expr.natLitToConstructor_inst, Expr.instantiate1',
                Expr.instantiate1'_closed hgoClosed,
                Expr.instantiate1'_closed hstateClosed,
                Expr.looseBVarRange', NatGcdFixCertificate.stateExpr,
                mkApp2, mkApp, mkAppB] using hprefixCert
            have hprefixEq := TrExprS.uniq (Us := []) wf
              (.refl wf (U := 0) (Δ := [(none, .vlam bodyL)])
                ⟨trivial, nofun, hptyL⟩) hprefixCert' hprefixWeak
            obtain ⟨hpTR, hinst⟩ :=
              VEnv.finish_bitwise_proof_equation wf hptyL hprefixCertT
                hbvarT hprefixCallT hpT hprefixEq heq₃
            have hleftToRight := hcallEq.trans wf trivial hinst
            have hrightInstS := TrExprS.inst (Us := []) (Δ := [])
              wf.ordered hpTR hbodyR hpS
            let proofSpec :=
              (((r.succProof.instantiate1'
                    (.natLitToConstructor fuel) 3)
                  |>.instantiate1' (.natLitToConstructor a) 2)
                  |>.instantiate1' (.natLitToConstructor b) 1)
                  |>.instantiate1' hpE
            have hrightS : TrExprS env [] []
                (mkAppN (mkApp2 r.core.goFn q(Nat.zero) q(Nat.zero))
                  #[.natLitToConstructor fuel,
                    r.stateExpr
                      (mkApp2 q(Nat.mod) (.natLitToConstructor b)
                        (mkApp q(Nat.succ) (.natLitToConstructor a)))
                      (mkApp q(Nat.succ) (.natLitToConstructor a)),
                    proofSpec])
                (bodyR.inst hpV) := by
              have hgoClosed := hgo.closed.looseBVarRange_zero
              simpa [mkAppN, proofSpec, Literal.toConstructor,
                NatGcdFixCertificate.stateExpr, Expr.instantiate1',
                Expr.natLitToConstructor_lift,
                Expr.natLitToConstructor_inst,
                Expr.instantiate1'_closed hgoClosed,
                Expr.instantiate1'_closed hstateClosed,
                mkApp2, mkApp, mkAppB] using hrightInstS
            generalize heRight : bodyR.inst hpV = rightV
              at hrightS hleftToRight
            cases hrightS with
            | app hrightPrefixT hproofSpecT hrightPrefix hproofSpecS =>
             cases hrightPrefix with
             | app hrightFuelT hrightStateT hrightFuel hrightState =>
              cases hrightFuel with
              | app hrightZerosT hrightFuelArgT hrightZeros hrightFuelArg =>
               simp at hproofSpecS hrightState hrightFuelArg
               cases hrightZeros with
               | app hrightGoZ1T hrightZ2T hrightGoZ1 hrightZ2 =>
                cases hrightGoZ1 with
                | app hrightGoT hrightZ1T hrightGo hrightZ1 =>
                  rename_i proofArgA proofArgB proofV
                    stateArgA stateArgB stateR
                    fuelArgA fuelArgB fuelR
                    z2ArgA z2ArgB z2V
                    goR z1ArgA z1ArgB z1V
                  have hzS :=
                    (hctors.natZeroS (Us := []) (Δ := [])).1
                  cases hrightZ1.unique (by trivial) hzS
                  cases hrightZ2.unique (by trivial) hzS
                  have hrightFuelEq := hrightFuelArg.uniq wf
                    (.refl wf (U := 0) (Δ := []) (by trivial)) hfS
                  have ⟨hmodT, hmodEval⟩ := hmod hmodC
                  obtain ⟨modCi, hmodCi, _, hmodLen⟩ :=
                    (hmodT 0 []).const_inv wf trivial
                  have hmodS : TrExprS env [] [] q(Nat.mod)
                      (.const ``Nat.mod []) :=
                    .const hmodCi rfl hmodLen
                  have hsaT := VEnv.HasType.app hsuccT haT
                  have hmodBS : TrExprS env [] []
                      (mkApp q(Nat.mod) (.natLitToConstructor b))
                      (.app (.const ``Nat.mod []) (.natLit b)) :=
                    .app (hmodT 0 []) hbT hmodS hbS
                  have hmodCallS : TrExprS env [] []
                      (mkApp2 q(Nat.mod) (.natLitToConstructor b)
                        (mkApp q(Nat.succ) (.natLitToConstructor a)))
                      (.app (.app (.const ``Nat.mod []) (.natLit b))
                        (.natLit (a+1))) :=
                    .app (VEnv.HasType.app (hmodT 0 []) hbT) hsaT
                      hmodBS hsaS
                  obtain ⟨stateNext, hstateNextS, hstateNextEq, -⟩ :=
                    NatGcdFixCertificate.stateExpr_canon wf hrightState
                      hrightStateT hmodCallS hsaS (hmodEval b (a+1))
                      hsaRefl hremS hsaCtorS
                  have hrightFuelPrefixEq := hrightFuelEq.app_arg wf
                    trivial hrightZerosT hrightFuelArgT
                  have hrightStatePrefixEq :=
                    hrightFuelPrefixEq.app_both wf trivial hstateNextEq
                      hrightFuelT hrightStateT
                  have hrightCallEq := hrightStatePrefixEq.app_same wf
                    trivial hrightPrefixT hproofSpecT
                  have hfuelSelf := hrightFuelEq.symm.trans wf trivial
                    hrightFuelEq
                  refine ⟨.app (.app (.app (.app (.app goR .natZero)
                    .natZero) (.natLit fuel)) stateNext) proofV, ?_,
                    hleftToRight.trans wf trivial hrightCallEq⟩
                  exact ⟨goR, .natLit fuel, stateNext, proofSpec, proofV,
                    hrightGo, hstateNextS, hproofSpecS, hfuelSelf, rfl⟩

/-- Every normalized generic-state certificate reflects Euclid's gcd. -/
theorem NatGcdFixCertificate.NormalizedValid.reflects
    {c : TypeChecker.VContext} {env : VEnv}
    {r : NatGcdFixCertificate} {gcd : Expr} {f : VExpr}
    (hv : r.NormalizedValid c gcd)
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hle : c.venv ≤ env) (hwf : env.WF)
    (hnat : c.venv.contains ``Nat)
    (hbeqC : c.venv.contains ``Nat.beq)
    (hmodC : c.venv.contains ``Nat.mod)
    (hmod : c.venv.ReflectsNatNatNat ``Nat.mod Nat.mod)
    (hgcd : TrExprS env [] [] gcd f)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.gcd [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.gcd []) f) :
    env.ReflectsNatNatNat ``Nat.gcd Nat.gcd := by
  rcases hv with ⟨hcore, htop, hzero, hsucc⟩
  rcases hcore.normalizeAux with ⟨heager, htrue, _hfalse⟩
  rcases heager with ⟨el, er, hel, her, heeq⟩
  rcases htrue with ⟨tl, tr, htl, htr, hteq⟩
  rcases htop with ⟨topL, topR, htopL, htopR, htopEq⟩
  rcases hzero with ⟨zeroL, zeroR, hzeroL, hzeroR, hzeroEq⟩
  rcases hsucc with ⟨succL, succR, hsuccL, hsuccR, hsuccEq⟩
  change TrExprS c.venv c.lparams c.vlctx
    r.core.expectedEagerLhs el at hel
  change TrExprS c.venv c.lparams c.vlctx
    r.core.expectedEagerRhs er at her
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx el er at heeq
  change TrExprS c.venv c.lparams c.vlctx
    r.core.expectedBoolTrueLhs tl at htl
  change TrExprS c.venv c.lparams c.vlctx
    r.core.expectedBoolTrueRhs tr at htr
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx tl tr at hteq
  change TrExprS c.venv c.lparams c.vlctx
    (r.expectedTopLhs gcd) topL at htopL
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedTopRhs topR at htopR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
    topL topR at htopEq
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedZeroLhs zeroL at hzeroL
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedZeroRhs zeroR at hzeroR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
    zeroL zeroR at hzeroEq
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedSuccLhs succL at hsuccL
  change TrExprS c.venv c.lparams c.vlctx
    r.expectedSuccRhs succR at hsuccR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
    succL succR at hsuccEq
  rw [hlparams, hvlctx] at hel her heeq htl htr hteq
  rw [hlparams, hvlctx] at htopL htopR htopEq
  rw [hlparams, hvlctx] at hzeroL hzeroR hzeroEq
  rw [hlparams, hvlctx] at hsuccL hsuccR hsuccEq
  have hprim := c.hasPrimitives
  have hctors := VEnv.HasNatConstructors.of_primitives hprim hnat
  have baseWf := c.Ewf
  have heager' (n) := VEnv.eager_natLit_of_aux_equations
    baseWf hprim hnat hbeqC hel her heeq htl htr hteq (n := n)
  have heagerCanon (n) : ∃ eager,
      TrExprS env [] [] q(WellFounded.Nat.eager) eager ∧
      env.IsDefEqU 0 [] (.app eager (.natLit n)) (.natLit n) := by
    have h := show ∃ eager,
        TrExprS c.venv [] [] q(WellFounded.Nat.eager) eager ∧
        c.venv.IsDefEqU 0 []
          (.app eager (.natLit n)) (.natLit n) by
      simpa [hcore.eagerFn_eq, Expr.instantiate1'] using heager' n
    rcases h with ⟨eager, hs, heq⟩
    exact ⟨eager, hs.mono hle, heq.mono hle⟩
  have hctors' := hctors.mono hle
  have hmodC' : env.contains ``Nat.mod :=
    let ⟨ci, hci⟩ := hmodC
    ⟨ci, hle.constants hci⟩
  have hmod' : env.ReflectsNatNatNat ``Nat.mod Nat.mod := by
    intro _
    exact ⟨fun U Γ => ((hmod hmodC).1 U Γ).mono hle,
      fun x y => ((hmod hmodC).2 x y).mono hle⟩
  have hfValue := (hcf.of_l hwf trivial (hf 0 [])).hasType.2
  have htop' := NatGcdFixCertificate.top_semantics hwf hctors'
    hcore.goFn_closed hcore.stateFn_closed
    (htopL.mono hle) (htopR.mono hle) (htopEq.mono hle)
    hgcd hfValue heagerCanon
  have hzero' := NatGcdFixCertificate.zero_semantics hwf hctors'
    hcore.stateFn_closed
    (hzeroL.mono hle) (hzeroR.mono hle) (hzeroEq.mono hle)
  have hsucc' := NatGcdFixCertificate.succ_semantics hwf hctors'
    hmodC' hmod' hcore.stateFn_closed
    (hsuccL.mono hle) (hsuccR.mono hle) (hsuccEq.mono hle)
  have hzeroT (Γ) : env.HasType 0 Γ .natZero .nat :=
    (hctors'.natZeroS (Us := []) (Δ := [])).2.weak0 hwf
  have hsuccT (Γ) : env.HasType 0 Γ .natSucc
      (.forallE .nat .nat) :=
    (hctors'.natSuccS (Us := []) (Δ := [])).2.weak0 hwf
  apply VEnv.ReflectsNatNatNat.of_gcd_fix_relation hwf
    hzeroT hsuccT hf hcf (VEnv.GcdGoCall env r) htop'
  intro fuel a b e hG he
  by_cases ha : a = 0
  · subst a
    simpa using hzero' fuel b e hG he
  · cases a with
    | zero => contradiction
    | succ a => simpa using hsucc' fuel a b e hG he

/-- Replace the old/vacuous `Nat.gcd` reflection field after inserting the
checked definition, while transporting every unrelated primitive fact. -/
theorem VEnv.HasPrimitives.addNatGcd {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.gcd ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatNat ``Nat.gcd Nat.gcd) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' :=
    (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.gcd ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : ``Nat.gcd ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) :
      env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolType := fun H => h.boolType (by
      change env''.constants ``Bool = some _ at H
      rwa [same ``Bool (by decide)] at H)
    boolFalse := fun H => h.boolFalse (by
      change env''.constants ``Bool.false = some _ at H
      rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      change env''.constants ``Bool.true = some _ at H
      rwa [same ``Bool.true (by decide)] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      change env''.constants ``Nat.zero = some _ at H
      rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      change env''.constants ``Nat.succ = some _ at H
      rwa [same ``Nat.succ (by decide)] at H)
    natPred := (h.natPred.addConst hadd (by decide)).addDefEq
    natAdd := (h.natAdd.addConst hadd (by decide)).addDefEq
    natSub := (h.natSub.addConst hadd (by decide)).addDefEq
    natMul := (h.natMul.addConst hadd (by decide)).addDefEq
    natPow := (h.natPow.addConst hadd (by decide)).addDefEq
    natGcd := href
    natMod := (h.natMod.addConst hadd (by decide)).addDefEq
    natDiv := (h.natDiv.addConst hadd (by decide)).addDefEq
    natBEq := (h.natBEq.addConst hadd (by decide)).addDefEq
    natBLE := (h.natBLE.addConst hadd (by decide)).addDefEq
    natBitwise := (h.natBitwise.addConst hadd (by decide)).addDefEq
    natLAnd := (h.natLAnd.addConst hadd (by decide)).addDefEq
    natLOr := (h.natLOr.addConst hadd (by decide)).addDefEq
    natXor := (h.natXor.addConst hadd (by decide)).addDefEq
    natShiftLeft :=
      (h.natShiftLeft.addConst hadd (by decide)).addDefEq
    natShiftRight :=
      (h.natShiftRight.addConst hadd (by decide)).addDefEq
    charOfNat := fun H => by
      obtain ⟨hu, hty⟩ := h.charOfNat (by
        change env''.constants ``Char.ofNat = some _ at H
        rwa [same ``Char.ofNat (by decide)] at H)
      exact ⟨hu, fun U Γ => (hty U Γ).mono le⟩
    stringOfList := fun H => by
      change env''.constants ``String.ofList = some _ at H
      rw [same ``String.ofList (by decide)] at H
      obtain ⟨hu, hty, hnil, hcons⟩ := h.stringOfList H
      exact ⟨hu, fun U Γ => (hty U Γ).mono le,
        hnil.mono le, hcons.mono le⟩ }

/-- Adding a definition accepted by the generic-state certificate preserves
the primitive reflection package. -/
theorem NatGcdFixCertificate.NormalizedValid.conservesHasPrimitives
    {c : TypeChecker.VContext} {base env' : VEnv}
    {r : NatGcdFixCertificate} {gcd : Expr} {v : VDefVal}
    (hv : r.NormalizedValid c gcd)
    (hlparams : c.lparams = []) (hvlctx : c.vlctx = [])
    (hnat : c.venv.contains ``Nat)
    (hbeqC : c.venv.contains ``Nat.beq)
    (hmodC : c.venv.contains ``Nat.mod)
    (hmod : c.venv.ReflectsNatNatNat ``Nat.mod Nat.mod)
    (hgcd : TrExprS c.venv [] [] gcd v.value)
    (hname : v.name = ``Nat.gcd)
    (hbase : base.HasPrimitives) (hbaseMono : c.venv ≤ base)
    (hadd : base.addConst ``Nat.gcd v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : c.venv.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat)) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have hle : c.venv ≤ env'' :=
    hbaseMono.trans <|
      (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.gcd [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.gcd = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono hle) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have href := hv.reflects hlparams hvlctx hle hwf hnat hbeqC
    hmodC hmod (hgcd.mono hle) hf hcf
  exact VEnv.HasPrimitives.addNatGcd hbase hadd href

/-- Semantic evidence retained by a successful `Nat.gcd` primitive check. -/
abbrev NatGcdPrimitiveEvidence
    (c : VContext) (src : DefinitionVal) (ty' : VExpr) : Prop :=
  ∃ cert : NatGcdFixCertificate,
    src.levelParams = [] ∧
    c.venv.contains ``Nat ∧
    c.venv.contains ``Nat.beq ∧
    c.venv.contains ``Nat.mod ∧
    c.venv.IsDefEqU c.lparams.length [] ty'
      (.forallE .nat <| .forallE .nat .nat) ∧
    cert.Valid c ∧ cert.shape src.value = true

set_option maxHeartbeats 800000 in
theorem checkPrimitiveDef.natGcd_eq (hname : v.name = ``Nat.gcd) :
    checkPrimitiveDefCore v = (do
      let env ← getEnv
      let fail {α} : M α :=
        throw <| .other s!"invalid form for primitive def {v.name}"
      _ ← checkNatGcdPrimitive env v fail
      pure true) := by
  simp only [checkPrimitiveDefCore, hname]

set_option maxHeartbeats 800000 in
theorem checkNatGcdPrimitive.WF_typed {c : VContext} {s : VState}
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty') :
    M.WF c s (checkNatGcdPrimitive c.env v
      (throw <| .other s!"invalid form for primitive def {v.name}"))
      fun cert _ =>
        v.levelParams = [] ∧
        c.venv.contains ``Nat ∧
        c.venv.contains ``Nat.beq ∧
        c.venv.contains ``Nat.mod ∧
        c.venv.IsDefEqU c.lparams.length [] ty'
          (.forallE .nat <| .forallE .nat .nat) ∧
        cert.Valid c ∧ cert.shape v.value = true := by
  unfold checkNatGcdPrimitive
  dsimp only
  by_cases hdeps : (c.env.contains ``Nat.mod &&
      c.env.contains ``Nat.beq && v.levelParams.isEmpty) = true
  · rw [if_pos hdeps]
    have hdeps' : (c.env.contains ``Nat.mod = true ∧
        c.env.contains ``Nat.beq = true) ∧
        v.levelParams.isEmpty = true := by
      simpa using hdeps
    have hlevels : v.levelParams = [] := by
      simpa using hdeps'.2
    have hmodC : c.venv.contains ``Nat.mod :=
      VContext.contains_safe_primitive c hdeps'.1.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hbeqC : c.venv.contains ``Nat.beq :=
      VContext.contains_safe_primitive c hdeps'.1.2 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hnat := VEnv.ReflectsNatNatNat.nat_of_contains
      c.Ewf c.hasPrimitives.natMod hmodC
    have hcanon : c.TrExprS q(Nat → Nat → Nat)
        (.forallE .nat <| .forallE .nat .nat) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact TrExprS.natBinaryType_of_contains
        c.Ewf c.hasPrimitives hnat c.lparams []
    exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      by_cases hb : b = true
      · rw [if_pos hb]
        have htyEq0 := htyEq hb
        change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx ty'
          (.forallE .nat <| .forallE .nat .nat) at htyEq0
        rw [hvlctx] at htyEq0
        cases heq : natWellFoundedEquation v.value
            q(type_of% Nat.gcd.eq_def) with
        | none =>
          simp only
          exact .throw
        | some equation =>
          simp only
          by_cases hclosed :
              (!equation.hasFVar && !equation.hasMVar) = true
          · rw [if_pos hclosed]
            let .forallE hnatTy _ hnatS _ := hcanon
            exact (unfoldNatWellFoundedNat2Cert.WF
                hnatS hnatTy heq).bind fun _ _ _ _ =>
              checkNatGcdFixCertificate.WF.bind
                fun cert _ _ hcert => by
                  exact M.WF.sandbox.bind fun _ _ _ _ =>
                    .pure ⟨hlevels, hnat, hbeqC, hmodC,
                      htyEq0, hcert.1, hcert.2⟩
          · rw [if_neg hclosed]
            exact .throw
      · rw [if_neg hb]
        exact .throw
  · rw [if_neg hdeps]
    exact .throw

set_option maxHeartbeats 800000 in
theorem checkPrimitiveDef.natGcd.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.gcd)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      NatGcdPrimitiveEvidence c v ty' := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  rw [checkPrimitiveDef.natGcd_eq hname]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  exact (checkNatGcdPrimitive.WF_typed hvlctx hty).bind
    fun cert _ _ h => .pure fun _ => ⟨cert, h⟩

theorem NatGcdPrimitiveEvidence.conservesHasPrimitives
    {c : VContext} {src : DefinitionVal}
    {v : VDefVal} {base env' : VEnv}
    (hcparams : c.lparams = src.levelParams) (hvlctx : c.vlctx = [])
    (hgcd : c.TrExprS src.value v.value)
    (hname : v.name = ``Nat.gcd)
    (huvars : src.levelParams.length = v.uvars)
    (hbase : base.HasPrimitives) (hbaseMono : c.venv ≤ base)
    (hadd : base.addConst ``Nat.gcd v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hevidence : NatGcdPrimitiveEvidence c src v.type) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  rcases hevidence with
    ⟨cert, hsrcParams, hnat, hbeqC, hmodC, hty, hvalid, hshape⟩
  have hclparams : c.lparams = [] := hcparams.trans hsrcParams
  have hvuvars : v.uvars = 0 := by
    rw [← huvars, hsrcParams]
    rfl
  change TrExprS c.venv c.lparams c.vlctx _ _ at hgcd
  rw [hclparams, hvlctx] at hgcd
  rw [hclparams] at hty
  exact (hvalid.normalize hshape).conservesHasPrimitives
    hclparams hvlctx hnat hbeqC hmodC c.hasPrimitives.natMod
    hgcd hname hbase hbaseMono hadd hwf hvuvars hty

end Lean4Lean.Environment
