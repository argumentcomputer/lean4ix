/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.NatDivChecker
import Lean4Lean.Verify.NatModReflect

/-!
# Verified Nat.div reflection

This module connects the retained Nat.div checker evidence to operational
reflection for the checked fuel-indexed quotient implementation. It is a
trust-aware adaptation of upstream lean4lean PR #32 at
`6cfd43a48d17be85c76414638655c12ef9a7ee23`.
-/

namespace Lean4Lean.Environment
open Lean

/-- The primitive certificate's reducible lift builder is definitionally the
proof library's structural loose-bvar lift. This replaces PR #32's opaque
`Lean.Expr.liftLooseBVars_eq` assumption. -/
theorem primitiveLiftLooseBVars_eq (e : Expr) (s d : Nat) :
    primitiveLiftLooseBVars e s d = e.liftLooseBVars' s d := by
  induction e generalizing s <;>
    simp [primitiveLiftLooseBVars, Expr.liftLooseBVars', *]

private theorem translated_closed
    {env : VEnv} (wf : env.WF) {e : Expr} {eV : VExpr}
    (h : TrExprS env [] [] e eV) : eV.ClosedN := by
  obtain ⟨_, heWF⟩ := h.wf wf.ordered (Us := []) (Δ := []) trivial
  exact (heWF.hasType.1.closedN' wf.ordered.closed trivial).1

private theorem natLitToConstructor_closed (n : Nat) :
    (Expr.natLitToConstructor n).looseBVarRange' = 0 := by
  cases n <;> simp [Expr.natLitToConstructor, Expr.natZero, Expr.natSucc,
    Expr.looseBVarRange']

private theorem translated_lifted_natConstructor
    {env : VEnv} (hctors : VEnv.HasNatBoolConstructors env)
    (n : Nat) (Δ : VLCtx) :
    TrExprS env [] Δ
      (primitiveLiftLooseBVars (Expr.natLitToConstructor n) 0 1)
      (.natLit n) := by
  rw [primitiveLiftLooseBVars_eq]
  have hnLit := hctors.natLitS n (Us := []) (Δ := Δ)
  cases hnLit.1 with
  | lit _ hnS =>
    have hlift : (Expr.natLitToConstructor n).liftLooseBVars' 0 1 =
        Expr.natLitToConstructor n := by
      exact Expr.liftLooseBVars_eq_self (e := Expr.natLitToConstructor n)
        (s := 0) (d := 1) (by
        rw [natLitToConstructor_closed]
        omega)
    rw [hlift]
    simpa [Literal.toConstructor] using hnS

private theorem translated_nat_type_eq
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {Δ : VLCtx} (hΔ : Δ.WF env 0) {natV : VExpr}
    (hnatV : TrExprS env [] Δ q(Nat) natV) :
    env.IsDefEqU 0 Δ.toCtx natV .nat := by
  have hzT := (hctors.natZeroS (Us := []) (Δ := Δ)).2
  obtain ⟨_, hnatType⟩ := hzT.isType wf hΔ.toCtx
  obtain ⟨ci, hci, _, hlen⟩ := hnatType.const_inv wf hΔ.toCtx
  have hnatS : TrExprS env [] Δ q(Nat) .nat :=
    .const hci rfl (by simpa using hlen)
  exact TrExprS.uniq (Us := []) wf (.refl wf hΔ) hnatV hnatS

private theorem translated_bvar_target_eq
    {env : VEnv} {Δ : VLCtx} {i : Nat} {e e₀ : VExpr}
    (hcanon : ∃ A, Δ.find? (.inl i) = some (e₀, A))
    (h : TrExprS env Us Δ (.bvar i) e) : e = e₀ := by
  rcases hcanon with ⟨A₀, hcanon⟩
  cases h with
  | bvar hfind =>
    rw [hcanon] at hfind
    cases hfind
    rfl

/-- The exact source expression obtained by instantiating the two binders of
the closed top-level division equation. -/
def natDivTopRhsInst (a b : Nat) : Expr :=
  ((natDivTopRhs (.bvar 1) (.bvar 0)).instantiate1'
    (.natLitToConstructor a) 1).instantiate1' (.natLitToConstructor b)

theorem natDivTopRhsInst_eq (a b : Nat) :
    natDivTopRhsInst a b =
      natDivTopRhs (.natLitToConstructor a) (.natLitToConstructor b) := by
  simp [natDivTopRhsInst, natDivTopRhs, Condition.reflectedDITE,
    Condition.natLE, Reflection.natDITE, Reflection.defn₁,
    primitiveLiftLooseBVars_eq, Lean.Expr.instantiate1', Lean.mkAppN,
    Expr.lam0, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]
  constructor
  · simp [Lean.Expr.instantiate1', Expr.liftLooseBVars']
  · simpa [Expr.liftLooseBVars', Lean.Expr.instantiate1'] using
      (Expr.instantiate1'_liftLooseBVars
        (e := .natLitToConstructor a) (a := .natLitToConstructor b)
        (s := 0) (d := 1))

def natDivTopPropInst (b : Nat) : Expr :=
  mkApp2 q(@LE.le Nat _) q(Nat.succ Nat.zero) (.natLitToConstructor b)

def natDivTopBleInst (b : Nat) : Expr :=
  mkApp2 q(Nat.ble) q(Nat.succ Nat.zero) (.natLitToConstructor b)

def natDivTopProofInst (b : Nat) : Expr :=
  match Condition.natLE.impl with
  | .reflectNatNat _ _ proof =>
    mkAppN proof #[q(Nat.succ Nat.zero), .natLitToConstructor b]
  | .bool => q(False.elim)

def natDivTopThenBodyInst (a b : Nat) : Expr :=
  let x := primitiveLiftLooseBVars (Expr.natLitToConstructor a) 0 1
  let y := primitiveLiftLooseBVars (Expr.natLitToConstructor b) 0 1
  mkApp5 q(Nat.div.go) y (.bvar 0) (mkApp q(Nat.succ) x) x
    (mkApp q(Nat.lt_succ_self) x)

def natDivTopThenInst (a b : Nat) : Expr :=
  .lam0 (natDivTopPropInst b) (natDivTopThenBodyInst a b)

def natDivTopElseInst (b : Nat) : Expr :=
  .lam0 (mkApp q(Not) (natDivTopPropInst b)) q(Nat.zero)

def natDivGoThenBody (y hy fuel x h : Expr) : Expr :=
  let succ := mkApp q(Nat.succ)
  let sub := mkApp2 q(Nat.sub)
  let go := mkApp5 q(Nat.div.go)
  succ (go (primitiveLiftLooseBVars y 0 1)
    (primitiveLiftLooseBVars hy 0 1)
    (primitiveLiftLooseBVars fuel 0 1)
    (sub (primitiveLiftLooseBVars x 0 1)
      (primitiveLiftLooseBVars y 0 1))
    (mkApp6 q(@Nat.div_rec_fuel_lemma)
      (primitiveLiftLooseBVars x 0 1)
      (primitiveLiftLooseBVars y 0 1)
      (primitiveLiftLooseBVars fuel 0 1)
      (primitiveLiftLooseBVars hy 0 1)
      (.bvar 0) (primitiveLiftLooseBVars h 0 1)))

def natDivGoThen (y hy fuel x h : Expr) : Expr :=
  .lam0 (natDivGoProp y x) (natDivGoThenBody y hy fuel x h)

def natDivGoElse (y x : Expr) : Expr :=
  .lam0 (mkApp q(Not) (natDivGoProp y x)) q(Nat.zero)

theorem natDivGoRhsBody_eq_parts (y hy fuel x h : Expr) :
    natDivGoRhsBody y hy fuel x h =
      mkApp5 Reflection.defn₁.natDITE (natDivGoProp y x)
        (natDivGoBle y x) (natDivGoProof y x)
        (natDivGoThen y hy fuel x h) (natDivGoElse y x) := by
  rfl

/-- Instantiate the closed top-level division equation at two concrete
naturals, retaining the translated reflected-selector RHS. -/
theorem VEnv.instantiate_natDivTop_equation
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {divFn : Expr} {divV topL topR : VExpr}
    (hdivFn : TrExprS env [] [] divFn divV)
    (hdivFnClosed : divFn.looseBVarRange' = 0)
    (hl : TrExprS env [] [] (natDivTopEquation divFn).1 topL)
    (hr : TrExprS env [] [] (natDivTopEquation divFn).2 topR)
    (heq : env.IsDefEqU 0 [] topL topR)
    (a b : Nat) :
    ∃ rhs,
      TrExprS env [] []
        (natDivTopRhs (.natLitToConstructor a)
          (.natLitToConstructor b)) rhs ∧
      env.IsDefEqU 0 []
        (.app (.app divV (.natLit a)) (.natLit b)) rhs := by
  have ⟨hnatS, hnatTy⟩ : TrExprS env [] [] q(Nat) .nat ∧
      env.IsType 0 [] .nat := by
    have hzT := (hctors.natZeroS (Us := []) (Δ := [])).2
    obtain ⟨u, hnatTy⟩ := hzT.isType wf trivial
    obtain ⟨ci, hci, _, hlen⟩ := hnatTy.const_inv wf trivial
    exact ⟨.const hci rfl (by simpa using hlen), ⟨u, hnatTy⟩⟩
  have haLit := hctors.natLitS a (Us := []) (Δ := [])
  have hbLit := hctors.natLitS b (Us := []) (Δ := [])
  cases haLit.1 with
  | lit _ haS =>
    cases hbLit.1 with
    | lit _ hbS =>
      simp only [natDivTopEquation] at hl hr
      obtain ⟨l₁, r₁, hl₁, hr₁, heq₁⟩ :=
        VEnv.instantiate_lam_equation wf
          (ty := q(Nat)) (by trivial) hl hr heq hnatS haS haLit.2
          (by trivial)
      obtain ⟨l₂, r₂, hl₂, hr₂, heq₂⟩ :=
        VEnv.instantiate_lam_equation wf
          (ty := q(Nat)) (by trivial) hl₁ hr₁ heq₁ hnatS hbS hbLit.2
          (by trivial)
      have hr₂' : TrExprS env [] []
          (natDivTopRhs (.natLitToConstructor a)
            (.natLitToConstructor b)) r₂ := by
        rw [← natDivTopRhsInst_eq]
        simpa [natDivTopRhsInst, Literal.toConstructor] using hr₂
      cases hl₂ with
      | app hinnerT hbT hinner hbLocalS =>
        cases hinner with
        | app hfnT haT hfnLocalS haLocalS =>
          have hctx : VLCtx.IsDefEq env 0 [] [] := .refl wf trivial
          have hfnLocalS' := hfnLocalS
          simp [Expr.instantiate1'_eq_self (by rw [hdivFnClosed]; omega)]
            at hfnLocalS'
          have haLocalS' := haLocalS
          have hbLocalS' := hbLocalS
          simp [Lean.Expr.instantiate1', Expr.instantiate1'_liftLooseBVars_0]
            at haLocalS' hbLocalS'
          have hfnEq := TrExprS.uniq (Us := []) wf hctx hfnLocalS' hdivFn
          have haEq := TrExprS.uniq (Us := []) wf hctx haLocalS' haS
          have hbEq := TrExprS.uniq (Us := []) wf hctx hbLocalS' hbS
          have hfnApp := hfnEq.app_same wf trivial hfnT haT
          have hdivT := (hfnEq.of_l wf trivial hfnT).hasType.2
          have haApp := haEq.app_arg wf trivial hdivT haT
          have hinnerEq := hfnApp.trans wf trivial haApp
          have hinnerEqB := hinnerEq.app_same wf trivial hinnerT hbT
          have hclosedInnerT :=
            (hinnerEq.of_l wf trivial hinnerT).hasType.2
          have hbApp := hbEq.app_arg wf trivial hclosedInnerT hbT
          exact ⟨r₂, hr₂',
            (hinnerEqB.trans wf trivial hbApp).symm.trans wf trivial heq₂⟩

/-- Normalize a translated top-level division RHS to the canonical checked
dependent selector, then select the branch determined by `0 < b`. -/
theorem VEnv.select_natDivTop_rhs
    {env : VEnv} (wf : env.WF)
    (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    (cert : VEnv.NatLESelectorCertificate env)
    (a b : Nat) {rhs : VExpr}
    (hrhs : TrExprS env [] []
      (natDivTopRhs (.natLitToConstructor a)
        (.natLitToConstructor b)) rhs) :
    ∃ pV bleV HV tV eV,
      TrExprS env [] [] (natDivTopPropInst b) pV ∧
      TrExprS env [] [] (natDivTopBleInst b) bleV ∧
      TrExprS env [] [] (natDivTopProofInst b) HV ∧
      TrExprS env [] [] (natDivTopThenInst a b) tV ∧
      TrExprS env [] [] (natDivTopElseInst b) eV ∧
      if 0 < b then
        ∃ proof, env.IsDefEqU 0 [] rhs (.app tV proof)
      else
        ∃ proof, env.IsDefEqU 0 [] rhs (.app eV proof) := by
  simp only [natDivTopRhs, Condition.reflectedDITE, Condition.natLE,
    Reflection.natDITE, mkApp5, mkApp3, mkApp2, mkApp, mkAppB] at hrhs
  cases hrhs with
  | app h₄T heT h₄ heS =>
    rename_i A₄ B₄ eV
    cases h₄ with
    | app h₃T htT h₃ htS =>
      rename_i A₃ B₃ tV
      cases h₃ with
      | app h₂T hHT h₂ hHS =>
        rename_i A₂ B₂ HV
        cases h₂ with
        | app h₁T hbleT h₁ hbleS =>
          rename_i A₁ B₁ bleV
          cases h₁ with
          | app hditeT hpT hditeS hpS =>
            rename_i diteV A₀ B₀ pV
            have hctx : VLCtx.IsDefEq env 0 [] [] := .refl wf trivial
            have hditeEq := TrExprS.uniq (Us := []) wf hctx
              hditeS cert.rditeS
            have h₁Eq := hditeEq.app_same wf trivial hditeT hpT
            have h₂Eq := h₁Eq.app_same wf trivial h₁T hbleT
            have h₃Eq := h₂Eq.app_same wf trivial h₂T hHT
            have h₄Eq := h₃Eq.app_same wf trivial h₃T htT
            have hcallEq := h₄Eq.app_same wf trivial h₄T heT
            have hcallT := (hcallEq.of_l wf trivial
              (.app h₄T heT)).hasType.2
            have hpS' : TrExprS env [] [] (natDivTopPropInst b) pV := by
              simpa [natDivTopPropInst, Lean.mkAppN] using hpS
            have hbleS' : TrExprS env [] [] (natDivTopBleInst b) bleV := by
              simpa [natDivTopBleInst, Lean.mkAppN] using hbleS
            have hHS' : TrExprS env [] [] (natDivTopProofInst b) HV := by
              simpa [natDivTopProofInst, Condition.natLE, Lean.mkAppN] using hHS
            have htS' : TrExprS env [] [] (natDivTopThenInst a b) tV := by
              simpa [natDivTopThenInst, natDivTopThenBodyInst,
                natDivTopPropInst, Expr.lam0, Lean.mkAppN, mkApp5,
                mkApp4, mkApp2, mkApp, mkAppB]
                using htS
            have heS' : TrExprS env [] [] (natDivTopElseInst b) eV := by
              simpa [natDivTopElseInst, natDivTopPropInst,
                Expr.lam0, Lean.mkAppN] using heS
            refine ⟨pV, bleV, HV, tV, eV,
              hpS', hbleS', hHS', htS', heS', ?_⟩
            have honeS : TrExprS env [] [] q(Nat.succ Nat.zero)
                (.natLit 1) := by
              simpa [VExpr.natLit] using
                (TrExprS.app
                  (hctors.natSuccS (Us := []) (Δ := [])).2
                  (hctors.natZeroS (Us := []) (Δ := [])).2
                  (hctors.natSuccS (Us := []) (Δ := [])).1
                  (hctors.natZeroS (Us := []) (Δ := [])).1)
            have hbCtorS : TrExprS env [] []
                (.natLitToConstructor b) (.natLit b) := by
              have hbLit := hctors.natLitS b (Us := []) (Δ := [])
              cases hbLit.1 with
              | lit _ hbS => simpa [Literal.toConstructor] using hbS
            have hbool := Condition.natBLE_application_eval_of_args
              wf hbleR hctors hbleC honeS hbCtorS
              (by simpa [natDivTopBleInst, Lean.mkAppN] using hbleS')
            have heqs := cert.dite_equations wf
            split
            · rename_i hb
              have hble : Nat.ble 1 b = true :=
                Nat.ble_eq_true_of_le hb
              rw [hble] at hbool
              obtain ⟨proof, hselect⟩ :=
                VEnv.reflectionNatDITE_true_of_condition wf
                  (translated_closed wf cert.rtypeS)
                  (translated_closed wf cert.rditeS)
                  (translated_closed wf cert.ofTrueS)
                  heqs.1 cert.rditeHas hcallT hbool
              exact ⟨proof, hcallEq.trans wf trivial hselect⟩
            · rename_i hb
              have hnle : ¬1 ≤ b := by omega
              have hble : Nat.ble 1 b = false := by
                cases h : Nat.ble 1 b <;> simp_all [Nat.ble_eq]
              rw [hble] at hbool
              obtain ⟨proof, hselect⟩ :=
                VEnv.reflectionNatDITE_false_of_condition wf
                  (translated_closed wf cert.rtypeS)
                  (translated_closed wf cert.rditeS)
                  (translated_closed wf cert.ofFalseS)
                  heqs.2 cert.rditeHas hcallT hbool
              exact ⟨proof, hcallEq.trans wf trivial hselect⟩

/-- Expose and beta-reduce the selected true top-level division branch while
retaining the translated `Nat.div.go` body. -/
theorem VEnv.natDivTopThen_beta
    {env : VEnv} (wf : env.WF) (a b : Nat)
    {tV proof R : VExpr}
    (htS : TrExprS env [] [] (natDivTopThenInst a b) tV)
    (happT : env.HasType 0 [] (.app tV proof) R) :
    ∃ propV bodyV,
      tV = .lam propV bodyV ∧
      env.IsType 0 [] propV ∧
      TrExprS env [] [(none, .vlam propV)]
        (natDivTopThenBodyInst a b) bodyV ∧
      env.HasType 0 [] proof propV ∧
      env.IsDefEqU 0 [] (.app tV proof) (bodyV.inst proof) := by
  have htSLam : TrExprS env [] []
      (.lam `_ (natDivTopPropInst b) (natDivTopThenBodyInst a b)
        (default : BinderInfo))
      tV := by
    simpa only [natDivTopThenInst, Expr.lam0] using htS
  cases htSLam with
  | lam hdomType hdomS hbodyS =>
    rename_i propV bodyV
    have hlamS : TrExprS env [] []
        (.lam `_ (natDivTopPropInst b) (natDivTopThenBodyInst a b)
          (default : BinderInfo))
        (.lam propV bodyV) := .lam hdomType hdomS hbodyS
    obtain ⟨bodyTy, hlamCanonT⟩ := TrExprS.closedLam_hasType wf hlamS
    obtain ⟨_, _, hlamT, hproofT⟩ := happT.app_inv wf.ordered trivial
    have hlamTyEq := hlamT.uniqU wf trivial hlamCanonT
    obtain ⟨_, hdomEq⟩ := (hlamTyEq.forallE_inv wf trivial).1
    have hproofT' := hproofT.defeqU_r wf trivial hdomEq.toU
    obtain ⟨_, hbodyWF⟩ := hbodyS.wf wf.ordered
      (Us := []) (Δ := [(none, .vlam propV)])
      ⟨trivial, nofun, hdomType⟩
    exact ⟨propV, bodyV, rfl, hdomType, hbodyS, hproofT',
      ⟨_, VEnv.IsDefEq.beta hbodyWF.hasType.1 hproofT'⟩⟩

/-- Decompose the retained true-branch body into the six translations that
form its `Nat.div.go` call. -/
theorem VEnv.natDivTopThenBody_shape
    {env : VEnv} {propV bodyV : VExpr} (a b : Nat)
    (hbodyS : TrExprS env [] [(none, .vlam propV)]
      (natDivTopThenBodyInst a b) bodyV) :
    ∃ goV yV hyV fuelV xV hfuelV,
      bodyV = .app (.app (.app (.app (.app goV yV) hyV) fuelV) xV) hfuelV ∧
      TrExprS env [] [(none, .vlam propV)] q(Nat.div.go) goV ∧
      TrExprS env [] [(none, .vlam propV)]
        (primitiveLiftLooseBVars (Expr.natLitToConstructor b) 0 1) yV ∧
      TrExprS env [] [(none, .vlam propV)] (.bvar 0) hyV ∧
      TrExprS env [] [(none, .vlam propV)]
        (mkApp q(Nat.succ)
          (primitiveLiftLooseBVars (Expr.natLitToConstructor a) 0 1)) fuelV ∧
      TrExprS env [] [(none, .vlam propV)]
        (primitiveLiftLooseBVars (Expr.natLitToConstructor a) 0 1) xV ∧
      TrExprS env [] [(none, .vlam propV)]
        (mkApp q(Nat.lt_succ_self)
          (primitiveLiftLooseBVars (Expr.natLitToConstructor a) 0 1)) hfuelV := by
  simp only [natDivTopThenBodyInst, mkApp5, mkApp4, mkApp, mkAppB] at hbodyS
  cases hbodyS with
  | app h₄T hfuelT h₄ hfuelS =>
    rename_i A₄ B₄ hfuelV
    cases h₄ with
    | app h₃T hxT h₃ hxS =>
      rename_i A₃ B₃ xV
      cases h₃ with
      | app h₂T hfuelArgT h₂ hfuelArgS =>
        rename_i A₂ B₂ fuelV
        cases h₂ with
        | app h₁T hhyT h₁ hhyS =>
          rename_i A₁ B₁ hyV
          cases h₁ with
          | app hgoT hyT hgoS hyS =>
            rename_i goV A₀ B₀ yV
            exact ⟨goV, yV, hyV, fuelV, xV, hfuelV, rfl,
              hgoS, hyS, hhyS, hfuelArgS, hxS, hfuelS⟩

/-- Normalize the non-proof components of a retained true-branch body. -/
theorem VEnv.natDivTopThenBody_components
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {propV bodyV : VExpr} (hpropType : env.IsType 0 [] propV)
    (a b : Nat)
    (hbodyS : TrExprS env [] [(none, .vlam propV)]
      (natDivTopThenBodyInst a b) bodyV) :
    ∃ yV fuelV xV hfuelV,
      bodyV = .app (.app (.app (.app (.app (.const ``Nat.div.go []) yV)
        (.bvar 0)) fuelV) xV) hfuelV ∧
      env.IsDefEqU 0 [propV] yV (.natLit b) ∧
      env.IsDefEqU 0 [propV] fuelV (.natLit (a + 1)) ∧
      env.IsDefEqU 0 [propV] xV (.natLit a) := by
  obtain ⟨goV, yV, hyV, fuelV, xV, hfuelV, rfl,
    hgoS, hyS, hhyS, hfuelS, hxS, hlastS⟩ :=
    VEnv.natDivTopThenBody_shape a b hbodyS
  have hgoV : goV = .const ``Nat.div.go [] := by
    cases hgoS with
    | const _ hus _ =>
      simp at hus
      subst hus
      rfl
  subst goV
  have hhyV : hyV = .bvar 0 := by
    cases hhyS with
    | bvar hfind =>
      simp [VLCtx.find?, VLCtx.next] at hfind
      rcases hfind with ⟨rfl, rfl⟩
      rfl
  subst hyV
  have hctx : VLCtx.IsDefEq env 0
      [(none, .vlam propV)] [(none, .vlam propV)] :=
    .refl wf ⟨trivial, nofun, hpropType⟩
  have hyCanon := translated_lifted_natConstructor hctors b
    [(none, .vlam propV)]
  have hxCanon := translated_lifted_natConstructor hctors a
    [(none, .vlam propV)]
  have hsucc := hctors.natSuccS
    (Us := []) (Δ := [(none, .vlam propV)])
  have haT := (hctors.natLitS a
    (Us := []) (Δ := [(none, .vlam propV)])).2
  have hfuelCanon : TrExprS env [] [(none, .vlam propV)]
      (mkApp q(Nat.succ)
        (primitiveLiftLooseBVars (Expr.natLitToConstructor a) 0 1))
      (.natLit (a + 1)) := by
    simpa [VExpr.natLit, Nat.add_comm] using
      (TrExprS.app hsucc.2 haT hsucc.1 hxCanon)
  exact ⟨yV, fuelV, xV, hfuelV, rfl,
    TrExprS.uniq (Us := []) wf hctx hyS hyCanon,
    TrExprS.uniq (Us := []) wf hctx hfuelS hfuelCanon,
    TrExprS.uniq (Us := []) wf hctx hxS hxCanon⟩

/-- Instantiate the normalized true-branch body, retaining its translated
fuel proof as the second proof argument of `VExpr.natDivGo`. -/
theorem VEnv.natDivTopThenBody_inst
    {env : VEnv} (wf : env.WF)
    (hctors : VEnv.HasNatBoolConstructors env)
    {propV bodyV proof : VExpr}
    (hpropType : env.IsType 0 [] propV)
    (hproofT : env.HasType 0 [] proof propV)
    (a b : Nat)
    (hbodyS : TrExprS env [] [(none, .vlam propV)]
      (natDivTopThenBodyInst a b) bodyV) :
    ∃ hfuel, env.IsDefEqU 0 [] (bodyV.inst proof)
      (.natDivGo b (a + 1) a proof hfuel) := by
  obtain ⟨yV, fuelV, xV, hfuelV, hbody,
    hyEq, hfuelEq, hxEq⟩ :=
    VEnv.natDivTopThenBody_components wf hctors hpropType a b hbodyS
  subst bodyV
  obtain ⟨_, hbodyWF⟩ := hbodyS.wf wf.ordered
    (Us := []) (Δ := [(none, .vlam propV)])
    ⟨trivial, nofun, hpropType⟩
  have hΓ : OnCtx [propV] (env.IsType 0) := ⟨trivial, hpropType⟩
  obtain ⟨_, _, h₄T, hlastT⟩ := hbodyWF.hasType.1.app_inv wf.ordered hΓ
  obtain ⟨_, _, h₃T, hxT⟩ := h₄T.app_inv wf.ordered hΓ
  obtain ⟨_, _, h₂T, hfuelT⟩ := h₃T.app_inv wf.ordered hΓ
  obtain ⟨_, _, h₁T, hhyT⟩ := h₂T.app_inv wf.ordered hΓ
  obtain ⟨_, _, hgoT, hyT⟩ := h₁T.app_inv wf.ordered hΓ
  have h₁Eq := hyEq.app_arg wf hΓ hgoT hyT
  have h₂Eq := h₁Eq.app_same wf hΓ h₁T hhyT
  have h₂CanonT := (h₂Eq.of_l wf hΓ h₂T).hasType.2
  have h₃ArgEq := hfuelEq.app_arg wf hΓ h₂CanonT hfuelT
  have h₃Same := h₂Eq.app_same wf hΓ h₂T hfuelT
  have h₃Eq := h₃Same.trans wf hΓ h₃ArgEq
  have h₃CanonT := (h₃Eq.of_l wf hΓ h₃T).hasType.2
  have h₄ArgEq := hxEq.app_arg wf hΓ h₃CanonT hxT
  have h₄Same := h₃Eq.app_same wf hΓ h₃T hxT
  have h₄Eq := h₄Same.trans wf hΓ h₄ArgEq
  have hbodyEq := h₄Eq.app_same wf hΓ h₄T hlastT
  have hrightT := (hbodyEq.of_l wf hΓ hbodyWF.hasType.1).hasType.2
  obtain ⟨u, hpropSort⟩ := hpropType
  have hlamEq : env.IsDefEqU 0 []
      (.lam propV
        (.app (.app (.app (.app (.app (.const ``Nat.div.go []) yV)
          (.bvar 0)) fuelV) xV) hfuelV))
      (.lam propV
        (.app (.app (.app (.app (.app (.const ``Nat.div.go []) (.natLit b))
          (.bvar 0)) (.natLit (a + 1))) (.natLit a)) hfuelV)) := by
    obtain ⟨T, hbodyEq⟩ := hbodyEq
    exact ⟨.forallE propV T, .lamDF hpropSort hbodyEq⟩
  have hinst := VEnv.IsDefEqU.lam_instU wf trivial hlamEq hpropSort
    hbodyWF.hasType.1 hrightT hproofT
  have hbClosed : (VExpr.natLit b).ClosedN :=
    ((hctors.natLitS b (Us := []) (Δ := [])).2.closedN'
      wf.ordered.closed trivial).1
  have haClosed : (VExpr.natLit a).ClosedN :=
    ((hctors.natLitS a (Us := []) (Δ := [])).2.closedN'
      wf.ordered.closed trivial).1
  have hfuelClosed : (VExpr.natLit (a + 1)).ClosedN :=
    ((hctors.natLitS (a + 1) (Us := []) (Δ := [])).2.closedN'
      wf.ordered.closed trivial).1
  exact ⟨hfuelV.inst proof, by
    simpa [VExpr.natDivGo, VExpr.inst, VExpr.instVar,
      hbClosed.instN_eq, haClosed.instN_eq, hfuelClosed.instN_eq]
      using hinst⟩

/-- Beta-reduce the false top-level division branch to zero. -/
theorem VEnv.natDivTopElse_beta
    {env : VEnv} (wf : env.WF) (b : Nat)
    {eV proof R : VExpr}
    (heS : TrExprS env [] [] (natDivTopElseInst b) eV)
    (happT : env.HasType 0 [] (.app eV proof) R) :
    env.IsDefEqU 0 [] (.app eV proof) .natZero := by
  have heSLam := heS
  simp only [natDivTopElseInst] at heSLam
  have heSLam' : TrExprS env [] []
      (.lam `_ (mkApp q(Not) (natDivTopPropInst b)) q(Nat.zero)
        (default : BinderInfo))
      eV := by
    simpa only [Expr.lam0] using heSLam
  cases heSLam' with
  | lam hdomType hdomS hbodyS =>
    rename_i tyV bodyV
    have hlamS : TrExprS env [] []
        (.lam `_ (mkApp q(Not) (natDivTopPropInst b)) q(Nat.zero)
          (default : BinderInfo))
        (.lam tyV bodyV) := .lam hdomType hdomS hbodyS
    obtain ⟨bodyTy, hlamCanonT⟩ := TrExprS.closedLam_hasType wf hlamS
    obtain ⟨_, _, hlamT, hproofT⟩ := happT.app_inv wf.ordered trivial
    have hlamTyEq := hlamT.uniqU wf trivial hlamCanonT
    obtain ⟨_, hdomEq⟩ := (hlamTyEq.forallE_inv wf trivial).1
    have hproofT' := hproofT.defeqU_r wf trivial hdomEq.toU
    obtain ⟨_, hbodyWF⟩ := hbodyS.wf wf.ordered
      (Us := []) (Δ := [(none, .vlam _)])
      ⟨trivial, nofun, hdomType⟩
    cases hbodyS with
    | const hzero hus hlen =>
      simp at hus
      subst hus
      exact ⟨_, by simpa [VLCtx.toCtx, VExpr.inst, VExpr.natZero] using
        (VEnv.IsDefEq.beta hbodyWF.hasType.1 hproofT')⟩

/-- The checked closed top-level division equation has exactly the semantic
shape required by `ReflectsNatNatNat.of_divCore_equations`. -/
theorem VEnv.natDivTop_semantics
    {env : VEnv} (wf : env.WF)
    (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    (cert : VEnv.NatLESelectorCertificate env)
    {divFn : Expr} {divV topL topR : VExpr}
    (hdivFn : TrExprS env [] [] divFn divV)
    (hdivFnClosed : divFn.looseBVarRange' = 0)
    (hdivT : env.HasType 0 [] divV
      (.forallE .nat <| .forallE .nat .nat))
    (hl : TrExprS env [] [] (natDivTopEquation divFn).1 topL)
    (hr : TrExprS env [] [] (natDivTopEquation divFn).2 topR)
    (heq : env.IsDefEqU 0 [] topL topR) :
    ∀ a b,
      if 0 < b then
        ∃ hy hfuel,
          env.HasType 0 [] (.natDivGo b (a + 1) a hy hfuel) .nat ∧
          env.IsDefEqU 0 []
            (.app (.app divV (.natLit a)) (.natLit b))
            (.natDivGo b (a + 1) a hy hfuel)
      else
        env.IsDefEqU 0 []
          (.app (.app divV (.natLit a)) (.natLit b)) .natZero := by
  intro a b
  obtain ⟨rhs, hrhs, htop⟩ := VEnv.instantiate_natDivTop_equation
    wf hctors hdivFn hdivFnClosed hl hr heq a b
  obtain ⟨pV, bleV, HV, tV, eV, hpS, hbleS, hHS, htS, heS, hselect⟩ :=
    VEnv.select_natDivTop_rhs wf hbleR hctors hbleC cert a b hrhs
  have haT := (hctors.natLitS a (Us := []) (Δ := [])).2
  have hbT := (hctors.natLitS b (Us := []) (Δ := [])).2
  have hcallT : env.HasType 0 []
      (.app (.app divV (.natLit a)) (.natLit b)) .nat :=
    .app (.app hdivT haT) hbT
  have hrhsT := (htop.of_l wf trivial hcallT).hasType.2
  split
  · rename_i hb
    rw [if_pos hb] at hselect
    obtain ⟨proof, hselect⟩ := hselect
    have hbranchT := (hselect.of_l wf trivial hrhsT).hasType.2
    obtain ⟨propV, bodyV, rfl, hpropType, hbodyS, hproofT, hbeta⟩ :=
      VEnv.natDivTopThen_beta wf a b htS hbranchT
    obtain ⟨hfuel, hbody⟩ := VEnv.natDivTopThenBody_inst
      wf hctors hpropType hproofT a b hbodyS
    have hbodyInstT := (hbeta.of_l wf trivial hbranchT).hasType.2
    have hgoT := (hbody.of_l wf trivial hbodyInstT).hasType.2
    exact ⟨proof, hfuel, hgoT,
      htop.trans wf trivial hselect |>.trans wf trivial hbeta
        |>.trans wf trivial hbody⟩
  · rename_i hb
    rw [if_neg hb] at hselect
    obtain ⟨proof, hselect⟩ := hselect
    have hbranchT := (hselect.of_l wf trivial hrhsT).hasType.2
    have hzero := VEnv.natDivTopElse_beta wf b heS hbranchT
    exact htop.trans wf trivial hselect |>.trans wf trivial hzero

abbrev VEnv.NatDivGoEquationTranslation (env : VEnv) : Prop :=
  VEnv.NatGoEquationTranslation env
    (natDivGoLhsBody (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
    (natDivGoRhsBody (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))

/-- Parse the checked closed recursive division equation into its two local
translated bodies. -/
theorem VEnv.NatDivGoEquationTranslation.of_checked
    {env : VEnv}
    {goL goR : VExpr}
    (hl : TrExprS env [] [] natDivGoEquation.1 goL)
    (hr : TrExprS env [] [] natDivGoEquation.2 goR)
    (heq : env.IsDefEqU 0 [] goL goR) :
    VEnv.NatDivGoEquationTranslation env := by
  simp only [natDivGoEquation] at hl hr
  cases hl with
  | lam hyTyLType hyTyLS hL₁ =>
    cases hL₁ with
    | lam hhyTyLType hhyTyLS hL₂ =>
      cases hL₂ with
      | lam hfuelTyLType hfuelTyLS hL₃ =>
        cases hL₃ with
        | lam hxTyLType hxTyLS hL₄ =>
          cases hL₄ with
          | lam hhTyLType hhTyLS hbodyL =>
            rename_i yTyL hyTyL fuelTyL xTyL hTyL bodyL
            cases hr with
            | lam hyTyRType hyTyRS hR₁ =>
              cases hR₁ with
              | lam hhyTyRType hhyTyRS hR₂ =>
                cases hR₂ with
                | lam hfuelTyRType hfuelTyRS hR₃ =>
                  cases hR₃ with
                  | lam hxTyRType hxTyRS hR₄ =>
                    cases hR₄ with
                    | lam hhTyRType hhTyRS hbodyR =>
                      rename_i yTyR hyTyR fuelTyR xTyR hTyR bodyR
                      have hbodyL' : TrExprS env []
                          [(none, .vlam hTyL), (none, .vlam xTyL),
                            (none, .vlam fuelTyL), (none, .vlam hyTyL),
                            (none, .vlam yTyL)]
                          (natDivGoLhsBody (.bvar 4) (.bvar 3) (.bvar 2)
                            (.bvar 1) (.bvar 0)) bodyL := by
                        simpa using hbodyL
                      have hbodyR' : TrExprS env []
                          [(none, .vlam hTyR), (none, .vlam xTyR),
                            (none, .vlam fuelTyR), (none, .vlam hyTyR),
                            (none, .vlam yTyR)]
                          (natDivGoRhsBody (.bvar 4) (.bvar 3) (.bvar 2)
                            (.bvar 1) (.bvar 0)) bodyR := by
                        simpa using hbodyR
                      exact .intro yTyL hyTyL fuelTyL xTyL hTyL bodyL
                        yTyR hyTyR fuelTyR xTyR hTyR bodyR
                        hyTyLS hhyTyLS hfuelTyLS hxTyLS hhTyLS
                        hyTyRS hhyTyRS hfuelTyRS hxTyRS hhTyRS
                        hyTyLType hhyTyLType hfuelTyLType hxTyLType hhTyLType
                        hyTyRType hhyTyRType hfuelTyRType hxTyRType hhTyRType
                        hbodyL' hbodyR' heq

theorem VEnv.natDivGoElse_canonical
    {env : VEnv} {yTy hyTy fuelTy xTy hTy eV : VExpr}
    (heS : TrExprS env []
      [(none, .vlam hTy), (none, .vlam xTy),
        (none, .vlam fuelTy), (none, .vlam hyTy),
        (none, .vlam yTy)]
      (natDivGoElse (.bvar 4) (.bvar 1)) eV) :
    ∃ propV, eV = .lam propV .natZero := by
  simp only [natDivGoElse, Expr.lam0] at heS
  cases heS with
  | lam hpropType hpS hbodyS =>
    rename_i propV bodyV
    cases hbodyS with
    | const _ hus _ =>
      simp at hus
      subst hus
      exact ⟨propV, rfl⟩

/-- The selected false recursive branch beta-reduces to zero after the
five outer equation binders have been instantiated. -/
theorem VEnv.natDivGoElse_beta
    {env : VEnv} (wf : env.WF)
    {yTy hyTy fuelTy xTy hTy eV hy hfuel proof R : VExpr}
    {y fuel x : Nat}
    (heS : TrExprS env []
      [(none, .vlam hTy), (none, .vlam xTy),
        (none, .vlam fuelTy), (none, .vlam hyTy),
        (none, .vlam yTy)]
      (natDivGoElse (.bvar 4) (.bvar 1)) eV)
    (happT : env.HasType 0 []
      (.app (natDivGoTargetInst eV y hy fuel x hfuel) proof) R) :
    env.IsDefEqU 0 []
      (.app (natDivGoTargetInst eV y hy fuel x hfuel) proof) .natZero := by
  obtain ⟨propV, rfl⟩ := VEnv.natDivGoElse_canonical heS
  simpa [natDivGoBranchInst, VExpr.inst, VExpr.natZero] using
    VEnv.natGoBranch_beta wf happT

/-- Normalize the computational skeleton of the retained true recursive
division branch, leaving only its generated fuel proof opaque. -/
theorem VEnv.natDivGoThen_canonical
    {env : VEnv} {yTy hyTy fuelTy xTy hTy tV : VExpr}
    (htS : TrExprS env []
      [(none, .vlam hTy), (none, .vlam xTy),
        (none, .vlam fuelTy), (none, .vlam hyTy),
        (none, .vlam yTy)]
      (natDivGoThen (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)) tV) :
    ∃ propV hfuelV,
      tV = .lam propV
        (.app .natSucc
          (.app
            (.app
              (.app
                (.app
                  (.app (.const ``Nat.div.go []) (.bvar 5))
                  (.bvar 4))
                (.bvar 3))
              (.app (.app (.const ``Nat.sub []) (.bvar 2)) (.bvar 5)))
            hfuelV)) := by
  simp only [natDivGoThen, Expr.lam0] at htS
  cases htS with
  | lam hpropType hpS hbodyS =>
    rename_i propV bodyV
    have hbodyS' : TrExprS env []
        [(none, .vlam propV), (none, .vlam hTy), (none, .vlam xTy),
          (none, .vlam fuelTy), (none, .vlam hyTy), (none, .vlam yTy)]
        (mkApp q(Nat.succ)
          (mkApp5 q(Nat.div.go) (.bvar 5) (.bvar 4) (.bvar 3)
            (mkApp2 q(Nat.sub) (.bvar 2) (.bvar 5))
            (mkApp6 q(@Nat.div_rec_fuel_lemma) (.bvar 2) (.bvar 5)
              (.bvar 3) (.bvar 4) (.bvar 0) (.bvar 1)))) bodyV := by
      simpa [natDivGoThenBody, primitiveLiftLooseBVars,
        mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, mkAppB]
        using hbodyS
    cases hbodyS' with
    | app hsuccT hcallT hsuccS hcallS =>
      rename_i succV A₆ B₆ callV
      obtain ⟨hfuelV, rfl⟩ := VEnv.natGoCallBody_canonical hcallS
      cases hsuccS with
      | const _ hsuccUs _ =>
        simp at hsuccUs
        subst hsuccUs
        exact ⟨propV, hfuelV, rfl⟩

/-- Beta-reduce the selected true recursive branch and evaluate its retained
`Nat.sub` argument, while preserving the generated recursive fuel proof. -/
theorem VEnv.natDivGoThen_beta
    {env : VEnv} (wf : env.WF)
    (hsubR : env.ReflectsNatNatNat ``Nat.sub Nat.sub)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hsubC : env.contains ``Nat.sub)
    {yTy hyTy fuelTy xTy hTy tV hy hfuel proof R A : VExpr}
    {y fuel x : Nat}
    (htS : TrExprS env []
      [(none, .vlam hTy), (none, .vlam xTy),
        (none, .vlam fuelTy), (none, .vlam hyTy),
        (none, .vlam yTy)]
      (natDivGoThen (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)) tV)
    (hhyT : env.HasType 0 [] hy A)
    (happT : env.HasType 0 []
      (.app (natDivGoTargetInst tV y hy fuel x hfuel) proof) R) :
    ∃ hfuel',
      env.HasType 0 [] (.natDivGo y fuel (x - y) hy hfuel') .nat ∧
      env.IsDefEqU 0 []
        (.app (natDivGoTargetInst tV y hy fuel x hfuel) proof)
        (.app .natSucc (.natDivGo y fuel (x - y) hy hfuel')) := by
  obtain ⟨propV, hfuelV, rfl⟩ := VEnv.natDivGoThen_canonical htS
  have hhyClosed := (hhyT.closedN' wf.ordered.closed trivial).1
  have hbeta : env.IsDefEqU 0 []
      (.app (natDivGoTargetInst
        (.lam propV
          (.app .natSucc
            (.app
              (.app
                (.app
                  (.app
                    (.app (.const ``Nat.div.go []) (.bvar 5)) (.bvar 4))
                  (.bvar 3))
                (.app (.app (.const ``Nat.sub []) (.bvar 2)) (.bvar 5)))
              hfuelV))) y hy fuel x hfuel) proof)
      (.app .natSucc
        (.app
          (.app
            (.app
              (.app
                (.app (.const ``Nat.div.go []) (.natLit y)) hy)
              (.natLit fuel))
            (.app (.app (.const ``Nat.sub []) (.natLit x)) (.natLit y)))
          (natDivGoBranchInst hfuelV y hy fuel x hfuel proof))) := by
    simpa [natDivGoBranchInst, VExpr.inst, VExpr.instVar,
      hhyClosed.liftN_eq (Nat.zero_le _),
      hhyClosed.instN_eq (Nat.zero_le _)] using
      VEnv.natGoBranch_beta wf happT
  have hbodyResultT := (hbeta.of_l wf trivial happT).hasType.2
  obtain ⟨_, _, hsuccFnT, hcallT⟩ :=
    hbodyResultT.app_inv wf.ordered trivial
  obtain ⟨_, _, hprefix₄T, hhfuelIT⟩ := hcallT.app_inv wf.ordered trivial
  obtain ⟨_, _, hprefix₃T, hsubArgT⟩ := hprefix₄T.app_inv wf.ordered trivial
  have hsubEq := (hsubR hsubC).2 x y
  have hprefix₄Eq := hsubEq.app_arg wf trivial hprefix₃T hsubArgT
  have hcallEq := hprefix₄Eq.app_same wf trivial hprefix₄T hhfuelIT
  have hsuccEq := hcallEq.app_arg wf trivial hsuccFnT hcallT
  have hrecRawT := (hcallEq.of_l wf trivial hcallT).hasType.2
  have hsuccT := (hctors.natSuccS (Us := []) (Δ := [])).2
  have hsuccTyEq := hsuccFnT.uniqU wf trivial hsuccT
  obtain ⟨_, hsuccDomEq⟩ := (hsuccTyEq.forallE_inv wf trivial).1
  have hrecT := hrecRawT.defeqU_r wf trivial hsuccDomEq.toU
  exact ⟨natDivGoBranchInst hfuelV y hy fuel x hfuel proof, hrecT,
    hbeta.trans wf trivial hsuccEq⟩

/-- The checked recursive division equation has the exact operational shape
required by `ReflectsNatNatNat.of_divCore_equations`. -/
theorem VEnv.natDivGo_semantics
    {env : VEnv} (wf : env.WF)
    (hbleR : env.ReflectsNatNatBool ``Nat.ble Nat.ble)
    (hsubR : env.ReflectsNatNatNat ``Nat.sub Nat.sub)
    (hctors : VEnv.HasNatBoolConstructors env)
    (hbleC : env.contains ``Nat.ble)
    (hsubC : env.contains ``Nat.sub)
    (selector : VEnv.NatLESelectorCertificate env)
    (eqCert : VEnv.NatDivGoEquationTranslation env)
    {goTyV : VExpr}
    (typeCert : VEnv.NatDivGoTypeTranslation env goTyV)
    (hgoT : env.HasType 0 [] (.const ``Nat.div.go []) goTyV) :
    ∀ y fuel x hy hfuel,
      env.HasType 0 [] (.natDivGo y (fuel + 1) x hy hfuel) .nat →
      if y ≤ x then
        ∃ hy' hfuel',
          env.HasType 0 [] (.natDivGo y fuel (x - y) hy' hfuel') .nat ∧
          env.IsDefEqU 0 []
            (.natDivGo y (fuel + 1) x hy hfuel)
            (.app .natSucc (.natDivGo y fuel (x - y) hy' hfuel'))
      else
        env.IsDefEqU 0 []
          (.natDivGo y (fuel + 1) x hy hfuel) .natZero := by
  cases eqCert with
  | intro yTyL hyTyL fuelTyL xTyL hTyL bodyL
      yTyR hyTyR fuelTyR xTyR hTyR bodyR
      yTyLS hyTyLS fuelTyLS xTyLS hTyLS
      yTyRS hyTyRS fuelTyRS xTyRS hTyRS
      yTyLType hyTyLType fuelTyLType xTyLType hTyLType
      yTyRType hyTyRType fuelTyRType xTyRType hTyRType
      leftS rightS heq =>
    intro y fuel x hy hfuel hcallT
    obtain ⟨yTy, hyTy, fuelTy, xTy, hTy, resultTy,
      yTyS, hyTyS, hhyCanon, hhfuelCanon⟩ :=
      typeCert.call_proof_types wf hgoT
        y (fuel + 1) x hcallT
    have hhyL := VEnv.align_natDivGo_first_proof wf hctors
      yTyLS hyTyLS yTyS hyTyS y hhyCanon
    have hleftShape := VEnv.natGoLhsBody_canonical hctors
      (by simpa [natDivGoLhsBody] using leftS)
    subst bodyL
    have hEq : env.IsDefEqU 0 []
        (.natDivGo y (fuel + 1) x hy hfuel)
        (natDivGoTargetInst bodyR y hy fuel x hfuel) := by
      simpa [natDivGoTargetInst, VExpr.natDivGo, VExpr.natLit,
        Nat.add_comm] using
        VEnv.instantiate_natGo_equation wf hctors
          yTyLS fuelTyLS xTyLS yTyRS fuelTyRS xTyRS
          yTyLType hyTyLType fuelTyLType yTyRType hyTyRType fuelTyRType
          heq y fuel x hhyL
          (by simpa [VExpr.natDivGo, VExpr.natLit, Nat.add_comm]
            using hcallT)
    have hrhsT := (hEq.of_l wf trivial hcallT).hasType.2
    rw [natDivGoRhsBody_eq_parts] at rightS
    obtain ⟨tV, eV, htS, heS, hselect⟩ :=
      VEnv.select_natGo_rhs wf hbleR hctors hbleC selector rightS
        y fuel x hhyL hhfuelCanon hrhsT
    split
    · rename_i hyx
      rw [if_pos hyx] at hselect
      obtain ⟨proof, hselect⟩ := hselect
      have hbranchT := (hselect.of_l wf trivial hrhsT).hasType.2
      obtain ⟨hfuel', hrecT, hbranch⟩ := VEnv.natDivGoThen_beta
        wf hsubR hctors hsubC htS hhyL hbranchT
      exact ⟨hy, hfuel', hrecT,
        hEq.trans wf trivial hselect |>.trans wf trivial hbranch⟩
    · rename_i hyx
      rw [if_neg hyx] at hselect
      obtain ⟨proof, hselect⟩ := hselect
      have hbranchT := (hselect.of_l wf trivial hrhsT).hasType.2
      have hbranch := VEnv.natDivGoElse_beta wf heS hbranchT
      exact hEq.trans wf trivial hselect |>.trans wf trivial hbranch

/-- Semantic evidence retained by the direct `Nat.div` primitive checker. -/
abbrev NatDivPrimitiveEvidence
    (c : TypeChecker.VContext) (src : DefinitionVal) (ty' : VExpr) : Prop :=
  ∃ go' goTy' topL' topR' goL' goR',
    c.TrExprS q(Nat.div.go) go' ∧
    c.TrExprS q(∀ y, Nat.succ Nat.zero ≤ y →
      ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) goTy' ∧
    c.TrExprS (natDivTopEquation src.value).1 topL' ∧
    c.TrExprS (natDivTopEquation src.value).2 topR' ∧
    c.TrExprS natDivGoEquation.1 goL' ∧
    c.TrExprS natDivGoEquation.2 goR' ∧
    src.levelParams = [] ∧
    c.venv.contains ``Nat ∧ c.venv.contains ``Bool ∧
    c.venv.contains ``Nat.ble ∧ c.venv.contains ``Nat.sub ∧
    c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
    ∃ _selector : VEnv.NatLESelectorCertificate c.venv,
      c.HasType go' goTy' ∧
      c.IsDefEqU topL' topR' ∧ c.IsDefEqU goL' goR'

theorem checkPrimitiveDef.natDiv.WF_typed
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    {src : DefinitionVal} {ty' value' : VExpr}
    (hname : src.name = ``Nat.div)
    (hcparams : c.lparams = src.levelParams) (hvlctx : c.vlctx = [])
    (hty : c.TrExprS src.type ty') (hvalue : c.TrExprS src.value value') :
    TypeChecker.M.WF c s (checkPrimitiveDef src) fun b _ => b →
      NatDivPrimitiveEvidence c src ty' := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  rw [checkPrimitiveDef.natDiv_eq hname]
  refine TypeChecker.getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  exact (checkNatDivPrimitive.WF_typed hcparams hty hvlctx hvalue
    (fun hlparams hfail =>
      Condition.natLE.checkForPrimitive.WF.selector
        hlparams hvlctx hfail)).bind fun _ _ _ h => by
      rcases h with ⟨go', goTy', topL', topR', goL', goR',
        hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
        hparams, hnat, hbool, hble, hsub, htyEq,
        ⟨selector, _⟩, hgoHas, htopEq, hgoEq⟩
      exact .pure fun _ =>
        ⟨go', goTy', topL', topR', goL', goR',
          hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
          hparams, hnat, hbool, hble, hsub, htyEq,
          selector, hgoHas, htopEq, hgoEq⟩

/-- Install a checked division definition in an arbitrary readiness safety
model while conserving the complete primitive-reflection invariant. -/
theorem NatDivPrimitiveEvidence.conservesHasPrimitives
    {c : TypeChecker.VContext}
    {src : DefinitionVal} {v : VDefVal} {base env' : VEnv}
    (hcparams : c.lparams = src.levelParams) (hvlctx : c.vlctx = [])
    (hdiv : c.TrExprS src.value v.value)
    (hname : v.name = ``Nat.div)
    (huvars : src.levelParams.length = v.uvars)
    (hbase : base.HasPrimitives) (hbaseMono : c.venv ≤ base)
    (hadd : base.addConst ``Nat.div v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hevidence : NatDivPrimitiveEvidence c src v.type) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  rcases hevidence with
    ⟨go', goTy', topL', topR', goL', goR',
      hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
      hsrcParams, hnat, hbool, hbleC, hsubC, hty,
      selector, hgoHas, htopEq, hgoEq⟩
  have hclparams : c.lparams = [] := hcparams.trans hsrcParams
  have hvuvars : v.uvars = 0 := by
    rw [← huvars, hsrcParams]
    rfl
  change TrExprS c.venv c.lparams c.vlctx _ _ at hdiv hgoS hgoTyS
  change TrExprS c.venv c.lparams c.vlctx _ _ at htopL htopR hgoL hgoR
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at hty
  change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at htopEq hgoEq
  change c.venv.HasType c.lparams.length c.vlctx.toCtx _ _ at hgoHas
  rw [hclparams, hvlctx] at hdiv hgoS hgoTyS htopL htopR hgoL hgoR
  rw [hclparams, hvlctx] at hty htopEq hgoEq hgoHas
  let env'' := env'.addDefEq v.toDefEq
  have hle : c.venv ≤ env'' :=
    hbaseMono.trans <| (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hctors : VEnv.HasNatBoolConstructors env'' :=
    (VEnv.HasNatBoolConstructors.of_primitives
      c.hasPrimitives hbool hnat).mono hle
  have hbleC' : env''.contains ``Nat.ble :=
    let ⟨ci, hci⟩ := hbleC
    ⟨ci, hle.constants hci⟩
  have hsubC' : env''.contains ``Nat.sub :=
    let ⟨ci, hci⟩ := hsubC
    ⟨ci, hle.constants hci⟩
  have hbleR : env''.ReflectsNatNatBool ``Nat.ble Nat.ble :=
    (hbase.natBLE.addConst hadd (by decide)).addDefEq
  have hsubR : env''.ReflectsNatNatNat ``Nat.sub Nat.sub :=
    (hbase.natSub.addConst hadd (by decide)).addDefEq
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.div [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.div = some v.toVConstant
      exact VEnv.addConst_self hadd) hvuvars (hty.mono hle) U Γ
  have hcf := VDefVal.const_defeq_value hwf hvuvars
  rw [hname] at hcf
  have hdivT : env''.HasType 0 [] v.value
      (.forallE .nat <| .forallE .nat .nat) :=
    (hcf.of_l hwf trivial (hf 0 [])).hasType.2
  have hgoShape : go' = .const ``Nat.div.go [] := by
    cases hgoS with
    | const _ hus _ =>
      simp at hus
      subst hus
      rfl
  subst go'
  have htop := VEnv.natDivTop_semantics hwf hbleR hctors hbleC'
    (selector.mono hle) (hdiv.mono hle)
    hdiv.closed.looseBVarRange_zero hdivT
    (htopL.mono hle) (htopR.mono hle) (htopEq.mono hle)
  have hgoEqCert := VEnv.NatDivGoEquationTranslation.of_checked
    (hgoL.mono hle) (hgoR.mono hle) (hgoEq.mono hle)
  have hgoTyCert := VEnv.NatDivGoTypeTranslation.of_translation
    (hgoTyS.mono hle)
  have hgo := VEnv.natDivGo_semantics hwf hbleR hsubR hctors
    hbleC' hsubC' (selector.mono hle) hgoEqCert hgoTyCert
    (hgoHas.mono hle)
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (hctors.natZeroS (Us := []) (Δ := [])).2.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc
      (.forallE .nat .nat) :=
    (hctors.natSuccS (Us := []) (Δ := [])).2.weak0 hwf
  have href := VEnv.ReflectsNatNatNat.of_divCore_equations
    hwf hzero hsucc hf hcf htop hgo
  exact hbase.addNatDiv hadd href

end Lean4Lean.Environment
