/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Primitive

/-!
# Fuel-indexed primitive recursion semantics

This module isolates the semantic interpreter spine shared by checked
fuel-indexed primitive recursions and instantiates it for `Nat.mod.go` and
`Nat.div.go`.
It is adapted from upstream lean4lean PR #32 at
`6cfd43a48d17be85c76414638655c12ef9a7ee23`.
-/

namespace Lean4Lean

@[simp] private theorem Nat.mod_eq_hmod (a b : Nat) : a.mod b = a % b := rfl

@[simp] private theorem Nat.div_eq_hdiv (a b : Nat) : a.div b = a / b := rfl

/-- One unfolding step of a fuel-indexed recursion: either a terminal value,
or a recursive call together with a post-processing of its result. -/
inductive FuelStep (α : Type) where
  | done (v : Nat)
  | recur (next : α) (post : Nat → Nat)

/-- The value of a step, given the meaning `F` of recursive calls. -/
def FuelStep.out (F : α → Nat) : FuelStep α → Nat
  | .done v => v
  | .recur next post => post (F next)

/-- The interpreter spine shared by every fuel-indexed primitive recursion.
If checked calls step according to `step` and `F` satisfies the same
recurrence, every well-formed call with sufficient fuel is definitionally
equal to `F`'s value. -/
theorem VEnv.natLit_defeq_of_fuel_relation (_henv : VEnv.WF env)
    {α : Type} {G : Nat → α → VExpr → Prop} {WT : VExpr → Prop}
    (μ : α → Nat) (F : α → Nat) (step : α → FuelStep α)
    (hF : ∀ x, F x = (step x).out F)
    (hdec : ∀ x (next : α) (post : Nat → Nat),
      step x = .recur next post → μ next < μ x)
    (hstep : ∀ fuel x e, G (fuel + 1) x e → WT e →
      match step x with
      | .done v => env.IsDefEqU 0 [] e (.natLit v)
      | .recur next post => ∃ e', G fuel next e' ∧ WT e' ∧
          ∀ q, env.IsDefEqU 0 [] e' (.natLit q) →
            env.IsDefEqU 0 [] e (.natLit (post q))) :
    ∀ fuel x e, G fuel x e → WT e → μ x < fuel →
      env.IsDefEqU 0 [] e (.natLit (F x)) := by
  intro fuel
  induction fuel with
  | zero => intro x e _ _ h; omega
  | succ fuel ih =>
    intro x e hG hWT hlt
    have h := hstep fuel x e hG hWT
    cases hs : step x with
    | done v =>
      rw [hs] at h
      rw [hF x, hs, FuelStep.out]
      exact h
    | recur next post =>
      rw [hs] at h
      obtain ⟨e', hG', hWT', hfin⟩ := h
      have hd := hdec x next post hs
      rw [hF x, hs, FuelStep.out]
      exact hfin _ (ih next e' hG' hWT' (by omega))

def VExpr.natModGo (y fuel x : Nat) (hy hfuel : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.const ``Nat.modCore.go []) (.natLit y)) hy)
    (.natLit fuel)) (.natLit x)) hfuel

/-- The fuel-level equations checked for `Nat.modCore.go` imply semantic
remainder reflection. The proof arguments are intentionally existential:
their identity is irrelevant, while their presence records the dependent
applications produced by the checker. -/
theorem VEnv.ReflectsNatNatNat.of_modCore_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.mod [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.mod []) f)
    (htop : ∀ a b,
      if 0 < b ∧ b ≤ a then
        ∃ hy hfuel,
          env.HasType 0 [] (.natModGo b (a + 1) a hy hfuel) .nat ∧
          env.IsDefEqU 0 []
            (.app (.app f (.natLit a)) (.natLit b))
            (.natModGo b (a + 1) a hy hfuel)
      else
        env.IsDefEqU 0 []
          (.app (.app f (.natLit a)) (.natLit b)) (.natLit a))
    (hgo : ∀ y fuel x hy hfuel,
      env.HasType 0 [] (.natModGo y (fuel + 1) x hy hfuel) .nat →
      if y ≤ x then
        ∃ hy' hfuel',
          env.HasType 0 [] (.natModGo y fuel (x - y) hy' hfuel') .nat ∧
          env.IsDefEqU 0 []
            (.natModGo y (fuel + 1) x hy hfuel)
            (.natModGo y fuel (x - y) hy' hfuel')
      else
        env.IsDefEqU 0 []
          (.natModGo y (fuel + 1) x hy hfuel) (.natLit x)) :
    env.ReflectsNatNatNat ``Nat.mod Nat.mod := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hcfApp (x y) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.mod []) (.natLit x)) (.natLit y))
      (.app (.app f (.natLit x)) (.natLit y)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit x [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit x [])) (hlit y [])
  have goEval (y : Nat) (hypos : 0 < y) :
      ∀ fuel x hy hfuel, x < fuel →
        env.HasType 0 [] (.natModGo y fuel x hy hfuel) .nat →
        env.IsDefEqU 0 []
        (.natModGo y fuel x hy hfuel) (.natLit (x.mod y)) := by
    intro fuel x hy hfuel hlt hcallT
    refine VEnv.natLit_defeq_of_fuel_relation henv
      (G := fun fuel x e => ∃ hy hfuel, e = VExpr.natModGo y fuel x hy hfuel)
      (WT := fun e => env.HasType 0 [] e .nat)
      id (fun x => x.mod y)
      (fun x => if y ≤ x then .recur (x - y) id else .done x)
      ?_ ?_ ?_ fuel x _ ⟨hy, hfuel, rfl⟩ hcallT hlt
    · intro x
      by_cases h : y ≤ x
      · simp only [if_pos h]
        show x.mod y = (x - y).mod y
        simpa [hypos, h] using Nat.mod_eq x y
      · simp only [if_neg h]
        show x.mod y = x
        simpa [h] using Nat.mod_eq x y
    · intro x next post hs
      by_cases h : y ≤ x
      · simp only [if_pos h] at hs
        cases hs
        exact Nat.sub_lt_self hypos h
      · simp only [if_neg h] at hs
        cases hs
    · rintro fuel x e ⟨hy, hfuel, rfl⟩ hWT
      have hg := hgo y fuel x hy hfuel hWT
      by_cases h : y ≤ x
      · simp only [if_pos h] at hg ⊢
        obtain ⟨hy', hfuel', hrecT, hg⟩ := hg
        exact ⟨_, ⟨hy', hfuel', rfl⟩, hrecT,
          fun q hq => hg.trans henv trivial hq⟩
      · simp only [if_neg h] at hg ⊢
        exact hg
  have ht := htop a b
  split at ht
  · rename_i hab
    obtain ⟨hy, hfuel, hcallT, ht⟩ := ht
    exact (hcfApp a b).trans henv trivial <|
      ht.trans henv trivial
        (goEval b hab.1 (a + 1) a hy hfuel (by omega) hcallT)
  · rename_i hab
    have heq : a.mod b = a := by
      simpa [hab] using Nat.mod_eq a b
    rw [heq]
    exact (hcfApp a b).trans henv trivial ht

def VExpr.natDivGo (y fuel x : Nat) (hy hfuel : VExpr) : VExpr :=
  .app (.app (.app (.app (.app (.const ``Nat.div.go []) (.natLit y)) hy)
    (.natLit fuel)) (.natLit x)) hfuel

/-- Fuel adequacy for the checked `Nat.div.go` equation, and hence semantic
reflection of natural-number division. -/
theorem VEnv.ReflectsNatNatNat.of_divCore_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.div [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.div []) f)
    (htop : ∀ a b,
      if 0 < b then
        ∃ hy hfuel,
          env.HasType 0 [] (.natDivGo b (a + 1) a hy hfuel) .nat ∧
          env.IsDefEqU 0 []
            (.app (.app f (.natLit a)) (.natLit b))
            (.natDivGo b (a + 1) a hy hfuel)
      else
        env.IsDefEqU 0 []
          (.app (.app f (.natLit a)) (.natLit b)) .natZero)
    (hgo : ∀ y fuel x hy hfuel,
      env.HasType 0 [] (.natDivGo y (fuel + 1) x hy hfuel) .nat →
      if y ≤ x then
        ∃ hy' hfuel',
          env.HasType 0 [] (.natDivGo y fuel (x - y) hy' hfuel') .nat ∧
          env.IsDefEqU 0 []
            (.natDivGo y (fuel + 1) x hy hfuel)
            (.app .natSucc (.natDivGo y fuel (x - y) hy' hfuel'))
      else
        env.IsDefEqU 0 []
          (.natDivGo y (fuel + 1) x hy hfuel) .natZero) :
    env.ReflectsNatNatNat ``Nat.div Nat.div := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have hlit (n) (Γ) : env.HasType 0 Γ (.natLit n) .nat := by
    induction n with
    | zero => exact hzeroT Γ
    | succ n ih => exact .app (hsuccT Γ) ih
  have hcfApp (x y) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.div []) (.natLit x)) (.natLit y))
      (.app (.app f (.natLit x)) (.natLit y)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit x [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit x [])) (hlit y [])
  have goEval (y : Nat) (hypos : 0 < y) :
      ∀ fuel x hy hfuel, x < fuel →
        env.HasType 0 [] (.natDivGo y fuel x hy hfuel) .nat →
        env.IsDefEqU 0 []
        (.natDivGo y fuel x hy hfuel) (.natLit (x.div y)) := by
    intro fuel x hy hfuel hlt hcallT
    refine VEnv.natLit_defeq_of_fuel_relation henv
      (G := fun fuel x e => ∃ hy hfuel, e = VExpr.natDivGo y fuel x hy hfuel)
      (WT := fun e => env.HasType 0 [] e .nat)
      id (fun x => x.div y)
      (fun x => if y ≤ x then .recur (x - y) (· + 1) else .done 0)
      ?_ ?_ ?_ fuel x _ ⟨hy, hfuel, rfl⟩ hcallT hlt
    · intro x
      by_cases h : y ≤ x
      · simp only [if_pos h]
        show x.div y = (x - y).div y + 1
        simpa [hypos, h] using Nat.div_eq x y
      · simp only [if_neg h]
        show x.div y = 0
        have hformula : x.div y =
            if 0 < y ∧ y ≤ x then (x - y).div y + 1 else 0 := by
          simpa using Nat.div_eq x y
        rw [hformula]
        simp [h]
    · intro x next post hs
      by_cases h : y ≤ x
      · simp only [if_pos h] at hs
        cases hs
        exact Nat.sub_lt_self hypos h
      · simp only [if_neg h] at hs
        cases hs
    · rintro fuel x e ⟨hy, hfuel, rfl⟩ hWT
      have hg := hgo y fuel x hy hfuel hWT
      by_cases h : y ≤ x
      · simp only [if_pos h] at hg ⊢
        obtain ⟨hy', hfuel', hrecT, hg⟩ := hg
        refine ⟨_, ⟨hy', hfuel', rfl⟩, hrecT, fun q hq => ?_⟩
        have hsucc := hq.app_arg henv trivial (hsuccT []) hrecT
        simpa [VExpr.natLit] using hg.trans henv trivial hsucc
      · simp only [if_neg h] at hg ⊢
        exact hg
  have ht := htop a b
  split at ht
  · rename_i hb
    obtain ⟨hy, hfuel, hgoT, ht⟩ := ht
    exact (hcfApp a b).trans henv trivial <|
      ht.trans henv trivial
        (goEval b hb (a + 1) a hy hfuel (by omega) hgoT)
  · rename_i hb
    have heq : a.div b = 0 := by
      have hformula : a.div b =
          if 0 < b ∧ b ≤ a then (a - b).div b + 1 else 0 := by
        simpa using Nat.div_eq a b
      rw [hformula]
      simp [hb]
    rw [heq]
    exact (hcfApp a b).trans henv trivial ht

end Lean4Lean
