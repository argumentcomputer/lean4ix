/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong

/-!
A bunch of important structural theorems which we can't prove :(
-/

namespace Lean4Lean
namespace VEnv

set_option warn.sorry false in
theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := sorry

set_option warn.sorry false in
theorem IsDefEqU.forallE_inv_stratified (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' := sorry

theorem IsDefEqU.forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) :=
  let ⟨_, eq⟩ := h1
  let ⟨h2, h3⟩ := (eq.strong henv hΓ).hasType'
  let ⟨_, h2⟩ := h2.stratify
  let ⟨_, h3⟩ := h3.stratify
  let ⟨⟨_, a1, _⟩, _, a2, _⟩ := IsDefEqU.forallE_inv_stratified henv hΓ h1 h2 h3
  ⟨⟨_, a1⟩, _, a2⟩

set_option warn.sorry false in
theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := sorry

/-- The quotient-head injectivity consequence consumed by operational
quotient reduction.  It is deliberately stated only at the classified
`Quot` application head: a definitional equality exposes the universe,
carrier, and relation components, but supplies no reduction equality.

The direct normalization/adequacy development is the intended producer of
this interface.  Keeping the proposition here lets Verify-side consumers
name the exact remaining boundary without assuming a registered equation's
contractum as input. -/
def QuotAppInj (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {u₁ u₂ : VLevel}
    {α₁ r₁ α₂ r₂ : VExpr},
    env.IsDefEqU U Γ
      (VExpr.appN (.const ``Quot [u₁]) [α₁, r₁])
      (VExpr.appN (.const ``Quot [u₂]) [α₂, r₂]) →
    u₁ ≈ u₂ ∧ env.IsDefEqU U Γ α₁ α₂ ∧
      env.IsDefEqU U Γ r₁ r₂

/-- info: 'Lean4Lean.VEnv.QuotAppInj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.QuotAppInj
