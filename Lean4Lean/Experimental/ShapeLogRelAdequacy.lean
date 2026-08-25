/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Experimental.ShapeLogRel
import Lean4Lean.Theory.Typing.Strong

namespace Lean4Lean

namespace SExpr
variable [Params] [Params.Semantic]

def LR.Adequate (Γ₀ Γ : List SExpr) (ρ : Valuation) (M N A : SExpr) (m a : WShape n) :=
  (∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ ρ →
    (LR Γ₀).DefEq (M.subst σ) (M.subst σ') (A.subst σ) m a ∧
    (LR Γ₀).DefEq (N.subst σ) (N.subst σ') (A.subst σ) m a) ∧
  ∀ {{σ}}, LR.SubstWF Γ₀ σ σ Γ ρ → (LR Γ₀).DefEq (M.subst σ) (N.subst σ) (A.subst σ) m a

/-- Additive direct adequacy.  Ordinary term semantics are unchanged; when
the ambient type shape is a sort, each substituted term edge additionally
retains a recursive direct type observation. -/
def LR.DirectAdequate (Γ₀ Γ : List SExpr) (ρ : Valuation)
    (M N A : SExpr) (m a : WShape n) :=
  (∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ ρ →
    LR.DirectDefEq Γ₀ (M.subst σ) (M.subst σ') (A.subst σ) m a ∧
    LR.DirectDefEq Γ₀ (N.subst σ) (N.subst σ') (A.subst σ) m a) ∧
  ∀ {{σ}}, LR.SubstWF Γ₀ σ σ Γ ρ →
    LR.DirectDefEq Γ₀ (M.subst σ) (N.subst σ) (A.subst σ) m a

/-- Forget the direct sidecar and recover the established adequacy
interface. -/
theorem LR.DirectAdequate.toAdequate
    (H : LR.DirectAdequate Γ₀ Γ ρ M N A m a) :
    LR.Adequate Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => ⟨(H.1 W).1.toDefEq, (H.1 W).2.toDefEq⟩,
    fun _ W => (H.2 W).toDefEq⟩

/-- The left congruence edge of direct adequacy at a sort exposes the
retained type observation. -/
theorem LR.DirectAdequate.leftTy
    (H : LR.DirectAdequate Γ₀ Γ ρ M N A m (.sort r))
    (W : LR.SubstWF Γ₀ σ σ' Γ ρ) :
    LR.DirectTyDefEq Γ₀ (M.subst σ) (M.subst σ') m :=
  (H.1 W).1.toTyDefEq

/-- The right congruence edge of direct adequacy at a sort. -/
theorem LR.DirectAdequate.rightTy
    (H : LR.DirectAdequate Γ₀ Γ ρ M N A m (.sort r))
    (W : LR.SubstWF Γ₀ σ σ' Γ ρ) :
    LR.DirectTyDefEq Γ₀ (N.subst σ) (N.subst σ') m :=
  (H.1 W).2.toTyDefEq

/-- The heterogeneous same-substitution edge of direct adequacy at a
sort. -/
theorem LR.DirectAdequate.edgeTy
    (H : LR.DirectAdequate Γ₀ Γ ρ M N A m (.sort r))
    (W : LR.SubstWF Γ₀ σ σ Γ ρ) :
    LR.DirectTyDefEq Γ₀ (M.subst σ) (N.subst σ) m :=
  (H.2 W).toTyDefEq

/-! #### Level-guarded direct substitutions and adequacy

The `LRD` tower cannot quantify over legacy substitutions: a context entry
whose declared type is itself a function must retain the direct action of
that function (the Nat eliminator motive is the first concrete example).
These definitions mirror `LR.Subst1`, `LR.SubstWF`, and `LR.Adequate`, but
use the relation at each entry's actual semantic shape level. -/

/-- One context entry realized in the level-guarded direct relation. -/
def LR.DirectSubst1 (Γ₀ : List SExpr)
    (x x' A₀ A A' : SExpr) (ρ : Valuation) (i := 0) : Prop :=
  IsDefEq Γ₀ x x' A ∧ ∀ {{n}} (a : WShape n), LE_Interp ρ a.T A₀ →
    (a.HasType .type →
      (∃ u, IsDefEq Γ₀ A A' (.sort u)) ∧
        (LRD Γ₀).TyDefEq A A' a) ∧
    ∀ {{m : WShape n}}, LE_Interp ρ m.T (.bvar i) → m.HasType a →
      (LRD Γ₀).DefEq x x' A m a

/-- Two-sided substitutions whose entries retain their direct semantic
actions, including actions at Pi-shaped declared types. -/
inductive LR.DirectSubstWF (Γ₀ : List SExpr) :
    Subst → Subst → List SExpr → Valuation → Prop where
  | id : LR.DirectSubstWF Γ₀ .id .id Γ₀ .nil
  | cons : LR.DirectSubstWF Γ₀ σ.tail σ'.tail Γ ρ →
    (∀ {a}, LE_Interp ρ a A →
      ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type) →
    LE_Interp ρ a A → x.HasType a → IsDefEq Γ A A (.sort u) →
    LR.DirectSubst1 Γ₀ σ.head σ'.head A.lift
      (A.subst σ.tail) (A.subst σ'.tail) (ρ.push x) →
    LR.DirectSubstWF Γ₀ σ σ' (A :: Γ) (ρ.push x)

/-- Forget one direct substitution entry. -/
theorem LR.DirectSubst1.toSubst1
    (H : LR.DirectSubst1 Γ₀ x x' A₀ A A' ρ i) :
    LR.Subst1 Γ₀ x x' A₀ A A' ρ i := by
  refine ⟨H.1, fun n a ha => ⟨fun ht => ?_, fun m hm hma => ?_⟩⟩
  · exact ⟨(H.2 a ha).1 ht |>.1,
      LRD.tyLegacy ((H.2 a ha).1 ht |>.2)⟩
  · exact LRD.defLegacy ((H.2 a ha).2 hm hma)

/-- Direct substitution well-formedness erases structurally to the existing
substitution interface. -/
theorem LR.DirectSubstWF.toSubstWF :
    LR.DirectSubstWF Γ₀ σ σ' Γ ρ → LR.SubstWF Γ₀ σ σ' Γ ρ
  | .id => .id
  | .cons W hfit hA hx hty h0 =>
    .cons W.toSubstWF hfit hA hx hty h0.toSubst1

theorem LR.DirectSubstWF.fits
    (W : LR.DirectSubstWF Γ₀ σ σ' Γ ρ) : ρ.Fits Γ₀ Γ :=
  W.toSubstWF.fits

theorem LR.DirectSubstWF.toSubstEq
    (W : LR.DirectSubstWF Γ₀ σ σ' Γ ρ) :
    Ctx.SubstEq Γ₀ σ σ' Γ :=
  W.toSubstWF.toSubstEq

/-- Retain the left endpoint of every entry in a direct substitution. -/
theorem LR.DirectSubstWF.left
    (W : LR.DirectSubstWF Γ₀ σ σ' Γ ρ) :
    LR.DirectSubstWF Γ₀ σ σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ hfit hA hx hty h₀ ih =>
    refine .cons ih hfit hA hx hty
      ⟨h₀.1.hasType.1, fun _ a ha =>
        ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨u, hraw⟩, hdirect⟩ := (h₀.2 a ha).1 ht
      exact ⟨⟨u, hraw.hasType.1⟩, LRD.TyDefEq.left hdirect⟩
    · exact LRD.DefEq.left ((h₀.2 a ha).2 hM hmem)

/--
info: 'Lean4Lean.SExpr.LR.DirectSubstWF.left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectSubstWF.left

/-- Reverse both endpoints of every direct substitution entry. -/
theorem LR.DirectSubstWF.symm
    (W : LR.DirectSubstWF Γ₀ σ σ' Γ ρ) :
    LR.DirectSubstWF Γ₀ σ' σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ hfit hA hx hty h₀ ih =>
    refine .cons ih hfit hA hx hty ⟨?_, fun _ a ha =>
      ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, hraw⟩, _⟩ :=
        (h₀.2 (n := 0) _ .bot).1 (.bot .sort)
      exact hraw.defeqDF h₀.1.symm
    · have ⟨⟨u, hraw⟩, hdirect⟩ := (h₀.2 a ha).1 ht
      exact ⟨⟨u, hraw.symm⟩, LRD.TyDefEq.symm hdirect⟩
    · let ⟨_, htype⟩ := (h₀.2 a ha).1 hmem.isType
      exact LRD.DefEq.conv htype <|
        LRD.DefEq.symm ((h₀.2 a ha).2 hM hmem)

/--
info: 'Lean4Lean.SExpr.LR.DirectSubstWF.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectSubstWF.symm

/-- Look up one variable through a direct substitution.  The head case is
exactly the retained entry payload; the tail case strips one weakening.
For the identity tail the semantic variable observation is bottom, which
is deliberately uninformative in `LRD`. -/
theorem LR.DirectSubstWF.bvar
    (W : LR.DirectSubstWF Γ₀ σ σ' Γ ρ)
    (hlookup : Lookup Γ i A)
    (hM : LE_Interp ρ m.T (.bvar i))
    (hA : LE_Interp ρ a.T A)
    (hmem : m.HasType a) :
    (LRD Γ₀).DefEq
      ((SExpr.bvar i).subst σ) ((SExpr.bvar i).subst σ')
      (A.subst σ) m a := by
  have hle := LE_Interp.bvar_iff.1 hM
  clear hM
  induction W generalizing i A with
  | id =>
    cases show m = .bot from TShape.le_bot.1 (hle.trans TShape.bot_le)
    exact LRD.DefEq.bot hmem.isType
  | cons W' _ _ _ _ h₀ ih =>
    cases hlookup with
    | zero => exact lift_subst ▸ (h₀.2 a hA).2 (.bvar hle) hmem
    | succ h' =>
      exact lift_subst ▸ ih h' (LE_Interp.weak_iff.1 hA) hle

/--
info: 'Lean4Lean.SExpr.LR.DirectSubstWF.bvar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectSubstWF.bvar

/-- Fundamental-theorem target for the level-guarded direct relation. -/
def LRD.Adequate (Γ₀ Γ : List SExpr) (ρ : Valuation)
    (M N A : SExpr) (m a : WShape n) : Prop :=
  (∀ {{σ σ'}}, LR.DirectSubstWF Γ₀ σ σ' Γ ρ →
    (LRD Γ₀).DefEq (M.subst σ) (M.subst σ') (A.subst σ) m a ∧
    (LRD Γ₀).DefEq (N.subst σ) (N.subst σ') (A.subst σ) m a) ∧
  ∀ {{σ}}, LR.DirectSubstWF Γ₀ σ σ Γ ρ →
    (LRD Γ₀).DefEq (M.subst σ) (N.subst σ) (A.subst σ) m a

/-- Reflexive direct adequacy from the relational-substitution edge. -/
theorem LRD.Adequate.refl
    (H : ∀ {{σ σ'}}, LR.DirectSubstWF Γ₀ σ σ' Γ ρ →
      (LRD Γ₀).DefEq (M.subst σ) (M.subst σ')
        (A.subst σ) m a) :
    LRD.Adequate Γ₀ Γ ρ M M A m a :=
  ⟨fun _ _ W => ⟨H W, H W⟩, fun _ W => H W⟩

/-- A bottom term observation is adequate at every well-shaped displayed
type.  As at the relation level, it deliberately carries no head evidence. -/
theorem LRD.Adequate.bot
    (ha : a.HasType .type) :
    LRD.Adequate Γ₀ Γ ρ M N A (.bot : WShape n) a :=
  ⟨fun _ _ _ => ⟨LRD.DefEq.bot ha, LRD.DefEq.bot ha⟩,
    fun _ _ => LRD.DefEq.bot ha⟩

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.bot

/-- Retain the left endpoint of direct adequacy. -/
theorem LRD.Adequate.left
    (H : LRD.Adequate Γ₀ Γ ρ M N A m a) :
    LRD.Adequate Γ₀ Γ ρ M M A m a :=
  .refl fun _ _ W => (H.1 W).1

/-- Symmetry of direct adequacy. -/
theorem LRD.Adequate.symm
    (H : LRD.Adequate Γ₀ Γ ρ M N A m a) :
    LRD.Adequate Γ₀ Γ ρ N M A m a :=
  ⟨fun _ _ W => (H.1 W).symm,
    fun _ W => LRD.DefEq.symm (H.2 W)⟩

/-- Transitivity of direct adequacy. -/
theorem LRD.Adequate.trans
    (H₁ : LRD.Adequate Γ₀ Γ ρ M₁ M₂ A m a)
    (H₂ : LRD.Adequate Γ₀ Γ ρ M₂ M₃ A m a) :
    LRD.Adequate Γ₀ Γ ρ M₁ M₃ A m a :=
  ⟨fun _ _ W => ⟨(H₁.1 W).1, (H₂.1 W).2⟩,
    fun _ W => LRD.DefEq.trans (H₁.2 W) (H₂.2 W)⟩

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.trans


/-- Lower the displayed type shape pointwise across direct adequacy. -/
theorem LRD.Adequate.mono_r_2
    (le : a ≤ a') (hm : m.HasType a) (ha' : a'.HasType .type)
    (H : LRD.Adequate Γ₀ Γ ρ M N A m a') :
    LRD.Adequate Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => ⟨
      LRD.DefEq.mono_r_2 le hm ha' (H.1 W).1,
      LRD.DefEq.mono_r_2 le hm ha' (H.1 W).2⟩,
    fun _ W => LRD.DefEq.mono_r_2 le hm ha' (H.2 W)⟩

/-- Raise the displayed type shape pointwise across direct adequacy when
the target type is directly self-valid under every direct substitution. -/
theorem LRD.Adequate.mono_r_1
    (le : a ≤ a') (hm : m.HasType a) (hm' : m.HasType a')
    (hTy : ∀ {{σ σ'}}, LR.DirectSubstWF Γ₀ σ σ' Γ ρ →
      (LRD Γ₀).TyDefEq (A.subst σ) (A.subst σ) a')
    (H : LRD.Adequate Γ₀ Γ ρ M N A m a) :
    LRD.Adequate Γ₀ Γ ρ M N A m a' :=
  ⟨fun _ _ W => ⟨
      LRD.DefEq.mono_r_1 le hm hm' (hTy W) (H.1 W).1,
      LRD.DefEq.mono_r_1 le hm hm' (hTy W) (H.1 W).2⟩,
    fun _ W => LRD.DefEq.mono_r_1 le hm hm' (hTy W) (H.2 W)⟩

/-- Lower the element shape pointwise across direct adequacy. -/
theorem LRD.Adequate.mono_l
    (le : m ≤ m') (hm : m.HasType a) (hm' : m'.HasType a)
    (H : LRD.Adequate Γ₀ Γ ρ M N A m' a) :
    LRD.Adequate Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => ⟨
      LRD.DefEq.mono_l le hm hm' (H.1 W).1,
      LRD.DefEq.mono_l le hm hm' (H.1 W).2⟩,
    fun _ W => LRD.DefEq.mono_l le hm hm' (H.2 W)⟩

/-- Canonical cross-level equivalence for direct adequacy. -/
theorem LRD.Adequate.lift
    {n n' : Nat} {m a : WShape n}
    (le : n ≤ n') (hma : m.HasType a) :
    (LRD.Adequate Γ₀ Γ ρ M N A (m.lift n') (a.lift n') ↔
      LRD.Adequate Γ₀ Γ ρ M N A m a) := by
  constructor <;> intro H
  · exact ⟨fun σ σ' W => ⟨
        (LRD.DefEq.lift (Γ := Γ₀) (n := n) (n' := n')
          (M := M.subst σ) (N := M.subst σ') (A := A.subst σ)
          (m := m) (a := a) le hma).1 (H.1 W).1,
        (LRD.DefEq.lift (Γ := Γ₀) (n := n) (n' := n')
          (M := N.subst σ) (N := N.subst σ') (A := A.subst σ)
          (m := m) (a := a) le hma).1 (H.1 W).2⟩,
      fun σ W => (LRD.DefEq.lift (Γ := Γ₀) (n := n) (n' := n')
        (M := M.subst σ) (N := N.subst σ) (A := A.subst σ)
        (m := m) (a := a) le hma).1 (H.2 W)⟩
  · exact ⟨fun σ σ' W => ⟨
        (LRD.DefEq.lift (Γ := Γ₀) (n := n) (n' := n')
          (M := M.subst σ) (N := M.subst σ') (A := A.subst σ)
          (m := m) (a := a) le hma).2 (H.1 W).1,
        (LRD.DefEq.lift (Γ := Γ₀) (n := n) (n' := n')
          (M := N.subst σ) (N := N.subst σ') (A := A.subst σ)
          (m := m) (a := a) le hma).2 (H.1 W).2⟩,
      fun σ W => (LRD.DefEq.lift (Γ := Γ₀) (n := n) (n' := n')
        (M := M.subst σ) (N := N.subst σ) (A := A.subst σ)
        (m := m) (a := a) le hma).2 (H.2 W)⟩

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.mono_r_2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.mono_r_2

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.mono_r_1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.mono_r_1

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.mono_l' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.mono_l

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.lift


/-- Extract guarded direct type validity from a term observation whose
semantic displayed type lies below a sort. -/
theorem LRD.toValTy
    {m : WShape n'} {b : WShape n}
    (le_n : n ≤ n') (le_a : b.T ≤ m.T)
    (ht : b.HasType .type)
    (hSort : LE_Interp ρ a.T (.sort u))
    (hmem' : m.HasType a)
    (H : (LRD Γ₀).DefEq M N (.sort u) m a) :
    (LRD Γ₀).TyDefEq M N b := by
  have hle := hSort.le_sort'
  refine (LRD.TyDefEq.lift le_n ht).1 ?_
  refine LRD.TyDefEq.mono_r_2
    ((TShape.LE.lift_l le_n).1 le_a)
    (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
    (WShape.HasType.mono_r hle .sort hmem').toType ?_
  exact LRD.DefEq.toTyDefEq <| LRD.DefEq.mono_r_1 hle hmem'
    (.mono_r hle .sort hmem') LRD.TyDefEq.sort H

/--
info: 'Lean4Lean.SExpr.LRD.toValTy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.toValTy


/-- Extend a guarded-direct substitution with one directly adequate
argument. -/
theorem LRD.Adequate.cons
    (ihA : ∀ {ρ n} {m a : WShape n},
      LE_Interp ρ m.T A → LE_Interp ρ a.T (.sort u) →
      m.HasType a → LRD.Adequate Γ₀ Γ ρ A A' (.sort u) m a)
    (HA : IsDefEqStrong Γ A A' (.sort u))
    {{k : Nat}} {{a₁ p : WShape k}} {{x x' σ σ' ρ}}
    (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁.T A)
    (hx : IsDefEq Γ₀ x x' (A.subst σ))
    (hv : (LRD Γ₀).DefEq x x' (A.subst σ) p a₁)
    (W : LR.DirectSubstWF Γ₀ σ σ' Γ ρ) :
    LR.DirectSubstWF Γ₀ (σ.cons x) (σ'.cons x')
      (A :: Γ) (ρ.push p.T) := by
  refine W.cons (fun hA => ?_) hA₁ hp.T HA.defeq.hasType.1
    ⟨hx, fun n a' ha' => ?_⟩
  · have ⟨_, _, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound HA W.fits).2 hA
    exact ⟨_, le_a, hA',
      (TShape.HasType.mono_r hSort.le_sort .sort hmem').toType⟩
  refine ⟨fun ht => ⟨⟨_, (HA.substCongr W.toSubstEq).1⟩, ?_⟩,
    fun m' hm' ht => ?_⟩
  · have ha' := LE_Interp.weak_iff.1 ha'
    have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound HA W.fits).2 ha' |>.out
    refine (LRD.TyDefEq.lift le_n ht).1 <|
      LRD.TyDefEq.mono_r_2 ((TShape.LE.lift_l le_n).1 le_a)
        (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
        (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType ?_
    exact LRD.DefEq.toTyDefEq <| LRD.DefEq.mono_r_1 hSort.le_sort'
      hmem' (.mono_r hSort.le_sort' .sort hmem') LRD.TyDefEq.sort
      ((ihA hA' hSort hmem').1 W).1
  · have ha' := LE_Interp.weak_iff.1 ha'
    have le_k := Nat.le_max_left k n
    have le_n := Nat.le_max_right k n
    have ht' := (WShape.HasType.lift le_n).2 ht
    have hp' := (WShape.HasType.lift le_k).2 hp
    have hle' := (TShape.LE.def le_n le_k).1
      (LE_Interp.bvar_iff.1 hm')
    have hta₁ := WShape.lift_type ▸
      (WShape.HasType.lift le_k).2 hp.isType
    have hta' := WShape.lift_type ▸
      (WShape.HasType.lift le_n).2 ht.isType
    have hc := hA₁.compat ha'
    have hj := (TShape.Join.def le_k le_n (Nat.le_refl _)).1 (.mk hc)
    rw [TShape.lift_join le_k le_n] at hj
    have ⟨hj1, hj2⟩ := hj.le
    have hJ := hta₁.join' hj hta'
    have hJ' := hJ.mono_r hj1 hp'
    refine (LRD.DefEq.lift le_n ht).1 <|
      LRD.DefEq.mono_r_2 hj2 ht' hJ <|
      LRD.DefEq.mono_l hle' (hJ.mono_r hj2 ht') hJ' <|
      LRD.DefEq.mono_r_1 hj1 hp' hJ' ?_ <|
      (LRD.DefEq.lift le_k hp).2 hv
    have valTyA {nd : Nat} {a : WShape nd}
        (hA : LE_Interp ρ a.T A) (ha : a.HasType .type) :
        (LRD Γ₀).TyDefEq (A.subst σ) (A.subst σ) a := by
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.sound HA W.left.fits).2 hA |>.out
      have v2 := (ihA hA' hSort hmem').2 W.left
      have vt := LRD.TyDefEq.left <| LRD.DefEq.toTyDefEq <|
        LRD.DefEq.mono_r_1 hSort.le_sort' hmem'
          (.mono_r hSort.le_sort' .sort hmem') LRD.TyDefEq.sort v2
      exact (LRD.TyDefEq.lift le_n ha).1 <|
        LRD.TyDefEq.mono_r_2 ((TShape.LE.lift_l le_n).1 le_a)
          (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ha)
          (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType vt
    exact LRD.TyDefEq.join ((TShape.Compat.def le_k le_n).2 hc)
      hta₁ hta'
      ((LRD.TyDefEq.lift le_k hp.isType).2 (valTyA hA₁ hp.isType))
      ((LRD.TyDefEq.lift le_n ht.isType).2 (valTyA ha' ht.isType))

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.cons' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.cons


/-- Exact informative Pi branch of guarded-direct self adequacy.  The
ordinary adequacy premise supplies the additive legacy projection; the
domain and codomain callbacks construct the retained direct sidecar. -/
theorem LRD.Adequate.forallESelf_exact
    {Γ₀ Γ : List SExpr} {ρ : Valuation}
    {A body : SExpr} {u v : SLevel}
    {k : Nat} {a₂ : WShape k} {a₁ : WShapeFun k} {r : Bool}
    (HA : IsDefEqStrong Γ A A (.sort u))
    (HBody : IsDefEqStrong (A :: Γ) body body (.sort v))
    (hM : LE_Interp ρ (WShape.forallE a₂ a₁).T
      (SExpr.forallE A body))
    (aty : WShape.HasTypePi a₁ a₂ r)
    (ihA : ∀ {ρ n} {ma aa : WShape n},
      LE_Interp ρ ma.T A → LE_Interp ρ aa.T (.sort u) →
      ma.HasType aa → LRD.Adequate Γ₀ Γ ρ A A (.sort u) ma aa)
    (ihBody : ∀ {ρ n} {mb ab : WShape n},
      LE_Interp ρ mb.T body → LE_Interp ρ ab.T (.sort v) →
      mb.HasType ab →
      LRD.Adequate Γ₀ (A :: Γ) ρ body body (.sort v) mb ab)
    (legacy : LR.Adequate Γ₀ Γ ρ
      (SExpr.forallE A body) (SExpr.forallE A body)
      (.sort (.imax u v)) (WShape.forallE a₂ a₁) (.sort r)) :
    LRD.Adequate Γ₀ Γ ρ
      (SExpr.forallE A body) (SExpr.forallE A body)
      (.sort (.imax u v)) (WShape.forallE a₂ a₁) (.sort r) := by
  have atyW := WShape.HasTypePi.iff.1 aty
  have hA1 := hM.forallE_inv.1
  have cons := LRD.Adequate.cons ihA HA
  have HPi : IsDefEqStrong Γ (SExpr.forallE A body)
      (SExpr.forallE A body) (.sort (.imax u v)) :=
    .forallEDF HA HBody HBody
  refine .refl fun σ σ' W => ?_
  have legacyEdge := (legacy.1 W.toSubstWF).1
  have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
    (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
  have HAσ := (HA.substCongr W.toSubstEq).1
  have S' := W.toSubstEq.lift HA.defeq.hasType.1
  have HBodyσ := (HBody.substCongr S').1
  have hPiCongr := HPi.substCongr W.toSubstEq
  have rootL : TypeWHRedPath Γ₀
      ((SExpr.forallE A body).subst σ)
      (SExpr.forallE (A.subst σ) (body.subst σ.lift)) := by
    simpa only [SExpr.subst] using
      TypeWHRedPath.refl hPiCongr.1.hasType.1
  have rootR : TypeWHRedPath Γ₀
      ((SExpr.forallE A body).subst σ')
      (SExpr.forallE (A.subst σ') (body.subst σ'.lift)) := by
    simpa only [SExpr.subst] using
      TypeWHRedPath.refl hPiCongr.1.hasType.2
  have domain : (LRD (n := k) Γ₀).TyDefEq
      (A.subst σ) (A.subst σ') a₂ :=
    LRD.toValTy le_n le_a atyW.1.isType hSort hmem'
      ((ihA hA' hSort hmem').1 W).1
  have pi : LR.DirectPiDefEq (LRD (n := k) Γ₀)
      (A.subst σ) (body.subst σ.lift) (body.subst σ'.lift)
      a₂ a₁ := by
    constructor
    · intro x x' p hp ha hv
      have hB := hM.forallE_inv'.2 p
      have WL := cons hp hA1 ha hv W.left
      have ⟨_, _, _, leL, leL', iBL, ivL, hmbL⟩ :=
        (LE_Interp.sound HBody WL.fits).2 hB |>.out
      have semL : (LRD (n := k) Γ₀).TyDefEq
          ((body.subst σ.lift).inst x)
          ((body.subst σ.lift).inst x') (a₁.app p) := by
        simpa [inst_lift_cons] using
          LRD.toValTy leL leL' (atyW.2 _ hp).toType ivL hmbL
            ((ihBody iBL ivL hmbL).1 WL).1
      have valA := LRD.toValTy le_n le_a atyW.1.isType
        hSort hmem' ((ihA hA' hSort hmem').1 W).1
      have WR := cons hp hA1 (HAσ.defeqDF ha)
        (LRD.DefEq.conv valA hv) W.symm.left
      have ⟨_, _, _, leR, leR', iBR, ivR, hmbR⟩ :=
        (LE_Interp.sound HBody WR.fits).2 hB |>.out
      have semR : (LRD (n := k) Γ₀).TyDefEq
          ((body.subst σ'.lift).inst x)
          ((body.subst σ'.lift).inst x') (a₁.app p) := by
        simpa [inst_lift_cons] using
          LRD.toValTy leR leR' (atyW.2 _ hp).toType ivR hmbR
            ((ihBody iBR ivR hmbR).1 WR).1
      have rawL : IsDefEq Γ₀
          ((body.subst σ.lift).inst x)
          ((body.subst σ.lift).inst x') (.sort v) := by
        simpa only [inst_lift_cons, SExpr.subst] using
          (HBody.substCongr WL.toSubstEq).1
      have rawR : IsDefEq Γ₀
          ((body.subst σ'.lift).inst x)
          ((body.subst σ'.lift).inst x') (.sort v) := by
        simpa only [inst_lift_cons, SExpr.subst] using
          (HBody.substCongr WR.toSubstEq).1
      exact ⟨semL, semR, ⟨v, rawL⟩, ⟨v, rawR⟩⟩
    · intro x p hp ha hv
      have hB := hM.forallE_inv'.2 p
      have WX := cons hp hA1 ha.hasType.1
        (LRD.DefEq.left hv) W
      have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
        (LE_Interp.sound HBody WX.fits).2 hB |>.out
      have hout : (LRD (n := k) Γ₀).TyDefEq
          ((body.subst σ.lift).inst x)
          ((body.subst σ'.lift).inst x) (a₁.app p) := by
        simpa [inst_lift_cons] using
          LRD.toValTy le le' (atyW.2 _ hp).toType iv hmb
            ((ihBody iB iv hmb).1 WX).1
      exact cast (by congr 1) hout
  have sidecar : LR.DirectValTyPi2 (LRD (n := k) Γ₀)
      ((SExpr.forallE A body).subst σ)
      ((SExpr.forallE A body).subst σ') a₂ a₁ :=
    ⟨A.subst σ, body.subst σ.lift,
      A.subst σ', body.subst σ'.lift, u, v,
      rootL, rootR, .single HAσ, .single HBodyσ, domain, pi⟩
  exact LRD.DefEq.of_sort legacyEdge <|
    LRD.TyDefEq.forallE ((LR Γ₀).toType legacyEdge) sidecar

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.forallESelf_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.forallESelf_exact


/-- Guarded-direct self adequacy for dependent products across every
semantic shape.  Noninformative and impossible cases are discharged by the
shape analysis; the informative Pi case preserves its typed roots and direct
domain/codomain action through `forallESelf_exact`. -/
theorem LRD.Adequate.forallESelf
    {Γ : List SExpr} {A body : SExpr} {u v : SLevel}
    {ρ : Valuation} {n : Nat} {m a : WShape n}
    (HA : IsDefEqStrong Γ A A (.sort u))
    (HBody : IsDefEqStrong (A :: Γ) body body (.sort v))
    (hM : LE_Interp ρ m.T (.forallE A body))
    (hA : LE_Interp ρ a.T (.sort (.imax u v)))
    (hmem : m.HasType a)
    (ihA : ∀ {ρ n} {ma aa : WShape n},
      LE_Interp ρ ma.T A → LE_Interp ρ aa.T (.sort u) →
      ma.HasType aa → LRD.Adequate Γ₀ Γ ρ A A (.sort u) ma aa)
    (ihBody : ∀ {ρ n} {mb ab : WShape n},
      LE_Interp ρ mb.T body → LE_Interp ρ ab.T (.sort v) →
      mb.HasType ab →
      LRD.Adequate Γ₀ (A :: Γ) ρ body body (.sort v) mb ab)
    (legacy : LR.Adequate Γ₀ Γ ρ
      (.forallE A body) (.forallE A body)
      (.sort (.imax u v)) m a) :
    LRD.Adequate Γ₀ Γ ρ (.forallE A body) (.forallE A body)
      (.sort (.imax u v)) m a := by
  cases hmem.unfold with
  | bot hm =>
    cases hm.unfold with
    | forallE =>
      let .sort h := hA
      cases (TShape.LE.lift_r (by simp [TShape.sort])).1 h
    | _ => exact .bot hmem.isType
  | sort =>
    cases n <;>
      have .forallE _ _ _ _ h := hM <;>
      cases TShape.sort_not_le_forallE h
  | @lam _ f₀ =>
    revert hM
    unfold WShape.lam'
    split <;> [skip; exact fun _ => .bot hmem.isType]
    intro | .forallE _ _ _ _ h => cases TShape.lam_not_le_forallE h
  | ctor =>
    have .forallE _ _ _ _ h := hM
    cases TShape.ctor_not_le_forallE h
  | indTy =>
    have .forallE _ _ _ _ h := hM
    cases TShape.indTy_not_le_forallE h
  | @forallE k a₂ a₁ r aty =>
    exact LRD.Adequate.forallESelf_exact
      HA HBody hM aty ihA ihBody legacy

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.forallESelf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.forallESelf


/-- Exact informative lambda branch of guarded-direct self adequacy.  The
legacy premise supplies the additive first projection; typed beta paths and
the direct body induction supply the retained extensional action. -/
theorem LRD.Adequate.lamSelf_exact
    {Γ₀ Γ : List SExpr} {ρ : Valuation}
    {A B body : SExpr} {u v : SLevel}
    {k : Nat} {g a₂ : WShapeFun k} {hg : g.NonZero}
    {a₁ : WShape k}
    (HA : IsDefEqStrong Γ A A (.sort u))
    (HB : IsDefEqStrong (A :: Γ) B B (.sort v))
    (HBody : IsDefEqStrong (A :: Γ) body body B)
    (hTerm : LE_Interp ρ (WShape.lam g hg).T (SExpr.lam A body))
    (hPi : LE_Interp ρ (WShape.forallE a₁ a₂).T
      (SExpr.forallE A B))
    (htm : WShape.HasTypeLam g a₁ a₂)
    (ihA : ∀ {ρ n} {ma aa : WShape n},
      LE_Interp ρ ma.T A → LE_Interp ρ aa.T (.sort u) →
      ma.HasType aa → LRD.Adequate Γ₀ Γ ρ A A (.sort u) ma aa)
    (ihB : ∀ {ρ n} {mb ab : WShape n},
      LE_Interp ρ mb.T B → LE_Interp ρ ab.T (.sort v) →
      mb.HasType ab →
      LRD.Adequate Γ₀ (A :: Γ) ρ B B (.sort v) mb ab)
    (ihBody : ∀ {ρ n} {mb ab : WShape n},
      LE_Interp ρ mb.T body → LE_Interp ρ ab.T B →
      mb.HasType ab → LRD.Adequate Γ₀ (A :: Γ) ρ body body B mb ab)
    (legacy : LR.Adequate Γ₀ Γ ρ
      (SExpr.lam A body) (SExpr.lam A body) (SExpr.forallE A B)
      (WShape.lam g hg) (WShape.forallE a₁ a₂)) :
    LRD.Adequate Γ₀ Γ ρ
      (SExpr.lam A body) (SExpr.lam A body) (SExpr.forallE A B)
      (WShape.lam g hg) (WShape.forallE a₁ a₂) := by
  have htmW := WShape.HasTypeLam.iff.1 htm
  have atyW := WShape.HasTypePi.iff.1 htm.1
  have hA1 := hPi.forallE_inv.1
  have cons := LRD.Adequate.cons ihA HA
  have HPi : IsDefEqStrong Γ (SExpr.forallE A B)
      (SExpr.forallE A B) (.sort (.imax u v)) :=
    .forallEDF HA HB HB
  refine .refl fun σ σ' W => ?_
  have legacyEdge := (legacy.1 W.toSubstWF).1
  have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
    (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
  have HAσ := (HA.substCongr W.toSubstEq).1
  have SLeft := W.left.toSubstEq.lift HA.defeq.hasType.1
  have SRight := W.symm.left.toSubstEq.lift HA.defeq.hasType.1
  have hTypA : IsDefEq Γ₀ (A.subst σ) (A.subst σ) (.sort u) :=
    HA.defeq.subst W.left.toSubstEq.left
  have hTypB : IsDefEq (A.subst σ :: Γ₀)
      (B.subst σ.lift) (B.subst σ.lift) (.sort v) :=
    HB.defeq.subst SLeft.left
  have root : TypeWHRedPath Γ₀ ((SExpr.forallE A B).subst σ)
      (SExpr.forallE (A.subst σ) (B.subst σ.lift)) := by
    simpa only [SExpr.subst] using
      TypeWHRedPath.refl (HPi.substCongr W.toSubstEq).1.hasType.1
  have domain : (LRD (n := k) Γ₀).TyDefEq
      (A.subst σ) (A.subst σ) a₁ :=
    LRD.TyDefEq.left <| LRD.toValTy le_n le_a atyW.1.isType
      hSort hmem' ((ihA hA' hSort hmem').2 W.left)
  have pi : LR.DirectPiDefEq (LRD (n := k) Γ₀)
      (A.subst σ) (B.subst σ.lift) (B.subst σ.lift) a₁ a₂ := by
    have edge : ∀ {{x x' p}}, p.HasType a₁ →
        IsDefEq Γ₀ x x' (A.subst σ) →
        (LRD (n := k) Γ₀).DefEq x x' (A.subst σ) p a₁ →
        LR.DirectPiInstDefEq (LRD (n := k) Γ₀)
          (B.subst σ.lift) (B.subst σ.lift) x x' (a₂.app p) := by
      intro x x' p hp ha hv
      have W' := cons hp hA1 ha hv W.left
      have hBsem := hPi.forallE_inv'.2 p
      have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
        (LE_Interp.sound HB W'.fits).2 hBsem |>.out
      have hsem : (LRD (n := k) Γ₀).TyDefEq
          ((B.subst σ.lift).inst x)
          ((B.subst σ.lift).inst x') (a₂.app p) := by
        simpa [inst_lift_cons] using
          LRD.toValTy le le' (atyW.2 _ hp).toType iv hmb
            ((ihB iB iv hmb).1 W').1
      have hraw : IsDefEq Γ₀
          ((B.subst σ.lift).inst x)
          ((B.subst σ.lift).inst x') (.sort v) := by
        simpa only [inst_lift_cons, SExpr.subst] using
          (HB.substCongr W'.toSubstEq).1
      exact ⟨hsem, hsem, ⟨v, hraw⟩, ⟨v, hraw⟩⟩
    exact ⟨edge, fun _ _ hp ha hv => (edge hp ha hv).leftTy⟩
  have action : LR.DirectLamDefEq (LRD (n := k) Γ₀)
      ((SExpr.lam A body).subst σ) ((SExpr.lam A body).subst σ')
      (A.subst σ) (B.subst σ.lift) g a₁ a₂ := by
    have betaL {t : SExpr} (ht : IsDefEq Γ₀ t t (A.subst σ)) :
        TypedWHRedS Γ₀
          (((SExpr.lam A body).subst σ).app t)
          ((body.subst σ.lift).inst t)
          ((B.subst σ.lift).inst t) := by
      simpa only [SExpr.subst] using
        TypedWHRedS.beta (HBody.defeq.subst SLeft.left) ht
    have betaR {t : SExpr} (ht : IsDefEq Γ₀ t t (A.subst σ')) :
        TypedWHRedS Γ₀
          (((SExpr.lam A body).subst σ').app t)
          ((body.subst σ'.lift).inst t)
          ((B.subst σ'.lift).inst t) := by
      simpa only [SExpr.subst] using
        TypedWHRedS.beta (HBody.defeq.subst SRight.left) ht
    constructor
    · intro x x' p hp ha hv
      have hBodySem := hTerm.lam_inv' p
      have hBsem := hPi.forallE_inv'.2 p
      have houtTy := htmW.2.2 p hp
      have WL := cons hp hA1 ha hv W.left
      have bodyL := ((ihBody hBodySem hBsem houtTy).1 WL).1
      have bodyL' : (LRD (n := k) Γ₀).DefEq
          ((body.subst σ.lift).inst x)
          ((body.subst σ.lift).inst x')
          ((B.subst σ.lift).inst x) (g.app p) (a₂.app p) := by
        simpa only [inst_lift_cons] using bodyL
      have piL := pi.1 hp ha hv
      obtain ⟨_, rawL⟩ := piL.leftDefEq
      have betaL' := betaL ha.hasType.2
      have betaLAt : TypedWHRedS Γ₀
          (((SExpr.lam A body).subst σ).app x')
          ((body.subst σ.lift).inst x')
          ((B.subst σ.lift).inst x) :=
        ⟨rawL.symm.defeqDF betaL'.defeq, betaL'.reduction⟩
      have outL := (LRD.DefEq.whr (LRD.TyDefEq.left piL.leftTy)
        (betaL ha.hasType.1) betaLAt).2 bodyL'

      have ha' : IsDefEq Γ₀ x x' (A.subst σ') :=
        HAσ.defeqDF ha
      have hv' := LRD.DefEq.conv
        (LRD.toValTy le_n le_a atyW.1.isType hSort hmem'
          ((ihA hA' hSort hmem').1 W).1) hv
      have WR := cons hp hA1 ha' hv' W.symm.left
      have bodyR := ((ihBody hBodySem hBsem houtTy).1 WR).1
      have bodyR0 : (LRD (n := k) Γ₀).DefEq
          ((body.subst σ'.lift).inst x)
          ((body.subst σ'.lift).inst x')
          ((B.subst σ'.lift).inst x) (g.app p) (a₂.app p) := by
        simpa only [inst_lift_cons] using bodyR
      have W2 := cons hp hA1 ha.hasType.1 (LRD.DefEq.left hv) W
      have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
        (LE_Interp.sound HB W2.fits).2 hBsem |>.out
      have vtBB : (LRD (n := k) Γ₀).TyDefEq
          ((B.subst σ.lift).inst x)
          ((B.subst σ'.lift).inst x) (a₂.app p) := by
        simpa [inst_lift_cons] using
          LRD.toValTy le le' (atyW.2 _ hp).toType iv hmb
            ((ihB iB iv hmb).1 W2).1
      have rawRx : IsDefEq Γ₀
          ((B.subst σ.lift).inst x)
          ((B.subst σ'.lift).inst x) (.sort v) := by
        simpa only [inst_lift_cons, SExpr.subst] using
          HB.subst W2.toSubstEq
      have Wcross := cons hp hA1 ha hv W
      have rawRx' : IsDefEq Γ₀
          ((B.subst σ.lift).inst x)
          ((B.subst σ'.lift).inst x') (.sort v) := by
        simpa only [inst_lift_cons, SExpr.subst] using
          HB.subst Wcross.toSubstEq
      have betaRx := betaR ha'.hasType.1
      have betaRx' := betaR ha'.hasType.2
      have betaRxAt : TypedWHRedS Γ₀
          (((SExpr.lam A body).subst σ').app x)
          ((body.subst σ'.lift).inst x)
          ((B.subst σ.lift).inst x) :=
        ⟨rawRx.symm.defeqDF betaRx.defeq, betaRx.reduction⟩
      have betaRx'At : TypedWHRedS Γ₀
          (((SExpr.lam A body).subst σ').app x')
          ((body.subst σ'.lift).inst x')
          ((B.subst σ.lift).inst x) :=
        ⟨rawRx'.symm.defeqDF betaRx'.defeq, betaRx'.reduction⟩
      have bodyR' := LRD.DefEq.conv (LRD.TyDefEq.symm vtBB) bodyR0
      have outR := (LRD.DefEq.whr (LRD.TyDefEq.left vtBB)
        betaRxAt betaRx'At).2 bodyR'
      exact ⟨outL, outR⟩
    · intro x p hp ha hv
      have hBodySem := hTerm.lam_inv' p
      have hBsem := hPi.forallE_inv'.2 p
      have houtTy := htmW.2.2 p hp
      have Wcross := cons hp hA1 ha.hasType.1 (LRD.DefEq.left hv) W
      have bodyCross := ((ihBody hBodySem hBsem houtTy).1 Wcross).1
      have bodyCross' : (LRD (n := k) Γ₀).DefEq
          ((body.subst σ.lift).inst x)
          ((body.subst σ'.lift).inst x)
          ((B.subst σ.lift).inst x) (g.app p) (a₂.app p) := by
        simpa only [inst_lift_cons] using bodyCross
      have rawCross : IsDefEq Γ₀
          ((B.subst σ.lift).inst x)
          ((B.subst σ'.lift).inst x) (.sort v) := by
        simpa only [inst_lift_cons, SExpr.subst] using
          HB.subst Wcross.toSubstEq
      have betaRx := betaR (HAσ.defeqDF ha).hasType.1
      have betaRAt : TypedWHRedS Γ₀
          (((SExpr.lam A body).subst σ').app x)
          ((body.subst σ'.lift).inst x)
          ((B.subst σ.lift).inst x) :=
        ⟨rawCross.symm.defeqDF betaRx.defeq, betaRx.reduction⟩
      exact (LRD.DefEq.whr (pi.2 hp ha (LRD.DefEq.left hv))
        (betaL ha) betaRAt).2 bodyCross'
  exact LRD.DefEq.lam legacyEdge
    ⟨A.subst σ, B.subst σ.lift, u, v, root,
      hTypA, domain, hTypB, pi, action⟩

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.lamSelf_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.lamSelf_exact


/-- Guarded-direct self adequacy for lambdas across every semantic shape.
The only informative branch is a non-bottom lambda paired with its Pi type;
all other branches are bottom or incompatible with the lambda interpreter. -/
theorem LRD.Adequate.lamSelf
    {Γ : List SExpr} {A B body : SExpr} {u v : SLevel}
    {ρ : Valuation} {n : Nat} {m a : WShape n}
    (HA : IsDefEqStrong Γ A A (.sort u))
    (HB : IsDefEqStrong (A :: Γ) B B (.sort v))
    (HBody : IsDefEqStrong (A :: Γ) body body B)
    (hTerm : LE_Interp ρ m.T (.lam A body))
    (hPi : LE_Interp ρ a.T (.forallE A B))
    (hmem : m.HasType a)
    (ihA : ∀ {ρ n} {ma aa : WShape n},
      LE_Interp ρ ma.T A → LE_Interp ρ aa.T (.sort u) →
      ma.HasType aa → LRD.Adequate Γ₀ Γ ρ A A (.sort u) ma aa)
    (ihB : ∀ {ρ n} {mb ab : WShape n},
      LE_Interp ρ mb.T B → LE_Interp ρ ab.T (.sort v) →
      mb.HasType ab →
      LRD.Adequate Γ₀ (A :: Γ) ρ B B (.sort v) mb ab)
    (ihBody : ∀ {ρ n} {mb ab : WShape n},
      LE_Interp ρ mb.T body → LE_Interp ρ ab.T B →
      mb.HasType ab → LRD.Adequate Γ₀ (A :: Γ) ρ body body B mb ab)
    (legacy : LR.Adequate Γ₀ Γ ρ
      (.lam A body) (.lam A body) (.forallE A B) m a) :
    LRD.Adequate Γ₀ Γ ρ
      (.lam A body) (.lam A body) (.forallE A B) m a := by
  cases hmem.unfold with
  | bot hm => exact .bot hm
  | sort =>
    cases n <;>
      let .lam _ _ _ h := hTerm <;>
      cases TShape.sort_not_le_lam' h
  | forallE =>
    let .lam _ _ _ h := hTerm
    cases TShape.forallE_not_le_lam' h
  | @lam k g a₁ a₂ htm =>
    unfold WShape.lam' at hTerm legacy ⊢
    split at hTerm <;> rename_i hg
    · simp only [dif_pos hg] at legacy ⊢
      exact LRD.Adequate.lamSelf_exact HA HB HBody hTerm hPi htm
        ihA ihB ihBody legacy
    · simp only [dif_neg hg] at legacy ⊢
      exact .bot hmem.isType
  | ctor =>
    let .lam _ _ _ h := hTerm
    cases TShape.ctor_not_le_lam' h
  | indTy =>
    let .lam _ _ _ h := hTerm
    cases TShape.indTy_not_le_lam' h

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.lamSelf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.lamSelf






/-- Exact-shape reflexive fundamental application for guarded direct
adequacy. -/
theorem LRD.Adequate.appSelf_exact
    {n : Nat} {Γ₀ Γ : List SExpr} {ρ : Valuation}
    {F X A B : SExpr}
    {mf : WShapeFun n} {hmf : mf.NonZero}
    {b p : WShape n} {tf : WShapeFun n}
    (hX : IsDefEqStrong Γ X X A)
    (hp : p.HasType b)
    (Hf : LRD.Adequate Γ₀ Γ ρ F F (SExpr.forallE A B)
      (WShape.lam mf hmf) (WShape.forallE b tf))
    (Hx : LRD.Adequate Γ₀ Γ ρ X X A p b) :
    LRD.Adequate Γ₀ Γ ρ (SExpr.app F X) (SExpr.app F X)
      (B.inst X) (mf.app p) (tf.app p) :=
  .refl fun σ σ' W => by
    simpa only [SExpr.subst, SExpr.subst_inst] using
      LRD.DefEq.app
        (by simpa only [SExpr.subst] using (Hf.1 W).1)
        hp (hX.substCongr W.toSubstEq).1 (Hx.1 W).1

/-- Exact-shape heterogeneous fundamental application.  The instantiated
result-type adequacy supplies the one conversion needed by the right
congruence edge. -/
theorem LRD.Adequate.app_exact
    {n : Nat} {Γ₀ Γ : List SExpr} {ρ : Valuation}
    {F F' X X' A B : SExpr} {v : SLevel} {r : Bool}
    {mf : WShapeFun n} {hmf : mf.NonZero}
    {b p : WShape n} {tf : WShapeFun n}
    (hX : IsDefEqStrong Γ X X' A)
    (hp : p.HasType b)
    (Hf : LRD.Adequate Γ₀ Γ ρ F F' (SExpr.forallE A B)
      (WShape.lam mf hmf) (WShape.forallE b tf))
    (Hx : LRD.Adequate Γ₀ Γ ρ X X' A p b)
    (HBa : LRD.Adequate Γ₀ Γ ρ (B.inst X) (B.inst X')
      (.sort v) (tf.app p) (.sort r)) :
    LRD.Adequate Γ₀ Γ ρ (SExpr.app F X) (SExpr.app F' X')
      (B.inst X) (mf.app p) (tf.app p) := by
  refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
  · simpa only [SExpr.subst, SExpr.subst_inst] using
      LRD.DefEq.app
        (by simpa only [SExpr.subst] using (Hf.1 W).1)
        hp (hX.substCongr W.toSubstEq).1 (Hx.1 W).1
  · have happ : (LRD (n := n) Γ₀).DefEq
        ((SExpr.app F' X').subst σ) ((SExpr.app F' X').subst σ')
        ((B.inst X').subst σ) (mf.app p) (tf.app p) := by
      simpa only [SExpr.subst, SExpr.subst_inst] using
        LRD.DefEq.app
          (by simpa only [SExpr.subst] using (Hf.1 W).2)
          hp (hX.substCongr W.toSubstEq).2 (Hx.1 W).2
    have hTy : (LRD (n := n) Γ₀).TyDefEq
        ((B.inst X').subst σ) ((B.inst X).subst σ) (tf.app p) :=
      LRD.TyDefEq.symm (LRD.DefEq.toTyDefEq (HBa.2 W.left))
    exact LRD.DefEq.conv hTy happ
  · simpa only [SExpr.subst, SExpr.subst_inst] using
      LRD.DefEq.app
        (by simpa only [SExpr.subst] using Hf.2 W)
        hp (hX.subst W.toSubstEq) (Hx.2 W)

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.appSelf_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.appSelf_exact

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.app_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.app_exact
/-- Guarded-direct adequacy is closed under dependent application.
The proof aligns the independently interpreted function, argument, and result
shapes at one common level, retains the joined result type directly, applies
the exact guarded Pi action, and lowers back to the requested observation. -/
theorem LRD.adequateApp
    {Γ : List SExpr} {A B F F' X X' : SExpr} {v : SLevel}
    {ρ : Valuation} {n : Nat} {m a : WShape n}
    (Hf : IsDefEqStrong Γ F F' (A.forallE B))
    (Ha : IsDefEqStrong Γ X X' A)
    (HBa : IsDefEqStrong Γ (B.inst X) (B.inst X') (.sort v))
    (hM : LE_Interp ρ m.T (.app F X))
    (hA : LE_Interp ρ a.T (B.inst X))
    (hmem : m.HasType a)
    (ihf : ∀ {n'} {mf af : WShape n'},
      LE_Interp ρ mf.T F → LE_Interp ρ af.T (.forallE A B) →
      mf.HasType af →
      LRD.Adequate Γ₀ Γ ρ F F' (.forallE A B) mf af)
    (iha : ∀ {n'} {ma aa : WShape n'},
      LE_Interp ρ ma.T X → LE_Interp ρ aa.T A → ma.HasType aa →
      LRD.Adequate Γ₀ Γ ρ X X' A ma aa)
    (ihBa : ∀ {n'} {mb av : WShape n'},
      LE_Interp ρ mb.T (B.inst X) → LE_Interp ρ av.T (.sort v) →
      mb.HasType av →
      LRD.Adequate Γ₀ Γ ρ (B.inst X) (B.inst X') (.sort v) mb av) :
    LRD.Adequate Γ₀ Γ ρ (.app F X) (.app F' X')
      (B.inst X) m a := by
  cases hM with
  | bot =>
    exact ⟨fun _ _ _ => ⟨LRD.DefEq.bot hmem.isType,
        LRD.DefEq.bot hmem.isType⟩,
      fun _ _ => LRD.DefEq.bot hmem.isType⟩
  | @app _ nf_app f _ _ _ x hif hia le_m =>
    suffices ∀ {F F' X X' σ σ'},
        LR.DirectSubstWF Γ₀ σ σ' Γ ρ →
        IsDefEqStrong Γ F F' (A.forallE B) →
        IsDefEqStrong Γ X X' A →
        IsDefEqStrong Γ (B.inst X) (B.inst X') (.sort v) →
        LE_Interp ρ f.T F → LE_Interp ρ x.T X →
        LE_Interp ρ a.T (B.inst X) →
        (∀ {n'} {mf af : WShape n'}, LE_Interp ρ mf.T F →
          LE_Interp ρ af.T (.forallE A B) → mf.HasType af →
          LRD.Adequate Γ₀ Γ ρ F F' (.forallE A B) mf af) →
        (∀ {n'} {ma aa : WShape n'}, LE_Interp ρ ma.T X →
          LE_Interp ρ aa.T A → ma.HasType aa →
          LRD.Adequate Γ₀ Γ ρ X X' A ma aa) →
        (∀ {n'} {mb av : WShape n'}, LE_Interp ρ mb.T (B.inst X) →
          LE_Interp ρ av.T (.sort v) → mb.HasType av →
          LRD.Adequate Γ₀ Γ ρ (B.inst X) (B.inst X')
            (.sort v) mb av) →
        (LRD Γ₀).DefEq (.subst (.app F X) σ)
          (.subst (.app F' X') σ')
          (.subst (B.inst X) σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩,
        fun σ W => this W Hf Ha HBa hif hia hA ihf iha ihBa⟩
      · refine this W (Hf.trans Hf.symm) (Ha.trans Ha.symm)
          (HBa.trans HBa.symm) hif hia hA ?_ ?_ ?_
        · exact fun hf hPi hmf => (ihf hf hPi hmf).left
        · exact fun ha hA hma => (iha ha hA hma).left
        · exact fun hB hv hmb => (ihBa hB hv hmb).left
      · refine LRD.DefEq.conv (LRD.TyDefEq.symm ?_) <| this W
          (Hf.symm.trans Hf) (Ha.symm.trans Ha)
          (HBa.symm.trans HBa)
          ((LE_Interp.sound Hf W.fits).1.1 hif)
          ((LE_Interp.sound Ha W.fits).1.1 hia)
          ((LE_Interp.sound HBa W.fits).1.1 hA)
          (fun hf hPi hmf => ?_) (fun ha hA hma => ?_)
          (fun hB hv hmb => ?_)
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.sound HBa W.fits).2 hA |>.out
          exact LRD.toValTy le le' hmem.isType iv hmb
            ((ihBa iB iv hmb).2 W.left)
        · exact (ihf ((LE_Interp.sound Hf W.left.fits).1.2 hf)
            hPi hmf).symm.left
        · exact (iha ((LE_Interp.sound Ha W.left.fits).1.2 ha)
            hA hma).symm.left
        · exact (ihBa ((LE_Interp.sound HBa W.left.fits).1.2 hB)
            hv hmb).symm.left
    intro F F' X X' σ σ' W hF hX hBa hif hia hA ihf iha ihBa
    have ⟨_, mf, _, le_nf, le_mf, hf', hPi, hmf⟩ :=
      (LE_Interp.sound hF W.left.fits).2 hif |>.out
    have Af := ihf hf' hPi hmf
    by_cases hm0 : mf = .bot
    · simp only [hm0] at le_mf hmf
      refine (?_ : m = .bot) ▸ LRD.DefEq.bot hmem.isType
      cases show f = .bot from TShape.le_bot.1 (le_mf.trans TShape.bot_le')
      exact TShape.le_bot.1
        ((WShape.bot_app ▸ le_m).trans TShape.bot_eqv.1)
    cases hPi with
    | bot => cases hm0 hmf.bot_r
    | forallE haA hbA hd hiB le =>
      cases hmf.unfold with
      | bot => cases hm0 rfl
      | lam hg =>
        rename_i n₁ b₁' b₂' f' n₂ b₁ b₂ f
        simp at le_nf
        let k := max n (max n₁ n₂)
        have hk := Nat.max_le.1 (Nat.le_refl k)
        rw [Nat.max_le] at hk
        have le_nf_k : nf_app ≤ k := Nat.le_trans le_nf hk.2.2
        have hA' := hA.lift hk.1
        have ⟨_, le_x', hx'_a₁, hgx2⟩ :=
          WShape.HasDom.iff.1 hg.2.1 (x.lift _)
        have hia' := (hia.lift le_nf).mono le_x'.T
        have hax' := LE_Interp.forallE' haA hbA hd hiB
          |>.mono le |>.forallE_inv.2 hia'
        have hJ := TShape.Join.mk (hA.compat hax')
        have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
        have hk' := Nat.max_le.2 ⟨hk.1, hk.2.2⟩
        have hJ1' := (TShape.LE.def hk.1 hk').1 hJ1
        have hJ2' := (TShape.LE.def hk.2.2 hk').1 hJ2
        have hgx' := (WShape.HasTypeLam.iff.1 hg).2.2 _ hx'_a₁
        have hJ_t := TShape.HasType.sort_r.2 hmem.isType
          |>.join' hJ <| TShape.HasType.sort_r.2 hgx'.isType
        have hmem_k := (WShape.HasType.lift hk.1).2 hmem
        rw [subst_inst]
        have hJ_t' := TShape.HasType.sort_r.1 <|
          hJ_t.mono_l (TShape.lift_eqv hk').2
            (TShape.lift_eqv hk').1
        refine (LRD.DefEq.lift hk.1 hmem).1 <|
          LRD.DefEq.mono_r_2 hJ1' hmem_k hJ_t' ?_
        have hgx'' := (WShape.HasType.lift hk.2.2).2 hgx'
        refine LRD.DefEq.mono_l ?_
          (.mono_r hJ1' hJ_t' hmem_k)
          (.mono_r hJ2' hJ_t' hgx'') ?_
        · exact (TShape.LE.def hk.1 hk.2.2).1 <| le_m.trans <|
            (TShape.app_mono le_mf (TShape.lift_eqv le_nf).2).trans
              (WShape.lam'_app ▸ hgx2.T)
        refine LRD.DefEq.mono_r_1 hJ2' hgx''
          (.mono_r hJ2' hJ_t' hgx'') ?_ ?_
        · have ⟨_, _, _, le_j, le_j', hBj, hSj, hmj⟩ :=
            (LE_Interp.sound hBa W.left.fits).2
              (hA.join hJ hax') |>.out
          exact LRD.TyDefEq.left <|
            (LRD.TyDefEq.lift hk'
              (TShape.HasType.sort_r.1 hJ_t)).2 <|
              subst_inst ▸ LRD.toValTy le_j le_j'
                (TShape.HasType.sort_r.1 hJ_t) hSj hmj
                ((ihBa hBj hSj hmj).2 W.left)
        · have hAf := LRD.DefEq.trans (Af.2 W.left) (Af.1 W).2
          have le' := (TShape.LE.def
            (Nat.succ_le_succ hk.2.2)
            (Nat.succ_le_succ hk.2.1)).1 le
          simp only [WShape.T, WShape.lift_forallE hk.2.2,
            WShape.lift_forallE hk.2.1,
            WShape.forallE_le_forallE] at le'
          have Aa := iha hia'
            (haA.mono ((TShape.LE.def hk.2.2 hk.2.1).2 le'.1))
            hx'_a₁
          have harg := LRD.DefEq.trans (Aa.2 W.left) (Aa.1 W).2
          have hfun :=
            (LRD.DefEq.lift (Nat.succ_le_succ hk.2.2) hmf).2 hAf
          rw [WShape.lift_lam' hk.2.2,
            WShape.lift_forallE hk.2.2] at hfun
          unfold WShape.lam' at hfun
          split at hfun
          · simpa only [SExpr.subst, WShapeFun.lift_app hk.2.2] using
              LRD.DefEq.app
                (by simpa only [SExpr.subst] using hfun)
                ((WShape.HasType.lift hk.2.2).2 hx'_a₁)
                (hX.subst W.toSubstEq)
                ((LRD.DefEq.lift hk.2.2 hx'_a₁).2 harg)
          · refine (hm0 ?_).elim
            unfold WShape.lam'
            split
            · rename_i hb
              exact (‹¬(WShapeFun.lift k b₁).NonZero›
                ((WShapeFun.NonZero.lift_iff hk.2.2).2 hb)).elim
            · rfl
      | _ =>
        refine have le₂ := Nat.succ_le_succ (Nat.le_max_right ..)
          have hbad := (TShape.LE.def
            (Nat.le_succ_of_le (Nat.le_max_left ..)) le₂).1 le
          ?_
        simp only [WShape.lift_sort, WShape.LE.def,
          WShape.lift_val le₂] at hbad
        cases hbad

/--
info: 'Lean4Lean.SExpr.LRD.adequateApp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.adequateApp



/-- The direct fundamental-theorem variable constructor. -/
theorem LRD.Adequate.bvar
    (hlookup : Lookup Γ i A)
    (hM : LE_Interp ρ m.T (.bvar i))
    (hA : LE_Interp ρ a.T A)
    (hmem : m.HasType a) :
    LRD.Adequate Γ₀ Γ ρ (.bvar i) (.bvar i) A m a :=
  .refl fun _ _ W => W.bvar hlookup hM hA hmem

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.bvar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.bvar

/-- The direct fundamental-theorem sort constructor.  The semantic shape
analysis is unchanged from the legacy proof; its informative sort branch
now constructs the path-typed observation explicitly. -/
theorem LRD.Adequate.sort
    (hM : LE_Interp ρ m.T (.sort l))
    (hmem : m.HasType a) :
    LRD.Adequate Γ₀ Γ ρ (.sort l) (.sort l) (.sort l.succ) m a := by
  suffices (LRD Γ₀).DefEq (.sort l) (.sort l) (.sort l.succ) m a from
    ⟨fun _ _ _ => ⟨this, this⟩, fun _ _ => this⟩
  cases hmem.unfold with
  | bot hm => exact LRD.DefEq.bot hm
  | sort => exact LRD.DefEq.sort
  | _ =>
    obtain h | h := WShape.le_sort.1 hM.le_sort'
    · dsimp only at h
      rw [h]
      exact LRD.DefEq.bot hmem.isType
    · simp [WShape.ext_iff, WShape.forallE, WShape.sort, Shape.sort,
        WShape.lam', WShape.lam, WShape.bot, WShape.ctor, WShape.indTy,
        Shape.bot] at h <;>
        first
        | split at h <;> simp_all only [reduceCtorEq]
        | simp_all

/--
info: 'Lean4Lean.SExpr.LRD.Adequate.sort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.Adequate.sort

/-- Adequacy specialized to one shape level.  Naming the indexed statement
separately makes the dependency of the joint adequacy/uniqueness
construction explicit: inversion at level `n + 1` can consume this package
without assuming the final polymorphic adequacy theorem. -/
def LR.AdequacyAt (Γ₀ : List SExpr) (n : Nat) : Prop :=
  ∀ {Γ : List SExpr} {ρ : Valuation} {M N A : SExpr} {m a : WShape n},
    IsDefEqStrong Γ M N A →
    LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
    LR.Adequate Γ₀ Γ ρ M N A m a

/-- Adequacy observed at one explicit stratified typing depth of its left
endpoint.  Shape levels remain polymorphic: semantic application chooses
them freely.  This is sufficient for bounded sort/Pi observations, but an
arbitrary left-endpoint certificate does not by itself bound every premise
of the accompanying strong equality; a coherent derivation certificate is
still required by the eventual adequacy induction rung. -/
def LR.AdequacyAtDepth (Γ₀ : List SExpr) (depth : Nat) : Prop :=
  ∀ {n : Nat} {Γ : List SExpr} {ρ : Valuation} {M N A B : SExpr}
      {core : Bool} {m a : WShape n},
    IsDefEqStrong Γ M N A →
    HasTypeStratifiedS Γ M B core depth →
    LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
    LR.Adequate Γ₀ Γ ρ M N A m a

/-- Depth-bounded adequacy uniformly over well-formed target contexts. -/
def LR.ContextualAdequacyAtDepth (depth : Nat) : Prop :=
  ∀ {Γ₀ : List SExpr}, Ctx.WF Γ₀ → LR.AdequacyAtDepth Γ₀ depth

/-- Guarded heterogeneous adequacy observed at one explicit stratified depth
of its left endpoint.  This is the direct counterpart of
`LR.AdequacyAtDepth`; it is kept separate from the self-only coherent result
because the conversion constructor genuinely consumes a heterogeneous type
edge at a strict predecessor depth. -/
def LRD.AdequacyAtDepth (Γ₀ : List SExpr) (depth : Nat) : Prop :=
  ∀ {n : Nat} {Γ : List SExpr} {ρ : Valuation} {M N A B : SExpr}
      {core : Bool} {m a : WShape n},
    IsDefEqStrong Γ M N A →
    HasTypeStratifiedS Γ M B core depth →
    LE_Interp ρ m.T M → LE_Interp ρ a.T A → m.HasType a →
    LRD.Adequate Γ₀ Γ ρ M N A m a

/-- Depth-bounded guarded heterogeneous adequacy uniformly over well-formed
target contexts. -/
def LRD.ContextualAdequacyAtDepth (depth : Nat) : Prop :=
  ∀ {Γ₀ : List SExpr}, Ctx.WF Γ₀ → LRD.AdequacyAtDepth Γ₀ depth

/-- Adequacy at one shape level, uniformly over well-formed target contexts.
The contextual quantifier is part of the induction unit: Pi uniqueness enters
an extended target context and therefore cannot be recovered from a package
fixed at the outer `Γ₀`. -/
def LR.ContextualAdequacyAt (n : Nat) : Prop :=
  ∀ {Γ₀ : List SExpr}, Ctx.WF Γ₀ → LR.AdequacyAt Γ₀ n

/-- Limited uniqueness at one shape level in every well-formed target
context. -/
def LogRel.ContextualLimitedUniq (n : Nat) : Prop :=
  ∀ {Γ : List SExpr}, Ctx.WF Γ →
    LogRel.LimitedUniq (LR Γ : LogRel Γ n)

/-- The exact successor lambda-retyping obligation, contextual because its
codomain branch is checked below a binder.  Unlike arbitrary Pi-observation
alignment, this term-indexed property is precisely what
`LRS.limitedUniq_of_typeUniq` consumes. -/
def LogRel.ContextualLamRetype (n : Nat) : Prop :=
  ∀ {Γ : List SExpr}, Ctx.WF Γ →
    LogRel.LimitedUniq.LamRetype (LR Γ : LogRel Γ n)

/-! #### Path-level positive bootstrap

The adequacy Pi observation deliberately retains heterogeneous type
equalities as `TypeDefEqPath`: adjacent edges can assign different universes
to their shared endpoint.  Collapsing those paths by assuming raw uniqueness
would make the level-zero bootstrap circular.  Instead, positive adequacy
transports a non-bottom sort or Pi observation across the whole path.  This
first proves path-level sort/Pi inversion, then stratified path uniqueness,
and only then collapses paths to ordinary weak equalities. -/

/-- Observe both endpoints of one strong equality at a fixed non-bottom sort
shape.  `LE_Interp.sound` supplies the declared type shape required by
adequacy, including when the displayed type is not syntactically a sort. -/
theorem IsDefEqStrong.sort_observe_of_adequacy
    {Γ : List SExpr} {X Y V : SExpr} {u : SLevel}
    (adequacy : LR.AdequacyAt Γ 1)
    (d : IsDefEqStrong Γ X Y V)
    (hX : LE_Interp .nil
      (WShape.T (n := 1) (.sort (decide (u ≠ .zero)))) X) :
    LE_Interp .nil
        (WShape.T (n := 1) (.sort (decide (u ≠ .zero)))) Y ∧
      ∃ w, Γ ⊢ X ⤳* .sort w ∧ Γ ⊢ Y ⤳* .sort w := by
  have hY := (LE_Interp.sound d .nil).1.1 hX
  have ⟨n, mX, mV, h1, h2, h3, hV, h5⟩ :=
    (LE_Interp.sound d .nil).2 hX |>.out
  have h2' := WShape.lift_sort ▸ (TShape.LE.lift_l h1).1 h2
  dsimp only at h2'
  cases WShape.sort_le.1 h2'
  cases show mV = (.sort true : WShape 1).lift n by
    let _ + 1 := n
    simp only [WShape.HasType, WShape.sort] at h5
    ext1
    generalize mV.val = mv at h5
    let .sort := Shape.HasType.unfold_iff.1 h5
    rfl
  have h1' : 1 ≤ n := h1
  have hrel := adequacy d hX (hV.unlift h1') .sort
  have hrel' := hrel.2 (.id)
  refine ⟨hY, ?_⟩
  exact (LR Γ).sort_iff.1
    (subst_id ▸ subst_id ▸ subst_id ▸ hrel')

/-- A heterogeneous type path between two syntactic sorts preserves their
exact universe level.  The semantic observation is propagated edge by edge;
weak-head determinism joins the exact sort exposed by adjacent edges. -/
theorem TypeDefEqPath.sort_inv_of_adequacy
    {Γ : List SExpr} {u v s : SLevel}
    (adequacy : LR.AdequacyAt Γ 1)
    (hΓ : Ctx.WF Γ)
    (H : TypeDefEqPath Γ (.sort u) (.sort v) s) : u = v := by
  let m : WShape 1 := .sort (decide (u ≠ .zero))
  have hstart : LE_Interp .nil m.T (.sort u) :=
    .sort TShape.sort_eqv.1
  have go : ∀ {X Y t}, TypeDefEqPath Γ X Y t →
      LE_Interp .nil m.T X → WHRedS Γ X (.sort u) →
      LE_Interp .nil m.T Y ∧ WHRedS Γ Y (.sort u) := by
    intro X Y t P
    induction P with
    | single h =>
      intro hX hred
      obtain ⟨hY, w, hredX, hredY⟩ :=
        h.strong hΓ |>.sort_observe_of_adequacy adequacy hX
      have hsort := hred.determ_l hredX .sort
      cases WHNF.sort.whRedS hsort
      exact ⟨hY, hredY⟩
    | trans _ _ ih₁ ih₂ =>
      intro hX hred
      obtain ⟨hY, hredY⟩ := ih₁ hX hred
      exact ih₂ hY hredY
  obtain ⟨_, hfinal⟩ := go H hstart .rfl
  cases WHNF.sort.whRedS hfinal
  rfl

/-- Observe both endpoints of one strong equality at the bottom-domain Pi
shape.  The successor type relation exposes their Pi weak-head forms and the
path-valued domain/codomain alignment without any uniqueness assumption. -/
theorem IsDefEqStrong.forallE_observe_of_adequacy
    {Γ : List SExpr} {X Y : SExpr} {s : SLevel}
    (adequacy : LR.AdequacyAt Γ 1)
    (d : IsDefEqStrong Γ X Y (.sort s))
    (hX : LE_Interp .nil
      (WShape.T (n := 1)
        (.forallE (.bot : WShape 0) WShapeFun.bot)) X) :
    LE_Interp .nil
        (WShape.T (n := 1)
          (.forallE (.bot : WShape 0) WShapeFun.bot)) Y ∧
      ∃ BX FX BY FY u v,
        Γ ⊢ X ⤳* .forallE BX FX ∧
        Γ ⊢ Y ⤳* .forallE BY FY ∧
        TypeDefEqPath Γ BX BY u ∧
        TypeDefEqPath (BX :: Γ) FX FY v := by
  have hY := (LE_Interp.sound d .nil).1.1 hX
  have hmem : WShape.HasType (n := 1)
      (.forallE (.bot : WShape 0) WShapeFun.bot)
      (.sort (s ≠ .zero)) := by
    refine WShape.HasType.forallE_l.2 ⟨_, ?_, rfl⟩
    refine WShape.HasTypePi.iff.2 ⟨.bot (.bot' .sort), fun x hx => ?_⟩
    cases WShape.HasType.bot_r hx
    exact WShapeFun.bot_app.symm ▸ .bot .sort
  have hA : LE_Interp .nil
      (WShape.T (n := 1) (.sort (s ≠ .zero))) (.sort s) :=
    .sort TShape.sort_eqv.1
  have hrel := (adequacy d hX hA hmem).2 (.id)
  refine ⟨hY, ?_⟩
  have hrel' := subst_id ▸ subst_id ▸ subst_id ▸ hrel
  change LRS.TyDefEq (LR0 (Γ := Γ)) X Y
    (.forallE (.bot : WShape 0) WShapeFun.bot) at hrel'
  obtain ⟨BX, FX, BY, FY, u, v, hredX, hredY, hdom, hcod, _⟩ := hrel'
  exact ⟨BX, FX, BY, FY, u, v, hredX, hredY, hdom, hcod⟩

/-- Pi injectivity for an entire heterogeneous type path.  At a path
junction the next codomain path is transported back through the accumulated
domain path one ordinary edge at a time. -/
theorem TypeDefEqPath.forallE_inv_of_adequacy
    {Γ : List SExpr} {A B A' B' : SExpr} {s : SLevel}
    (adequacy : LR.AdequacyAt Γ 1)
    (hΓ : Ctx.WF Γ)
    (H : TypeDefEqPath Γ (.forallE A B) (.forallE A' B') s) :
    ∃ u v, TypeDefEqPath Γ A A' u ∧
      TypeDefEqPath (A :: Γ) B B' v := by
  let p : WShape 1 := .forallE (.bot : WShape 0) WShapeFun.bot
  have hstart : LE_Interp .nil p.T (.forallE A B) := by
    refine .forallE' .bot .bot (.bot <| .bot' .sort) fun _ h => ?_
    cases h.bot_r
    exact WShapeFun.bot_app.symm ▸ .bot
  have go : ∀ {X Y t A B}, TypeDefEqPath Γ X Y t →
      LE_Interp .nil p.T X → WHRedS Γ X (.forallE A B) →
      LE_Interp .nil p.T Y ∧
        ∃ AY BY u v, WHRedS Γ Y (.forallE AY BY) ∧
          TypeDefEqPath Γ A AY u ∧
          TypeDefEqPath (A :: Γ) B BY v := by
    intro X Y t A B P
    induction P generalizing A B with
    | single h =>
      intro hX hred
      obtain ⟨hY, BX, FX, BY, FY, u, v,
          hredX, hredY, hdom, hcod⟩ :=
        h.strong hΓ |>.forallE_observe_of_adequacy adequacy hX
      cases hred.determ .forallE hredX .forallE
      exact ⟨hY, BY, FY, u, v, hredY, hdom, hcod⟩
    | trans _ _ ih₁ ih₂ =>
      intro hX hred
      obtain ⟨hY, AY, BY, u₁, v₁, hredY, hdom₁, hcod₁⟩ :=
        ih₁ hX hred
      obtain ⟨hZ, AZ, BZ, u₂, v₂, hredZ, hdom₂, hcod₂⟩ :=
        ih₂ hY hredY
      obtain ⟨_, hdom₁'⟩ := hdom₁.symm
      have hcod₂' := hdom₁'.defeqDF_l_path hcod₂
      exact ⟨hZ, AZ, BZ, u₁, v₁, hredZ,
        .trans hdom₁ hdom₂, .trans hcod₁ hcod₂'⟩
  obtain ⟨_, AX, BX, u, v, hfinal, hdom, hcod⟩ :=
    go H hstart .rfl
  cases WHNF.forallE.whRedS hfinal
  exact ⟨u, v, hdom, hcod⟩

/-- Lift a codomain path through a fixed Pi domain. -/
theorem TypeDefEqPath.forallE_right
    (hA : IsDefEq Γ A A (.sort u))
    (H : TypeDefEqPath (A :: Γ) B C v) :
    TypeDefEqPath Γ (.forallE A B) (.forallE A C) (.imax u v) := by
  induction H with
  | single h => exact .single (.forallEDF hA h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- The path-valued inversion package obtained before heterogeneous paths are
collapsed.  Endpoint stratifications may initially name different universe
levels; `sortPathInv` aligns them without raw uniqueness. -/
structure JointStratifiedPathInversion : Prop where
  sortPathInv : ∀ {Γ : List SExpr} {u v s : SLevel},
    Ctx.WF Γ → TypeDefEqPath Γ (.sort u) (.sort v) s → u = v
  forallEInv : ∀ {Γ : List SExpr} {A B A' B' V V' : SExpr}
      {s : SLevel} {n n' : Nat},
    Ctx.WF Γ →
    TypeDefEqPath Γ (.forallE A B) (.forallE A' B') s →
    HasTypeStratifiedS Γ (.forallE A B) V true n →
    HasTypeStratifiedS Γ (.forallE A' B') V' true n' →
    (∃ up uL uR, TypeDefEqPath Γ A A' up ∧
      HasTypeStratifiedS Γ A (.sort uL) true (n - 1) ∧
      HasTypeStratifiedS Γ A' (.sort uR) true (n' - 1)) ∧
    ∃ vp vL vR, TypeDefEqPath (A :: Γ) B B' vp ∧
      HasTypeStratifiedS (A :: Γ) B (.sort vL) true (n - 1) ∧
      HasTypeStratifiedS (A' :: Γ) B' (.sort vR) true (n' - 1)

/-- Positive adequacy supplies path-valued sort/Pi inversion directly. -/
theorem JointStratifiedPathInversion.of_adequacy
    (adequacy : LR.ContextualAdequacyAt 1) :
    JointStratifiedPathInversion where
  sortPathInv hΓ H := H.sort_inv_of_adequacy (adequacy hΓ) hΓ
  forallEInv := by
    intro Γ A B A' B' V V' s n n' hΓ h hL hR
    obtain ⟨uL, vL, hAL, hBL⟩ := hL.forallE_inv
    obtain ⟨uR, vR, hAR, hBR⟩ := hR.forallE_inv
    obtain ⟨up, vp, hAA, hBB⟩ :=
      TypeDefEqPath.forallE_inv_of_adequacy (adequacy hΓ) hΓ h
    exact ⟨⟨up, uL, uR, hAA, hAL, hAR⟩,
      vp, vL, vR, hBB, hBL, hBR⟩

/-- Positive adequacy supplies the residual of the repaired chain wall.

`LRS.PiPathInv` (SLR) is exactly `TypeDefEqPath.forallE_inv_of_adequacy`
above, packaged contextually.  Nothing is added in the packaging: that
theorem already requests no stratification certificate, which is why the
constructor-spine discipline it discharges carries no depth index either. -/
theorem LRS.PiPathInv.of_adequacy (adequacy : LR.ContextualAdequacyAt 1) :
    LRS.PiPathInv := fun hΓ H =>
  TypeDefEqPath.forallE_inv_of_adequacy (adequacy hΓ) hΓ H

/-- Faithfulness certificate: the path-valued inversion package the tree
already builds implies the residual, so this is a weakening rather than a
restatement.  The endpoint stratifications that `forallEInv` demands are
recovered from the path's own two self-typings — retaining the path is what
makes the narrower statement sufficient. -/
theorem LRS.PiPathInv.of_jointStratifiedPathInversion
    (inv : JointStratifiedPathInversion) : LRS.PiPathInv := by
  intro Γ A B A' B' s hΓ H
  obtain ⟨n₁, h₁, _⟩ := (H.leftType.strong hΓ).stratify
  obtain ⟨_, H'⟩ := H.right
  obtain ⟨n₂, h₂, _⟩ := (H'.leftType.strong hΓ).stratify
  obtain ⟨⟨up, _, _, hdom, _, _⟩, vp, _, _, hcod, _, _⟩ :=
    inv.forallEInv hΓ H h₁ h₂
  exact ⟨up, vp, hdom, hcod⟩

/-- Weak type uniqueness with a heterogeneous path as its result.

This is the acyclic form of the stratified proof: path-level Pi inversion is
already available from positive adequacy, while every recursive comparison
of two sort indices is resolved by `sortPathInv`. -/
theorem IsDefEq.uniqPath_of_stratified_inversion
    (inv : JointStratifiedPathInversion) (hΓ : Ctx.WF Γ)
    (h1 : IsDefEq Γ e₁ e₂ A) (h2 : IsDefEq Γ e₂ e₃ B) :
    ∃ u, TypeDefEqPath Γ A B u := by
  suffices ∀ {e A B b n₁ n₂ n}, n₁ ≤ n → n₂ ≤ n →
      HasTypeStratifiedS Γ e A b n₁ →
      HasTypeStratifiedS Γ e B b n₂ →
      ∃ up uA uB, TypeDefEqPath Γ A B up ∧
        HasTypeStratifiedS Γ A (.sort uA) true (n - 1) ∧
        HasTypeStratifiedS Γ B (.sort uB) true (n - 1) by
    obtain ⟨n₁, _, h1A⟩ := (h1.strong hΓ).stratify
    obtain ⟨n₂, h2B, _⟩ := (h2.strong hΓ).stratify
    obtain ⟨u, _, _, h, _⟩ :=
      this (Nat.le_max_left ..) (Nat.le_max_right ..) h1A h2B
    exact ⟨u, h⟩
  clear h1 h2
  intro e A B b n₁ n₂ n le₁ le₂ H1
  induction n using WellFounded.induction Nat.lt_wfRel.2
    generalizing n₁ n₂ Γ e A B b with
  | _ n IH =>
  induction H1 generalizing B n₂ n with
  | bvar a1 a2 =>
    intro (.bvar b1 b2)
    cases a1.uniq b1
    exact ⟨_, _, _, .single b2.hasType,
      b2.mono (Nat.sub_le_sub_right le₂ 1),
      b2.mono (Nat.sub_le_sub_right le₂ 1)⟩
  | sort' =>
    intro (.sort')
    exact ⟨_, _, _, .single .sort, .base .sort', .base .sort'⟩
  | const a1 a2 a3 =>
    intro (.const b1 b2 b3)
    cases a1.symm.trans b1
    replace le₁ := Nat.sub_le_sub_right le₁ 1
    exact ⟨_, _, _, .single a3.hasType, a3.mono le₁, a3.mono le₁⟩
  | app a1 a2 a3 a4 a5 ih1 ih2 ih3 ih4 ih5 =>
    intro (.app b1 b2 b3 b4 b5)
    have ⟨_, _, _, c1, c3, c4⟩ :=
      ih3 n IH hΓ (Nat.le_of_succ_le le₁) (Nat.le_of_succ_le le₂) b3
    have ⟨⟨_, _, _, d1, d2, d2'⟩,
        _, _, _, d3, d4, d5⟩ :=
      inv.forallEInv hΓ c1 c3 c4
    let n + 1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have hΓA : Ctx.WF (_ :: _) := ⟨hΓ, ⟨_, a1.hasType⟩⟩
    have d4n := d4.mono (n := n) (by omega)
    have ⟨_, _, _, e1, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓA le₁ (Nat.le_refl _) a2 d4n
    have ev1 := inv.sortPathInv hΓA e1
    cases ev1
    have hΓB : Ctx.WF (_ :: _) := ⟨hΓ, ⟨_, b1.hasType⟩⟩
    have d5n := d5.mono (n := n) (by omega)
    have ⟨_, _, _, e2, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓB le₂ (Nat.le_refl _) b2 d5n
    have ev2 := inv.sortPathInv hΓB e2
    cases ev2
    have hinst := d3.subst
      (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar a4.hasType)
    have hleft := a5.mono le₁
    have hright := b5.mono le₂
    exact ⟨_, _, _, by simpa only [SExpr.inst] using hinst, hleft, hright⟩
  | lam a1 a2 a3 a4 ih1 ih2 ih3 ih4 =>
    intro (.lam b1 b2 b3 b4)
    have hΓA : Ctx.WF (_ :: _) := ⟨hΓ, ⟨_, a1.hasType⟩⟩
    have ⟨_, _, _, c1, c3, c4⟩ := ih3 n IH hΓA
      (Nat.le_of_succ_le le₁) (Nat.le_of_succ_le le₂) b3
    let n + 1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have ⟨_, _, _, d1, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓ le₁ le₂ a1 b1
    have eu := inv.sortPathInv hΓ d1
    cases eu
    have ⟨_, _, _, d2, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓA le₁ (Nat.le_refl _) a2 c3
    have ev1 := inv.sortPathInv hΓA d2
    cases ev1
    have ⟨_, _, _, d3, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓA le₂ (Nat.le_refl _) b2 c4
    have ev2 := inv.sortPathInv hΓA d3
    cases ev2
    exact ⟨_, _, _, c1.forallE_right a1.hasType,
      a4.mono le₁, b4.mono le₂⟩
  | forallE a1 a2 ih1 ih2 =>
    intro (.forallE b1 b2)
    let n + 1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have ⟨_, _, _, hA, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓ le₁ le₂ a1 b1
    have eu := inv.sortPathInv hΓ hA
    cases eu
    have hΓ' : Ctx.WF (_ :: _) := ⟨hΓ, ⟨_, a1.hasType⟩⟩
    have ⟨_, _, _, hB, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓ' le₁ le₂ a2 b2
    have ev := inv.sortPathInv hΓ' hB
    cases ev
    exact ⟨_, _, _, .single .sort, .base .sort', .base .sort'⟩
  | @base Γ e A n₁ a1 ih =>
    intro H2
    replace ih {n'} le :=
      @ih n' (fun y hlt => IH y (Nat.lt_of_lt_of_le hlt le)) hΓ
    generalize eq : true = b at H2
    induction H2 with cases eq
    | base b1 _ => exact ih (Nat.le_refl _) le₁ le₂ b1
    | defeq bEq bA bB be ihA' ihB' ihe' =>
      have ⟨_, _, _, c1, c3, c4⟩ :=
        ihe' a1 hΓ (Nat.le_of_succ_le le₂) ih rfl
      let n + 1 := n
      replace le₂ := Nat.le_of_succ_le_succ le₂
      have ⟨_, _, _, d1, _, _⟩ :=
        IH _ (Nat.lt_succ_self _) hΓ le₂ (Nat.le_refl _) bA c4
      have eu := inv.sortPathInv hΓ d1
      cases eu
      exact ⟨_, _, _, .trans c1 (.single bEq.defeq), c3, bB.mono le₂⟩
  | defeq hEq hA hB he ihA ihB ihe =>
    intro H2
    have ⟨_, _, _, c1, c3, c4⟩ :=
      ihe n IH hΓ (Nat.le_of_succ_le le₁) le₂ H2
    let n + 1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    have ⟨_, _, _, d1, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓ le₁ (Nat.le_refl _) hA c3
    have eu := inv.sortPathInv hΓ d1
    cases eu
    exact ⟨_, _, _, .trans (.single hEq.defeq.symm) c1,
      hB.mono le₁, c4⟩

/-- Collapse a heterogeneous type path after deriving the universe alignment
at every junction from path-level stratified uniqueness. -/
theorem TypeDefEqPath.collapse_of_stratified_inversion
    (inv : JointStratifiedPathInversion) (hΓ : Ctx.WF Γ)
    (H : TypeDefEqPath Γ A B u) : IsDefEq Γ A B (.sort u) := by
  induction H with
  | single h => exact h
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨_, huv⟩ :=
      IsDefEq.uniqPath_of_stratified_inversion
        inv hΓ ih₁.hasType.2 ih₂.hasType.1
    have huv' := inv.sortPathInv hΓ huv
    cases huv'
    exact ih₁.trans ih₂

/-- Positive level-one adequacy is sufficient to derive contextual raw weak
type uniqueness; no raw-uniqueness premise occurs in the construction. -/
theorem LogRel.contextualRawTypeUniq_of_adequacy
    (adequacy : LR.ContextualAdequacyAt 1) :
    LogRel.ContextualRawTypeUniq := by
  let inv := JointStratifiedPathInversion.of_adequacy adequacy
  intro Γ hΓ x A B hxA hxB
  obtain ⟨u, hAB⟩ :=
    IsDefEq.uniqPath_of_stratified_inversion inv hΓ hxA hxB
  exact ⟨u, hAB.collapse_of_stratified_inversion inv hΓ⟩

/-- The two syntactic inversion facts needed by stratified weak type
uniqueness.  Keeping the package independent of adequacy makes the
well-founded boundary explicit: the semantic construction supplies these
observations, while the theorem below consumes only their statements. -/
structure JointStratifiedInversion : Prop where
  sortInv : ∀ {Γ : List SExpr} {u v : SLevel} {V : SExpr},
    Ctx.WF Γ → IsDefEqStrong Γ (.sort u) (.sort v) V → u = v
  forallEInv : ∀ {Γ : List SExpr} {A B A' B' V V' : SExpr}
      {s : SLevel} {n n' : Nat},
    Ctx.WF Γ →
    IsDefEqStrong Γ (.forallE A B) (.forallE A' B') (.sort s) →
    HasTypeStratifiedS Γ (.forallE A B) V true n →
    HasTypeStratifiedS Γ (.forallE A' B') V' true n' →
    (∃ u, IsDefEq Γ A A' (.sort u) ∧
      HasTypeStratifiedS Γ A (.sort u) true (n - 1)) ∧
    ∃ v, IsDefEq (A :: Γ) B B' (.sort v) ∧
      HasTypeStratifiedS (A :: Γ) B (.sort v) true (n - 1) ∧
      HasTypeStratifiedS (A' :: Γ) B' (.sort v) true (n' - 1)

/-- Restriction interface for ordinary stratified inversion up to one typing
depth.  Every use records the depths of the endpoint stratifications
explicitly.  Bounded adequacy directly constructs only the path-valued
package below; no bounded path-collapse constructor for this stronger
interface is claimed. -/
structure JointStratifiedInversionAt (depth : Nat) : Prop where
  sortInv : ∀ {Γ : List SExpr} {u v : SLevel} {V : SExpr} {d : Nat},
    d ≤ depth → Ctx.WF Γ →
    IsDefEqStrong Γ (.sort u) (.sort v) V →
    HasTypeStratifiedS Γ (.sort u) V true d →
    u = v
  forallEInv : ∀ {Γ : List SExpr} {A B A' B' V V' : SExpr}
      {s : SLevel} {n n' : Nat},
    n ≤ depth → n' ≤ depth → Ctx.WF Γ →
    IsDefEqStrong Γ (.forallE A B) (.forallE A' B') (.sort s) →
    HasTypeStratifiedS Γ (.forallE A B) V true n →
    HasTypeStratifiedS Γ (.forallE A' B') V' true n' →
    (∃ u, IsDefEq Γ A A' (.sort u) ∧
      HasTypeStratifiedS Γ A (.sort u) true (n - 1)) ∧
    ∃ v, IsDefEq (A :: Γ) B B' (.sort v) ∧
      HasTypeStratifiedS (A :: Γ) B (.sort v) true (n - 1) ∧
      HasTypeStratifiedS (A' :: Γ) B' (.sort v) true (n' - 1)

/-- The non-collapsed depth rung obtained directly from bounded adequacy.
The endpoint depth certificates are retained alongside each path, so the
subsequent path-collapse proof can recurse strictly below the two Pi
typings instead of appealing to global raw uniqueness. -/
structure JointStratifiedPathInversionAt (depth : Nat) : Prop where
  sortInv : ∀ {Γ : List SExpr} {u v : SLevel} {V B : SExpr}
      {core : Bool} {d : Nat},
    d ≤ depth → Ctx.WF Γ →
    IsDefEqStrong Γ (.sort u) (.sort v) V →
    HasTypeStratifiedS Γ (.sort u) B core d →
    u = v
  forallEInv : ∀ {Γ : List SExpr} {A B A' B' V V' : SExpr}
      {s : SLevel} {n n' : Nat},
    n ≤ depth → n' ≤ depth → Ctx.WF Γ →
    IsDefEqStrong Γ (.forallE A B) (.forallE A' B') (.sort s) →
    HasTypeStratifiedS Γ (.forallE A B) V true n →
    HasTypeStratifiedS Γ (.forallE A' B') V' true n' →
    (∃ up uL uR, TypeDefEqPath Γ A A' up ∧
      HasTypeStratifiedS Γ A (.sort uL) true (n - 1) ∧
      HasTypeStratifiedS Γ A' (.sort uR) true (n' - 1)) ∧
    ∃ vp vL vR, TypeDefEqPath (A :: Γ) B B' vp ∧
      HasTypeStratifiedS (A :: Γ) B (.sort vL) true (n - 1) ∧
      HasTypeStratifiedS (A' :: Γ) B' (.sort vR) true (n' - 1)

/-- Restrict an already-complete inversion package to a finite depth. -/
theorem JointStratifiedInversion.at
    (inv : JointStratifiedInversion) (depth : Nat) :
    JointStratifiedInversionAt depth where
  sortInv _ hΓ h _ := inv.sortInv hΓ h
  forallEInv _ _ hΓ h hL hR := inv.forallEInv hΓ h hL hR

/-- A depth-bounded adequacy rung already determines the universe of a sort
observation at that same typing depth.  No inversion or uniqueness package
is consumed here. -/
theorem IsDefEqStrong.sort_inv_of_adequacyAtDepth
    {Γ : List SExpr} {u v : SLevel} {V B : SExpr} {core : Bool}
    {depth : Nat}
    (adequacy : LR.AdequacyAtDepth Γ depth)
    (d : IsDefEqStrong Γ (.sort u) (.sort v) V)
    (hstrat : HasTypeStratifiedS Γ (.sort u) B core depth) :
    u = v := by
  let m : WShape 1 := .sort (decide (u ≠ .zero))
  have hM : LE_Interp .nil m.T (.sort u) :=
    .sort TShape.sort_eqv.1
  obtain ⟨n, mU, mV, hlevel, hterm, htype, hV, htyped⟩ :=
    (LE_Interp.sound d .nil).2 hM |>.out
  have hterm' := WShape.lift_sort ▸ (TShape.LE.lift_l hlevel).1 hterm
  dsimp only at hterm'
  cases WShape.sort_le.1 hterm'
  cases show mV = (.sort true : WShape 1).lift n by
    let _ + 1 := n
    simp only [WShape.HasType, WShape.sort] at htyped
    ext1
    generalize mV.val = mv at htyped
    let .sort := Shape.HasType.unfold_iff.1 htyped
    rfl
  have hlevel' : 1 ≤ n := hlevel
  have hrel := (adequacy d hstrat hM (hV.unlift hlevel') .sort).2 .id
  obtain ⟨w, hu, hv⟩ :=
    (LR Γ).sort_iff.1 (subst_id ▸ subst_id ▸ subst_id ▸ hrel)
  cases WHNF.sort.whRedS hu
  cases WHNF.sort.whRedS hv
  rfl

/-! #### The §4.4 shape facts, and the rung each one costs

Ported from `plans/probes/probeW-disjointness.lean`.  The definitions and the
three soundness-derived facts live in `ShapeLogRel.lean` — they are statements
about `LE_Interp`, not about adequacy.  What is *here* is the depth ledger:
which rung, if any, each fact charges.

The answer is that **three of the four charge nothing** and the fourth charges
**depth 0**.  `LRS.SortInv` is the only one that needs a rung, because
`WShape.sort` records only `decide (u ≠ .zero)` (`LRS.sortInv_bit_only`, SLR,
is the negative control) and the level itself has to come out of
`LogRel.sort_iff`.  It charges depth `0` and nothing more, because the
*subject* of the observation is a syntactic sort, whose certificate is the
nullary `HasTypeStratifiedS.sort'` at depth `0`
(`HasTypeStratifiedS.sort_zero`, SLR).  A leaf therefore supplies no anchor
here at all, which is exactly the asymmetry with `LRS.PiPathInv`, whose
subject is an arbitrary type. -/

/-- **The depth-0 producer.**  Bounded adequacy at depth `0` already delivers
full sort injectivity, in every context and at every level pair — no
restriction to shallow subjects survives, because the observation's subject is
a sort. -/
theorem LRS.SortInv.of_adequacyAtDepth_zero
    (adequacy : LR.ContextualAdequacyAtDepth 0) : LRS.SortInv :=
  fun hΓ h =>
    IsDefEqStrong.sort_inv_of_adequacyAtDepth (adequacy hΓ) (h.strong hΓ)
      HasTypeStratifiedS.sort_zero

/-- The same producer in `…At` form, matching `JointStratifiedInversionAt`. -/
theorem LRS.SortInvAt.of_adequacyAtDepth_zero
    (adequacy : LR.ContextualAdequacyAtDepth 0) : LRS.SortInvAt 0 := by
  intro Γ u v V B core d hd hΓ hEq hstrat
  cases Nat.le_zero.1 hd
  exact IsDefEqStrong.sort_inv_of_adequacyAtDepth (adequacy hΓ) (hEq.strong hΓ)
    hstrat

/-- **The depth arithmetic.**  Restated in the exact shape the depth bootstrap
hands to a leaf (compare `JointStratifiedPathInversionAt.of_predecessorAdequacy`
and `LR.FixedHeadTypeValidStep.of_lowerAdequacy`): at any rung `depth ≥ 1`, the
*strictly smaller* adequacy family already supplies the whole of
`LRS.SortInv`.  Consumed at rung `depth`, produced at rung `0`; `0 < depth`, so
this is strictly below, not same-rung. -/
theorem LRS.SortInv.of_lowerAdequacy {depth : Nat} (hdepth : 0 < depth)
    (lower : ∀ d, d < depth → LR.ContextualAdequacyAtDepth d) : LRS.SortInv :=
  LRS.SortInv.of_adequacyAtDepth_zero (lower 0 hdepth)

/-- The three disjointness facts are available at rung `0` as well, where the
strictly-lower family is **empty**.  This is the sharpest possible form of
"strictly below the consumer": below every rung, including the base. -/
theorem LRS.shapeDisj_at_rung_zero
    (_lower : ∀ d, d < 0 → LR.ContextualAdequacyAtDepth d) :
    LRS.SortForallEDisj ∧ LRS.PiNotFunTyped ∧ LRS.PiNotProof :=
  ⟨LRS.SortForallEDisj.of_soundness, LRS.PiNotFunTyped.of_soundness,
    LRS.PiNotProof.of_soundness⟩

/-- All four §4.4 facts as one package, from a strictly-lower adequacy family
at any positive rung.  Three of its four fields need no input at all. -/
theorem LRS.ShapeDisj.of_lowerAdequacy {depth : Nat} (hdepth : 0 < depth)
    (lower : ∀ d, d < depth → LR.ContextualAdequacyAtDepth d) :
    LRS.ShapeDisj where
  sortInv := LRS.SortInv.of_lowerAdequacy hdepth lower
  sortForallEDisj := LRS.SortForallEDisj.of_soundness
  piNotFunTyped := LRS.PiNotFunTyped.of_soundness
  piNotProof := LRS.PiNotProof.of_soundness

/-- Depth-bounded adequacy exposes the Pi domains and codomains selected by
one strong equality.  The result deliberately remains path-valued: collapsing
those heterogeneous paths is the recursive part of the depth bootstrap. -/
theorem IsDefEqStrong.forallE_invPath_of_adequacyAtDepth
    {Γ : List SExpr} {A B A' B' V : SExpr} {core : Bool}
    {s : SLevel} {depth : Nat}
    (adequacy : LR.AdequacyAtDepth Γ depth)
    (d : IsDefEqStrong Γ (.forallE A B) (.forallE A' B') (.sort s))
    (hstrat : HasTypeStratifiedS Γ (.forallE A B) V core depth) :
    ∃ u v, TypeDefEqPath Γ A A' u ∧
      TypeDefEqPath (A :: Γ) B B' v := by
  let p : WShape 1 := .forallE (.bot : WShape 0) WShapeFun.bot
  have hPi : LE_Interp .nil p.T (.forallE A B) := by
    refine .forallE' .bot .bot (.bot <| .bot' .sort) fun _ h => ?_
    cases h.bot_r
    exact WShapeFun.bot_app.symm ▸ .bot
  have hmem : p.HasType (.sort (s ≠ .zero)) := by
    refine WShape.HasType.forallE_l.2 ⟨_, ?_, rfl⟩
    refine WShape.HasTypePi.iff.2 ⟨.bot (.bot' .sort), fun x hx => ?_⟩
    cases WShape.HasType.bot_r hx
    exact WShapeFun.bot_app.symm ▸ .bot .sort
  have hSort : LE_Interp .nil
      (WShape.T (n := 1) (.sort (s ≠ .zero))) (.sort s) :=
    .sort TShape.sort_eqv.1
  have hrel := (adequacy d hstrat hPi hSort hmem).2 .id
  have hrel' := subst_id ▸ subst_id ▸ subst_id ▸ hrel
  change LRS.TyDefEq (LR0 (Γ := Γ)) (.forallE A B) (.forallE A' B') p at hrel'
  obtain ⟨A₀, B₀, A₁, B₁, u, v,
      hred₀, hred₁, hdom, hcod, _⟩ := hrel'
  cases WHNF.forallE.whRedS hred₀
  cases WHNF.forallE.whRedS hred₁
  exact ⟨u, v, hdom, hcod⟩

/-- Assemble the path-valued inversion rung from all bounded adequacy facts
up to `depth`.  This theorem is the semantic half of the depth bootstrap;
it performs no path collapse and therefore consumes no uniqueness theorem. -/
theorem JointStratifiedPathInversionAt.of_adequacyAtDepth
    (depth : Nat)
    (adequacy : ∀ d, d ≤ depth → LR.ContextualAdequacyAtDepth d) :
    JointStratifiedPathInversionAt depth where
  sortInv hd hΓ h hstrat :=
    h.sort_inv_of_adequacyAtDepth (adequacy _ hd hΓ) hstrat
  forallEInv := by
    intro Γ A B A' B' V V' s n n' hn hn' hΓ h hL hR
    obtain ⟨uL, vL, hAL, hBL⟩ := hL.forallE_inv
    obtain ⟨uR, vR, hAR, hBR⟩ := hR.forallE_inv
    obtain ⟨up, vp, hAA, hBB⟩ :=
      h.forallE_invPath_of_adequacyAtDepth (adequacy _ hn hΓ) hL
    exact ⟨⟨up, uL, uR, hAA, hAL, hAR⟩,
      vp, vL, vR, hBB, hBL, hBR⟩

/-- Restate the bounded inversion rung against a strict predecessor
family: the contextual adequacy rungs strictly below `depth + 1` are
exactly the bounded family up to `depth`.  This is the form a successor
joint leaf receives from the depth bootstrap, so the leaf can assemble
its own predecessor inversion package without a same-depth adequacy
consumption. -/
theorem JointStratifiedPathInversionAt.of_predecessorAdequacy
    (depth : Nat)
    (adequacy : ∀ d, d < depth + 1 → LR.ContextualAdequacyAtDepth d) :
    JointStratifiedPathInversionAt depth :=
  .of_adequacyAtDepth depth fun d hd => adequacy d (Nat.lt_succ_of_le hd)

/-- Construct the direct stratified inversion package from positive adequacy
without assuming raw type uniqueness.  The path-valued bootstrap above first
derives uniqueness and collapses its own paths; this theorem merely aligns
the endpoint stratification indices with those collapsed equalities. -/
theorem JointStratifiedInversion.of_adequacy
    (adequacy : LR.ContextualAdequacyAt 1) :
    JointStratifiedInversion where
  sortInv := by
    intro Γ u v V hΓ h
    let m : WShape 1 := .sort (decide (u ≠ .zero))
    have hstart : LE_Interp .nil m.T (.sort u) :=
      .sort TShape.sort_eqv.1
    obtain ⟨_, w, hu, hv⟩ :=
      h.sort_observe_of_adequacy (adequacy hΓ) hstart
    cases WHNF.sort.whRedS hu
    cases WHNF.sort.whRedS hv
    rfl
  forallEInv := by
    intro Γ A B A' B' V V' s n n' hΓ h hL hR
    let inv := JointStratifiedPathInversion.of_adequacy adequacy
    obtain ⟨⟨up, uL, uR, hAAp, hAL, hAR⟩,
        vp, vL, vR, hBBp, hBL, hBR⟩ :=
      inv.forallEInv hΓ (.single h.defeq) hL hR
    have hAA := hAAp.collapse_of_stratified_inversion inv hΓ
    obtain ⟨_, huLp⟩ :=
      IsDefEq.uniqPath_of_stratified_inversion
        inv hΓ hAL.hasType hAA.hasType.1
    have huL : uL = up := inv.sortPathInv hΓ huLp
    cases huL
    obtain ⟨_, huRp⟩ :=
      IsDefEq.uniqPath_of_stratified_inversion
        inv hΓ hAR.hasType hAA.hasType.2
    have huR : uR = up := inv.sortPathInv hΓ huRp
    cases huR
    have hΓA : Ctx.WF (A :: Γ) := ⟨hΓ, ⟨up, hAA.hasType.1⟩⟩
    have hBB := hBBp.collapse_of_stratified_inversion inv hΓA
    obtain ⟨_, hvLp⟩ :=
      IsDefEq.uniqPath_of_stratified_inversion
        inv hΓA hBL.hasType hBB.hasType.1
    have hvL : vL = vp := inv.sortPathInv hΓA hvLp
    cases hvL
    have hΓA' : Ctx.WF (A' :: Γ) := ⟨hΓ, ⟨up, hAA.hasType.2⟩⟩
    have hBB' : IsDefEq (A' :: Γ) B' B' (.sort vp) :=
      hAA.defeqDF_l hBB.hasType.2
    obtain ⟨_, hvRp⟩ :=
      IsDefEq.uniqPath_of_stratified_inversion
        inv hΓA' hBR.hasType hBB'
    have hvR : vR = vp := inv.sortPathInv hΓA' hvRp
    cases hvR
    exact ⟨⟨up, hAA, hAL⟩, vp, hBB, hBL, hBR⟩

/-- Raw weak type uniqueness from only stratified sort and Pi inversion.

The proof is well founded on the maximum stratification depth.  Its
application and lambda cases recurse under a binder; this is why both the
inversion package and the eventual adequacy stage must be contextual. -/
theorem IsDefEq.uniq_of_stratified_inversion
    (inv : JointStratifiedInversion) (hΓ : Ctx.WF Γ)
    (h1 : IsDefEq Γ e₁ e₂ A) (h2 : IsDefEq Γ e₂ e₃ B) :
    ∃ u, IsDefEq Γ A B (.sort u) := by
  suffices ∀ {e A B b n₁ n₂ n}, n₁ ≤ n → n₂ ≤ n →
      HasTypeStratifiedS Γ e A b n₁ →
      HasTypeStratifiedS Γ e B b n₂ →
      ∃ u, IsDefEq Γ A B (.sort u) ∧
        HasTypeStratifiedS Γ A (.sort u) true (n - 1) ∧
        HasTypeStratifiedS Γ B (.sort u) true (n - 1) by
    obtain ⟨n₁, _, h1A⟩ := (h1.strong hΓ).stratify
    obtain ⟨n₂, h2B, _⟩ := (h2.strong hΓ).stratify
    obtain ⟨u, h, _⟩ := this (Nat.le_max_left ..) (Nat.le_max_right ..) h1A h2B
    exact ⟨u, h⟩
  clear h1 h2
  intro e A B b n₁ n₂ n le₁ le₂ H1
  induction n using WellFounded.induction Nat.lt_wfRel.2
    generalizing n₁ n₂ Γ e A B b with
  | _ n IH =>
  induction H1 generalizing B n₂ n with
  | bvar a1 a2 =>
    intro (.bvar b1 b2)
    cases a1.uniq b1
    exact ⟨_, b2.hasType,
      b2.mono (Nat.sub_le_sub_right le₂ 1),
      b2.mono (Nat.sub_le_sub_right le₂ 1)⟩
  | sort' =>
    intro (.sort')
    exact ⟨_, .sort, .base .sort', .base .sort'⟩
  | const a1 a2 a3 =>
    intro (.const b1 b2 b3)
    cases a1.symm.trans b1
    replace le₁ := Nat.sub_le_sub_right le₁ 1
    exact ⟨_, a3.hasType, a3.mono le₁, a3.mono le₁⟩
  | app a1 a2 a3 a4 a5 ih1 ih2 ih3 ih4 ih5 =>
    intro (.app b1 b2 b3 b4 b5)
    have ⟨_, c1, c3, c4⟩ :=
      ih3 n IH hΓ (Nat.le_of_succ_le le₁) (Nat.le_of_succ_le le₂) b3
    have ⟨⟨_, d1, d2⟩, _, d3, d4, d5⟩ :=
      inv.forallEInv hΓ (c1.strong hΓ) c3 c4
    let n + 1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have hΓA : Ctx.WF (_ :: _) := ⟨hΓ, ⟨_, a1.hasType⟩⟩
    have d4n := d4.mono (n := n) (by omega)
    have ⟨_, e1, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓA le₁ (Nat.le_refl _) a2 d4n
    have ev1 := inv.sortInv hΓA (e1.strong hΓA)
    have hΓB : Ctx.WF (_ :: _) := ⟨hΓ, ⟨_, b1.hasType⟩⟩
    have d5n := d5.mono (n := n) (by omega)
    have ⟨_, e2, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓB le₂ (Nat.le_refl _) b2 d5n
    have ev2 := inv.sortInv hΓB (e2.strong hΓB)
    cases ev1
    cases ev2
    have hinst := d3.subst
      (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar a4.hasType)
    simpa using ⟨_, hinst, a5.mono le₁, b5.mono le₂⟩
  | lam a1 a2 a3 a4 ih1 ih2 ih3 ih4 =>
    intro (.lam b1 b2 b3 b4)
    have hΓA : Ctx.WF (_ :: _) := ⟨hΓ, ⟨_, a1.hasType⟩⟩
    have ⟨_, c1, c3, c4⟩ := ih3 n IH hΓA
      (Nat.le_of_succ_le le₁) (Nat.le_of_succ_le le₂) b3
    let n + 1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have ⟨_, d1, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓ le₁ le₂ a1 b1
    have eu := inv.sortInv hΓ (d1.strong hΓ)
    cases eu
    have ⟨_, d2, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓA le₁ (Nat.le_refl _) a2 c3
    have ev1 := inv.sortInv hΓA (d2.strong hΓA)
    cases ev1
    have ⟨_, d3, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓA le₂ (Nat.le_refl _) b2 c4
    have ev2 := inv.sortInv hΓA (d3.strong hΓA)
    cases ev2
    exact ⟨_, .forallEDF a1.hasType c1, a4.mono le₁, b4.mono le₂⟩
  | forallE a1 a2 ih1 ih2 =>
    intro (.forallE b1 b2)
    let n + 1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    replace le₂ := Nat.le_of_succ_le_succ le₂
    have ⟨_, hA, _, _⟩ := IH _ (Nat.lt_succ_self _) hΓ le₁ le₂ a1 b1
    have eu := inv.sortInv hΓ (hA.strong hΓ)
    cases eu
    have hΓ' : Ctx.WF (_ :: _) := ⟨hΓ, ⟨_, a1.hasType⟩⟩
    have ⟨_, hB, _, _⟩ := IH _ (Nat.lt_succ_self _) hΓ' le₁ le₂ a2 b2
    have ev := inv.sortInv hΓ' (hB.strong hΓ')
    cases ev
    exact ⟨_, .sort, .base .sort', .base .sort'⟩
  | @base Γ e A n₁ a1 ih =>
    intro H2
    replace ih {n'} le :=
      @ih n' (fun y hlt => IH y (Nat.lt_of_lt_of_le hlt le)) hΓ
    generalize eq : true = b at H2
    induction H2 with cases eq
    | base b1 _ => exact ih (Nat.le_refl _) le₁ le₂ b1
    | defeq bEq bA bB be ihA' ihB' ihe' =>
      have ⟨_, c1, c3, c4⟩ :=
        ihe' a1 hΓ (Nat.le_of_succ_le le₂) ih rfl
      let n + 1 := n
      replace le₂ := Nat.le_of_succ_le_succ le₂
      have ⟨_, d1, _, _⟩ :=
        IH _ (Nat.lt_succ_self _) hΓ le₂ (Nat.le_refl _) bA c4
      have eu := inv.sortInv hΓ (d1.strong hΓ)
      cases eu
      exact ⟨_, c1.trans bEq.defeq, c3, bB.mono le₂⟩
  | defeq hEq hA hB he ihA ihB ihe =>
    intro H2
    have ⟨_, c1, c3, c4⟩ :=
      ihe n IH hΓ (Nat.le_of_succ_le le₁) le₂ H2
    let n + 1 := n
    replace le₁ := Nat.le_of_succ_le_succ le₁
    have ⟨_, d1, _, _⟩ :=
      IH _ (Nat.lt_succ_self _) hΓ le₁ (Nat.le_refl _) hA c3
    have eu := inv.sortInv hΓ (d1.strong hΓ)
    cases eu
    exact ⟨_, hEq.defeq.symm.trans c1, hB.mono le₁, c4⟩

/-- Strip outer conversions from a stratified typing and align the resulting
syntax-directed core type with the original type. -/
theorem HasTypeStratifiedS.core_aligned_of_typeUniq
    (uniq : LogRel.RawTypeUniq Γ)
    (H : HasTypeStratifiedS Γ e A true n) :
    ∃ A' u, HasTypeStratifiedS Γ e A' false n ∧
      IsDefEq Γ A' A (.sort u) := by
  obtain ⟨A', hcore⟩ := H.to_core
  obtain ⟨u, hty⟩ := uniq hcore.hasType H.hasType
  exact ⟨A', u, hcore, hty⟩

/-- Every weak self-typing has a syntax-directed stratified core, with its
type aligned by the joint inversion theorem. -/
theorem IsDefEq.core_aligned_of_stratified_inversion
    (inv : JointStratifiedInversion) (hΓ : Ctx.WF Γ)
    (H : IsDefEq Γ e e A) :
    ∃ n A' u, HasTypeStratifiedS Γ e A' false n ∧
      IsDefEq Γ A' A (.sort u) := by
  obtain ⟨n, hs, _⟩ := (H.strong hΓ).stratify
  obtain ⟨A', u, hcore, hty⟩ :=
    hs.core_aligned_of_typeUniq (fun h1 h2 =>
      IsDefEq.uniq_of_stratified_inversion inv hΓ h1 h2)
  exact ⟨n, A', u, hcore, hty⟩

/-- One weak-head step preserves a supplied type once the joint stratified
inversion package is available.  Application reduction recurses at the
syntax-directed function/argument typing; beta uses Pi inversion to align
the lambda's native binder with the application's domain; a registered
step uses the type carried by its `Pattern.Action`. -/
theorem WHRed.defeq_of_stratified_inversion
    (inv : JointStratifiedInversion) (hΓ : Ctx.WF Γ)
    (H : WHRed Γ e1 e2) (he : IsDefEq Γ e1 e1 A) :
    IsDefEq Γ e1 e2 A := by
  let uniq : LogRel.RawTypeUniq Γ := fun h1 h2 =>
    IsDefEq.uniq_of_stratified_inversion inv hΓ h1 h2
  induction H generalizing A with
  | app hred ih =>
    obtain ⟨_, _, _, hcore, hty⟩ :=
      he.core_aligned_of_stratified_inversion inv hΓ
    cases hcore with
    | app hD hC hf ha hR =>
      exact hty.defeqDF (.appDF (ih hf.hasType) ha.hasType)
  | major hmajor hred ih =>
    obtain ⟨_, _, _, hcore, hty⟩ :=
      he.core_aligned_of_stratified_inversion inv hΓ
    cases hcore with
    | app hD hC hf ha hR =>
      exact hty.defeqDF (.appDF hf.hasType (ih ha.hasType))
  | beta =>
    obtain ⟨_, _, _, hcore, hty⟩ :=
      he.core_aligned_of_stratified_inversion inv hΓ
    cases hcore with
    | app hD hC hlam ha hR =>
      obtain ⟨_, _, _, hlamCore, hlamTy⟩ :=
        hlam.hasType.core_aligned_of_stratified_inversion inv hΓ
      cases hlamCore with
      | lam hDom hCod hBody hPi =>
        have hPiRight := HasTypeStratifiedS.base
          (HasTypeStratifiedS.forallE hD hC)
        have ⟨⟨_, hDomEq, _⟩, _, hCodEq, _, _⟩ :=
          inv.forallEInv hΓ (hlamTy.strong hΓ) hPi hPiRight
        have haDom := hDomEq.symm.defeqDF ha.hasType
        have hβ := IsDefEq.beta hBody.hasType haDom
        have hCodInst := hCodEq.subst
          (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar haDom)
        exact hty.defeqDF (hCodInst.defeqDF hβ)
  | extra action =>
    obtain ⟨_, _, _, hcore, hty⟩ :=
      he.core_aligned_of_stratified_inversion inv hΓ
    obtain ⟨_, hActionTy⟩ := uniq hcore.hasType action.sound.hasType.1
    exact hty.defeqDF (hActionTy.symm.defeqDF action.sound)

/-- Multi-step weak-head subject reduction from the same joint inversion
package.  Each next step is typed by the previous step's right endpoint. -/
theorem WHRedS.defeq_of_stratified_inversion
    (inv : JointStratifiedInversion) (hΓ : Ctx.WF Γ)
    (H : WHRedS Γ e1 e2) (he : IsDefEq Γ e1 e1 A) :
    IsDefEq Γ e1 e2 A := by
  induction H with
  | rfl => exact he
  | tail hred hstep ih =>
    exact ih.trans
      (hstep.defeq_of_stratified_inversion inv hΓ ih.hasType.2)

/-- One completed stage of the contextual joint development.  The indices
are deliberately offset: adequacy at the first positive shape level supplies
the sort/Pi observations used to establish limited uniqueness at level zero.
The latter is then consumed while constructing adequacy one level higher. -/
structure LR.JointStage (n : Nat) : Prop where
  adequacyNext : LR.ContextualAdequacyAt (n + 1)
  uniq : LogRel.ContextualLimitedUniq n

/-- The acyclic builder for the joint adequacy/uniqueness tower.

The former interface claimed that `LimitedUniq (LR Γ₀ n)` followed from
`AdequacyAt Γ₀ n` alone.  That is too strong: at bottom shapes the logical
relation forgets the weak typing evidence, and an arbitrary target context
need not even be well formed.  The actual shape induction has a positive
bootstrap.  Level-zero adequacy is built first; a specialized base argument
builds level-one adequacy without predecessor uniqueness.  The path-level
positive bootstrap derives stratified inversion and raw weak type uniqueness
from that package, hence level-zero alignment, with no additional callback.
Each later stage consumes alignment at `n` to build adequacy at `n + 2`, then
proves only the exact, term-indexed lambda-retyping case at `n + 1`;
`LRS.limitedUniq_of_typeUniq` discharges every other shape.  Successor
adequacy also receives adequacy at `n + 1`: transport frames can finish a
native result at a lifted observation and need the already-built lower
theorem to reconstruct the endpoint self-relations before semantic
retyping.  Predecessor uniqueness alone does not provide those witnesses. -/
structure LR.JointBuilder : Prop where
  zero : LR.ContextualAdequacyAt 0
  first : LR.ContextualAdequacyAt 0 → LR.ContextualAdequacyAt 1
  succ : ∀ n, LR.ContextualAdequacyAt (n + 1) →
    LogRel.ContextualLimitedUniq n →
    LR.ContextualAdequacyAt (n + 2)
  uniqSucc : ∀ n,
    LogRel.ContextualLimitedUniq n →
    LR.ContextualAdequacyAt (n + 2) →
    LogRel.ContextualLamRetype n

/-- The context-wide raw uniqueness fact is obtained once from the positive
bootstrap and reused at every successor stratum. -/
theorem LR.JointBuilder.rawTypeUniq (B : LR.JointBuilder) :
    LogRel.ContextualRawTypeUniq :=
  LogRel.contextualRawTypeUniq_of_adequacy (B.first B.zero)

/-- The base inversion package selected by the completed positive
bootstrap. -/
theorem LR.JointBuilder.stratifiedInversion (B : LR.JointBuilder) :
    JointStratifiedInversion :=
  JointStratifiedInversion.of_adequacy (B.first B.zero)

/-- The exact root subject-reduction callback consumed by normalized
constructor chains. -/
theorem WHRedS.defeq_of_jointBuilder
    (B : LR.JointBuilder) (hΓ : Ctx.WF Γ)
    (H : WHRedS Γ e1 e2) (he : IsDefEq Γ e1 e1 A) :
    IsDefEq Γ e1 e2 A :=
  H.defeq_of_stratified_inversion B.stratifiedInversion hΓ he

/-- Consume a normalized constructor observation with both root reductions
discharged by a supplied stratified inversion package.  Native links are
retyped using the raw uniqueness theorem derived from that same package.

This is the depth-bootstrap consumer boundary: a caller may use the
strictly earlier inversion rung directly, without first manufacturing the
completed level-polymorphic `JointBuilder`. -/
theorem LRS.CtorDefEq.foldRaw_of_stratifiedInversion
    (inv : JointStratifiedInversion) (hΓ : Ctx.WF Γ)
    (alg : LRS.CtorChain.RawAlgebra Γ IH m D Q)
    (H : LRS.CtorDefEq Γ IH M N m)
    (hM : IsDefEq Γ M M D) (hN : IsDefEq Γ N N D) : Q M N := by
  let uniq : LogRel.RawTypeUniq Γ := fun h₁ h₂ =>
    IsDefEq.uniq_of_stratified_inversion inv hΓ h₁ h₂
  apply H.foldRaw uniq alg
  · intro X V
    cases V with
    | intro hcl hred =>
      exact hred.defeq_of_stratified_inversion inv hΓ hM
  · intro Y V
    cases V with
    | intro hcl hred =>
      exact hred.defeq_of_stratified_inversion inv hΓ hN

/-- Compatibility wrapper for callers that already carry the completed
joint builder. -/
theorem LRS.CtorDefEq.foldRaw_of_jointBuilder
    (B : LR.JointBuilder) (hΓ : Ctx.WF Γ)
    (alg : LRS.CtorChain.RawAlgebra Γ IH m D Q)
    (H : LRS.CtorDefEq Γ IH M N m)
    (hM : IsDefEq Γ M M D) (hN : IsDefEq Γ N N D) : Q M N :=
  H.foldRaw_of_stratifiedInversion B.stratifiedInversion hΓ alg hM hN

/-- The exact residual of a normalized constructor-chain fold, named apart
from any inversion package.

`LRS.CtorPath.foldRaw` spends raw type uniqueness once per interior chain
vertex — the middle terms introduced by `LRS.CtorDefEq.trans`, which
retains no typing for them — and `LRS.CtorChain.foldRaw`'s two root
callbacks are exactly weak-head subject reduction at the two endpoints.
Nothing else is consumed by the fold, so the two facts are recorded here as
separate fields rather than bundled as `JointStratifiedInversion`: a
producer may reach either half by other means.

This is the whole major-side residual of the coherent iota leaf.  The
per-link consumers (`LRS.iotaDefEq_of_ctorExactAt_coherent` and the
synchronized rectangle `LRS.iotaDefEqRect_of_ctorExactAt`) consume no
inversion, uniqueness or subject-reduction fact at all.

Neither field is reachable from a strict predecessor adequacy rung: an
interior vertex is an arbitrary term whose stratified depth is bounded by
no certificate available at the leaf.  The surviving constraint is
consolidated in the NORM work package of `plans/roadmap.md`; the full
2026-08-15 rung audit remains in git history. -/
structure LR.MajorChainFoldStep (Γ₀ : List SExpr) : Prop where
  /-- Retyping of the interior chain vertices at the externally chosen
  domain. -/
  uniq : LogRel.RawTypeUniq Γ₀
  /-- The two root views' weak-head reductions preserve the root domain. -/
  subjectRed : ∀ {e₁ e₂ A : SExpr}, WHRedS Γ₀ e₁ e₂ →
    IsDefEq Γ₀ e₁ e₁ A → IsDefEq Γ₀ e₁ e₂ A

/-- The completed inversion package supplies both halves.  This certifies
that the two named fields are precisely the facts the existing
`foldRaw_of_stratifiedInversion` consumer spends, with nothing else hidden
in the package. -/
theorem LR.MajorChainFoldStep.of_stratifiedInversion
    (inv : JointStratifiedInversion) (hΓ₀ : Ctx.WF Γ₀) :
    LR.MajorChainFoldStep Γ₀ where
  uniq h₁ h₂ := IsDefEq.uniq_of_stratified_inversion inv hΓ₀ h₁ h₂
  subjectRed hred he := hred.defeq_of_stratified_inversion inv hΓ₀ he

/-- Consume the free constructor-observation closure from the named
chain-fold residual alone.  No well-formedness hypothesis and no inversion
package appear: both are already spent inside the two fields. -/
theorem LRS.CtorDefEq.foldRaw_of_majorChainFoldStep
    (step : LR.MajorChainFoldStep Γ₀)
    (alg : LRS.CtorChain.RawAlgebra Γ₀ IH m D Q)
    (H : LRS.CtorDefEq Γ₀ IH M N m)
    (hM : IsDefEq Γ₀ M M D) (hN : IsDefEq Γ₀ N N D) : Q M N := by
  apply H.foldRaw step.uniq alg
  · intro X V
    cases V with
    | intro _ hred => exact step.subjectRed hred hM
  · intro Y V
    cases V with
    | intro _ hred => exact step.subjectRed hred hN

/-- The chain-fold residual after the 2026-08-15 structural repair.

`LR.MajorChainFoldStep` above is the residual as it stood: raw type uniqueness
for *arbitrary* terms at *arbitrary* types, plus *unrestricted* weak-head
subject reduction.  Both fields are weakened here, independently:

* `ctorRetype` replaces `LogRel.RawTypeUniq Γ₀` by the per-leaf transport of
  `LRS.CtorAnchorDisciplineAt`.  Its subject always carries a native
  `LRS.CtorExact` certificate — head typing, telescope and field payload all
  retained — and it is scoped to a frame of the root observation.  This is the
  field that removed the chain's interior vertices from the obligation
  altogether: `LRS.CtorPath.foldRaw_of_anchorDiscipline` identifies no types.
* `rootRed` replaces unrestricted subject reduction by subject reduction *to a
  classified constructor spine*.  That is exactly the two root callbacks of
  `LRS.CtorChain.foldRaw`, i.e. the two endpoint majors — the terms a redex's
  own stratified certificate does bound, via `HasTypeStratifiedS.app`.

The reduction is faithful in the checkable sense: `of_majorChainFoldStep`
below derives this Prop from the old one, so nothing has been strengthened,
and `LRS.CtorDefEq.foldRaw_of_majorChainAnchorStep` reaches the same
conclusion as `foldRaw_of_majorChainFoldStep` from the weaker inputs. -/
structure LR.MajorChainAnchorStep (Γ₀ : List SExpr) : Prop where
  /-- Each framed native leaf retypes itself at any domain typing one of its
  endpoints. -/
  ctorRetype : ∀ {n k : Nat} {IH : LogRel Γ₀ n} {J : LogRel Γ₀ k}
      {m : WShape (n + 1)} {p : WShape (k + 1)} {X Y : SExpr},
      LRS.CtorFrame Γ₀ IH m J p → LRS.CtorExact Γ₀ J X Y p →
      LRS.CtorRetype Γ₀ X Y
  /-- Weak-head reduction of a root to its classified constructor spine
  preserves the root's type. -/
  rootRed : ∀ {M X A : SExpr}, LRS.CtorView Γ₀ M X →
      IsDefEq Γ₀ M M A → IsDefEq Γ₀ M X A

/-- The environment-level constructor result-type discipline plus root subject
reduction supply the step.  This is the intended producer: the first component
has no depth index at all, having left the adequacy fixpoint entirely. -/
theorem LR.MajorChainAnchorStep.of_ctorSpineTypeUniqPath
    (disc : LRS.CtorSpineTypeUniqPath Γ₀)
    (red : ∀ {M X A : SExpr}, LRS.CtorView Γ₀ M X →
      IsDefEq Γ₀ M M A → IsDefEq Γ₀ M X A) :
    LR.MajorChainAnchorStep Γ₀ where
  ctorRetype _ leaf := leaf.retype_of_ctorSpineTypeUniqPath disc
  rootRed := red

/-- The previous residual implies the repaired one, so the repair is a
weakening and not a restatement. -/
theorem LR.MajorChainAnchorStep.of_majorChainFoldStep
    (step : LR.MajorChainFoldStep Γ₀) : LR.MajorChainAnchorStep Γ₀ :=
  LR.MajorChainAnchorStep.of_ctorSpineTypeUniqPath
    (LRS.CtorSpineTypeUniqPath.of_rawTypeUniq step.uniq)
    (fun V he => by
      cases V with
      | intro _ hred => exact step.subjectRed hred he)

/-- **Both fields of the repaired residual, from one depth-free proposition.**

`LRS.PiPathInv` — Pi injectivity for heterogeneous type paths — discharges
`ctorRetype` and `rootRed` together.  What that replaces is worth stating
exactly, since it is the whole content of the 2026-08-15 repair:

* `ctorRetype` used to be `LogRel.RawTypeUniq Γ₀` at arbitrary terms.  It is
  now the environment-level fact that a *registered-constant* spine has one
  result type (`LRS.constSpineTypeUniqPath`), which reduces to Pi injectivity
  plus two premise-free steps — `HasTypeStratifiedS.spineWF_of_foldl` and
  `LRS.constTypeUniqPath`, the latter consuming nothing at all.
* `rootRed` used to be subject reduction from the full
  `JointStratifiedInversion` package.  It is now
  `WHRedS.defeq_of_piPathInv`, whose per-step lemma names no depth, so the
  multi-step induction re-certifies nothing.  The general form is proved:
  the restriction to classified spines is not used.

Nothing below charges `TypeDefEqPath.collapse` (raw type uniqueness),
`sortPathInv`, or any stratification index. -/
theorem LR.MajorChainAnchorStep.of_piPathInv
    (piInv : LRS.PiPathInv) (hΓ₀ : Ctx.WF Γ₀) :
    LR.MajorChainAnchorStep Γ₀ :=
  LR.MajorChainAnchorStep.of_ctorSpineTypeUniqPath
    (LRS.CtorSpineTypeUniqPath.of_piPathInv piInv hΓ₀)
    (fun V he => by
      cases V with
      | intro _ hred => exact hred.defeq_of_piPathInv piInv hΓ₀ he)

/-- **The same, back to the ladder rungs** (2026-08-15).  With rung R11 landed
(`LRS.PiEdgeInv.of_crLadder`, SLR) the sole input of `of_piPathInv` above is
itself produced by `LRS.PiPathInv.of_crLadder_R11`, so the whole
constructor-observation anchor rests on three Church–Rosser / standardization
rungs and **no adequacy rung at all**.

Recorded because it settles the *ADQ-fixpoint* scheduling question for this
residual the same way `LRS.PiPathInv.of_crLadder_noAdequacy` settles it for the
chain wall: the anchor step needs nothing from the adequacy fixpoint.

It does **not** make the anchor cheaper than the leaf.  The three ladder rungs
are downstream of `LRS.PiPathInv` itself — see the circularity note on
`LRS.crComplete_is_the_last_input` (SLR) — so the honest reading is "the anchor
costs exactly the leaf, and nothing beyond it". -/
theorem LR.MajorChainAnchorStep.of_crLadder
    (srp : LRS.ParRedSDefeq) (cr : LRS.CRComplete) (std : LRS.PiStandard)
    (hΓ₀ : Ctx.WF Γ₀) : LR.MajorChainAnchorStep Γ₀ :=
  LR.MajorChainAnchorStep.of_piPathInv
    (LRS.PiPathInv.of_crLadder_R11 srp cr std) hΓ₀

/-- The free constructor-observation closure folds from the repaired residual
alone.  Same statement as `LRS.CtorDefEq.foldRaw_of_majorChainFoldStep`, with
the interior of the chain no longer spending any type identification:
`ctorRetype` is used once per native leaf and `rootRed` only at the two root
views. -/
theorem LRS.CtorDefEq.foldRaw_of_majorChainAnchorStep
    (step : LR.MajorChainAnchorStep Γ₀)
    (alg : LRS.CtorChain.RawAlgebra Γ₀ IH m D Q)
    (H : LRS.CtorDefEq Γ₀ IH M N m)
    (hM : IsDefEq Γ₀ M M D) (hN : IsDefEq Γ₀ N N D) : Q M N := by
  have disc : LRS.CtorAnchorDisciplineAt Γ₀ IH m :=
    fun frame leaf => step.ctorRetype frame leaf
  refine H.foldRaw_of_anchorDiscipline disc alg ?_ ?_
  · intro X V
    exact step.rootRed V hM
  · intro Y V
    exact step.rootRed V hN

/-- Primitive recursion realizes the offset joint tower; no stage requests
same-level uniqueness before constructing the positive-level adequacy that
justifies it. -/
theorem LR.JointBuilder.build (B : LR.JointBuilder) :
    ∀ n, LR.JointStage n
  | 0 =>
    let adequacyNext : LR.ContextualAdequacyAt 1 := B.first B.zero
    { adequacyNext := adequacyNext
      uniq := fun hΓ => LR0.limitedUniq_of_typeUniq
        (B.rawTypeUniq hΓ) }
  | n + 1 =>
    let prev := B.build n
    let adequacyNext : LR.ContextualAdequacyAt (n + 2) :=
      B.succ n prev.adequacyNext prev.uniq
    { adequacyNext := adequacyNext
      uniq := fun hΓ => LRS.limitedUniq_of_typeUniq
        (B.rawTypeUniq hΓ) (B.uniqSucc n prev.uniq adequacyNext hΓ) }

/-- Recover adequacy at every shape level from the offset tower. -/
theorem LR.JointBuilder.adequacy (B : LR.JointBuilder) :
    ∀ n, LR.ContextualAdequacyAt n
  | 0 => B.zero
  | n + 1 => (B.build n).adequacyNext

/-- Recover limited uniqueness at every predecessor level. -/
theorem LR.JointBuilder.limitedUniq (B : LR.JointBuilder) (n : Nat) :
    LogRel.ContextualLimitedUniq n :=
  (B.build n).uniq

/-- Compatibility name for the corrected builder.  Contextuality is now
inside every stage rather than wrapped around already-built fixed-context
towers. -/
abbrev LR.ContextualJointBuilder := LR.JointBuilder

/-- The contextual tower exports the raw uniqueness package consumed by
path collapse and binder inversion. -/
theorem LR.ContextualJointBuilder.rawTypeUniq
    (B : LR.ContextualJointBuilder) : LogRel.ContextualRawTypeUniq := by
  exact LR.JointBuilder.rawTypeUniq B

/-- Turn a raw equality between types into a logical type equality once both
endpoints are already valid at the same observation.

This is the conversion handoff supplied by the merged adequacy/uniqueness
tower.  Sort observations use typed weak-head subject reduction and sort
inversion.  At a Pi observation, direct stratified Pi inversion aligns the
two exposed domains and codomains; the predecessor relation then handles the
domain and every instantiated codomain recursively.  No general
Church--Rosser assumption or new evaluator premise is used. -/
theorem LR.TyDefEq.of_defeq_of_stratifiedInversion
    (inv : JointStratifiedInversion) :
    ∀ {n : Nat} {Γ : List SExpr} {A B : SExpr} {u : SLevel}
      {a : WShape n},
      Ctx.WF Γ →
      IsDefEq Γ A B (.sort u) →
      (LR Γ).TyDefEq A A a →
      (LR Γ).TyDefEq B B a →
      (LR Γ).TyDefEq A B a := by
  intro n
  induction n with
  | zero =>
    intro Γ A B u a hΓ hAB hAA hBB
    rw [LR_zero] at hAA hBB ⊢
    cases a using WShape.casesOn with
    | bot => trivial
    | sort r =>
      rcases hAA with ⟨uA, hA, _⟩
      rcases hBB with ⟨uB, hB, _⟩
      have hAred := hA.defeq_of_stratified_inversion inv hΓ hAB.hasType.1
      have hBred := hB.defeq_of_stratified_inversion inv hΓ hAB.hasType.2
      have hSort : IsDefEq Γ (.sort uA) (.sort uB) (.sort u) :=
        hAred.symm.trans (hAB.trans hBred)
      have huv := inv.sortInv hΓ (hSort.strong hΓ)
      cases huv
      exact ⟨uA, hA, hB⟩
  | succ n ih =>
    intro Γ A B u a hΓ hAB hAA hBB
    rw [LR_succ] at hAA hBB ⊢
    cases a using WShape.casesOn' with
    | bot => trivial
    | lam => trivial
    | ctor => trivial
    | indTy => exact ⟨hAA.1, hBB.2⟩
    | sort r =>
      rcases hAA with ⟨uA, hA, _⟩
      rcases hBB with ⟨uB, hB, _⟩
      have hAred := hA.defeq_of_stratified_inversion inv hΓ hAB.hasType.1
      have hBred := hB.defeq_of_stratified_inversion inv hΓ hAB.hasType.2
      have hSort : IsDefEq Γ (.sort uA) (.sort uB) (.sort u) :=
        hAred.symm.trans (hAB.trans hBred)
      have huv := inv.sortInv hΓ (hSort.strong hΓ)
      cases huv
      exact ⟨uA, hA, hB⟩
    | forallE b f =>
      rcases hAA with
        ⟨A₁, F₁, A₁', F₁', uA, vA, hA₁, hA₂,
          hDomA, hCodA, hValDomA, hPiA⟩
      have hAeq : SExpr.forallE A₁ F₁ = SExpr.forallE A₁' F₁' :=
        hA₁.determ .forallE hA₂ .forallE
      cases hAeq
      rcases hBB with
        ⟨B₁, G₁, B₁', G₁', uB, vB, hB₁, hB₂,
          hDomB, hCodB, hValDomB, hPiB⟩
      have hBeq : SExpr.forallE B₁ G₁ = SExpr.forallE B₁' G₁' :=
        hB₁.determ .forallE hB₂ .forallE
      cases hBeq
      have hAred := hA₁.defeq_of_stratified_inversion inv hΓ hAB.hasType.1
      have hBred := hB₁.defeq_of_stratified_inversion inv hΓ hAB.hasType.2
      have hPiEq : IsDefEq Γ (.forallE A₁ F₁) (.forallE B₁ G₁)
          (.sort u) := hAred.symm.trans (hAB.trans hBred)
      have hPiStrong := hPiEq.strong hΓ
      obtain ⟨depth, hPiLeft, hPiRight⟩ := hPiStrong.stratify
      obtain ⟨⟨uDom, hDom, _⟩, vCod, hCod, _, _⟩ :=
        inv.forallEInv hΓ hPiStrong hPiLeft hPiRight
      have hValDom : (LR Γ).TyDefEq A₁ B₁ b :=
        ih hΓ hDom hValDomA hValDomB
      have hPi : LRS.PiDefEq (LR Γ) A₁ F₁ G₁ b f := by
        constructor
        · intro x y p hp hxy hrel
          have left := hPiA.1 hp hxy hrel
          have hxyB : Γ ⊢ x ≡ y : B₁ := hDom.defeqDF hxy
          have hrelB : (LR Γ).DefEq x y B₁ p b :=
            (LR Γ).conv hValDom hrel
          have right := hPiB.1 hp hxyB hrelB
          exact ⟨left.leftTy, right.rightTy,
            left.leftDefEq, right.rightDefEq⟩
        · intro x p hp hx hrel
          have left := hPiA.2 hp hx hrel
          have hxB : Γ ⊢ x : B₁ := hDom.defeqDF hx
          have hrelB : (LR Γ).DefEq x x B₁ p b :=
            (LR Γ).conv hValDom hrel
          have right := hPiB.2 hp hxB hrelB
          have hCodInst : Γ ⊢ F₁.inst x ≡ G₁.inst x : .sort vCod := by
            simpa only [SExpr.inst, SExpr.subst] using hCod.subst
              (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar hx)
          exact ih hΓ hCodInst left right
      exact ⟨A₁, F₁, B₁, G₁, uDom, vCod,
        hA₁, hB₁, .single hDom, .single hCod, hValDom, hPi⟩

/-- Compatibility wrapper exposing the conversion handoff from a completed
joint builder.  The proof itself only needs the positive-bootstrap
stratified inversion package; keeping that smaller dependency explicit is
what lets the fixed-head consumer participate in the staged joint tower. -/
theorem LR.TyDefEq.of_defeq_of_jointBuilder
    (J : LR.JointBuilder) :
    ∀ {n : Nat} {Γ : List SExpr} {A B : SExpr} {u : SLevel}
      {a : WShape n},
      Ctx.WF Γ →
      IsDefEq Γ A B (.sort u) →
      (LR Γ).TyDefEq A A a →
      (LR Γ).TyDefEq B B a →
      (LR Γ).TyDefEq A B a :=
  LR.TyDefEq.of_defeq_of_stratifiedInversion J.stratifiedInversion

theorem LR.Adequate.bot (ha : a.HasType .type) : Adequate Γ₀ Γ ρ M N A .bot a :=
  ⟨fun _ _ _ => ⟨(LR _).bot ha, (LR _).bot ha⟩, fun _ _ => (LR _).bot ha⟩

theorem LR.Adequate.fits
    (H : ρ.Fits Γ₀ Γ → Adequate Γ₀ Γ ρ M N A m a) : Adequate Γ₀ Γ ρ M N A m a :=
  ⟨fun _ _ W => (H W.fits).1 W, fun _ W => (H W.fits).2 W⟩

theorem LR.Adequate.refl
    (H : ∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ ρ →
      (LR Γ₀).DefEq (M.subst σ) (M.subst σ') (A.subst σ) m a) :
    Adequate Γ₀ Γ ρ M M A m a := ⟨fun _ _ W => ⟨H W, H W⟩, fun _ W => H W⟩

/-- Expose adequacy's two endpoint congruences and its heterogeneous edge as
one rectangle.  The diagonal is oriented from the left substitution to the
right substitution: first use same-substitution adequacy on the left, then
the right-head congruence supplied by the relational substitution.  All
three edges therefore retain the left-oriented result type required by
dependent application. -/
theorem LR.Adequate.rect
    (H : Adequate Γ₀ Γ ρ M N A m a)
    (W : LR.SubstWF Γ₀ σ σ' Γ ρ) :
    LogRel.DefEqRect (LR Γ₀)
      (M.subst σ) (M.subst σ') (N.subst σ) (N.subst σ')
      (A.subst σ) m a := by
  have hcongr := H.1 W
  exact ⟨hcongr.1, hcongr.2,
    (LR Γ₀).trans (H.2 W.left) hcongr.2⟩

theorem LR.Adequate.left : Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ M M A m a
  | ⟨h1, _⟩ => .refl fun _ _ W => (h1 W).1

theorem LR.Adequate.symm : Adequate Γ₀ Γ ρ M N A m a → Adequate Γ₀ Γ ρ N M A m a
  | ⟨h1, h2⟩ => ⟨fun _ _ W => (h1 W).symm, fun _ W => (LR _).symm (h2 W)⟩

theorem LR.Adequate.trans :
    Adequate Γ₀ Γ ρ M₁ M₂ A m a → Adequate Γ₀ Γ ρ M₂ M₃ A m a → Adequate Γ₀ Γ ρ M₁ M₃ A m a
  | ⟨a1, a2⟩, ⟨b1, b2⟩ =>
    ⟨fun _ _ W => ⟨(a1 W).1, (b1 W).2⟩, fun _ W => (LR _).trans (a2 W) (b2 W)⟩

theorem LR.Adequate.trans' : Adequate Γ₀ Γ ρ A₁ A₂ (.sort u) a s →
    Adequate Γ₀ Γ ρ A₂ A₃ (.sort v) a (.sort r) → Adequate Γ₀ Γ ρ A₁ A₃ (.sort u) a s
  | ⟨a1, a2⟩, ⟨b1, b2⟩ => by
    refine ⟨fun σ σ' W => ⟨(a1 W).1, ?_⟩, fun _ W => (LR _).trans' (a2 W) (b2 W)⟩
    have h1 := (LR _).trans' (a1 W.left).2 (b2 W.left)
    have h2 := (LR _).trans' (a1 W.symm.left).2 (b2 W.symm.left)
    exact (LR _).trans ((LR _).symm h1) <| (LR _).trans (a1 W).2 h2

/-- Bottom term observations are directly adequate; a sort-shaped ambient
obligation receives the direct bottom constructor. -/
theorem LR.DirectAdequate.bot (ha : a.HasType .type) :
    DirectAdequate Γ₀ Γ ρ M N A .bot a := by
  have direct {X Y T : SExpr} : LR.DirectDefEq Γ₀ X Y T .bot a :=
    ⟨(LR Γ₀).bot ha, fun _ _ => .bot⟩
  exact ⟨fun _ _ _ => ⟨direct, direct⟩, fun _ _ => direct⟩

/-- Reflexive direct adequacy from the relational-substitution congruence
edge. -/
theorem LR.DirectAdequate.refl
    (H : ∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Γ ρ →
      LR.DirectDefEq Γ₀ (M.subst σ) (M.subst σ') (A.subst σ) m a) :
    DirectAdequate Γ₀ Γ ρ M M A m a :=
  ⟨fun _ _ W => ⟨H W, H W⟩, fun _ W => H W⟩

theorem LR.DirectAdequate.left :
    DirectAdequate Γ₀ Γ ρ M N A m a →
      DirectAdequate Γ₀ Γ ρ M M A m a
  | ⟨h1, _⟩ => .refl fun _ _ W => (h1 W).1

theorem LR.DirectAdequate.symm :
    DirectAdequate Γ₀ Γ ρ M N A m a →
      DirectAdequate Γ₀ Γ ρ N M A m a
  | ⟨h1, h2⟩ =>
    ⟨fun _ _ W => (h1 W).symm, fun _ W => (h2 W).symm⟩

theorem LR.DirectAdequate.trans :
    DirectAdequate Γ₀ Γ ρ M₁ M₂ A m a →
    DirectAdequate Γ₀ Γ ρ M₂ M₃ A m a →
      DirectAdequate Γ₀ Γ ρ M₁ M₃ A m a
  | ⟨a1, a2⟩, ⟨b1, b2⟩ =>
    ⟨fun _ _ W => ⟨(a1 W).1, (b1 W).2⟩,
      fun _ W => (a2 W).trans (b2 W)⟩

/--
info: 'Lean4Lean.SExpr.LR.DirectAdequate.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectAdequate.trans

/-- Lower adequacy from a saturated semantic witness to a compatible smaller
witness.  Constant evaluation recursively builds finite approximants; this
lemma reconciles the resulting type witnesses through their join. -/
theorem LR.Adequate.mono_r {Γ₀ Γ : List SExpr} {ρ : Valuation} {M N A : SExpr}
    {n n' : Nat} {m a : WShape n} {m' a' : WShape n'}
    (le : m.T ≤ m'.T) (hmem : m.HasType a) (hmem' : m'.HasType a')
    (hc : a.T.Compat a'.T)
    (hAty : ∀ {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ),
      (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) a)
    (hAty' : ∀ {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ),
      (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) a')
    (H : Adequate Γ₀ Γ ρ M N A m' a') : Adequate Γ₀ Γ ρ M N A m a := by
  have hJ := TShape.Join.mk hc
  have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
  have hkn : n ≤ max n n' := Nat.le_max_left ..
  have hkn' : n' ≤ max n n' := Nat.le_max_right ..
  have hjk : (a.T.join a'.T).1 ≤ max n n' := Nat.max_le.2 ⟨hkn, hkn'⟩
  have hJ1' := (TShape.LE.def hkn hjk).1 hJ1
  have hJ2' := (TShape.LE.def hkn' hjk).1 hJ2
  have hJ_t := (TShape.HasType.sort_r.2 hmem.isType).join' hJ
    (TShape.HasType.sort_r.2 hmem'.isType)
  have hmem_k := (WShape.HasType.lift hkn).2 hmem
  have hmem'_k := (WShape.HasType.lift hkn').2 hmem'
  have hJ_t' := TShape.HasType.sort_r.1 <|
    hJ_t.mono_l (TShape.lift_eqv hjk).2 (TShape.lift_eqv hjk).1
  have lower : ∀ {M₀ N₀ : SExpr} {{σ σ'}} (W : LR.SubstWF Γ₀ σ σ' Γ ρ),
      (LR Γ₀).DefEq M₀ N₀ (A.subst σ) m' a' →
      (LR Γ₀).DefEq M₀ N₀ (A.subst σ) m a := by
    intro M₀ N₀ σ σ' W hv
    have ha_kty : (WShape.lift (max n n') a).HasType .type := by
      simpa using (WShape.HasType.lift hkn).2 hmem.isType
    have ha'_kty : (WShape.lift (max n n') a').HasType .type := by
      simpa using (WShape.HasType.lift hkn').2 hmem'.isType
    have tyJ := (LR Γ₀).join_ty ((TShape.Compat.def hkn hkn').2 hc) ha_kty ha'_kty
      ((TyDefEq.lift hkn hmem.isType).2 (hAty W))
      ((TyDefEq.lift hkn' hmem'.isType).2 (hAty' W))
    have tyJ' : (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ)
        ((a.T.join a'.T).snd.lift (max n n')) := WShape.lift_self ▸ tyJ
    refine (DefEq.lift hkn hmem).1 <| (LR Γ₀).mono_r_2 hJ1' hmem_k hJ_t' <|
      (LR Γ₀).mono_l ((TShape.LE.def hkn hkn').1 le)
        (.mono_r hJ1' hJ_t' hmem_k) (.mono_r hJ2' hJ_t' hmem'_k) <|
      (LR Γ₀).mono_r_1 hJ2' hmem'_k (.mono_r hJ2' hJ_t' hmem'_k) tyJ' <|
        (DefEq.lift hkn' hmem').2 hv
  exact ⟨fun σ σ' W => ⟨lower W (H.1 W).1, lower W (H.1 W).2⟩,
    fun σ W => lower W (H.2 W)⟩

theorem LR.Adequate.cons
    (ihA : ∀ {ρ n} {m a : WShape n}, LE_Interp ρ m.T A → LE_Interp ρ a.T (.sort u) →
      m.HasType a → Adequate Γ₀ Γ ρ A A' (sort u) m a)
    (HA : IsDefEqStrong Γ A A' (.sort u))
    {{k : Nat}} {{a₁ p : WShape k}} {{x x' σ σ' ρ}}
    (hp : p.HasType a₁) (hA₁ : LE_Interp ρ a₁.T A)
    (hx : Γ₀ ⊢ x ≡ x' : A.subst σ) (hv : (LR Γ₀).DefEq x x' (A.subst σ) p a₁)
    (W : SubstWF Γ₀ σ σ' Γ ρ) : SubstWF Γ₀ (σ.cons x) (σ'.cons x') (A :: Γ) (ρ.push p.T) := by
  refine W.cons (fun hA => ?_) hA₁ hp.T HA.defeq.hasType.1 ⟨hx, fun n a' ha' => ?_⟩
  · have ⟨_, _, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.fits).2 hA
    exact ⟨_, le_a, hA', (TShape.HasType.mono_r hSort.le_sort .sort hmem').toType⟩
  have ha' := LE_Interp.weak_iff.1 ha'
  refine ⟨fun ht => ⟨⟨_, (HA.substCongr W.toSubstEq).1⟩, ?_⟩, fun m' hm' ht => ?_⟩
  · have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.fits).2 ha' |>.out
    refine (TyDefEq.lift le_n ht).1 <| (LR Γ₀).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
      (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
      (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType ?_
    exact (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hSort.le_sort' hmem'
      (.mono_r hSort.le_sort' .sort hmem') .sort ((ihA hA' hSort hmem').1 W).1
  · have le_k := Nat.le_max_left k n; have le_n := Nat.le_max_right k n
    have ht' := (WShape.HasType.lift le_n).2 ht
    have hp' := (WShape.HasType.lift le_k).2 hp
    have hle' := (TShape.LE.def le_n le_k).1 (LE_Interp.bvar_iff.1 hm')
    have hta₁ := WShape.lift_type ▸ (WShape.HasType.lift le_k).2 hp.isType
    have hta' := WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht.isType
    have hc := hA₁.compat ha'
    have hj := (TShape.Join.def le_k le_n (Nat.le_refl _)).1 (.mk hc)
    rw [TShape.lift_join le_k le_n] at hj
    have ⟨hj1, hj2⟩ := hj.le
    have hJ := hta₁.join' hj hta'
    have hJ' := hJ.mono_r hj1 hp'
    refine (DefEq.lift le_n ht).1 <|
      (LR Γ₀).mono_r_2 hj2 ht' hJ <|
      (LR Γ₀).mono_l hle' (hJ.mono_r hj2 ht') hJ' <|
      (LR Γ₀).mono_r_1 hj1 hp' hJ' ?_ <| (DefEq.lift le_k hp).2 hv
    have valTyA {nd : Nat} {a : WShape nd} (hA : LE_Interp ρ a.T A) (ha : a.HasType .type) :
        (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) a :=
      have ⟨_, _, _, le_n, le_a, hA', hSort, hmem'⟩ := (LE_Interp.sound HA W.left.fits).2 hA |>.out
      have v2 := (ihA hA' hSort hmem').2 W.left
      have vt := (LR Γ₀).left_ty <| (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hSort.le_sort' hmem'
        (.mono_r hSort.le_sort' .sort hmem') .sort v2
      (TyDefEq.lift le_n ha).1 <| (LR Γ₀).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
        (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ha)
        (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType vt
    refine (LR Γ₀).join_ty ((TShape.Compat.def le_k le_n).2 hc) hta₁ hta' ?_ ?_
    · exact (TyDefEq.lift le_k hp.isType).2 (valTyA hA₁ hp.isType)
    · exact (TyDefEq.lift le_n ht.isType).2 (valTyA ha' ht.isType)

/-- Extract `TyDefEq` from a `DefEq` at sort type. -/
theorem LR.toValTy {m : WShape n'} {b : WShape n} (le_n : n ≤ n') (le_a : b.T ≤ m.T)
    (ht : b.HasType .type) (hSort : LE_Interp ρ a.T (.sort u)) (hmem' : m.HasType a)
    (H : (LR Γ₀).DefEq M N (.sort u) m a) : (LR Γ₀).TyDefEq M N b := by
  have hle := hSort.le_sort'
  refine (LR.TyDefEq.lift le_n ht).1 ?_
  refine (LR Γ₀).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
    (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 ht)
    (WShape.HasType.mono_r hle .sort hmem').toType ?_
  exact (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hle hmem'
    (.mono_r hle .sort hmem') .sort H

/-- One function layer of constant evaluation.  The continuation receives
the original strictly smaller semantic branch together with the input and
output bounds that select it.  Keeping that provenance explicit lets the
caller recurse on the actual `Const.lam` child rather than on a reconstructed
`lift`/`mono` proof of equal depth. -/
theorem LR.constLamDefEq
    {n n' nArgs : Nat} {f : WShapeFun n} {f' : WShapeFun n'} {hf : f.NonZero}
    {M N : SExpr}
    {a₁ : WShape n} {a₂ : WShapeFun n}
    {A₁ A₂ : SExpr}
    (htm : WShape.HasTypeLam f a₁ a₂)
    (hlam : (WShape.lam' f).T ≤ (WShape.lam' f').T)
    (eval : ∀ {x y : SExpr} {p : WShape (max n nArgs)}
      {x₀ y₀ : WShape n'},
      p.HasType (a₁.lift (max n nArgs)) →
      Γ₀ ⊢ x ≡ y : A₁ →
      (LR Γ₀).DefEq x y A₁ p (a₁.lift (max n nArgs)) →
      (x₀, y₀) ∈ f' → x₀.T ≤ p.T →
      ((f.lift (max n nArgs)).app p).T ≤ y₀.T →
      LogRel.DefEqRect (LR Γ₀)
        (M.app x) (M.app y) (N.app x) (N.app y)
        (A₂.inst x) ((f.lift (max n nArgs)).app p)
          ((a₂.lift (max n nArgs)).app p)) :
    LRS.LamDefEq (LR Γ₀) M N A₁ A₂ f a₁ a₂ := by
  let k := max n nArgs
  have hn : n ≤ k := Nat.le_max_left ..
  have hnArgs : nArgs ≤ k := Nat.le_max_right ..
  have childBounds (p : WShape n) :
      ∃ x₀ y₀ : WShape n', (x₀, y₀) ∈ f' ∧
        x₀.T ≤ p.T ∧ (f.app p).T ≤ y₀.T := by
    let K := max n n'
    have hnK : n ≤ K := Nat.le_max_left ..
    have hn'K : n' ≤ K := Nat.le_max_right ..
    have hffT : TShapeFun.LE f f' := TShape.LE.lam'_decomp hlam
    have hff : f.lift K ≤ f'.lift K :=
      (TShapeFun.LE.def hnK hn'K).1 hffT
    obtain ⟨x, hx, hmem⟩ := (f.lift K).app_eq (p.lift K)
    obtain ⟨x', y', hmem', hx', hy'⟩ :=
      WShapeFun.LE.def'.1 hff _ _ hmem
    obtain ⟨x₀, y₀, hmem₀, rfl, rfl⟩ :=
      (WShapeFun.mem_lift hn'K).1 hmem'
    have hxT : x₀.T ≤ p.T :=
      (TShape.lift_eqv hn'K).2 |>.trans
        ((hx'.trans hx).T) |>.trans (TShape.lift_eqv hnK).1
    have hyLift : (f.app p).lift K ≤ y₀.lift K := by
      simpa only [WShapeFun.lift_app hnK] using hy'
    have hyT : (f.app p).T ≤ y₀.T :=
      (TShape.lift_eqv hnK).2 |>.trans hyLift.T |>.trans
        (TShape.lift_eqv hn'K).1
    exact ⟨x₀, y₀, hmem₀, hxT, hyT⟩
  have lower {x y : SExpr} {p : WShape n}
      (hp : p.HasType a₁) (hxy : Γ₀ ⊢ x ≡ y : A₁)
      (hv : (LR Γ₀).DefEq x y A₁ p a₁) :
      LogRel.DefEqRect (LR Γ₀)
        (M.app x) (M.app y) (N.app x) (N.app y)
        (A₂.inst x) (f.app p) (a₂.app p) := by
    have hpₖ : (p.lift k).HasType (a₁.lift k) :=
      (WShape.HasType.lift hn).2 hp
    have hvₖ : (LR Γ₀).DefEq x y A₁ (p.lift k) (a₁.lift k) :=
      (LR.DefEq.lift hn hp).2 hv
    obtain ⟨x₀, y₀, hmem₀, hx₀, hy₀⟩ := childBounds p
    have hy₀k : ((f.lift k).app (p.lift k)).T ≤ y₀.T := by
      rw [← WShapeFun.lift_app hn]
      exact (TShape.lift_eqv hn).1.trans hy₀
    have hout := eval hpₖ hxy hvₖ hmem₀
      (hx₀.trans (TShape.lift_eqv hn).2) hy₀k
    have lowerEdge {P Q : SExpr}
        (H : (LR Γ₀).DefEq P Q (A₂.inst x)
          ((f.lift k).app (p.lift k)) ((a₂.lift k).app (p.lift k))) :
        (LR Γ₀).DefEq P Q (A₂.inst x) (f.app p) (a₂.app p) := by
      have H' : (LR Γ₀).DefEq P Q (A₂.inst x)
          ((f.app p).lift k) ((a₂.app p).lift k) := by
        simpa only [WShapeFun.lift_app hn] using H
      exact (LR.DefEq.lift hn
        ((WShape.HasTypeLam.iff.1 htm).2.2 p hp)).1 H'
    exact ⟨lowerEdge hout.left, lowerEdge hout.right, lowerEdge hout.cross⟩
  refine ⟨fun _ _ _ hp hxy hv => ?_, fun _ _ hp hx hv => ?_⟩
  · have H := lower hp hxy hv
    exact ⟨H.left, H.right⟩
  · exact (lower hp hx hv).cross
/-- The synchronized guarded rectangle produced by evaluating related
heads at related arguments. -/
structure LR.DirectDefEqRect (IH : LR.DirectRelBase Γ n)
    (M₁ M₂ N₁ N₂ A : SExpr) (m a : WShape n) : Prop where
  left : IH.DefEq M₁ M₂ A m a
  right : IH.DefEq N₁ N₂ A m a
  cross : IH.DefEq M₁ N₂ A m a

/-- A single guarded edge supplies the synchronized diagonal rectangle. -/
theorem LR.DirectDefEqRect.diagonal
    (H : IH.DefEq M N A m a) :
    LR.DirectDefEqRect IH M N M N A m a :=
  ⟨H, H, H⟩

/-- Compose synchronized guarded rectangles at their common middle pair. -/
theorem LR.DirectDefEqRect.trans
    (H₁ : LR.DirectDefEqRect IH M₁ M₂ N₁ N₂ A m a)
    (H₂ : LR.DirectDefEqRect IH M₂ M₃ N₂ N₃ A m a)
    (trans : ∀ {X Y Z},
      IH.DefEq X Y A m a → IH.DefEq Y Z A m a →
      IH.DefEq X Z A m a) :
    LR.DirectDefEqRect IH M₁ M₃ N₁ N₃ A m a :=
  ⟨trans H₁.left H₂.left, trans H₁.right H₂.right,
    trans H₁.cross H₂.right⟩

/-- Specialize rectangle composition to the guarded logical relation. -/
theorem LR.DirectDefEqRect.transLRD
    (H₁ : LR.DirectDefEqRect (LRD Γ) M₁ M₂ N₁ N₂ A m a)
    (H₂ : LR.DirectDefEqRect (LRD Γ) M₂ M₃ N₂ N₃ A m a) :
    LR.DirectDefEqRect (LRD Γ) M₁ M₃ N₁ N₃ A m a :=
  H₁.trans H₂ LRD.DefEq.trans

theorem LR.DirectDefEqRect.toLegacy
    {Γ : List SExpr} {n : Nat} {IH : LR.DirectRelBase Γ n}
    {m a : WShape n}
    (H : LR.DirectDefEqRect IH M₁ M₂ N₁ N₂ A m a) :
    LogRel.DefEqRect (LR Γ) M₁ M₂ N₁ N₂ A m a :=
  ⟨IH.defLegacy H.left, IH.defLegacy H.right, IH.defLegacy H.cross⟩

/--
info: 'Lean4Lean.SExpr.LR.DirectDefEqRect.transLRD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectDefEqRect.transLRD

/-- One guarded rectangle for every native link of a normalized constructor
path, at one fixed root recursor site.  The root-major bridge is threaded
explicitly so a concrete generated-rule producer can reuse the selected
major rather than reselect semantic evidence at an interior vertex. -/
def LR.DirectMajorLinkRectAt (Γ₀ : List SExpr)
    {n : Nat} (rootShape : WShape (n + 1)) (D : SExpr)
    (rec : Name) (ls : List SLevel) (recXs recYs : List SExpr)
    (rootMajor A : SExpr) (out outTy : WShape (n + 1)) : Prop :=
  ∀ {k : Nat} {J : LogRel Γ₀ k} {p : WShape (k + 1)} {X Y : SExpr},
    LRS.CtorFrame Γ₀ (LR Γ₀) rootShape J p →
    LRS.CtorExact Γ₀ J X Y p →
    IsDefEq Γ₀ X Y D →
    IsDefEq Γ₀ rootMajor X D →
    LR.DirectDefEqRect (LRD Γ₀)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec ls)).app X)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec ls)).app Y)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec ls)).app X)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec ls)).app Y)
      A out outTy

/-- Reuse the left recursor prefix at any term equal to the recorded left
major.  The instantiated codomain is connected back to the recorded result
by a heterogeneous type path, so the two universe indices are never
identified. -/
theorem SpineWF.LastPair.fullXAt
    (hΓ : Ctx.WF Γ)
    (H : SExpr.SpineWF.LastPair Γ Head xs ys x y A)
    (hxz : IsDefEq Γ x z H.domain) :
    SExpr.SpineWF Γ Head (xs.reverse ++ [z]) A := by
  obtain ⟨⟨u, hDomain⟩, v, hCodomain⟩ :=
    (H.pi.strong hΓ).forallE_inv' (.inr rfl)
  have W : Ctx.SubstEq Γ (.one z) (.one x) (H.domain :: Γ) := by
    refine .cons .nil hDomain.defeq ?_
    show IsDefEq Γ z x (H.domain.subst SExpr.Subst.id)
    rw [SExpr.subst_id]
    exact hxz.symm
  have hinst : IsDefEq Γ (H.codomain.inst z) (H.codomain.inst x)
      (.sort v) := by
    simpa only [SExpr.inst, SExpr.subst] using
      (hCodomain.substCongr W).1
  exact SpineWF.ret_path
    ((TypeDefEqPath.single hinst).trans
      (TypeDefEqPath.single H.resultX))
    (H.prefixX.snoc_path (.single H.pi) hxz.hasType.2)

/-- Reuse the right recursor prefix at any term equal to the recorded right
major, with the same path-valued result transport as `fullXAt`. -/
theorem SpineWF.LastPair.fullYAt
    (hΓ : Ctx.WF Γ)
    (H : SExpr.SpineWF.LastPair Γ Head xs ys x y A)
    (hyz : IsDefEq Γ y z H.domain) :
    SExpr.SpineWF Γ Head (ys.reverse ++ [z]) A :=
  H.symm.fullXAt hΓ hyz

/--
info: 'Lean4Lean.SExpr.SpineWF.LastPair.fullXAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpineWF.LastPair.fullXAt

/--
info: 'Lean4Lean.SExpr.SpineWF.LastPair.fullYAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SpineWF.LastPair.fullYAt

/-- Fold a free constructor-major observation into the guarded cross edge at
one fixed recursor site.

The constructor closure is first normalized to a root view and a native path.
Only the path is folded by `DirectMajorLinkRectAt`; afterward the two literal
root majors are transported to its endpoints using `TypedWHRedS` built from
the retained `LastPair` Pi/result certificates.  Thus the final guarded
weak-head step consumes typed reductions and never manufactures conversion
evidence from a raw `WHRedS`. -/
theorem LRD.iotaDefEq_of_ctorDefEqAt
    {n : Nat} {rootShape out outTy : WShape (n + 1)}
    {majorX majorY CHead A : SExpr}
    {rec : Name} {ls : List SLevel} {recXs recYs : List SExpr}
    (anchor : LR.MajorChainAnchorStep Γ₀)
    (hmajor : LRS.CtorDefEq Γ₀ (LR Γ₀)
      majorX majorY rootShape)
    (hpair : SExpr.SpineWF.LastPair Γ₀ CHead
      recXs recYs majorX majorY A)
    (hhead : IsDefEq Γ₀ (.const rec ls) (.const rec ls) CHead)
    (hmajorPremX : IsMajorPremise
      (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec ls)))
    (hmajorPremY : IsMajorPremise
      (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec ls)))
    (hA : (LRD Γ₀).TyDefEq A A outTy)
    (link : LR.DirectMajorLinkRectAt Γ₀ rootShape hpair.domain
      rec ls recXs recYs majorX A out outTy) :
    (LRD Γ₀).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec ls)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec ls)).app majorY)
      A out outTy := by
  cases hmajor.toChain with
  | @intro X Y hleft hright path =>
    have hMX : IsDefEq Γ₀ majorX X hpair.domain :=
      anchor.rootRed hleft hpair.major.hasType.1
    have hNY : IsDefEq Γ₀ majorY Y hpair.domain :=
      anchor.rootRed hright hpair.major.hasType.2
    have disc : LRS.CtorAnchorDisciplineAt Γ₀ (LR Γ₀) rootShape :=
      fun frame leaf => anchor.ctorRetype frame leaf
    have hfold := path.foldRaw_of_anchorDiscipline
      (D := hpair.domain)
      (Q := fun X Y =>
        IsDefEq Γ₀ majorX X hpair.domain →
          LR.DirectDefEqRect (LRD Γ₀)
            ((recXs.foldr (fun (a f : SExpr) => f.app a)
              (.const rec ls)).app X)
            ((recXs.foldr (fun (a f : SExpr) => f.app a)
              (.const rec ls)).app Y)
            ((recYs.foldr (fun (a f : SExpr) => f.app a)
              (.const rec ls)).app X)
            ((recYs.foldr (fun (a f : SExpr) => f.app a)
              (.const rec ls)).app Y)
            A out outTy ∧
          IsDefEq Γ₀ majorX Y hpair.domain)
      disc
      { exact := fun frame leaf hXY hbridge =>
          ⟨link frame leaf hXY hbridge, hbridge.trans hXY⟩
        trans := fun h₁ h₂ hbridge => by
          obtain ⟨r₁, hY⟩ := h₁ hbridge
          obtain ⟨r₂, hZ⟩ := h₂ hY
          exact ⟨r₁.transLRD r₂, hZ⟩ }
      hMX.hasType.2
    obtain ⟨rect, _hY⟩ := hfold hMX
    have hprefixX : IsDefEq Γ₀
        (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec ls))
        (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec ls))
        hpair.prefixType := by
      simpa only [List.foldl_reverse] using hpair.prefixX.hasType hhead
    have hprefixY : IsDefEq Γ₀
        (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec ls))
        (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec ls))
        hpair.prefixType := by
      simpa only [List.foldl_reverse] using hpair.prefixY.hasType hhead
    have hredX : TypedWHRedS Γ₀
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec ls)).app majorX)
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec ls)).app X)
        A := by
      refine ⟨hpair.resultX.defeqDF
        (.appDF (hpair.pi.defeqDF hprefixX) hMX), ?_⟩
      cases hleft with
      | intro _ hred => exact .major hmajorPremX hred
    have hredY : TypedWHRedS Γ₀
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec ls)).app majorY)
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec ls)).app Y)
        A := by
      refine ⟨hpair.resultY.defeqDF
        (.appDF (hpair.pi.defeqDF hprefixY) hNY), ?_⟩
      cases hright with
      | intro _ hred => exact .major hmajorPremY hred
    exact (LRD.DefEq.whr hA hredX hredY).2 rect.cross

/--
info: 'Lean4Lean.SExpr.LR.DirectMajorLinkRectAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectMajorLinkRectAt

/--
info: 'Lean4Lean.SExpr.LRD.iotaDefEq_of_ctorDefEqAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaDefEq_of_ctorDefEqAt

theorem LRD.constLamDefEq
    {n n' nArgs : Nat} {f : WShapeFun n} {f' : WShapeFun n'}
    {hf : f.NonZero} {M N : SExpr}
    {a₁ : WShape n} {a₂ : WShapeFun n} {A₁ A₂ : SExpr}
    (htm : WShape.HasTypeLam f a₁ a₂)
    (hlam : (WShape.lam' f).T ≤ (WShape.lam' f').T)
    (eval : ∀ {x y : SExpr} {p : WShape (max n nArgs)}
      {x₀ y₀ : WShape n'},
      p.HasType (a₁.lift (max n nArgs)) →
      IsDefEq Γ₀ x y A₁ →
      (LRD Γ₀).DefEq x y A₁ p (a₁.lift (max n nArgs)) →
      (x₀, y₀) ∈ f' → x₀.T ≤ p.T →
      ((f.lift (max n nArgs)).app p).T ≤ y₀.T →
      LR.DirectDefEqRect (LRD Γ₀)
        (M.app x) (M.app y) (N.app x) (N.app y)
        (A₂.inst x) ((f.lift (max n nArgs)).app p)
          ((a₂.lift (max n nArgs)).app p)) :
    LR.DirectLamDefEq (LRD Γ₀) M N A₁ A₂ f a₁ a₂ := by
  let k := max n nArgs
  have hn : n ≤ k := Nat.le_max_left ..
  have childBounds (p : WShape n) :
      ∃ x₀ y₀ : WShape n', (x₀, y₀) ∈ f' ∧
        x₀.T ≤ p.T ∧ (f.app p).T ≤ y₀.T := by
    let K := max n n'
    have hnK : n ≤ K := Nat.le_max_left ..
    have hn'K : n' ≤ K := Nat.le_max_right ..
    have hffT : TShapeFun.LE f f' := TShape.LE.lam'_decomp hlam
    have hff : f.lift K ≤ f'.lift K :=
      (TShapeFun.LE.def hnK hn'K).1 hffT
    obtain ⟨x, hx, hmem⟩ := (f.lift K).app_eq (p.lift K)
    obtain ⟨x', y', hmem', hx', hy'⟩ :=
      WShapeFun.LE.def'.1 hff _ _ hmem
    obtain ⟨x₀, y₀, hmem₀, rfl, rfl⟩ :=
      (WShapeFun.mem_lift hn'K).1 hmem'
    have hxT : x₀.T ≤ p.T :=
      (TShape.lift_eqv hn'K).2 |>.trans
        ((hx'.trans hx).T) |>.trans (TShape.lift_eqv hnK).1
    have hyLift : (f.app p).lift K ≤ y₀.lift K := by
      simpa only [WShapeFun.lift_app hnK] using hy'
    have hyT : (f.app p).T ≤ y₀.T :=
      (TShape.lift_eqv hnK).2 |>.trans hyLift.T |>.trans
        (TShape.lift_eqv hn'K).1
    exact ⟨x₀, y₀, hmem₀, hxT, hyT⟩
  have lower {x y : SExpr} {p : WShape n}
      (hp : p.HasType a₁) (hxy : IsDefEq Γ₀ x y A₁)
      (hv : (LRD Γ₀).DefEq x y A₁ p a₁) :
      LR.DirectDefEqRect (LRD Γ₀)
        (M.app x) (M.app y) (N.app x) (N.app y)
        (A₂.inst x) (f.app p) (a₂.app p) := by
    have hpₖ : (p.lift k).HasType (a₁.lift k) :=
      (WShape.HasType.lift hn).2 hp
    have hvₖ : (LRD Γ₀).DefEq x y A₁
        (p.lift k) (a₁.lift k) :=
      (LRD.DefEq.lift hn hp).2 hv
    obtain ⟨x₀, y₀, hmem₀, hx₀, hy₀⟩ := childBounds p
    have hy₀k : ((f.lift k).app (p.lift k)).T ≤ y₀.T := by
      rw [← WShapeFun.lift_app hn]
      exact (TShape.lift_eqv hn).1.trans hy₀
    have hout := eval hpₖ hxy hvₖ hmem₀
      (hx₀.trans (TShape.lift_eqv hn).2) hy₀k
    have lowerEdge {P Q : SExpr}
        (H : (LRD Γ₀).DefEq P Q (A₂.inst x)
          ((f.lift k).app (p.lift k))
          ((a₂.lift k).app (p.lift k))) :
        (LRD Γ₀).DefEq P Q (A₂.inst x)
          (f.app p) (a₂.app p) := by
      have H' : (LRD Γ₀).DefEq P Q (A₂.inst x)
          ((f.app p).lift k) ((a₂.app p).lift k) := by
        simpa only [WShapeFun.lift_app hn] using H
      exact (LRD.DefEq.lift hn
        ((WShape.HasTypeLam.iff.1 htm).2.2 p hp)).1 H'
    exact ⟨lowerEdge hout.left, lowerEdge hout.right,
      lowerEdge hout.cross⟩
  refine ⟨fun _ _ _ hp hxy hv => ?_, fun _ _ hp hx hv => ?_⟩
  · have H := lower hp hxy hv
    exact ⟨H.left, H.right⟩
  · exact (lower hp hx hv).cross

/--
info: 'Lean4Lean.SExpr.LR.DirectDefEqRect.toLegacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectDefEqRect.toLegacy

/--
info: 'Lean4Lean.SExpr.LRD.constLamDefEq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.constLamDefEq

/-- The final semantic application carried by the constant evaluator.  This
packages the raw final-Pi spine together with the *same* logical-relation
argument witness and Pi edge.  Keeping these fields in one dependent record
prevents the reached iota leaf from forgetting that the constructor major is
related at the domain used by the recursor application. -/
structure LR.PatternLeafSpine (Γ : List SExpr) (IH : LogRel Γ n)
    (Head : SExpr) (args args' : List SExpr) (rargs : List (WShape n))
    (A : SExpr) (out outTy : WShape n) where
  majorX : SExpr
  recXs : List SExpr
  majorY : SExpr
  recYs : List SExpr
  majorShape : WShape n
  recShapes : List (WShape n)
  majorTypeShape : WShape n
  resultShape : WShapeFun n
  resultTypeShape : WShapeFun n
  args_eq : args = majorX :: recXs
  args'_eq : args' = majorY :: recYs
  rargs_eq : rargs = majorShape :: recShapes
  out_eq : out = resultShape.app majorShape
  outTy_eq : outTy = resultTypeShape.app majorShape
  pair : SExpr.SpineWF.LastPair Γ Head recXs recYs majorX majorY A
  majorHasType : majorShape.HasType majorTypeShape
  resultType : WShape.HasTypePi resultTypeShape majorTypeShape true
  majorType : IH.TyDefEq pair.domain pair.domain majorTypeShape
  majorRel : IH.DefEq majorX majorY pair.domain majorShape majorTypeShape
  aligned : LRS.CtorSpineDefEq IH Head args args' rargs A
  pi : LRS.PiDefEq IH pair.domain pair.codomain pair.codomain
    majorTypeShape resultTypeShape

/-- Extend an aligned prefix to the next semantic application when its Pi
type is exposed by a heterogeneous path.  The prefix spines and constructor
alignment absorb the path via `SpineWF.snoc_path`/
`CtorSpineDefEq.cons_path`; the `LastPair` record uses the literal Pi
endpoint and its self-typing.  Thus no path collapse or `PiPathInv` premise
is needed at this evaluator step. -/
theorem LR.PatternLeafSpine.of_cons_path
    {Γ : List SExpr} {n : Nat} {IH : LogRel Γ n}
    {Head A B F x y : SExpr} {xs ys : List SExpr}
    {p a : WShape n} {ps : List (WShape n)}
    {g f : WShapeFun n} {u v : SLevel}
    (prefixX : SExpr.SpineWF Γ Head xs.reverse A)
    (prefixY : SExpr.SpineWF Γ Head ys.reverse A)
    (aligned : LRS.CtorSpineDefEq IH Head xs ys ps A)
    (path : TypeDefEqPath Γ A (.forallE B F) u)
    (hp : p.HasType a)
    (htpi : WShape.HasTypePi f a true)
    (hB : IH.TyDefEq B B a)
    (hxy : IsDefEq Γ x y B)
    (hrel : IH.DefEq x y B p a)
    (hresult : IsDefEq Γ (F.inst y) (F.inst x) (.sort v))
    (hPi : LRS.PiDefEq IH B F F a f) :
    Nonempty (LR.PatternLeafSpine Γ IH Head
      (x :: xs) (y :: ys) (p :: ps) (F.inst x) (g.app p) (f.app p)) := by
  obtain ⟨w, hPiTy⟩ := path.rightType
  exact ⟨{
    majorX := x
    recXs := xs
    majorY := y
    recYs := ys
    majorShape := p
    recShapes := ps
    majorTypeShape := a
    resultShape := g
    resultTypeShape := f
    args_eq := rfl
    args'_eq := rfl
    rargs_eq := rfl
    out_eq := rfl
    outTy_eq := rfl
    pair := {
      prefixType := .forallE B F
      domain := B
      codomain := F
      piSort := w
      resultSortX := v
      resultSortY := v
      prefixX := SpineWF.ret_path path prefixX
      prefixY := SpineWF.ret_path path prefixY
      pi := hPiTy
      major := hxy
      resultX := hresult.hasType.2
      resultY := hresult }
    majorHasType := hp
    resultType := htpi
    majorType := hB
    majorRel := hrel
    aligned := aligned.cons_path path hp hB hxy hrel hresult
    pi := hPi }⟩

/--
info: 'Lean4Lean.SExpr.LR.PatternLeafSpine.of_cons_path' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.PatternLeafSpine.of_cons_path
/-- Guarded relational evidence for a complete newest-first argument list.
Unlike `LRS.CtorArgsDefEq`, this finite payload needs no `LogRel` wrapper: it
uses exactly the type and term fields of the lower direct relation. -/
inductive LR.DirectCtorArgsDefEq (IH : LR.DirectRelBase Γ n) :
    List SExpr → List SExpr → List (WShape n) → Prop where
  | nil : DirectCtorArgsDefEq IH [] [] []
  | cons (hp : p.HasType a)
      (htyLegacy : (LR Γ).TyDefEq A A a)
      (htyDirect : IH.TyDefEq A A a)
      (hxy : IsDefEq Γ x y A)
      (hvLegacy : (LR Γ).DefEq x y A p a)
      (hvDirect : IH.DefEq x y A p a)
      (hrest : DirectCtorArgsDefEq IH xs ys ps) :
      DirectCtorArgsDefEq IH (x :: xs) (y :: ys) (p :: ps)

/-- Guarded argument evidence with every formerly hidden capture datum made
an explicit newest-first list index.

`DirectCtorArgsDefEq` deliberately hides the raw type expression and type
shape of each argument.  That is sufficient for ordinary iota congruence,
but a registered fixed-head producer must reuse the exact Pi domains that
generated its semantic type tower.  This refinement records those two lists
alongside the already-indexed syntax and element-shape lists. -/
inductive LR.DirectCtorArgsDefEqListed (IH : LR.DirectRelBase Γ n) :
    List SExpr → List SExpr → List SExpr →
      List (WShape n) → List (WShape n) → Prop where
  | nil : DirectCtorArgsDefEqListed IH [] [] [] [] []
  | cons (hp : p.HasType a)
      (htyLegacy : (LR Γ).TyDefEq A A a)
      (htyDirect : IH.TyDefEq A A a)
      (hxy : IsDefEq Γ x y A)
      (hvLegacy : (LR Γ).DefEq x y A p a)
      (hvDirect : IH.DefEq x y A p a)
      (hrest : DirectCtorArgsDefEqListed IH xs ys types ps typeShapes) :
      DirectCtorArgsDefEqListed IH
        (x :: xs) (y :: ys) (A :: types) (p :: ps) (a :: typeShapes)

/-- Forget the explicit capture-type lists while retaining the paired direct
argument relation. -/
theorem LR.DirectCtorArgsDefEqListed.toDirectArgs
    (H : LR.DirectCtorArgsDefEqListed IH xs ys types ps typeShapes) :
    LR.DirectCtorArgsDefEq IH xs ys ps := by
  induction H with
  | nil => exact .nil
  | cons hp htyLegacy htyDirect hxy hvLegacy hvDirect _ ih =>
    exact .cons hp htyLegacy htyDirect hxy hvLegacy hvDirect ih

/-- All five lists in an explicitly listed direct argument payload have the
same length. -/
theorem LR.DirectCtorArgsDefEqListed.lengths
    (H : LR.DirectCtorArgsDefEqListed IH xs ys types ps typeShapes) :
    xs.length = ps.length ∧ ys.length = ps.length ∧
      types.length = ps.length ∧ typeShapes.length = ps.length := by
  induction H with
  | nil => simp
  | cons _ _ _ _ _ _ _ ih =>
    simp only [List.length_cons, Nat.succ.injEq]
    exact ⟨ih.1, ih.2.1, ih.2.2.1, ih.2.2.2⟩

/-- Lift an explicitly listed direct constructor payload without reselecting
any of its proof-relevant element or type shapes. -/
theorem LR.DirectCtorArgsDefEqListed.lift
    {n n' : Nat} {xs ys types : List SExpr}
    {ps typeShapes : List (WShape n)} (le : n ≤ n')
    (H : LR.DirectCtorArgsDefEqListed
      (LRD Γ : LR.DirectRelBase Γ n)
      xs ys types ps typeShapes) :
    LR.DirectCtorArgsDefEqListed
      (LRD Γ : LR.DirectRelBase Γ n')
      xs ys types (ps.map (.lift n')) (typeShapes.map (.lift n')) := by
  induction H with
  | nil => exact .nil
  | cons hp htyLegacy htyDirect hxy hvLegacy hvDirect hrest ih =>
    simp only [List.map_cons]
    exact .cons
      ((WShape.HasType.lift le).2 hp)
      ((LR.TyDefEq.lift le hp.isType).2 htyLegacy)
      ((LRD.TyDefEq.lift le hp.isType).2 htyDirect)
      hxy
      ((LR.DefEq.lift le hp).2 hvLegacy)
      ((LRD.DefEq.lift le hp).2 hvDirect)
      ih

/-- Keep the left endpoint of every explicitly listed guarded argument
edge.  The capture types and both shape lists remain literally unchanged. -/
theorem LR.DirectCtorArgsDefEqListed.left
    (H : LR.DirectCtorArgsDefEqListed (LRD Γ)
      xs ys types ps typeShapes) :
    LR.DirectCtorArgsDefEqListed (LRD Γ)
      xs xs types ps typeShapes := by
  induction H with
  | nil => exact .nil
  | cons hp htyLegacy htyDirect hxy hvLegacy hvDirect _ ih =>
    exact .cons hp htyLegacy htyDirect hxy.hasType.1
      ((LR Γ).left hvLegacy) (LRD.DefEq.left hvDirect) ih

/-- Keep the right endpoint of every explicitly listed guarded argument
edge.  The capture types and both shape lists remain literally unchanged. -/
theorem LR.DirectCtorArgsDefEqListed.right
    (H : LR.DirectCtorArgsDefEqListed (LRD Γ)
      xs ys types ps typeShapes) :
    LR.DirectCtorArgsDefEqListed (LRD Γ)
      ys ys types ps typeShapes := by
  induction H with
  | nil => exact .nil
  | cons hp htyLegacy htyDirect hxy hvLegacy hvDirect _ ih =>
    exact .cons hp htyLegacy htyDirect hxy.hasType.2
      ((LR Γ).left ((LR Γ).symm hvLegacy))
      (LRD.DefEq.left (LRD.DefEq.symm hvDirect)) ih

/-- The three newest-first lists retained by a direct argument bundle have
the same length. -/
theorem LR.DirectCtorArgsDefEq.lengths
    (H : LR.DirectCtorArgsDefEq IH xs ys ps) :
    xs.length = ps.length ∧ ys.length = ps.length := by
  induction H with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ _ _ _ _ ih =>
    exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

/-- Drop the newest paired direct argument. -/
theorem LR.DirectCtorArgsDefEq.tail
    (H : LR.DirectCtorArgsDefEq IH (x :: xs) (y :: ys) (p :: ps)) :
    LR.DirectCtorArgsDefEq IH xs ys ps := by
  cases H with
  | cons _ _ _ _ _ _ hrest => exact hrest

/-- Keep the left endpoint of every guarded argument edge. -/
theorem LR.DirectCtorArgsDefEq.left
    (H : LR.DirectCtorArgsDefEq (LRD Γ) xs ys ps) :
    LR.DirectCtorArgsDefEq (LRD Γ) xs xs ps := by
  induction H with
  | nil => exact .nil
  | cons hp htyLegacy htyDirect hxy hvLegacy hvDirect _ ih =>
    exact .cons hp htyLegacy htyDirect hxy.hasType.1
      ((LR Γ).left hvLegacy) (LRD.DefEq.left hvDirect) ih

/-- Keep the right endpoint of every guarded argument edge. -/
theorem LR.DirectCtorArgsDefEq.right
    (H : LR.DirectCtorArgsDefEq (LRD Γ) xs ys ps) :
    LR.DirectCtorArgsDefEq (LRD Γ) ys ys ps := by
  induction H with
  | nil => exact .nil
  | cons hp htyLegacy htyDirect hxy hvLegacy hvDirect _ ih =>
    exact .cons hp htyLegacy htyDirect hxy.hasType.2
      ((LR Γ).left ((LR Γ).symm hvLegacy))
      (LRD.DefEq.left (LRD.DefEq.symm hvDirect)) ih

/-- Keep the related newest argument while using the left tail at both
endpoints.  This is the direct recursor-prefix projection used by the left
row of a synchronized iota rectangle. -/
theorem LR.DirectCtorArgsDefEq.leftPrefixes
    (H : LR.DirectCtorArgsDefEq (LRD Γ)
      (x :: xs) (y :: ys) (p :: ps)) :
    LR.DirectCtorArgsDefEq (LRD Γ)
      (x :: xs) (y :: xs) (p :: ps) := by
  cases H with
  | cons hp htyLegacy htyDirect hxy hvLegacy hvDirect hrest =>
    exact .cons hp htyLegacy htyDirect hxy hvLegacy hvDirect hrest.left

/-- Keep the related newest argument while using the right tail at both
endpoints.  This is the direct recursor-prefix projection used by the right
row of a synchronized iota rectangle. -/
theorem LR.DirectCtorArgsDefEq.rightPrefixes
    (H : LR.DirectCtorArgsDefEq (LRD Γ)
      (x :: xs) (y :: ys) (p :: ps)) :
    LR.DirectCtorArgsDefEq (LRD Γ)
      (x :: ys) (y :: ys) (p :: ps) := by
  cases H with
  | cons hp htyLegacy htyDirect hxy hvLegacy hvDirect hrest =>
    exact .cons hp htyLegacy htyDirect hxy hvLegacy hvDirect hrest.right

/-- One captured argument with legacy and direct evidence sharing the exact
same syntax, shape, and raw type. -/
def LR.DirectCaptureDefEqAt (IH : LR.DirectRelBase Γ n)
    (m : TShape) (x y : SExpr) : Prop :=
  ∃ (elemShape typeShape : WShape n) (typeExpr : SExpr),
    m ≤ elemShape.T ∧ elemShape.HasType typeShape ∧
    (LR Γ).TyDefEq typeExpr typeExpr typeShape ∧
    IH.TyDefEq typeExpr typeExpr typeShape ∧
    IsDefEq Γ x y typeExpr ∧
    (LR Γ).DefEq x y typeExpr elemShape typeShape ∧
    IH.DefEq x y typeExpr elemShape typeShape

/-- Data chosen once from a paired direct capture.  The legacy and guarded
projections retain the same literal type expression and semantic shapes. -/
structure LR.DirectCaptureDefEqAt.Witness
    (IH : LR.DirectRelBase Γ n) (m : TShape) (x y : SExpr) where
  elemShape : WShape n
  typeShape : WShape n
  typeExpr : SExpr
  shape : m ≤ elemShape.T
  hasType : elemShape.HasType typeShape
  typeRelatedLegacy : (LR Γ).TyDefEq typeExpr typeExpr typeShape
  typeRelatedDirect : IH.TyDefEq typeExpr typeExpr typeShape
  defeq : IsDefEq Γ x y typeExpr
  relatedLegacy : (LR Γ).DefEq x y typeExpr elemShape typeShape
  relatedDirect : IH.DefEq x y typeExpr elemShape typeShape

/-- Select the evidence-rich representative of one paired direct capture. -/
noncomputable def LR.DirectCaptureDefEqAt.witness
    (H : LR.DirectCaptureDefEqAt IH m x y) :
    LR.DirectCaptureDefEqAt.Witness IH m x y :=
  Classical.choice (by
    rcases H with ⟨elemShape, typeShape, typeExpr, hshape, htype,
      htyLegacy, htyDirect, hxy, hvLegacy, hvDirect⟩
    exact ⟨⟨elemShape, typeShape, typeExpr, hshape, htype,
      htyLegacy, htyDirect, hxy, hvLegacy, hvDirect⟩⟩)

/-- Paired direct capture evidence aligned to the type chosen by the
surrounding dependent application spine. -/
def LR.DirectCaptureDefEqAligned (IH : LR.DirectRelBase Γ n)
    (m : TShape) (x y typeExpr : SExpr) : Prop :=
  ∃ (elemShape typeShape : WShape n),
    m ≤ elemShape.T ∧ elemShape.HasType typeShape ∧
    (LR Γ).TyDefEq typeExpr typeExpr typeShape ∧
    IH.TyDefEq typeExpr typeExpr typeShape ∧
    IsDefEq Γ x y typeExpr ∧
    (LR Γ).DefEq x y typeExpr elemShape typeShape ∧
    IH.DefEq x y typeExpr elemShape typeShape

/-- Repackage a chosen direct capture at its exact selected type. -/
theorem LR.DirectCaptureDefEqAt.Witness.aligned
    (H : LR.DirectCaptureDefEqAt.Witness IH m x y) :
    LR.DirectCaptureDefEqAligned IH m x y H.typeExpr :=
  ⟨H.elemShape, H.typeShape, H.shape, H.hasType,
    H.typeRelatedLegacy, H.typeRelatedDirect, H.defeq,
    H.relatedLegacy, H.relatedDirect⟩

/-- The fields of a paired guarded capture at one literal element/type
shape pair.  Keeping both projections here lets legacy consumers erase the
payload while guarded application reuses the very same semantic indices. -/
def LR.DirectCaptureDefEqAligned.AtShapes
    (IH : LR.DirectRelBase Γ n) (m : TShape)
    (x y typeExpr : SExpr) (elemShape typeShape : WShape n) : Prop :=
  m ≤ elemShape.T ∧ elemShape.HasType typeShape ∧
    (LR Γ).TyDefEq typeExpr typeExpr typeShape ∧
    IH.TyDefEq typeExpr typeExpr typeShape ∧
    IsDefEq Γ x y typeExpr ∧
    (LR Γ).DefEq x y typeExpr elemShape typeShape ∧
    IH.DefEq x y typeExpr elemShape typeShape

/-- Evidence-rich representative of a paired guarded capture aligned to the
dependent spine's selected type expression. -/
structure LR.DirectCaptureDefEqAligned.Witness
    (IH : LR.DirectRelBase Γ n) (m : TShape)
    (x y typeExpr : SExpr) where
  elemShape : WShape n
  typeShape : WShape n
  shape : m ≤ elemShape.T
  hasType : elemShape.HasType typeShape
  typeRelatedLegacy : (LR Γ).TyDefEq typeExpr typeExpr typeShape
  typeRelatedDirect : IH.TyDefEq typeExpr typeExpr typeShape
  defeq : IsDefEq Γ x y typeExpr
  relatedLegacy : (LR Γ).DefEq x y typeExpr elemShape typeShape
  relatedDirect : IH.DefEq x y typeExpr elemShape typeShape

/-- Choose the synchronized shape pair of one aligned guarded capture once. -/
noncomputable def LR.DirectCaptureDefEqAligned.witness
    (H : LR.DirectCaptureDefEqAligned IH m x y typeExpr) :
    LR.DirectCaptureDefEqAligned.Witness IH m x y typeExpr :=
  Classical.choice (by
    rcases H with ⟨elemShape, typeShape, hshape, htype,
      htyLegacy, htyDirect, hxy, hvLegacy, hvDirect⟩
    exact ⟨⟨elemShape, typeShape, hshape, htype,
      htyLegacy, htyDirect, hxy, hvLegacy, hvDirect⟩⟩)

/-- Expose every paired field at the witness's literal shape indices. -/
theorem LR.DirectCaptureDefEqAligned.Witness.atShapes
    (H : LR.DirectCaptureDefEqAligned.Witness IH m x y typeExpr) :
    LR.DirectCaptureDefEqAligned.AtShapes IH m x y typeExpr
      H.elemShape H.typeShape :=
  ⟨H.shape, H.hasType, H.typeRelatedLegacy, H.typeRelatedDirect,
    H.defeq, H.relatedLegacy, H.relatedDirect⟩

/-- Lift a literally chosen paired direct capture without reselecting either
shape.  Both the legacy projection and the guarded relation are transported
along their canonical lift equivalences. -/
theorem LR.DirectCaptureDefEqAligned.AtShapes.lift
    {m : TShape} {x y A : SExpr} {elemShape typeShape : WShape n}
    (le : n ≤ n')
    (H : LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
      m x y A elemShape typeShape) :
    LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
      m x y A (elemShape.lift n') (typeShape.lift n') := by
  exact ⟨H.1.trans (TShape.lift_eqv le).2,
    (WShape.HasType.lift le).2 H.2.1,
    (LR.TyDefEq.lift le H.2.1.isType).2 H.2.2.1,
    (LRD.TyDefEq.lift le H.2.1.isType).2 H.2.2.2.1,
    H.2.2.2.2.1,
    (LR.DefEq.lift le H.2.1).2 H.2.2.2.2.2.1,
    (LRD.DefEq.lift le H.2.1).2 H.2.2.2.2.2.2⟩

/-- A paired direct capture at an existential canonical shape level. -/
def LR.DirectCaptureDefEqAligned.AtSomeLevel (Γ : List SExpr)
    (m : TShape) (x y typeExpr : SExpr) : Prop :=
  ∃ (n : Nat) (elemShape typeShape : WShape n),
    LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
      m x y typeExpr elemShape typeShape

/-- Package an aligned guarded capture at its existing level. -/
theorem LR.DirectCaptureDefEqAligned.atSomeLevel
    (H : LR.DirectCaptureDefEqAligned (LRD Γ : LR.DirectRelBase Γ n)
      m x y typeExpr) :
    LR.DirectCaptureDefEqAligned.AtSomeLevel Γ m x y typeExpr := by
  rcases H with ⟨elemShape, typeShape, hshape, htyped,
    htypeLegacy, htypeDirect, hraw, hrelLegacy, hrelDirect⟩
  exact ⟨n, elemShape, typeShape, hshape, htyped,
    htypeLegacy, htypeDirect, hraw, hrelLegacy, hrelDirect⟩

omit [Params.Semantic] in
/-- The two guarded fields missing from one legacy aligned capture, at the
exact shapes already selected by that proof-relevant capture witness. -/
structure LR.DirectCaptureDefEqAligned.Upgrade
    {n : Nat} {Γ : List SExpr} {m : TShape} {x y A : SExpr}
    (H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ n) m x y A) : Prop where
  typeRelatedDirect : (LRD Γ).TyDefEq A A H.witness.typeShape
  relatedDirect : (LRD Γ).DefEq x y A
    H.witness.elemShape H.witness.typeShape

omit [Params.Semantic] in
/-- Pair an exact guarded upgrade with its legacy witness and expose the
combined capture at an existential canonical level. -/
theorem LR.DirectCaptureDefEqAligned.Upgrade.atSomeLevel
    {n : Nat} {Γ : List SExpr} {m : TShape} {x y A : SExpr}
    {H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ n) m x y A}
    (U : LR.DirectCaptureDefEqAligned.Upgrade H) :
    LR.DirectCaptureDefEqAligned.AtSomeLevel Γ m x y A := by
  let W := H.witness
  exact ⟨n, W.elemShape, W.typeShape, W.shape, W.hasType,
    W.typeRelated, U.typeRelatedDirect, W.defeq,
    W.related, U.relatedDirect⟩

omit [Params.Semantic] in
/-- A bottom displayed-type observation has no guarded sidecar.  Its element
shape is forced to bottom by the retained typing witness. -/
theorem LR.DirectCaptureDefEqAligned.Upgrade.of_typeShape_bot
    {n : Nat} {Γ : List SExpr} {m : TShape} {x y A : SExpr}
    {H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ n) m x y A}
    (hbot : H.witness.typeShape = (.bot : WShape n)) :
    LR.DirectCaptureDefEqAligned.Upgrade H := by
  let W := H.witness
  have htyped : W.elemShape.HasType (.bot : WShape n) := by
    rw [← hbot]
    exact W.hasType
  have helem : W.elemShape = (.bot : WShape n) := htyped.bot_r
  refine ⟨?_, ?_⟩
  · simpa only [W, hbot] using
      (LRD.TyDefEq.bot (Γ := Γ) (A := A) (B := A) (n := n))
  · simpa only [W, hbot, helem] using
      (LRD.DefEq.bot (Γ := Γ) (M := x) (N := y) (A := A)
        htyped.isType)

omit [Params.Semantic] in
/-- At an inductive displayed type both guarded fields are exactly their
legacy projections, so the upgrade adds no semantic premise. -/
theorem LR.DirectCaptureDefEqAligned.Upgrade.of_typeShape_indTy
    {n : Nat} {Γ : List SExpr} {m : TShape} {x y A : SExpr}
    {H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ (n + 1)) m x y A}
    (hind : H.witness.typeShape = (.indTy : WShape (n + 1))) :
    LR.DirectCaptureDefEqAligned.Upgrade H := by
  let W := H.witness
  have htype : (LR Γ).TyDefEq A A (.indTy : WShape (n + 1)) := by
    simpa only [W, hind] using W.typeRelated
  have hterm : (LR Γ).DefEq x y A W.elemShape
      (.indTy : WShape (n + 1)) := by
    simpa only [W, hind] using W.related
  refine ⟨?_, ?_⟩
  · simpa only [W, hind] using LRD.TyDefEq.of_legacy_indTy htype
  · simpa only [W, hind] using LRD.DefEq.of_legacy_indTy hterm

/-- A capture whose raw and legacy typing remain aligned, while only its
term relation is required in the guarded tower.  The guarded domain type is
reconstructed later from the actual Pi edge of `PathSpineWF`. -/
def LR.DirectTermCaptureDefEqAligned.AtShapes
    (IH : LR.DirectRelBase Γ n) (m : TShape)
    (x y typeExpr : SExpr) (elemShape typeShape : WShape n) : Prop :=
  m ≤ elemShape.T ∧ elemShape.HasType typeShape ∧
    (LR Γ).TyDefEq typeExpr typeExpr typeShape ∧
    IsDefEq Γ x y typeExpr ∧
    (LR Γ).DefEq x y typeExpr elemShape typeShape ∧
    IH.DefEq x y typeExpr elemShape typeShape

/-- A term-guarded capture at an existential canonical shape level. -/
def LR.DirectTermCaptureDefEqAligned.AtSomeLevel (Γ : List SExpr)
    (m : TShape) (x y typeExpr : SExpr) : Prop :=
  ∃ (n : Nat) (elemShape typeShape : WShape n),
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      m x y typeExpr elemShape typeShape

/-- Forget only the precomputed direct type sidecar of a fully paired
capture. -/
theorem LR.DirectCaptureDefEqAligned.AtShapes.toTerm
    (H : LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
      m x y A elemShape typeShape) :
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
  m x y A elemShape typeShape :=
  ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.2.1,
    H.2.2.2.2.2.1, H.2.2.2.2.2.2⟩

/-- Forget a fully paired existential capture to the term-guarded payload. -/
theorem LR.DirectCaptureDefEqAligned.AtSomeLevel.toTerm
    (H : LR.DirectCaptureDefEqAligned.AtSomeLevel Γ m x y A) :
    LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ m x y A := by
  rcases H with ⟨n, elemShape, typeShape, hcapture⟩
  exact ⟨n, elemShape, typeShape, hcapture.toTerm⟩

omit [Params.Semantic] in
/-- The single guarded field missing from one legacy aligned capture, at
the exact shapes already selected by its proof-relevant witness. -/
structure LR.DirectTermCaptureDefEqAligned.Upgrade
    {n : Nat} {Γ : List SExpr} {m : TShape} {x y A : SExpr}
    (H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ n) m x y A) : Prop where
  relatedDirect : (LRD Γ).DefEq x y A
    H.witness.elemShape H.witness.typeShape

omit [Params.Semantic] in
/-- Combine the legacy witness with its exact guarded term relation. -/
theorem LR.DirectTermCaptureDefEqAligned.Upgrade.atSomeLevel
    {n : Nat} {Γ : List SExpr} {m : TShape} {x y A : SExpr}
    {H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ n) m x y A}
    (U : LR.DirectTermCaptureDefEqAligned.Upgrade H) :
    LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ m x y A := by
  let W := H.witness
  exact ⟨n, W.elemShape, W.typeShape, W.shape, W.hasType,
    W.typeRelated, W.defeq, W.related, U.relatedDirect⟩

omit [Params.Semantic] in
/-- A full guarded upgrade contains the weaker term-only upgrade. -/
theorem LR.DirectCaptureDefEqAligned.Upgrade.toTerm
    {n : Nat} {Γ : List SExpr} {m : TShape} {x y A : SExpr}
    {H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ n) m x y A}
    (U : LR.DirectCaptureDefEqAligned.Upgrade H) :
    LR.DirectTermCaptureDefEqAligned.Upgrade H :=
  ⟨U.relatedDirect⟩

omit [Params.Semantic] in
/-- Bottom displayed types also close the weaker term-only upgrade. -/
theorem LR.DirectTermCaptureDefEqAligned.Upgrade.of_typeShape_bot
    {n : Nat} {Γ : List SExpr} {m : TShape} {x y A : SExpr}
    {H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ n) m x y A}
    (hbot : H.witness.typeShape = (.bot : WShape n)) :
    LR.DirectTermCaptureDefEqAligned.Upgrade H :=
  (LR.DirectCaptureDefEqAligned.Upgrade.of_typeShape_bot hbot).toTerm

omit [Params.Semantic] in
/-- A bottom element observation needs no information about its displayed
type beyond the retained fact that the latter is itself a type. -/
theorem LR.DirectTermCaptureDefEqAligned.Upgrade.of_elemShape_bot
    {n : Nat} {Γ : List SExpr} {m : TShape} {x y A : SExpr}
    {H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ n) m x y A}
    (hbot : H.witness.elemShape = (.bot : WShape n)) :
    LR.DirectTermCaptureDefEqAligned.Upgrade H := by
  refine ⟨?_⟩
  rw [hbot]
  exact LRD.DefEq.bot H.witness.hasType.isType

omit [Params.Semantic] in
/-- Inductive displayed types also close the weaker term-only upgrade. -/
theorem LR.DirectTermCaptureDefEqAligned.Upgrade.of_typeShape_indTy
    {n : Nat} {Γ : List SExpr} {m : TShape} {x y A : SExpr}
    {H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ (n + 1)) m x y A}
    (hind : H.witness.typeShape = (.indTy : WShape (n + 1))) :
    LR.DirectTermCaptureDefEqAligned.Upgrade H :=
  (LR.DirectCaptureDefEqAligned.Upgrade.of_typeShape_indTy hind).toTerm

/-- Lift a term-guarded capture while preserving its literal shape pair. -/
theorem LR.DirectTermCaptureDefEqAligned.AtShapes.lift
    {m : TShape} {x y A : SExpr} {elemShape typeShape : WShape n}
    (le : n ≤ n')
    (H : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      m x y A elemShape typeShape) :
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      m x y A (elemShape.lift n') (typeShape.lift n') := by
  exact ⟨H.1.trans (TShape.lift_eqv le).2,
    (WShape.HasType.lift le).2 H.2.1,
    (LR.TyDefEq.lift le H.2.1.isType).2 H.2.2.1,
    H.2.2.2.1,
    (LR.DefEq.lift le H.2.1).2 H.2.2.2.2.1,
    (LRD.DefEq.lift le H.2.1).2 H.2.2.2.2.2⟩

/-- The syntax-independent shape ladder for one guarded fixed-head
application spine.

Each application layer retains a paired legacy/direct capture at the exact
element and type shapes used by the ladder.  `liftHead` raises only the
current head observation, allowing semantic layers, recursive tails, and
captures born at different finite levels to meet at a common maximum without
projecting any guarded observation downward. -/
inductive LR.DirectFixedHeadShapeChain (Γ : List SExpr)
    {p : Pattern} (mcap : p.Path → TShape)
    (mx my captureType : p.Path → SExpr) :
    ∀ (paths : List p.Path)
      {headLevel : Nat}, WShape headLevel → WShape headLevel →
      ∀ {outLevel : Nat}, WShape outLevel → WShape outLevel → Prop where
  | nil {n : Nat} {out outTy : WShape n} :
      LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        [] out outTy out outTy
  | cons
      {n : Nat} {path : p.Path} {paths : List p.Path}
      {termFun typeFun : WShapeFun n} {hterm : termFun.NonZero}
      {argCap tyDom : WShape n}
      {outLevel : Nat} {out outTy : WShape outLevel}
      (capture : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
        (mcap path) (mx path) (my path) (captureType path)
        argCap tyDom)
      (tail : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        paths (termFun.app argCap) (typeFun.app argCap) out outTy) :
      LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        (path :: paths) (.lam termFun hterm) (.forallE tyDom typeFun)
        out outTy
  | liftHead
      {n n' : Nat} {head headTy : WShape n}
      {paths : List p.Path} {outLevel : Nat}
      {out outTy : WShape outLevel}
      (le : n ≤ n') (htyped : head.HasType headTy)
      (tail : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        paths head headTy out outTy) :
      LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        paths (head.lift n') (headTy.lift n') out outTy

/-- A monotone fixed-head telescope whose capture payload already contains
the guarded term edge at the literal element/type shapes selected by each
layer.  Unlike the existential shape-chain constructor below, this package
also retains the registered head-type observation threaded by the ordered
type peel. -/
def LR.DirectFixedHeadTelescopeLE (Γ : List SExpr)
    {p : Pattern} {mcap : p.Path → TShape}
    (mx my captureType : p.Path → SExpr)
    {head out headTy outTy : TShape} {paths : List p.Path}
    (_spine : LE_Interp.RHS.ShapeSpine mcap head paths out) : Prop :=
  LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
    (m2 := mcap)
    (fun {n} path (elemShape typeShape : WShape n) =>
      LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
        (mcap path) (mx path) (my path) (captureType path)
        elemShape typeShape)
    head paths out headTy outTy

omit [Params.Semantic] in
/-- Empty guarded monotone telescope at the caller's terminal observation. -/
theorem LR.DirectFixedHeadTelescopeLE.nil
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr} {head headTy outTy : TShape}
    (htyped : head.HasType outTy) (hle : outTy ≤ headTy) :
    LR.DirectFixedHeadTelescopeLE
      (headTy := headTy) (outTy := outTy)
      Γ mx my captureType
      (LE_Interp.RHS.ShapeSpine.nil (m2 := mcap) (head := head)) :=
  LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.nil htyped hle

omit [Params.Semantic] in
/-- Prepend one guarded capture layer to a monotone direct telescope.  The
semantic argument bound, typed domain, legacy relation, and guarded term edge
are all read from the same literal capture payload. -/
theorem LR.DirectFixedHeadTelescopeLE.cons
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {n : Nat} {f : WShape (n + 1)} {a : WShape n}
    {m out : TShape} {path : p.Path} {paths : List p.Path}
    (harg : a.T ≤ mcap path) (happ : m ≤ (f.app a).T)
    (rest : LE_Interp.RHS.ShapeSpine mcap m paths out)
    {tyDom : WShape n} {tyFun : WShapeFun n} {argCap : WShape n}
    {outTy : TShape}
    (capture : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mcap path) (mx path) (my path) (captureType path)
      argCap tyDom)
    (tail : LR.DirectFixedHeadTelescopeLE
      (headTy := (tyFun.app argCap).T) (outTy := outTy)
      Γ mx my captureType rest) :
    LR.DirectFixedHeadTelescopeLE
      (headTy := (WShape.forallE tyDom tyFun).T) (outTy := outTy)
      Γ mx my captureType
      (LE_Interp.RHS.ShapeSpine.cons harg happ rest) := by
  have hargCap : a ≤ argCap :=
    WShape.LE.T_iff.1 (harg.trans capture.1)
  exact LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.cons
    harg happ hargCap capture.2.1 capture tail

/-- Fold a guarded monotone telescope into a direct fixed-head chain while
preserving the comparison from the chain's selected head-type shape to the
registered head-type observation.

The proof is the guarded payload specialization of the ordinary monotone
telescope fold.  In particular, the terminal comparison is threaded through
the same recursive choices as every direct capture; no head or capture
representative is selected a second time. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.directFixedHeadShapeChain
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {outShape outTyShape : TShape}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
      (m2 := mcap)
      (fun {n} path (elemShape typeShape : WShape n) =>
        LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
          (mcap path) (mx path) (my path) (captureType path)
          elemShape typeShape)
      head paths outShape headTy outTyShape)
    (houtShapeEq : out.T = outShape)
    (houtTyShapeEq : outTy.T = outTyShape)
    (houtNonbot : ¬out.T ≤ TShape.bot) :
    ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
      headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
        headElemTy.T ≤ headTy ∧ ¬headElem.T ≤ TShape.bot ∧
        LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
          paths headElem headElemTy out outTy := by
  revert out outTy
  revert outLevel
  let Motive := fun (head : TShape) (paths : List p.Path)
      (outShape headTy outTyShape : TShape)
      (_ : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
        (m2 := mcap)
        (fun {n} path (elemShape typeShape : WShape n) =>
          LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
            (mcap path) (mx path) (my path) (captureType path)
            elemShape typeShape)
        head paths outShape headTy outTyShape) =>
      ∀ (outLevel : Nat) (out outTy : WShape outLevel),
        out.T = outShape → outTy.T = outTyShape →
        (¬out.T ≤ TShape.bot) →
        ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
          headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
            headElemTy.T ≤ headTy ∧ ¬headElem.T ≤ TShape.bot ∧
            LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
              paths headElem headElemTy out outTy
  change Motive head paths outShape headTy outTyShape H
  refine LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.rec
    (motive := Motive) ?_ ?_ H
  · intro head headTy terminalTy htyped hle
    intro outLevel out outTy houtShapeEq houtTyShapeEq houtNonbot
    have houtLe : out.T ≤ head := by
      rw [houtShapeEq]
      exact TShape.LE.rfl
    have houtTyLe : outTy.T ≤ headTy := by
      rw [houtTyShapeEq]
      exact hle
    have houtTyped : out.HasType outTy := by
      apply WShape.HasType.T_iff.1
      rw [houtShapeEq, houtTyShapeEq]
      exact htyped
    exact ⟨outLevel, out, outTy, houtLe, houtTyped, houtTyLe,
      houtNonbot, LR.DirectFixedHeadShapeChain.nil⟩
  · intro n f a m outT path paths tyDom tyFun argCap outTyT
      harg happ hargCap hcapDom capture tail ih
    intro outLevel out outTy houtShapeEq houtTyShapeEq houtNonbot
    obtain ⟨nextLevel, next, nextTy, hnext, hnextTy,
      hnextTyLe, hnextNonbot, tailChain⟩ :=
      ih outLevel out outTy houtShapeEq houtTyShapeEq houtNonbot
    have hnextApp : next.T ≤ (f.app a).T := hnext.trans happ
    cases f using WShape.casesOn' with
    | bot => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | sort => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | forallE => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | ctor => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | indTy => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | @lam g hg =>
      let k := max n nextLevel
      have hk : n ≤ k ∧ nextLevel ≤ k := by
        dsimp [k]
        omega
      let aK : WShape k := a.lift k
      let argCapK : WShape k := argCap.lift k
      let tyDomK : WShape k := tyDom.lift k
      let nextK : WShape k := next.lift k
      let nextTyK : WShape k := nextTy.lift k
      let elemFun : WShapeFun k := .single argCapK nextK
      let typeFun : WShapeFun k := .single argCapK nextTyK
      have hargCapK : aK ≤ argCapK :=
        WShape.lift_mono hk.1 hargCap
      have hnextAppK : nextK ≤ (g.lift k).app argCapK := by
        have hnextApp' : next.T ≤ ((WShape.lam g hg).app a).T := by
          simpa using hnextApp
        have hmono : ((WShape.lam g hg).app a).T ≤
            ((WShape.lam (g.lift k)
              (WShapeFun.NonZero.lift_iff hk.1 |>.2 hg)).app argCapK).T := by
          apply TShape.app_mono
          · have hLift := (TShape.lift_eqv
              (a := (WShape.lam g hg).T)
              (Nat.succ_le_succ hk.1)).2
            rw [WShape.lift_lam hk.1] at hLift
            exact hLift
          · exact hargCap.T.trans (TShape.lift_eqv hk.1).2
        have hT : next.T ≤ ((g.lift k).app argCapK).T := by
          simpa [WShape.lam_eq_lam'] using hnextApp'.trans hmono
        have hTK := (TShape.LE.def hk.2 (Nat.le_refl k)).1 hT
        simpa only [nextK, WShape.lift_self] using hTK
      have hnextTyKLe : nextTyK ≤ (tyFun.lift k).app argCapK := by
        have hTK := (TShape.LE.def
          (a := nextTy.T) (b := (tyFun.app argCap).T)
          hk.2 hk.1).1 hnextTyLe
        simpa only [nextTyK, argCapK, WShape.lift_self,
          WShapeFun.lift_app hk.1] using hTK
      have hnextKTy : nextK.HasType nextTyK :=
        (WShape.HasType.lift hk.2).2 hnextTy
      have hnextKNonbot : ¬nextK.T ≤ TShape.bot := by
        intro hbot
        exact hnextNonbot <|
          (TShape.lift_eqv hk.2).2.trans
            (hbot.trans TShape.bot_eqv.1)
      have helemNonzero : elemFun.NonZero := by
        rw [WShapeFun.NonZero.iff]
        refine ⟨(argCapK, nextK),
          WShapeFun.mem_single.2 (.inl rfl), ?_⟩
        intro hbot
        exact hnextKNonbot <|
          (WShape.LE.T hbot).trans TShape.bot_eqv.1
      let headElem : WShape (k + 1) := .lam elemFun helemNonzero
      let headElemTy : WShape (k + 1) := .forallE tyDomK typeFun
      have hcaptureK : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
          (mcap path) (mx path) (my path) (captureType path)
          argCapK tyDomK := by
        exact capture.lift hk.1
      have hheadTyped : headElem.HasType headElemTy := by
        change (WShape.lam elemFun helemNonzero).HasType
          (WShape.forallE tyDomK typeFun)
        rw [WShape.lam_eq_lam']
        apply WShape.HasType.lam
        refine WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
        · refine WShape.HasTypePi.def.2
            ⟨WShape.HasDom.single.2 (.inl hcaptureK.2.1), ?_⟩
          intro x y hxy
          obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ :=
            WShapeFun.mem_single.1 hxy
          · exact hnextKTy.isType
          · exact .bot' .sort
        · exact WShape.HasDom.single.2 (.inl hcaptureK.2.1)
        · simp only [elemFun, typeFun, WShapeFun.single_app]
          split <;> [exact hnextKTy; exact .bot' (.bot' .sort)]
      have hheadLeK : headElem ≤ .lam' (g.lift k) := by
        change WShape.lam elemFun helemNonzero ≤ .lam' (g.lift k)
        rw [WShape.lam_eq_lam']
        apply WShape.lam'_le_lam'.2
        obtain ⟨x', hx', hmem⟩ := (g.lift k).app_eq argCapK
        exact WShapeFun.single_le.2
          ⟨x', _, hmem, hx', hnextAppK⟩
      have hliftHead : (WShape.lam' (g.lift k)).T ≤
          (WShape.lam g hg).T := by
        have hLift := (TShape.lift_eqv
          (a := (WShape.lam g hg).T)
          (Nat.succ_le_succ hk.1)).1
        rw [WShape.lift_lam hk.1, WShape.lam_eq_lam'] at hLift
        exact hLift
      have hheadLe : headElem.T ≤ (WShape.lam g hg).T :=
        hheadLeK.T.trans hliftHead
      have htypeFunLe : typeFun ≤ tyFun.lift k := by
        obtain ⟨x', hx', hmem⟩ := (tyFun.lift k).app_eq argCapK
        exact WShapeFun.single_le.2
          ⟨x', _, hmem, hx', hnextTyKLe⟩
      have hheadTyLeK : headElemTy ≤
          .forallE tyDomK (tyFun.lift k) := by
        exact WShape.forallE_le_forallE.2 ⟨.rfl, htypeFunLe⟩
      have hliftHeadTy : (WShape.forallE tyDomK (tyFun.lift k)).T ≤
          (WShape.forallE tyDom tyFun).T := by
        have hLift := (TShape.lift_eqv
          (a := (WShape.forallE tyDom tyFun).T)
          (Nat.succ_le_succ hk.1)).1
        rw [WShape.lift_forallE hk.1] at hLift
        exact hLift
      have hheadTyLe : headElemTy.T ≤
          (WShape.forallE tyDom tyFun).T :=
        hheadTyLeK.T.trans hliftHeadTy
      have tailK : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
          paths nextK nextTyK out outTy :=
        LR.DirectFixedHeadShapeChain.liftHead hk.2 hnextTy tailChain
      have tailApp : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
          paths (elemFun.app argCapK) (typeFun.app argCapK)
            out outTy := by
        simpa only [elemFun, typeFun, WShapeFun.single_app,
          WShape.LE.rfl, ↓reduceIte] using tailK
      have chain : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
          (path :: paths) headElem headElemTy out outTy := by
        exact LR.DirectFixedHeadShapeChain.cons hcaptureK tailApp
      exact ⟨k + 1, headElem, headElemTy, hheadLe,
        hheadTyped, hheadTyLe, by
          intro hbot
          have happBotSame : (headElem.app argCapK).T ≤
              ((WShape.bot (n := k + 1)).app argCapK).T :=
            TShape.app_mono
              (hbot.trans (TShape.bot_eqv (n := k + 1)).2)
              TShape.LE.rfl
          rw [WShape.bot_app] at happBotSame
          have happBot : (headElem.app argCapK).T ≤ TShape.bot :=
            happBotSame.trans TShape.bot_eqv.1
          apply hnextKNonbot
          simpa only [headElem, WShape.lam_eq_lam', WShape.lam'_app,
            elemFun, WShapeFun.single_app, WShape.LE.rfl, ↓reduceIte]
            using happBot,
        chain⟩

/-- Add the registered syntax witness to the guarded telescope's literal
lower endpoint.  The witness is weakened only along the head-type comparison
returned by the same fold that builds the direct application chain. -/
theorem LR.DirectFixedHeadTelescopeLE.withWitnessAndChain
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    (H : LR.DirectFixedHeadTelescopeLE
      (headTy := headTy) (outTy := outTy.T)
      Γ mx my captureType spine)
    (hTy : LE_Interp.Witness ρ headTy B)
    (houtNonbot : ¬out.T ≤ TShape.bot) :
    ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
      headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
        Nonempty (LE_Interp.Witness ρ headElemTy.T B) ∧
        LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
          paths headElem headElemTy out outTy := by
  obtain ⟨headLevel, headElem, headElemTy, hhead, htyped,
    hheadTy, _hheadNonbot, chain⟩ :=
    LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.directFixedHeadShapeChain
      H rfl rfl houtNonbot
  exact ⟨headLevel, headElem, headElemTy, hhead, htyped,
    ⟨hTy.mono hheadTy⟩, chain⟩

/-- Proof-relevant producer for a guarded fixed-head fold.

Continuation passing keeps the registered type witness paired with the
guarded telescope that selected its head observation.  The consumer can
therefore lower that witness to the direct chain's exact type shape without
inventing a witness at an arbitrary `HasType` observation. -/
def LR.DirectFixedHeadProducer (Γ : List SExpr) (ρ : Valuation)
    {p : Pattern} {mcap : p.Path → TShape}
    (mx my captureType : p.Path → SExpr)
    {paths : List p.Path} {head : TShape} {headType : SExpr}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (hshape : LE_Interp.RHS.ShapeSpine mcap head paths out.T) : Prop :=
  ∀ {C : Prop},
    (∀ headTy : TShape,
      LR.DirectFixedHeadTelescopeLE
        (headTy := headTy) (outTy := outTy.T)
        Γ mx my captureType hshape →
      LE_Interp.Witness ρ headTy headType → C) → C

omit [Params.Semantic] in
/-- An explicitly synchronized guarded telescope and registered type witness
form a direct fixed-head producer without any further choice. -/
theorem LR.DirectFixedHeadProducer.of_telescope
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape} {headType : SExpr}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    (htel : LR.DirectFixedHeadTelescopeLE
      (headTy := headTy) (outTy := outTy.T)
      Γ mx my captureType spine)
    (hTy : LE_Interp.Witness ρ headTy headType) :
    LR.DirectFixedHeadProducer Γ ρ mx my captureType spine
      (headType := headType) (outTy := outTy) := by
  intro C K
  exact K headTy htel hTy

/-- Concrete layers for a guarded fixed-head producer.

Each application node retains the semantic spine edge and the direct capture
at the literal element/domain shapes used to build its singleton Pi tower.
The terminal node is data at the observation actually reached: it records the
caller's result typing and only the comparison from the caller's type
observation to that reached observation.  Thus the package contains neither a
type-functionality law nor an independently reselected capture witness. -/
inductive LR.DirectFixedHeadDominanceSpine (Γ : List SExpr) {p : Pattern}
    (mcap : p.Path → TShape) (mx my captureType : p.Path → SExpr)
    (outTy : TShape) :
    {n : Nat} → TShape → List p.Path → TShape → WShape n → Prop where
  | nil {n : Nat} {out : TShape} {w : WShape n}
      (hw : out.HasType outTy) (hle : outTy ≤ w.T) :
      LR.DirectFixedHeadDominanceSpine Γ mcap mx my captureType outTy
        out [] out w
  | cons
      {n : Nat} {f : WShape (n + 1)} {a argCap tyDom inner : WShape n}
      {m out : TShape} {path : p.Path} {paths : List p.Path}
      (harg : a.T ≤ mcap path) (happ : m ≤ (f.app a).T)
      (capture : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
        (mcap path) (mx path) (my path) (captureType path)
        argCap tyDom)
      (tail : LR.DirectFixedHeadDominanceSpine Γ mcap mx my captureType
        outTy m paths out inner) :
      LR.DirectFixedHeadDominanceSpine Γ mcap mx my captureType outTy
        f.T (path :: paths) out
        (.forallE tyDom (.single argCap inner))

omit [Params.Semantic] in
/-- Recover the semantic application spine stored by the guarded layer
package. -/
theorem LR.DirectFixedHeadDominanceSpine.spine
    {Γ : List SExpr} {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {outTy head out : TShape} {paths : List p.Path}
    {n : Nat} {tower : WShape n}
    (H : LR.DirectFixedHeadDominanceSpine Γ mcap mx my captureType outTy
      head paths out tower) :
    LE_Interp.RHS.ShapeSpine mcap head paths out := by
  induction H with
  | nil _ _ => exact .nil
  | cons harg happ _ _ ih => exact .cons harg happ ih

omit [Params.Semantic] in
/-- Fold concrete guarded layers into the monotone telescope selected by
their singleton Pi tower. -/
theorem LR.DirectFixedHeadDominanceSpine.telescopeLE
    {Γ : List SExpr} {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {outTy head out : TShape} {paths : List p.Path}
    {n : Nat} {tower : WShape n}
    (H : LR.DirectFixedHeadDominanceSpine Γ mcap mx my captureType outTy
      head paths out tower) :
    LR.DirectFixedHeadTelescopeLE
      (headTy := tower.T) (outTy := outTy)
      Γ mx my captureType H.spine := by
  induction H with
  | nil hw hle =>
    exact LR.DirectFixedHeadTelescopeLE.nil hw hle
  | @cons n f a argCap tyDom inner m out path paths harg happ capture tail ih =>
    refine LR.DirectFixedHeadTelescopeLE.cons harg happ tail.spine capture ?_
    have happEq : (WShapeFun.single argCap inner).app argCap = inner := by
      rw [WShapeFun.single_app]
      exact if_pos WShape.LE.rfl
    rw [happEq]
    exact ih

omit [Params.Semantic] in
/-- A concrete guarded dominance spine plus the registered type's witness at
its singleton Pi tower is a complete direct fixed-head producer. -/
theorem LR.DirectFixedHeadDominanceSpine.producer
    {Γ : List SExpr} {ρ : Valuation}
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType : SExpr} {headShape : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {n : Nat} {tower : WShape n}
    (H : LR.DirectFixedHeadDominanceSpine Γ mcap mx my captureType outTy.T
      headShape paths out.T tower)
    (hTy : LE_Interp.Witness ρ tower.T headType) :
    LR.DirectFixedHeadProducer Γ ρ mx my captureType H.spine
      (headType := headType) (outTy := outTy) :=
  LR.DirectFixedHeadProducer.of_telescope H.telescopeLE hTy

/-- Semantic typing aligned with the concrete guarded dominance spine.

The package deliberately exposes the comparison that a fixed-head producer
actually needs: the singleton Pi tower built from the literal captures lies
below the registered type observation selected together with the semantic
term witness.  Merely knowing that the semantic head and the constructed
tower are both typings of a non-bottom term is insufficient; those type
observations need not even be compatible.

Keeping the term witness, type witness, retained child trees, dominance
spine, and comparison in one existential prevents a later consumer from
silently pairing the tower with a different semantic typing package. -/
def LR.DirectFixedHeadAlignedTyping
    (Γ : List SExpr) (ρ : Valuation)
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    {p : Pattern} {mcap : p.Path → TShape}
    (mx my captureType : p.Path → SExpr)
    {paths : List p.Path} {head : TShape} {body headType : SExpr}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (_hshape : LE_Interp.RHS.ShapeSpine mcap head paths out.T) : Prop :=
  ∃ (semanticHead registeredTy : TShape)
      (hBody : LE_Interp.Witness ρ semanticHead body)
      (hTy : LE_Interp.Witness ρ registeredTy headType),
    head ≤ semanticHead ∧ semanticHead.HasType registeredTy ∧
      hBody.RDeepChildren P ∧ hTy.RDeepChildren P ∧
        ∃ (towerLevel : Nat) (tower : WShape towerLevel),
          LR.DirectFixedHeadDominanceSpine Γ mcap mx my captureType
              outTy.T head paths out.T tower ∧
            tower.T ≤ registeredTy

omit [Params.Semantic] in
/-- Forget the explicit tower alignment while retaining the synchronized
proof-relevant semantic typing. -/
theorem LR.DirectFixedHeadAlignedTyping.toTypedRDeep
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head : TShape} {body headType : SExpr}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {hshape : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    (H : LR.DirectFixedHeadAlignedTyping Γ ρ mx my captureType
      (P := P) (body := body) (headType := headType)
      (outTy := outTy) hshape) :
    LE_Interp.Witness.TypedRDeep P ρ head body headType := by
  obtain ⟨semanticHead, registeredTy, hBody, hTy, hhead, htyped,
    cBody, cTy, _⟩ := H
  exact ⟨semanticHead, registeredTy, hBody, hTy, hhead, htyped,
    cBody, cTy⟩

omit [Params.Semantic] in
/-- Consume the explicit tower-to-registered-type comparison to obtain the
ordinary direct fixed-head producer. -/
theorem LR.DirectFixedHeadAlignedTyping.producer
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head : TShape} {body headType : SExpr}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {hshape : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    (H : LR.DirectFixedHeadAlignedTyping Γ ρ mx my captureType
      (P := P) (body := body) (headType := headType)
      (outTy := outTy) hshape) :
    LR.DirectFixedHeadProducer Γ ρ mx my captureType hshape
      (headType := headType) (outTy := outTy) := by
  obtain ⟨_semanticHead, registeredTy, _hBody, hTy, _hhead,
    _htyped, _cBody, _cTy, towerLevel, tower, hdom, htower⟩ := H
  exact hdom.producer (hTy.mono htower)

/-- Per-layer input for the guarded ordered peel.  It is the ordinary
`FixedHeadOrderedLink` with the capture strengthened at the same literal
shapes by exactly the guarded term edge consumed by the direct zipper. -/
def LR.DirectFixedHeadOrderedLink
    (Γ : List SExpr) (ρ : Valuation) {p : Pattern}
    (mcap : p.Path → TShape) (mx my captureType : p.Path → SExpr) : Prop :=
  ∀ {C : Prop} {n : Nat} (path : p.Path) (a : WShape n)
      (headTy : TShape) (B : SExpr),
    a.T ≤ mcap path →
    LE_Interp.Witness ρ headTy B →
    (∀ (tyDom : WShape n) (tyFun : WShapeFun n) (argCap : WShape n)
        (Bdom Bbody : SExpr),
      headTy = (WShape.forallE tyDom tyFun).T →
      B = .forallE Bdom Bbody →
      a ≤ argCap →
      LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
        (mcap path) (mx path) (my path) (captureType path)
        argCap tyDom →
      LE_Interp.Witness ρ argCap.T (mx path) → C) → C

/-- Peel a registered type witness along a semantic shape spine while
building the guarded telescope at the same captures.

As in the ordinary repaired peel, the terminal observation is returned to
the caller together with a factory.  The caller supplies its own result
typing and the single comparison to that reached observation. -/
theorem LR.DirectFixedHeadTelescopeLE.ofOrderedLink
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head out : TShape}
    (spine : LE_Interp.RHS.ShapeSpine mcap head paths out)
    (link : LR.DirectFixedHeadOrderedLink Γ ρ
      mcap mx my captureType) :
    ∀ {C : Prop} {headTy : TShape} {B : SExpr},
      LE_Interp.Witness ρ headTy B →
      (∀ (reachedTy : TShape) (Bend : SExpr),
        LE_Interp.Witness ρ reachedTy Bend →
        (∀ outTy : TShape, out.HasType outTy → outTy ≤ reachedTy →
          LR.DirectFixedHeadTelescopeLE
            (headTy := headTy) (outTy := outTy)
            Γ mx my captureType spine) → C) → C := by
  induction spine with
  | @nil head0 =>
    intro C headTy B hTy K
    exact K headTy B hTy
      (fun _ htyped hle => LR.DirectFixedHeadTelescopeLE.nil htyped hle)
  | @cons n f a m out path paths harg happ rest ih =>
    intro C headTy B hTy K
    refine link path a headTy B harg hTy ?_
    intro tyDom tyFun argCap Bdom Bbody hheadTy hB hargCap capture hArg
    subst hheadTy
    subst hB
    refine ih (hTy.forallE_inst hArg) ?_
    intro reachedTy Bend hEnd factory
    exact K reachedTy Bend hEnd
      (fun outTy htyped hle =>
        LR.DirectFixedHeadTelescopeLE.cons harg happ rest capture
          (factory outTy htyped hle))

/-- Build the complete guarded shape ladder below one non-bottom semantic
RHS spine.

The construction proceeds backward from the result.  At every layer it
raises the semantic function/argument, recursive head, and paired capture to
one common maximum level, then records the exact singleton lambda/Pi
observation consumed by the later path-semantics zipper. -/
theorem LE_Interp.RHS.ShapeSpine.directFixedHeadShapeChain
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LE_Interp.RHS.ShapeSpine mcap head paths out.T)
    (hcap : ∀ path, LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ
      (mcap path) (mx path) (my path) (captureType path))
    (hout : out.HasType outTy) (houtNonbot : ¬out.T ≤ TShape.bot) :
    ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
      headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
        ¬headElem.T ≤ TShape.bot ∧
        LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
          paths headElem headElemTy out outTy := by
  generalize houtT : out.T = outT at H
  induction H generalizing outLevel out outTy with
  | @nil head0 =>
    have houtLe : out.T ≤ head0 := by
      rw [houtT]
      exact TShape.LE.rfl
    exact ⟨outLevel, out, outTy, houtLe, hout, houtNonbot,
      LR.DirectFixedHeadShapeChain.nil⟩
  | @cons n f a m outT path paths harg happ hrest ih =>
    obtain ⟨nextLevel, next, nextTy, hnext, hnextTy,
      hnextNonbot, tail⟩ := ih hout houtNonbot houtT
    obtain ⟨capLevel, argCap, tyDom, capture⟩ := hcap path
    have hnextApp : next.T ≤ (f.app a).T := hnext.trans happ
    cases f using WShape.casesOn' with
    | bot => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | sort => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | forallE => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | ctor => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | indTy => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | @lam g hg =>
      let k := max n (max nextLevel capLevel)
      have hk : n ≤ k ∧ nextLevel ≤ k ∧ capLevel ≤ k := by
        dsimp [k]
        omega
      let aK : WShape k := a.lift k
      let argCapK : WShape k := argCap.lift k
      let tyDomK : WShape k := tyDom.lift k
      let nextK : WShape k := next.lift k
      let nextTyK : WShape k := nextTy.lift k
      let elemFun : WShapeFun k := .single argCapK nextK
      let typeFun : WShapeFun k := .single argCapK nextTyK
      have hargBound : a.T ≤ argCap.T := harg.trans capture.1
      have hargK : aK ≤ argCapK := by
        exact (TShape.LE.def hk.1 hk.2.2).1 hargBound
      have hnextAppK : nextK ≤ (g.lift k).app argCapK := by
        have hmono : ((WShape.lam g hg).app a).T ≤
            ((WShape.lam (g.lift k)
              (WShapeFun.NonZero.lift_iff hk.1 |>.2 hg)).app argCapK).T := by
          apply TShape.app_mono
          · have hLift := (TShape.lift_eqv
              (a := (WShape.lam g hg).T)
              (Nat.succ_le_succ hk.1)).2
            rw [WShape.lift_lam hk.1] at hLift
            exact hLift
          · exact hargBound.trans (TShape.lift_eqv hk.2.2).2
        have hT : next.T ≤ ((g.lift k).app argCapK).T := by
          simpa [WShape.lam_eq_lam'] using hnextApp.trans hmono
        have hTK := (TShape.LE.def hk.2.1 (Nat.le_refl k)).1 hT
        simpa only [nextK, WShape.lift_self] using hTK
      have hnextKTy : nextK.HasType nextTyK :=
        (WShape.HasType.lift hk.2.1).2 hnextTy
      have hnextKNonbot : ¬nextK.T ≤ TShape.bot := by
        intro hbot
        exact hnextNonbot <|
          (TShape.lift_eqv hk.2.1).2.trans
            (hbot.trans TShape.bot_eqv.1)
      have helemNonzero : elemFun.NonZero := by
        rw [WShapeFun.NonZero.iff]
        refine ⟨(argCapK, nextK),
          WShapeFun.mem_single.2 (.inl rfl), ?_⟩
        intro hbot
        exact hnextKNonbot <|
          (WShape.LE.T hbot).trans TShape.bot_eqv.1
      let headElem : WShape (k + 1) := .lam elemFun helemNonzero
      let headElemTy : WShape (k + 1) := .forallE tyDomK typeFun
      have hcaptureK : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
          (mcap path) (mx path) (my path) (captureType path)
          argCapK tyDomK := by
        exact capture.lift hk.2.2
      have hheadTyped : headElem.HasType headElemTy := by
        change (WShape.lam elemFun helemNonzero).HasType
          (WShape.forallE tyDomK typeFun)
        rw [WShape.lam_eq_lam']
        apply WShape.HasType.lam
        refine WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
        · refine WShape.HasTypePi.def.2
            ⟨WShape.HasDom.single.2 (.inl hcaptureK.2.1), ?_⟩
          intro x y hxy
          obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ :=
            WShapeFun.mem_single.1 hxy
          · exact hnextKTy.isType
          · exact .bot' .sort
        · exact WShape.HasDom.single.2 (.inl hcaptureK.2.1)
        · simp only [elemFun, typeFun, WShapeFun.single_app]
          split <;> [exact hnextKTy; exact .bot' (.bot' .sort)]
      have hheadLeK : headElem ≤ .lam' (g.lift k) := by
        change WShape.lam elemFun helemNonzero ≤ .lam' (g.lift k)
        rw [WShape.lam_eq_lam']
        apply WShape.lam'_le_lam'.2
        obtain ⟨x', hx', hmem⟩ := (g.lift k).app_eq argCapK
        exact WShapeFun.single_le.2
          ⟨x', _, hmem, hx', hnextAppK⟩
      have hliftHead : (WShape.lam' (g.lift k)).T ≤
          (WShape.lam g hg).T := by
        have hLift := (TShape.lift_eqv
          (a := (WShape.lam g hg).T)
          (Nat.succ_le_succ hk.1)).1
        rw [WShape.lift_lam hk.1, WShape.lam_eq_lam'] at hLift
        exact hLift
      have hheadLe : headElem.T ≤ (WShape.lam g hg).T :=
        hheadLeK.T.trans hliftHead
      have tailK : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
          paths nextK nextTyK out outTy :=
        LR.DirectFixedHeadShapeChain.liftHead hk.2.1 hnextTy tail
      have tailApp : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
          paths (elemFun.app argCapK) (typeFun.app argCapK) out outTy := by
        simpa only [elemFun, typeFun, WShapeFun.single_app,
          WShape.LE.rfl, ↓reduceIte] using tailK
      have chain : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
          (path :: paths) headElem headElemTy out outTy := by
        exact LR.DirectFixedHeadShapeChain.cons hcaptureK tailApp
      exact ⟨k + 1, headElem, headElemTy, hheadLe,
        hheadTyped, by
          intro hbot
          have happBotSame : (headElem.app argCapK).T ≤
              ((WShape.bot (n := k + 1)).app argCapK).T :=
            TShape.app_mono
              (hbot.trans (TShape.bot_eqv (n := k + 1)).2)
              TShape.LE.rfl
          rw [WShape.bot_app] at happBotSame
          have happBot : (headElem.app argCapK).T ≤ TShape.bot :=
            happBotSame.trans TShape.bot_eqv.1
          apply hnextKNonbot
          simpa only [headElem, WShape.lam_eq_lam', WShape.lam'_app,
            elemFun, WShapeFun.single_app, WShape.LE.rfl, ↓reduceIte]
            using happBot,
        chain⟩

/-- A guarded term relation at the head of a nonempty fixed-head shape chain
already validates its displayed head type at the chain's exact type shape.

The first application frame is necessarily an informative lambda/Pi.  Head
lifts are erased to the recursive frame, the Pi type is extracted there, and
the result is lifted back along the same canonical equivalence. -/
theorem LR.DirectFixedHeadShapeChain.headTyOfNonempty
    {Γ : List SExpr} {p : Pattern}
    {mcap : p.Path → TShape} {mx my captureType : p.Path → SExpr}
    {paths : List p.Path}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
      paths head headTy out outTy)
    (hne : paths ≠ []) {X headType : SExpr}
    (hterm : (LRD Γ).DefEq X X headType head headTy) :
    (LRD Γ).TyDefEq headType headType headTy := by
  induction H with
  | nil => exact (hne rfl).elim
  | cons capture tail =>
    exact LRD.DefEq.piDisplayedTy hterm
  | liftHead le htyped tail ih =>
    exact (LRD.TyDefEq.lift le htyped.isType).2 <|
      ih hne ((LRD.DefEq.lift le htyped).1 hterm)

/-- Apply one guarded function edge to the exact guarded capture retained by
the synchronized semantic telescope. -/
theorem LR.DirectCaptureDefEqAligned.AtShapes.app
    {m : TShape} {x y A B M N : SExpr}
    {elemShape typeShape : WShape n}
    {termFun typeFun : WShapeFun n} {hterm : termFun.NonZero}
    (H : LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
      m x y A elemShape typeShape)
    (hfun : (LRD (n := n + 1) Γ).DefEq M N (.forallE A B)
      (.lam termFun hterm) (.forallE typeShape typeFun)) :
    (LRD (n := n) Γ).DefEq (M.app x) (N.app y) (B.inst x)
      (termFun.app elemShape) (typeFun.app elemShape) := by
  exact LRD.DefEq.app hfun H.2.1 H.2.2.2.2.1 H.2.2.2.2.2.2

/-- Retarget a guarded capture to the domain exposed by a dependent
application spine.  The raw path converts syntax typing, while the completed
guarded type edge transports both logical projections at the unchanged
semantic shapes. -/
theorem LR.DirectCaptureDefEqAligned.AtShapes.conv
    {m : TShape} {x y A B : SExpr}
    {elemShape typeShape : WShape n}
    (H : LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
      m x y A elemShape typeShape)
    (raw : TypeDefEqPath Γ A B u)
    (hTy : (LRD Γ).TyDefEq A B typeShape) :
    LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
      m x y B elemShape typeShape := by
  have hB : (LRD Γ).TyDefEq B B typeShape :=
    LRD.TyDefEq.left (LRD.TyDefEq.symm hTy)
  exact ⟨H.1, H.2.1, LRD.tyLegacy hB, hB,
    raw.defeqDF H.2.2.2.2.1,
    (LR Γ).conv (LRD.tyLegacy hTy) H.2.2.2.2.2.1,
    LRD.DefEq.conv hTy H.2.2.2.2.2.2⟩

/-- Canonical guarded fixed-head application chain.  Every layer lowers the
guard index exactly once and reuses the paired capture's literal shapes. -/
inductive LR.DirectFixedHeadChain (Γ : List SExpr)
    {p : Pattern} (mcap : p.Path → TShape)
    (mx my captureType : p.Path → SExpr) :
    ∀ (paths : List p.Path) (headType resultType : SExpr)
      {headLevel : Nat}, WShape headLevel → WShape headLevel →
      ∀ {outLevel : Nat}, WShape outLevel → WShape outLevel → Prop where
  | nil {A : SExpr} {n : Nat} {out outTy : WShape n} :
      LR.DirectFixedHeadChain Γ mcap mx my captureType
        [] A A out outTy out outTy
  | cons
      {n : Nat} {path : p.Path} {paths : List p.Path}
      {body resultType : SExpr}
      {termFun typeFun : WShapeFun n} {hterm : termFun.NonZero}
      {argCap tyDom : WShape n}
      {outLevel : Nat} {out outTy : WShape outLevel}
      (capture : LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
        (mcap path) (mx path) (my path) (captureType path)
        argCap tyDom)
      (tail : LR.DirectFixedHeadChain Γ mcap mx my captureType
        paths (body.inst (mx path)) resultType
        (termFun.app argCap) (typeFun.app argCap) out outTy) :
      LR.DirectFixedHeadChain Γ mcap mx my captureType
        (path :: paths) (.forallE (captureType path) body) resultType
        (.lam termFun hterm) (.forallE tyDom typeFun) out outTy

/-- Fold a canonical guarded fixed-head chain by dependent application. -/
theorem LR.DirectFixedHeadChain.apply
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType resultType : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LR.DirectFixedHeadChain Γ mcap mx my captureType
      paths headType resultType head headTy out outTy)
    {M N : SExpr}
    (hhead : (LRD Γ).DefEq M N headType head headTy) :
    (LRD Γ).DefEq
      (paths.foldl (fun f path => f.app (mx path)) M)
      (paths.foldl (fun f path => f.app (my path)) N)
      resultType out outTy := by
  induction H generalizing M N with
  | nil => exact hhead
  | cons capture tail ih =>
    simp only [List.foldl_cons]
    exact ih (capture.app hhead)

/-- Conversion-safe guarded application chain over one generated capture
spine.  Each application stores the actual weak-head Pi exposed at that
layer and the completed guarded domain edge; raw `PathSpineWF` conversions
are therefore never promoted by the consumer. -/
inductive LR.DirectFixedHeadExposedChain (Γ : List SExpr)
    {p : Pattern} (mcap : p.Path → TShape)
    (mx my captureType : p.Path → SExpr) :
    ∀ (paths : List p.Path) (headType resultType : SExpr)
      {headLevel : Nat}, WShape headLevel → WShape headLevel →
      ∀ {outLevel : Nat}, WShape outLevel → WShape outLevel → Prop where
  | nil {A : SExpr} {n : Nat} {out outTy : WShape n} :
      LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
        [] A A out outTy out outTy
  | cons
      {n : Nat} {path : p.Path} {paths : List p.Path}
      {headType A₁ A₂ resultType : SExpr} {u : SLevel}
      {termFun typeFun : WShapeFun n} {hterm : termFun.NonZero}
      {argCap tyDom : WShape n}
      {outLevel : Nat} {out outTy : WShape outLevel}
      (headRed : WHRedS Γ headType (.forallE A₁ A₂))
      (capture : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
        (mcap path) (mx path) (my path) (captureType path)
        argCap tyDom)
      (domainRaw : TypeDefEqPath Γ (captureType path) A₁ u)
      (domainRel : (LRD Γ).TyDefEq (captureType path) A₁ tyDom)
      (tail : LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
        paths (A₂.inst (mx path)) resultType
        (termFun.app argCap) (typeFun.app argCap) out outTy) :
      LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
        (path :: paths) headType resultType
        (.lam termFun hterm) (.forallE tyDom typeFun) out outTy
  | liftHead
      {n n' : Nat} {head headTy : WShape n}
      {paths : List p.Path} {headType resultType : SExpr}
      {outLevel : Nat} {out outTy : WShape outLevel}
      (le : n ≤ n') (htyped : head.HasType headTy)
      (tail : LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
        paths headType resultType head headTy out outTy) :
      LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
        paths headType resultType
        (head.lift n') (headTy.lift n') out outTy
  | ret
      {paths : List p.Path} {headType resultType resultType' : SExpr}
      {u : SLevel}
      {headLevel : Nat} {head headTy : WShape headLevel}
      {outLevel : Nat} {out outTy : WShape outLevel}
      (tail : LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
        paths headType resultType head headTy out outTy)
      (resultRaw : TypeDefEqPath Γ resultType resultType' u)
      (resultRel : (LRD Γ).TyDefEq resultType resultType' outTy) :
      LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
        paths headType resultType' head headTy out outTy

/-- Consume a conversion-safe guarded fixed-head chain.  Every conversion
uses a stored guarded type edge, and every function application uses the
typed Pi root already retained by the current `LRD` observation. -/
theorem LR.DirectFixedHeadExposedChain.apply
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType resultType : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
      paths headType resultType head headTy out outTy)
    {M N : SExpr}
    (hhead : (LRD Γ).DefEq M N headType head headTy) :
    (LRD Γ).DefEq
      (paths.foldl (fun f path => f.app (mx path)) M)
      (paths.foldl (fun f path => f.app (my path)) N)
      resultType out outTy := by
  induction H generalizing M N with
  | nil => exact hhead
  | @cons n path paths headType A₁ A₂ resultType u termFun typeFun
      hterm argCap tyDom outLevel out outTy headRed capture domainRaw
      domainRel tail ih =>
    simp only [List.foldl_cons]
    obtain ⟨B, F, _u, _v, root, _hB, _domain, _hF, _pi, apply⟩ :=
      LRD.DefEq.app_exposed hhead capture.2.1
    have hPiEq : SExpr.forallE B F = .forallE A₁ A₂ :=
      root.toWHRedS.determ WHNF.forallE headRed WHNF.forallE
    cases hPiEq
    apply ih
    exact apply
      (domainRaw.defeqDF capture.2.2.2.1)
      (LRD.DefEq.conv domainRel capture.2.2.2.2.2)
  | liftHead le htyped tail ih =>
    exact ih ((LRD.DefEq.lift le htyped).1 hhead)
  | ret tail _resultRaw resultRel ih =>
    exact LRD.DefEq.conv resultRel (ih hhead)

/-- Change the declared type at a guarded fixed head after its direct
cross-type observation has already been constructed.  The retained right Pi
root is synchronized with the existing chain; the reversed guarded domain
edge then retargets the capture and propagates the dependent codomain edge to
the tail. -/
theorem LR.DirectFixedHeadExposedChain.rehead
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType headType' resultType : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
      paths headType' resultType head headTy out outTy)
    {u : SLevel}
    (hraw : TypeDefEqPath Γ headType headType' u)
    (hrel : (LRD Γ).TyDefEq headType headType' headTy) :
    LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
      paths headType resultType head headTy out outTy := by
  induction H generalizing headType u with
  | nil =>
    exact LR.DirectFixedHeadExposedChain.ret
      LR.DirectFixedHeadExposedChain.nil hraw hrel
  | @cons n path paths headType' A₁ A₂ resultType v termFun typeFun
      hterm argCap tyDom outLevel out outTy headRed capture domainRaw
      domainRel tail ih =>
    rw [LRD_succ] at hrel
    obtain ⟨B₁, F₁, B₂, F₂, _u₁, u₂,
      hred₁, hred₂, hdom, hcod, hvalDom, hpi⟩ :=
      hrel.2.2 tyDom typeFun rfl
    have hPiEq : SExpr.forallE B₂ F₂ = .forallE A₁ A₂ :=
      hred₂.toWHRedS.determ WHNF.forallE headRed WHNF.forallE
    cases hPiEq
    obtain ⟨_, hdomSymm⟩ := hdom.symm
    let domainRaw' : TypeDefEqPath Γ (captureType path) B₁ v :=
      .trans domainRaw hdomSymm
    let domainRel' : (LRD Γ).TyDefEq
        (captureType path) B₁ tyDom :=
      LRD.TyDefEq.trans domainRel (LRD.TyDefEq.symm hvalDom)
    have hargRaw : IsDefEq Γ (mx path) (my path) B₁ :=
      domainRaw'.defeqDF capture.2.2.2.1
    have hargRel : (LRD Γ).DefEq
        (mx path) (my path) B₁ argCap tyDom :=
      LRD.DefEq.conv domainRel' capture.2.2.2.2.2
    have hcodInst : TypeDefEqPath Γ
        (F₁.inst (mx path)) (A₂.inst (mx path)) u₂ := by
      simpa only [SExpr.inst] using hcod.subst
        (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar hargRaw.hasType.1)
    have hcodRel : (LRD Γ).TyDefEq
        (F₁.inst (mx path)) (A₂.inst (mx path))
        (typeFun.app argCap) :=
      hpi.2 capture.2.1 hargRaw.hasType.1 (LRD.DefEq.left hargRel)
    exact LR.DirectFixedHeadExposedChain.cons hred₁.toWHRedS capture
      domainRaw' domainRel' (ih hcodInst hcodRel)
  | liftHead le htyped tail ih =>
    exact LR.DirectFixedHeadExposedChain.liftHead le htyped <|
      ih hraw ((LRD.TyDefEq.lift le htyped.isType).1 hrel)
  | ret tail resultRaw resultRel ih =>
    exact LR.DirectFixedHeadExposedChain.ret
      (ih hraw hrel) resultRaw resultRel

/-- Guarded conversion at one fixed-head path-spine edge. -/
def LRD.FixedHeadConvertStep (Γ : List SExpr) : Prop :=
  ∀ {n : Nat} {A B : SExpr} {u : SLevel} {a : WShape n},
    IsDefEq Γ A B (.sort u) →
    (LRD Γ).TyDefEq A A a →
    (LRD Γ).TyDefEq A B a

/-- Legacy cross-relation producer used by guarded completion. -/
def LRD.FixedHeadLegacyConvertStep (Γ : List SExpr) : Prop :=
  ∀ {n : Nat} {A B : SExpr} {u : SLevel} {a : WShape n},
    IsDefEq Γ A B (.sort u) →
    (LR Γ).TyDefEq A A a →
    (LR Γ).TyDefEq A B a

/-- Right endpoint validity at the exact observation threaded by a guarded
path-spine conversion edge. -/
def LRD.FixedHeadConvertRightValidStep (Γ : List SExpr) : Prop :=
  ∀ {n : Nat} {A B : SExpr} {u : SLevel} {a : WShape n},
    IsDefEq Γ A B (.sort u) →
    (LRD Γ).TyDefEq A A a →
    (LRD Γ).TyDefEq B B a

/-- Complete a guarded fixed-head conversion from its legacy cross edge and
an independently justified guarded right endpoint at the same shape. -/
theorem LRD.FixedHeadConvertStep.of_parts
    (legacy : LRD.FixedHeadLegacyConvertStep Γ)
    (right : LRD.FixedHeadConvertRightValidStep Γ) :
    LRD.FixedHeadConvertStep Γ := by
  intro n A B u a raw left
  exact LRD.TyDefEq.complete
    (legacy raw (LRD.tyLegacy left)) left (right raw left)

/-- Guarded semantic payloads for one concrete path-indexed typing spine.

This certificate zips a syntax-independent `DirectFixedHeadShapeChain` with
the actual `PathSpineWF` derivation used by a generated RHS.  Raw conversion
edges remain syntax-only: each one carries a separately constructed guarded
type edge at the exact shape threaded by the chain. -/
inductive LR.DirectFixedHeadPathSemantics (Γ : List SExpr)
    {p : Pattern} (mcap : p.Path → TShape)
    (mx my captureType : p.Path → SExpr) :
    ∀ {paths : List p.Path} {headType resultType : SExpr}
      {headLevel : Nat} {head headTy : WShape headLevel}
      {outLevel : Nat} {out outTy : WShape outLevel},
      LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        paths head headTy out outTy →
      SExpr.PathSpineWF Γ mx captureType
        headType paths resultType → Prop where
  | nil {A : SExpr} {n : Nat} {out outTy : WShape n} :
      LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
        (LR.DirectFixedHeadShapeChain.nil (out := out) (outTy := outTy))
        (SExpr.PathSpineWF.nil (A := A))
  | cons
      {n : Nat} {path : p.Path} {paths : List p.Path}
      {A₁ A₂ resultType : SExpr} {u : SLevel}
      {termFun typeFun : WShapeFun n} {hterm : termFun.NonZero}
      {argCap tyDom : WShape n}
      {outLevel : Nat} {out outTy : WShape outLevel}
      {capture : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
        (mcap path) (mx path) (my path) (captureType path)
        argCap tyDom}
      {tailShape : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        paths (termFun.app argCap) (typeFun.app argCap) out outTy}
      {domainRaw : IsDefEq Γ (captureType path) A₁ (.sort u)}
      {tailRaw : SExpr.PathSpineWF Γ mx captureType
        (A₂.inst (mx path)) paths resultType}
      (domainRel : (LRD Γ).TyDefEq (captureType path) A₁ tyDom)
      (tail : LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
        tailShape tailRaw) :
      LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
        (LR.DirectFixedHeadShapeChain.cons (hterm := hterm) capture tailShape)
        (SExpr.PathSpineWF.cons domainRaw tailRaw)
  | liftHead
      {n n' : Nat} {head headTy : WShape n}
      {paths : List p.Path} {headType resultType : SExpr}
      {outLevel : Nat} {out outTy : WShape outLevel}
      {le : n ≤ n'} {htyped : head.HasType headTy}
      {tailShape : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        paths head headTy out outTy}
      {raw : SExpr.PathSpineWF Γ mx captureType
        headType paths resultType}
      (tail : LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
        tailShape raw) :
      LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
        (LR.DirectFixedHeadShapeChain.liftHead le htyped tailShape) raw
  | conv
      {paths : List p.Path} {headType headType' resultType : SExpr}
      {u : SLevel}
      {headLevel : Nat} {head headTy : WShape headLevel}
      {outLevel : Nat} {out outTy : WShape outLevel}
      {shape : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        paths head headTy out outTy}
      {headRaw : IsDefEq Γ headType headType' (.sort u)}
      {tailRaw : SExpr.PathSpineWF Γ mx captureType
        headType' paths resultType}
      (headRel : (LRD Γ).TyDefEq headType headType' headTy)
      (tail : LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
        shape tailRaw) :
      LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType shape
        (SExpr.PathSpineWF.conv headRaw tailRaw)
  | ret
      {paths : List p.Path} {headType resultType resultType' : SExpr}
      {u : SLevel}
      {headLevel : Nat} {head headTy : WShape headLevel}
      {outLevel : Nat} {out outTy : WShape outLevel}
      {shape : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        paths head headTy out outTy}
      {tailRaw : SExpr.PathSpineWF Γ mx captureType
        headType paths resultType}
      {resultRaw : IsDefEq Γ resultType resultType' (.sort u)}
      (resultRel : (LRD Γ).TyDefEq resultType resultType' outTy)
      (tail : LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
        shape tailRaw) :
      LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType shape
        (SExpr.PathSpineWF.ret tailRaw resultRaw)

/-- Zip an empty concrete spine with a guarded shape chain containing only
terminal and head-lift frames. -/
theorem LR.DirectFixedHeadShapeChain.pathSemanticsNil
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {shapePaths : List p.Path} {A : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (shape : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
      shapePaths head headTy out outTy)
    (hpaths : shapePaths = []) :
    LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
      (hpaths ▸ shape) (SExpr.PathSpineWF.nil (A := A)) := by
  induction shape with
  | nil =>
    cases hpaths
    exact LR.DirectFixedHeadPathSemantics.nil
  | cons capture tail =>
    cases hpaths
  | liftHead le htyped tail ih =>
    cases hpaths
    exact LR.DirectFixedHeadPathSemantics.liftHead
      (le := le) (htyped := htyped)
      (raw := SExpr.PathSpineWF.nil (A := A))
      (ih rfl)

/-- Zip one concrete application edge after stripping leading head-lift
frames from the guarded shape chain. -/
theorem LR.DirectFixedHeadShapeChain.pathSemanticsCons
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {shapePaths : List p.Path}
    {path : p.Path} {paths : List p.Path}
    {A₁ A₂ resultType : SExpr} {u : SLevel}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (shape : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
      shapePaths head headTy out outTy)
    (hpaths : shapePaths = path :: paths)
    (domainRaw : IsDefEq Γ (captureType path) A₁ (.sort u))
    (tailRaw : SExpr.PathSpineWF Γ mx captureType
      (A₂.inst (mx path)) paths resultType)
    (headRel : (LRD Γ).TyDefEq
      (.forallE A₁ A₂) (.forallE A₁ A₂) headTy)
    (convert : LRD.FixedHeadConvertStep Γ)
    (tailSemantics : ∀ {tailLevel : Nat}
        {tailHead tailHeadTy : WShape tailLevel},
      (tailShape : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
        paths tailHead tailHeadTy out outTy) →
      (LRD Γ).TyDefEq
        (A₂.inst (mx path)) (A₂.inst (mx path)) tailHeadTy →
      LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
        tailShape tailRaw) :
    LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
      (hpaths ▸ shape) (SExpr.PathSpineWF.cons domainRaw tailRaw) := by
  induction shape with
  | nil =>
    cases hpaths
  | @cons n path₀ paths₀ termFun typeFun hterm argCap tyDom
      outLevel out outTy capture tail =>
    cases hpaths
    rw [LRD_succ] at headRel
    obtain ⟨B₁, F₁, B₂, F₂, _u₁, _u₂,
      hred₁, hred₂, _hdom, _hcod, domainSelf, hpi⟩ :=
      headRel.2.2 tyDom typeFun rfl
    have hPi₁ : SExpr.forallE B₁ F₁ = .forallE A₁ A₂ :=
      hred₁.toWHRedS.determ WHNF.forallE .rfl WHNF.forallE
    have hPi₂ : SExpr.forallE B₂ F₂ = .forallE A₁ A₂ :=
      hred₂.toWHRedS.determ WHNF.forallE .rfl WHNF.forallE
    cases hPi₁
    cases hPi₂
    have domainRelRev : (LRD Γ).TyDefEq
        A₁ (captureType path) tyDom :=
      convert domainRaw.symm domainSelf
    have domainRel : (LRD Γ).TyDefEq
        (captureType path) A₁ tyDom :=
      LRD.TyDefEq.symm domainRelRev
    have argRaw : IsDefEq Γ (mx path) (my path) A₁ :=
      domainRaw.defeqDF capture.2.2.2.1
    have argRel : (LRD Γ).DefEq
        (mx path) (my path) A₁ argCap tyDom :=
      LRD.DefEq.conv domainRel capture.2.2.2.2.2
    have tailHeadRel : (LRD Γ).TyDefEq
        (A₂.inst (mx path)) (A₂.inst (mx path))
        (typeFun.app argCap) :=
      hpi.2 capture.2.1 argRaw.hasType.1 (LRD.DefEq.left argRel)
    exact LR.DirectFixedHeadPathSemantics.cons
      (u := u) (capture := capture)
      (domainRaw := domainRaw) (tailRaw := tailRaw)
      domainRel (tailSemantics tail tailHeadRel)
  | liftHead le htyped tail ih =>
    cases hpaths
    exact LR.DirectFixedHeadPathSemantics.liftHead
      (le := le) (htyped := htyped)
      (raw := SExpr.PathSpineWF.cons domainRaw tailRaw) <|
      ih rfl ((LRD.TyDefEq.lift le htyped.isType).1 headRel)
        tailSemantics

/-- Add guarded semantic payloads to one concrete path-indexed typing spine.

The conversion callback is invoked only for an equality edge actually
present in `raw`, and only after its source is already a guarded type at the
exact shape threaded by the fixed-head chain. -/
theorem LR.DirectFixedHeadShapeChain.pathSemantics
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType resultType : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (shape : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
      paths head headTy out outTy)
    (raw : SExpr.PathSpineWF Γ mx captureType
      headType paths resultType)
    (headRel : (LRD Γ).TyDefEq headType headType headTy)
    (resultRel : (LRD Γ).TyDefEq resultType resultType outTy)
    (convert : LRD.FixedHeadConvertStep Γ) :
    LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType shape raw := by
  induction raw generalizing headLevel head headTy with
  | @nil A =>
    simpa only using shape.pathSemanticsNil (A := A) rfl
  | @cons path A₁ u paths resultType A₂ domainRaw tailRaw ih =>
    exact shape.pathSemanticsCons rfl domainRaw tailRaw headRel convert
      (fun tail tailHeadRel => ih tail tailHeadRel resultRel)
  | @conv headType headType' u paths resultType headRaw tailRaw ih =>
    have headCross : (LRD Γ).TyDefEq headType headType' headTy :=
      convert headRaw headRel
    have tailHeadRel : (LRD Γ).TyDefEq headType' headType' headTy :=
      LRD.TyDefEq.left (LRD.TyDefEq.symm headCross)
    exact LR.DirectFixedHeadPathSemantics.conv
      (u := u) (headRaw := headRaw) (tailRaw := tailRaw) headCross
      (ih shape tailHeadRel resultRel)
  | @ret headType paths resultType resultType' u tailRaw resultRaw ih =>
    have resultCrossRev : (LRD Γ).TyDefEq
        resultType' resultType outTy :=
      convert resultRaw.symm resultRel
    have tailResultRel : (LRD Γ).TyDefEq
        resultType resultType outTy :=
      LRD.TyDefEq.left (LRD.TyDefEq.symm resultCrossRev)
    exact LR.DirectFixedHeadPathSemantics.ret
      (u := u) (tailRaw := tailRaw) (resultRaw := resultRaw)
      (LRD.TyDefEq.symm resultCrossRev)
      (ih shape headRel tailResultRel)

/-- Forget zipper provenance and expose the conversion-safe guarded
fixed-head application certificate consumed by `apply`. -/
theorem LR.DirectFixedHeadPathSemantics.exposed
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType resultType : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {shape : LR.DirectFixedHeadShapeChain Γ mcap mx my captureType
      paths head headTy out outTy}
    {raw : SExpr.PathSpineWF Γ mx captureType
      headType paths resultType}
    (H : LR.DirectFixedHeadPathSemantics Γ mcap mx my captureType
      shape raw) :
    LR.DirectFixedHeadExposedChain Γ mcap mx my captureType
      paths headType resultType head headTy out outTy := by
  induction H with
  | nil => exact LR.DirectFixedHeadExposedChain.nil
  | @cons n path paths A₁ A₂ resultType u termFun typeFun hterm
      argCap tyDom outLevel out outTy capture tailShape domainRaw tailRaw
      domainRel tail ih =>
    exact LR.DirectFixedHeadExposedChain.cons .rfl capture
      (.single domainRaw) domainRel ih
  | @liftHead n n' head headTy paths headType resultType outLevel out outTy
      le htyped tailShape raw tail ih =>
    exact LR.DirectFixedHeadExposedChain.liftHead le htyped ih
  | @conv paths headType headType' resultType u headLevel head headTy
      outLevel out outTy shape headRaw tailRaw headRel tail ih =>
    exact ih.rehead (.single headRaw) headRel
  | @ret paths headType resultType resultType' u headLevel head headTy
      outLevel out outTy shape tailRaw resultRaw resultRel tail ih =>
    exact LR.DirectFixedHeadExposedChain.ret ih (.single resultRaw) resultRel

/-- Complete a nonempty guarded fixed-head application spine from one exact
self-relation for the selected lower head.

Shape synthesis chooses the common finite levels, `headTyOfNonempty` recovers
the head type relation from the informative term observation, and the path
zipper stores only conversion edges explicitly authorized by `convert`.  The
terminal term/type observation remains exactly the caller's `out`/`outTy`. -/
theorem LE_Interp.RHS.ShapeSpine.directApplyWithHeadSelf
    {Γ : List SExpr} {p : Pattern}
    {mcap : p.Path → TShape} {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head : TShape}
    {headType resultType X : SExpr}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LE_Interp.RHS.ShapeSpine mcap head paths out.T)
    (hcap : ∀ path, LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ
      (mcap path) (mx path) (my path) (captureType path))
    (hout : out.HasType outTy) (houtNonbot : ¬out.T ≤ TShape.bot)
    (hne : paths ≠ [])
    (raw : SExpr.PathSpineWF Γ mx captureType
      headType paths resultType)
    (resultRel : (LRD Γ).TyDefEq resultType resultType outTy)
    (convert : LRD.FixedHeadConvertStep Γ)
    (headSelf : ∀ {headLevel : Nat}
        {headElem headElemTy : WShape headLevel},
      headElem.T ≤ head → headElem.HasType headElemTy →
      (LRD Γ).DefEq X X headType headElem headElemTy) :
    (LRD Γ).DefEq
      (paths.foldl (fun f path => f.app (mx path)) X)
      (paths.foldl (fun f path => f.app (my path)) X)
      resultType out outTy := by
  obtain ⟨headLevel, headElem, headElemTy, helem, htyped,
    _hnonbot, chain⟩ := H.directFixedHeadShapeChain hcap hout houtNonbot
  have hterm : (LRD Γ).DefEq X X headType headElem headElemTy :=
    headSelf helem htyped
  have hheadTy : (LRD Γ).TyDefEq headType headType headElemTy :=
    chain.headTyOfNonempty hne hterm
  exact (chain.pathSemantics raw hheadTy resultRel convert).exposed.apply hterm

/-- Rewrite the guarded fixed-head fold back to the exact generated RHS
syntax stored by an iota descriptor.  The descriptor's `rhsTower` is the
only syntactic rewrite; all semantic levels and the terminal observation are
those selected by `directApplyWithHeadSelf`. -/
theorem LE_Interp.RHS.ShapeSpine.directApplyRuleWithHeadSelf
    {Γ : List SExpr} {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {recLs : List SLevel}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
    {mx my captureType :
      (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {resultType : SExpr} {head : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LE_Interp.RHS.ShapeSpine mcap head rule.capturePaths out.T)
    (hcap : ∀ path, LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ
      (mcap path) (mx path) (my path) (captureType path))
    (hout : out.HasType outTy) (houtNonbot : ¬out.T ≤ TShape.bot)
    (hne : rule.capturePaths ≠ [])
    (raw : SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths resultType)
    (resultRel : (LRD Γ).TyDefEq resultType resultType outTy)
    (convert : LRD.FixedHeadConvertStep Γ)
    (headSelf : ∀ {headLevel : Nat}
        {headElem headElemTy : WShape headLevel},
      headElem.T ≤ head → headElem.HasType headElemTy →
      (LRD Γ).DefEq
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) headElem headElemTy) :
    (LRD Γ).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my)
      resultType out outTy := by
  rw [← rule.rhsApply recLs mx, ← rule.rhsApply recLs my]
  simpa only [List.foldl_map] using
    H.directApplyWithHeadSelf hcap hout houtNonbot hne raw resultRel
      convert headSelf

/-- Complete a nonempty guarded fixed-head application from a
proof-relevant guarded telescope producer.

Unlike `directApplyWithHeadSelf`, the callback receives the registered
head-type witness at the exact lower type shape selected by the direct
chain.  The telescope, lowered witness, and direct captures all arise from
one producer elimination, so the callback never has to justify an arbitrary
typed observation. -/
theorem LE_Interp.RHS.ShapeSpine.directApplyWithProducerHeadSelf
    {Γ : List SExpr} {ρ : Valuation} {p : Pattern}
    {mcap : p.Path → TShape} {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head : TShape}
    {headType resultType X : SExpr}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LE_Interp.RHS.ShapeSpine mcap head paths out.T)
    (producer : LR.DirectFixedHeadProducer Γ ρ mx my captureType H
      (headType := headType) (outTy := outTy))
    (houtNonbot : ¬out.T ≤ TShape.bot)
    (hne : paths ≠ [])
    (raw : SExpr.PathSpineWF Γ mx captureType
      headType paths resultType)
    (resultRel : (LRD Γ).TyDefEq resultType resultType outTy)
    (convert : LRD.FixedHeadConvertStep Γ)
    (headSelf : ∀ {headLevel : Nat}
        {headElem headElemTy : WShape headLevel},
      headElem.T ≤ head → headElem.HasType headElemTy →
      LE_Interp.Witness ρ headElemTy.T headType →
      (LRD Γ).DefEq X X headType headElem headElemTy) :
    (LRD Γ).DefEq
      (paths.foldl (fun f path => f.app (mx path)) X)
      (paths.foldl (fun f path => f.app (my path)) X)
      resultType out outTy := by
  refine producer ?_
  intro headTy htel hTyReg
  obtain ⟨headLevel, headElem, headElemTy, helem, htyped,
    ⟨hTy⟩, chain⟩ := htel.withWitnessAndChain hTyReg houtNonbot
  have hterm : (LRD Γ).DefEq X X headType headElem headElemTy :=
    headSelf helem htyped hTy
  have hheadTy : (LRD Γ).TyDefEq headType headType headElemTy :=
    chain.headTyOfNonempty hne hterm
  exact (chain.pathSemantics raw hheadTy resultRel convert).exposed.apply hterm

/-- The producer-driven guarded fold, rewritten to the generated RHS syntax
stored by an iota descriptor. -/
theorem LE_Interp.RHS.ShapeSpine.directApplyRuleWithProducerHeadSelf
    {Γ : List SExpr} {ρ : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {recLs : List SLevel}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
    {mx my captureType :
      (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {resultType : SExpr} {head : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LE_Interp.RHS.ShapeSpine mcap head rule.capturePaths out.T)
    (producer : LR.DirectFixedHeadProducer Γ ρ mx my captureType H
      (headType := SExpr.mkInst recLs rule.df.type) (outTy := outTy))
    (houtNonbot : ¬out.T ≤ TShape.bot)
    (hne : rule.capturePaths ≠ [])
    (raw : SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths resultType)
    (resultRel : (LRD Γ).TyDefEq resultType resultType outTy)
    (convert : LRD.FixedHeadConvertStep Γ)
    (headSelf : ∀ {headLevel : Nat}
        {headElem headElemTy : WShape headLevel},
      headElem.T ≤ head → headElem.HasType headElemTy →
      LE_Interp.Witness ρ headElemTy.T
        (SExpr.mkInst recLs rule.df.type) →
      (LRD Γ).DefEq
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) headElem headElemTy) :
    (LRD Γ).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my)
      resultType out outTy := by
  rw [← rule.rhsApply recLs mx, ← rule.rhsApply recLs my]
  simpa only [List.foldl_map] using
    H.directApplyWithProducerHeadSelf producer houtNonbot hne raw
      resultRel convert headSelf

/--
info: 'Lean4Lean.SExpr.LE_Interp.RHS.ShapeSpine.directFixedHeadShapeChain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.RHS.ShapeSpine.directFixedHeadShapeChain

/--
info: 'Lean4Lean.SExpr.LR.DirectFixedHeadShapeChain.headTyOfNonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectFixedHeadShapeChain.headTyOfNonempty

/--
info: 'Lean4Lean.SExpr.LR.DirectFixedHeadShapeChain.pathSemantics' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectFixedHeadShapeChain.pathSemantics

/--
info: 'Lean4Lean.SExpr.LR.DirectFixedHeadPathSemantics.exposed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectFixedHeadPathSemantics.exposed

/--
info: 'Lean4Lean.SExpr.LE_Interp.RHS.ShapeSpine.directApplyWithHeadSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.RHS.ShapeSpine.directApplyWithHeadSelf

/--
info: 'Lean4Lean.SExpr.LE_Interp.RHS.ShapeSpine.directApplyRuleWithHeadSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.RHS.ShapeSpine.directApplyRuleWithHeadSelf

/--
info: 'Lean4Lean.SExpr.LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.directFixedHeadShapeChain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.directFixedHeadShapeChain

/--
info: 'Lean4Lean.SExpr.LR.DirectFixedHeadTelescopeLE.withWitnessAndChain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectFixedHeadTelescopeLE.withWitnessAndChain

/--
info: 'Lean4Lean.SExpr.LR.DirectFixedHeadProducer.of_telescope' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectFixedHeadProducer.of_telescope

/--
info: 'Lean4Lean.SExpr.LR.DirectFixedHeadTelescopeLE.ofOrderedLink' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectFixedHeadTelescopeLE.ofOrderedLink

/--
info: 'Lean4Lean.SExpr.LR.DirectFixedHeadDominanceSpine.telescopeLE' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectFixedHeadDominanceSpine.telescopeLE

/--
info: 'Lean4Lean.SExpr.LR.DirectFixedHeadDominanceSpine.producer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectFixedHeadDominanceSpine.producer

/--
info: 'Lean4Lean.SExpr.LE_Interp.RHS.ShapeSpine.directApplyWithProducerHeadSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.RHS.ShapeSpine.directApplyWithProducerHeadSelf

/--
info: 'Lean4Lean.SExpr.LE_Interp.RHS.ShapeSpine.directApplyRuleWithProducerHeadSelf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.RHS.ShapeSpine.directApplyRuleWithProducerHeadSelf

/--
info: 'Lean4Lean.SExpr.LR.DirectCaptureDefEqAligned.AtShapes.toTerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCaptureDefEqAligned.AtShapes.toTerm

/--
info: 'Lean4Lean.SExpr.LR.DirectCaptureDefEqAligned.AtSomeLevel.toTerm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCaptureDefEqAligned.AtSomeLevel.toTerm

/--
info: 'Lean4Lean.SExpr.LR.DirectTermCaptureDefEqAligned.Upgrade.atSomeLevel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectTermCaptureDefEqAligned.Upgrade.atSomeLevel

/--
info: 'Lean4Lean.SExpr.LR.DirectCaptureDefEqAligned.Upgrade.toTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCaptureDefEqAligned.Upgrade.toTerm

/--
info: 'Lean4Lean.SExpr.LR.DirectTermCaptureDefEqAligned.AtShapes.lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectTermCaptureDefEqAligned.AtShapes.lift

/--
info: 'Lean4Lean.SExpr.LR.DirectCaptureDefEqAligned.Upgrade.of_typeShape_bot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCaptureDefEqAligned.Upgrade.of_typeShape_bot

/--
info: 'Lean4Lean.SExpr.LR.DirectCaptureDefEqAligned.Upgrade.of_typeShape_indTy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCaptureDefEqAligned.Upgrade.of_typeShape_indTy

/--
info: 'Lean4Lean.SExpr.LR.DirectTermCaptureDefEqAligned.Upgrade.of_typeShape_bot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectTermCaptureDefEqAligned.Upgrade.of_typeShape_bot

/--
info: 'Lean4Lean.SExpr.LR.DirectTermCaptureDefEqAligned.Upgrade.of_elemShape_bot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectTermCaptureDefEqAligned.Upgrade.of_elemShape_bot

/--
info: 'Lean4Lean.SExpr.LR.DirectTermCaptureDefEqAligned.Upgrade.of_typeShape_indTy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectTermCaptureDefEqAligned.Upgrade.of_typeShape_indTy

/--
info: 'Lean4Lean.SExpr.LR.DirectCaptureDefEqAligned.Upgrade.atSomeLevel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCaptureDefEqAligned.Upgrade.atSomeLevel

/--
info: 'Lean4Lean.SExpr.LRD.FixedHeadConvertStep.of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.FixedHeadConvertStep.of_parts

/--
info: 'Lean4Lean.SExpr.LR.DirectFixedHeadChain.apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectFixedHeadChain.apply

/--
info: 'Lean4Lean.SExpr.LR.DirectFixedHeadExposedChain.apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectFixedHeadExposedChain.apply

/-- Materialize a semantic `varN` match from a complete paired direct
argument list.  The induction is purely structural and, crucially, chooses
the capture type only once for both projections. -/
theorem LE_Interp.Matches.varN_materializeDirectAt
    {IH : LR.DirectRelBase Γ n}
    {c c' : Name} {arity : Nat} {rargs : List (WShape n)}
    {mcap : (Pattern.varN (.const c) arity).Path → TShape}
    {xs ys : List SExpr} {ls ls' : List SLevel}
    (hm : LE_Interp.Matches (Pattern.varN (.const c) arity)
      c' rargs mcap)
    (hargs : LR.DirectCtorArgsDefEq IH xs ys rargs) :
    c' = c ∧ ∃ mx my,
      (Pattern.varN (.const c) arity).MatchesS
        (xs.foldr (fun a f => f.app a) (.const c ls)) ls mx ∧
      (Pattern.varN (.const c) arity).MatchesS
        (ys.foldr (fun a f => f.app a) (.const c ls')) ls' my ∧
      ∀ path, LR.DirectCaptureDefEqAt IH
        (mcap path) (mx path) (my path) := by
  induction arity generalizing c' n rargs xs ys with
  | zero =>
    simp only [Pattern.varN] at hm
    cases hm
    cases hargs
    refine ⟨rfl, nofun, nofun, ?_, ?_, nofun⟩
    · exact .const
    · exact .const
  | succ arity ih =>
    simp only [Pattern.varN] at hm
    cases hm with
    | var hm =>
      cases hargs with
      | @cons A a x y p xs ys ps hp htyLegacy htyDirect hxy
          hvLegacy hvDirect hrest =>
        obtain ⟨rfl, mx, my, hmx, hmy, hcap⟩ := ih hm hrest
        refine ⟨rfl, (fun path => Option.elim path x mx),
          (fun path => Option.elim path y my), hmx.var, hmy.var, ?_⟩
        intro path
        cases path with
        | none =>
          exact ⟨_, _, _, TShape.LE.rfl, hp, htyLegacy, htyDirect,
            hxy, hvLegacy, hvDirect⟩
        | some path => exact hcap path

/-- Materialize a semantic `varN` match while retaining the literal capture
type and both literal shapes stored by the paired direct argument spine.

Unlike `varN_materializeDirectAt`, this form does not existentially package
each capture and then choose a representative.  The capture maps, type map,
and shape maps are constructed together by the same structural recursion, so
a registered-type trace can later identify them layer-for-layer without a
type-functionality or shape-projection principle. -/
theorem LE_Interp.Matches.varN_materializeDirectAlignedAt
    {IH : LR.DirectRelBase Γ n}
    {c c' : Name} {arity : Nat} {rargs : List (WShape n)}
    {mcap : (Pattern.varN (.const c) arity).Path → TShape}
    {xs ys : List SExpr} {ls ls' : List SLevel}
    (hm : LE_Interp.Matches (Pattern.varN (.const c) arity)
      c' rargs mcap)
    (hargs : LR.DirectCtorArgsDefEq IH xs ys rargs) :
    c' = c ∧
      ∃ (mx my : (Pattern.varN (.const c) arity).Path → SExpr)
        (captureType : (Pattern.varN (.const c) arity).Path → SExpr)
        (elemShape typeShape :
          (Pattern.varN (.const c) arity).Path → WShape n),
        (Pattern.varN (.const c) arity).MatchesS
          (xs.foldr (fun a f => f.app a) (.const c ls)) ls mx ∧
        (Pattern.varN (.const c) arity).MatchesS
          (ys.foldr (fun a f => f.app a) (.const c ls')) ls' my ∧
        (Pattern.varNPaths (.const c) arity).map mx = xs.reverse ∧
        (Pattern.varNPaths (.const c) arity).map my = ys.reverse ∧
        (Pattern.varNPaths (.const c) arity).map elemShape = rargs.reverse ∧
        ∀ path, LR.DirectCaptureDefEqAligned.AtShapes IH
          (mcap path) (mx path) (my path) (captureType path)
          (elemShape path) (typeShape path) := by
  induction arity generalizing c' n rargs xs ys with
  | zero =>
    simp only [Pattern.varN] at hm
    cases hm
    cases hargs
    refine ⟨rfl, nofun, nofun, nofun, nofun, nofun,
      ?_, ?_, rfl, rfl, rfl, nofun⟩
    · exact .const
    · exact .const
  | succ arity ih =>
    simp only [Pattern.varN] at hm
    cases hm with
    | @var _ _ _ _ _ p hm =>
      cases hargs with
      | @cons A a x y p xs ys ps hp htyLegacy htyDirect hxy
          hvLegacy hvDirect hrest =>
        obtain ⟨rfl, mx, my, captureType, elemShape, typeShape,
            hmx, hmy, hmxPaths, hmyPaths, helemPaths, hcap⟩ :=
          ih hm hrest
        refine ⟨rfl,
          (fun path => Option.elim path x mx),
          (fun path => Option.elim path y my),
          (fun path => Option.elim path A captureType),
          (fun path => Option.elim path p elemShape),
          (fun path => Option.elim path a typeShape),
          hmx.var, hmy.var, ?_, ?_, ?_, ?_⟩
        · simp only [Pattern.varNPaths, List.map_append, List.map_map,
            List.map_cons, List.map_nil, List.reverse_cons]
          have hcomp :
              (fun path => Option.elim path x mx) ∘ some = mx := by
            funext path
            rfl
          rw [hcomp, hmxPaths]
          rfl
        · simp only [Pattern.varNPaths, List.map_append, List.map_map,
            List.map_cons, List.map_nil, List.reverse_cons]
          have hcomp :
              (fun path => Option.elim path y my) ∘ some = my := by
            funext path
            rfl
          rw [hcomp, hmyPaths]
          rfl
        · simp only [Pattern.varNPaths, List.map_append, List.map_map,
            List.map_cons, List.map_nil, List.reverse_cons]
          have hcomp :
              (fun path => Option.elim path p elemShape) ∘ some =
                elemShape := by
            funext path
            rfl
          rw [hcomp, helemPaths]
          rfl
        · intro path
          cases path with
          | none =>
            exact ⟨TShape.LE.rfl, hp, htyLegacy, htyDirect,
              hxy, hvLegacy, hvDirect⟩
          | some path => exact hcap path

/-- Fully listed form of direct `varN` materialization.  Besides the exact
capture payload, the five canonical path traversals are proved equal to the
reversed newest-first lists supplied by the evaluator. -/
theorem LE_Interp.Matches.varN_materializeDirectListedAt
    {IH : LR.DirectRelBase Γ n}
    {c c' : Name} {arity : Nat} {rargs typeShapes : List (WShape n)}
    {mcap : (Pattern.varN (.const c) arity).Path → TShape}
    {xs ys types : List SExpr} {ls ls' : List SLevel}
    (hm : LE_Interp.Matches (Pattern.varN (.const c) arity)
      c' rargs mcap)
    (hargs : LR.DirectCtorArgsDefEqListed IH
      xs ys types rargs typeShapes) :
    c' = c ∧
      ∃ (mx my : (Pattern.varN (.const c) arity).Path → SExpr)
        (captureType : (Pattern.varN (.const c) arity).Path → SExpr)
        (elemShape typeShape :
          (Pattern.varN (.const c) arity).Path → WShape n),
        (Pattern.varN (.const c) arity).MatchesS
          (xs.foldr (fun a f => f.app a) (.const c ls)) ls mx ∧
        (Pattern.varN (.const c) arity).MatchesS
          (ys.foldr (fun a f => f.app a) (.const c ls')) ls' my ∧
        (Pattern.varNPaths (.const c) arity).map mx = xs.reverse ∧
        (Pattern.varNPaths (.const c) arity).map my = ys.reverse ∧
        (Pattern.varNPaths (.const c) arity).map captureType =
          types.reverse ∧
        (Pattern.varNPaths (.const c) arity).map elemShape =
          rargs.reverse ∧
        (Pattern.varNPaths (.const c) arity).map typeShape =
          typeShapes.reverse ∧
        ∀ path, LR.DirectCaptureDefEqAligned.AtShapes IH
          (mcap path) (mx path) (my path) (captureType path)
          (elemShape path) (typeShape path) := by
  induction arity generalizing c' n rargs typeShapes xs ys types with
  | zero =>
    simp only [Pattern.varN] at hm
    cases hm
    cases hargs
    refine ⟨rfl, nofun, nofun, nofun, nofun, nofun,
      ?_, ?_, rfl, rfl, rfl, rfl, rfl, nofun⟩
    · exact .const
    · exact .const
  | succ arity ih =>
    simp only [Pattern.varN] at hm
    cases hm with
    | @var _ _ _ _ _ p hm =>
      cases hargs with
      | @cons A a x y p xs ys types ps typeShapes hp htyLegacy
          htyDirect hxy hvLegacy hvDirect hrest =>
        obtain ⟨rfl, mx, my, captureType, elemShape, typeShape,
            hmx, hmy, hmxPaths, hmyPaths, htypePaths,
            helemPaths, htypeShapePaths, hcap⟩ := ih hm hrest
        refine ⟨rfl,
          (fun path => Option.elim path x mx),
          (fun path => Option.elim path y my),
          (fun path => Option.elim path A captureType),
          (fun path => Option.elim path p elemShape),
          (fun path => Option.elim path a typeShape),
          hmx.var, hmy.var, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Pattern.varNPaths, List.map_append, List.map_map,
            List.map_cons, List.map_nil, List.reverse_cons]
          have hcomp :
              (fun path => Option.elim path x mx) ∘ some = mx := by
            funext path
            rfl
          rw [hcomp, hmxPaths]
          rfl
        · simp only [Pattern.varNPaths, List.map_append, List.map_map,
            List.map_cons, List.map_nil, List.reverse_cons]
          have hcomp :
              (fun path => Option.elim path y my) ∘ some = my := by
            funext path
            rfl
          rw [hcomp, hmyPaths]
          rfl
        · simp only [Pattern.varNPaths, List.map_append, List.map_map,
            List.map_cons, List.map_nil, List.reverse_cons]
          have hcomp :
              (fun path => Option.elim path A captureType) ∘ some =
                captureType := by
            funext path
            rfl
          rw [hcomp, htypePaths]
          rfl
        · simp only [Pattern.varNPaths, List.map_append, List.map_map,
            List.map_cons, List.map_nil, List.reverse_cons]
          have hcomp :
              (fun path => Option.elim path p elemShape) ∘ some =
                elemShape := by
            funext path
            rfl
          rw [hcomp, helemPaths]
          rfl
        · simp only [Pattern.varNPaths, List.map_append, List.map_map,
            List.map_cons, List.map_nil, List.reverse_cons]
          have hcomp :
              (fun path => Option.elim path a typeShape) ∘ some =
                typeShape := by
            funext path
            rfl
          rw [hcomp, htypeShapePaths]
          rfl
        · intro path
          cases path with
          | none =>
            exact ⟨TShape.LE.rfl, hp, htyLegacy, htyDirect,
              hxy, hvLegacy, hvDirect⟩
          | some path => exact hcap path

/-- Materialize an iota match with paired direct evidence for every
accumulated recursor argument and the established predecessor relation for
constructor fields.  This is the exact mixed-level payload needed by the Nat
successor branch: motives and recursive arguments stay guarded, while the
constructor predecessor remains in the ordinary inductive relation. -/
theorem LE_Interp.Matches.iota_materializeDirectRecAt
    {rec ctor ctor' : Name} {major arity n : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor' ctorShapes mctor)
    (hrecargs : LR.DirectCtorArgsDefEq (LRD Γ)
      recXs recYs recShapes)
    (hctorargs : LRS.CtorArgsDefEq (LR Γ)
      ctorXs ctorYs ctorShapes)
    (hMajorX : WHRedS Γ majorX
      (ctorXs.foldr (fun a f => f.app a) (.const ctor' ctorLs)))
    (hMajorY : WHRedS Γ majorY
      (ctorYs.foldr (fun a f => f.app a) (.const ctor' ctorLs'))) :
    ∃ mx my,
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs)))
        recLs mx ∧
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs')))
        recLs my ∧
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LR.DirectCaptureDefEqAt (n := n + 1) (LRD Γ)
            (mrec p) (mx path) (my path)
        | Sum.inr p => LRS.CaptureDefEqAt (n := n) (LR Γ)
            (mctor p) (mx path) (my path)) ∧
      WHRedS Γ
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorX)
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) ∧
      WHRedS Γ
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorY)
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) := by
  obtain ⟨_, mxf, myf, hmxf, hmyf, hcapf⟩ :=
    hmf.varN_materializeDirectAt (ls := recLs) (ls' := recLs)
      hrecargs
  obtain ⟨hctor, mxa, mya, hmxa, hmya, hcapa⟩ :=
    hma.varN_materializeAt (ls := ctorLs) (ls' := ctorLs') hctorargs
  subst ctor'
  refine ⟨Sum.elim mxf mxa, Sum.elim myf mya,
    hmxf.app hmxa, hmyf.app hmya, ?_, ?_, ?_⟩
  · intro path
    cases path with
    | inl path =>
      change LR.DirectCaptureDefEqAt (n := n + 1) (LRD Γ)
        (mrec path) (mxf path) (myf path)
      exact hcapf path
    | inr path =>
      change LRS.CaptureDefEqAt (n := n) (LR Γ)
        (mctor path) (mxa path) (mya path)
      exact hcapa path
  · exact hMajorX.major ⟨_, ⟨_, hpat⟩, _, _, .refl, _, _, hmxf⟩
  · exact hMajorY.major ⟨_, ⟨_, hpat⟩, _, _, .refl, _, _, hmyf⟩

/-- Materialize an iota match while preserving the literal aligned data of
every recursor-prefix capture.

The recursor side is built by `varN_materializeDirectAlignedAt`, so its
capture type and both shapes are never reselected.  Constructor fields stay
at predecessor level and use the established aligned witness selection.  In
the nullary-constructor case (notably `Nat.zero`) the latter branch is empty,
leaving the whole live capture inventory choice-free. -/
theorem LE_Interp.Matches.iota_materializeDirectRecAlignedAt
    {rec ctor ctor' : Name} {major arity n : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor' ctorShapes mctor)
    (hrecargs : LR.DirectCtorArgsDefEq (LRD Γ)
      recXs recYs recShapes)
    (hctorargs : LRS.CtorArgsDefEq (LR Γ)
      ctorXs ctorYs ctorShapes)
    (hMajorX : WHRedS Γ majorX
      (ctorXs.foldr (fun a f => f.app a) (.const ctor' ctorLs)))
    (hMajorY : WHRedS Γ majorY
      (ctorYs.foldr (fun a f => f.app a) (.const ctor' ctorLs'))) :
    ∃ (mx my captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (recElemShape recTypeShape :
        (Pattern.varN (.const rec) major).Path → WShape (n + 1)),
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs)))
        recLs mx ∧
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs')))
        recLs my ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => mx (.inl path)) = recXs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => my (.inl path)) = recYs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map recElemShape =
        recShapes.reverse ∧
      (∀ path : (Pattern.varN (.const rec) major).Path,
        LR.DirectCaptureDefEqAligned.AtShapes (n := n + 1) (LRD Γ)
          (mrec path) (mx (.inl path)) (my (.inl path))
          (captureType (.inl path)) (recElemShape path)
          (recTypeShape path)) ∧
      (∀ path : (Pattern.varN (.const ctor) arity).Path,
        LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor path) (mx (.inr path)) (my (.inr path))
          (captureType (.inr path))) ∧
      WHRedS Γ
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorX)
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) ∧
      WHRedS Γ
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorY)
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) := by
  obtain ⟨_, mxf, myf, recCaptureType, recElemShape, recTypeShape,
      hmxf, hmyf, hmxfPaths, hmyfPaths, helemPaths, hcapf⟩ :=
    hmf.varN_materializeDirectAlignedAt
      (ls := recLs) (ls' := recLs) hrecargs
  obtain ⟨hctor, mxa, mya, hmxa, hmya, hcapa⟩ :=
    hma.varN_materializeAt (ls := ctorLs) (ls' := ctorLs') hctorargs
  subst ctor'
  classical
  let captureType :
      (RecursorIotaPattern rec major ctor arity).Path → SExpr :=
    fun path => match path with
      | Sum.inl path => recCaptureType path
      | Sum.inr path =>
        (LRS.CaptureDefEqAt.witness (hcapa path)).typeExpr
  refine ⟨Sum.elim mxf mxa, Sum.elim myf mya, captureType,
    recElemShape, recTypeShape, hmxf.app hmxa, hmyf.app hmya,
    ?_, ?_, helemPaths, ?_, ?_, ?_, ?_⟩
  · simpa only [Sum.elim_inl] using hmxfPaths
  · simpa only [Sum.elim_inl] using hmyfPaths
  · intro path
    change LR.DirectCaptureDefEqAligned.AtShapes (n := n + 1) (LRD Γ)
      (mrec path) (mxf path) (myf path) (recCaptureType path)
      (recElemShape path) (recTypeShape path)
    exact hcapf path
  · intro path
    change LRS.CaptureDefEqAligned (n := n) (LR Γ)
      (mctor path) (mxa path) (mya path)
      (LRS.CaptureDefEqAt.witness (hcapa path)).typeExpr
    exact (LRS.CaptureDefEqAt.witness (hcapa path)).aligned
  · exact hMajorX.major ⟨_, ⟨_, hpat⟩, _, _, .refl, _, _, hmxf⟩
  · exact hMajorY.major ⟨_, ⟨_, hpat⟩, _, _, .refl, _, _, hmyf⟩

/-- Iota materialization from an explicitly listed recursor-prefix payload.
All five recursor capture maps are returned with their canonical readback
equations; constructor fields retain the established predecessor-level
aligned witnesses. -/
theorem LE_Interp.Matches.iota_materializeDirectRecListedAt
    {rec ctor ctor' : Name} {major arity n : Nat}
    {recShapes recTypeShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs recTypes ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor' ctorShapes mctor)
    (hrecargs : LR.DirectCtorArgsDefEqListed (LRD Γ)
      recXs recYs recTypes recShapes recTypeShapes)
    (hctorargs : LRS.CtorArgsDefEq (LR Γ)
      ctorXs ctorYs ctorShapes)
    (hMajorX : WHRedS Γ majorX
      (ctorXs.foldr (fun a f => f.app a) (.const ctor' ctorLs)))
    (hMajorY : WHRedS Γ majorY
      (ctorYs.foldr (fun a f => f.app a) (.const ctor' ctorLs'))) :
    ∃ (mx my captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (recElemShape recTypeShape :
        (Pattern.varN (.const rec) major).Path → WShape (n + 1)),
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) recLs mx ∧
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) recLs my ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => mx (.inl path)) = recXs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => my (.inl path)) = recYs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => captureType (.inl path)) = recTypes.reverse ∧
      (Pattern.varNPaths (.const rec) major).map recElemShape =
        recShapes.reverse ∧
      (Pattern.varNPaths (.const rec) major).map recTypeShape =
        recTypeShapes.reverse ∧
      (∀ path : (Pattern.varN (.const rec) major).Path,
        LR.DirectCaptureDefEqAligned.AtShapes (n := n + 1) (LRD Γ)
          (mrec path) (mx (.inl path)) (my (.inl path))
          (captureType (.inl path)) (recElemShape path)
          (recTypeShape path)) ∧
      (∀ path : (Pattern.varN (.const ctor) arity).Path,
        LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor path) (mx (.inr path)) (my (.inr path))
          (captureType (.inr path))) ∧
      WHRedS Γ
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorX)
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) ∧
      WHRedS Γ
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorY)
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) := by
  obtain ⟨_, mxf, myf, recCaptureType, recElemShape, recTypeShape,
      hmxf, hmyf, hmxfPaths, hmyfPaths, htypePaths,
      helemPaths, htypeShapePaths, hcapf⟩ :=
    hmf.varN_materializeDirectListedAt
      (ls := recLs) (ls' := recLs) hrecargs
  obtain ⟨hctor, mxa, mya, hmxa, hmya, hcapa⟩ :=
    hma.varN_materializeAt (ls := ctorLs) (ls' := ctorLs') hctorargs
  subst ctor'
  classical
  let captureType :
      (RecursorIotaPattern rec major ctor arity).Path → SExpr :=
    fun path => match path with
      | Sum.inl path => recCaptureType path
      | Sum.inr path =>
        (LRS.CaptureDefEqAt.witness (hcapa path)).typeExpr
  refine ⟨Sum.elim mxf mxa, Sum.elim myf mya, captureType,
    recElemShape, recTypeShape, hmxf.app hmxa, hmyf.app hmya,
    ?_, ?_, ?_, helemPaths, htypeShapePaths, ?_, ?_, ?_, ?_⟩
  · simpa only [Sum.elim_inl] using hmxfPaths
  · simpa only [Sum.elim_inl] using hmyfPaths
  · simpa only [captureType] using htypePaths
  · intro path
    change LR.DirectCaptureDefEqAligned.AtShapes (n := n + 1) (LRD Γ)
      (mrec path) (mxf path) (myf path) (recCaptureType path)
      (recElemShape path) (recTypeShape path)
    exact hcapf path
  · intro path
    change LRS.CaptureDefEqAligned (n := n) (LR Γ)
      (mctor path) (mxa path) (mya path)
      (LRS.CaptureDefEqAt.witness (hcapa path)).typeExpr
    exact (LRS.CaptureDefEqAt.witness (hcapa path)).aligned
  · exact hMajorX.major ⟨_, ⟨_, hpat⟩, _, _, .refl, _, _, hmxf⟩
  · exact hMajorY.major ⟨_, ⟨_, hpat⟩, _, _, .refl, _, _, hmyf⟩

/-- Fully listed iota materialization when both the recursor prefix and the
constructor fields already carry paired guarded evidence.

The constructor half deliberately remains at level `n`, but unlike the
legacy mixed materializer it exposes the exact field types and both semantic
shape lists.  A framed unary constructor can therefore rebuild its root
field relation once and let the generated RHS consume that same selected
predecessor without an existential re-selection. -/
theorem LE_Interp.Matches.iota_materializeDirectListedAt
    {rec ctor ctor' : Name} {major arity n : Nat}
    {recShapes recTypeShapes : List (WShape (n + 1))}
    {ctorShapes ctorTypeShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs recTypes ctorXs ctorYs ctorTypes : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor' ctorShapes mctor)
    (hrecargs : LR.DirectCtorArgsDefEqListed (LRD Γ)
      recXs recYs recTypes recShapes recTypeShapes)
    (hctorargs : LR.DirectCtorArgsDefEqListed (LRD Γ)
      ctorXs ctorYs ctorTypes ctorShapes ctorTypeShapes)
    (hMajorX : WHRedS Γ majorX
      (ctorXs.foldr (fun a f => f.app a) (.const ctor' ctorLs)))
    (hMajorY : WHRedS Γ majorY
      (ctorYs.foldr (fun a f => f.app a) (.const ctor' ctorLs'))) :
    ∃ (mx my captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (recElemShape recTypeShape :
        (Pattern.varN (.const rec) major).Path → WShape (n + 1))
      (ctorElemShape ctorTypeShape :
        (Pattern.varN (.const ctor) arity).Path → WShape n),
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) recLs mx ∧
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) recLs my ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => mx (.inl path)) = recXs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => my (.inl path)) = recYs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => captureType (.inl path)) = recTypes.reverse ∧
      (Pattern.varNPaths (.const rec) major).map recElemShape =
        recShapes.reverse ∧
      (Pattern.varNPaths (.const rec) major).map recTypeShape =
        recTypeShapes.reverse ∧
      (Pattern.varNPaths (.const ctor) arity).map
        (fun path => mx (.inr path)) = ctorXs.reverse ∧
      (Pattern.varNPaths (.const ctor) arity).map
        (fun path => my (.inr path)) = ctorYs.reverse ∧
      (Pattern.varNPaths (.const ctor) arity).map
        (fun path => captureType (.inr path)) = ctorTypes.reverse ∧
      (Pattern.varNPaths (.const ctor) arity).map ctorElemShape =
        ctorShapes.reverse ∧
      (Pattern.varNPaths (.const ctor) arity).map ctorTypeShape =
        ctorTypeShapes.reverse ∧
      (∀ path : (Pattern.varN (.const rec) major).Path,
        LR.DirectCaptureDefEqAligned.AtShapes (n := n + 1) (LRD Γ)
          (mrec path) (mx (.inl path)) (my (.inl path))
          (captureType (.inl path)) (recElemShape path)
          (recTypeShape path)) ∧
      (∀ path : (Pattern.varN (.const ctor) arity).Path,
        LR.DirectCaptureDefEqAligned.AtShapes (n := n) (LRD Γ)
          (mctor path) (mx (.inr path)) (my (.inr path))
          (captureType (.inr path)) (ctorElemShape path)
          (ctorTypeShape path)) ∧
      WHRedS Γ
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorX)
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) ∧
      WHRedS Γ
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorY)
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) := by
  obtain ⟨_, mxf, myf, recCaptureType, recElemShape, recTypeShape,
      hmxf, hmyf, hmxfPaths, hmyfPaths, hrecTypePaths,
      hrecElemPaths, hrecTypeShapePaths, hcapf⟩ :=
    hmf.varN_materializeDirectListedAt
      (ls := recLs) (ls' := recLs) hrecargs
  obtain ⟨hctor, mxa, mya, ctorCaptureType, ctorElemShape,
      ctorTypeShape, hmxa, hmya, hmxaPaths, hmyaPaths, hctorTypePaths,
      hctorElemPaths, hctorTypeShapePaths, hcapa⟩ :=
    hma.varN_materializeDirectListedAt
      (ls := ctorLs) (ls' := ctorLs') hctorargs
  subst ctor'
  let mx := Sum.elim mxf mxa
  let my := Sum.elim myf mya
  let captureType := Sum.elim recCaptureType ctorCaptureType
  refine ⟨mx, my, captureType, recElemShape, recTypeShape,
    ctorElemShape, ctorTypeShape, hmxf.app hmxa, hmyf.app hmya,
    ?_, ?_, ?_, hrecElemPaths, hrecTypeShapePaths,
    ?_, ?_, ?_, hctorElemPaths, hctorTypeShapePaths,
    ?_, ?_, ?_, ?_⟩
  · simpa only [mx, Sum.elim_inl] using hmxfPaths
  · simpa only [my, Sum.elim_inl] using hmyfPaths
  · simpa only [captureType, Sum.elim_inl] using hrecTypePaths
  · simpa only [mx, Sum.elim_inr] using hmxaPaths
  · simpa only [my, Sum.elim_inr] using hmyaPaths
  · simpa only [captureType, Sum.elim_inr] using hctorTypePaths
  · intro path
    simpa only [mx, my, captureType, Sum.elim_inl] using hcapf path
  · intro path
    simpa only [mx, my, captureType, Sum.elim_inr] using hcapa path
  · exact hMajorX.major ⟨_, ⟨_, hpat⟩, _, _, .refl, _, _, hmxf⟩
  · exact hMajorY.major ⟨_, ⟨_, hpat⟩, _, _, .refl, _, _, hmyf⟩

/--
info: 'Lean4Lean.SExpr.LR.DirectCtorArgsDefEq.left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCtorArgsDefEq.left

/--
info: 'Lean4Lean.SExpr.LR.DirectCtorArgsDefEq.right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCtorArgsDefEq.right

/--
info: 'Lean4Lean.SExpr.LR.DirectCtorArgsDefEqListed.left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCtorArgsDefEqListed.left

/--
info: 'Lean4Lean.SExpr.LR.DirectCtorArgsDefEqListed.right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCtorArgsDefEqListed.right

/--
info: 'Lean4Lean.SExpr.LE_Interp.Matches.varN_materializeDirectAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.Matches.varN_materializeDirectAt

/--
info: 'Lean4Lean.SExpr.LE_Interp.Matches.varN_materializeDirectAlignedAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.Matches.varN_materializeDirectAlignedAt

/--
info: 'Lean4Lean.SExpr.LE_Interp.Matches.varN_materializeDirectListedAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.Matches.varN_materializeDirectListedAt

/--
info: 'Lean4Lean.SExpr.LE_Interp.Matches.iota_materializeDirectRecAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.Matches.iota_materializeDirectRecAt

/--
info: 'Lean4Lean.SExpr.LE_Interp.Matches.iota_materializeDirectRecAlignedAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.Matches.iota_materializeDirectRecAlignedAt

/--
info: 'Lean4Lean.SExpr.LE_Interp.Matches.iota_materializeDirectRecListedAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.Matches.iota_materializeDirectRecListedAt

/--
info: 'Lean4Lean.SExpr.LE_Interp.Matches.iota_materializeDirectListedAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.Matches.iota_materializeDirectListedAt

/-- A pattern-leaf spine whose established projection and guarded action
share the same syntactic and semantic endpoints.  The complete direct
argument list is retained in addition to the final Pi edge, so a generated
RHS can reuse any earlier recursor capture without reselecting evidence. -/
structure LR.DirectPatternLeafSpine (Γ : List SExpr)
    (IH : LR.DirectRelBase Γ n)
    (Head : SExpr) (args args' : List SExpr)
    (rargs : List (WShape n)) (A : SExpr)
    (out outTy : WShape n) where
  legacy : LR.PatternLeafSpine Γ (LR Γ)
    Head args args' rargs A out outTy
  directArgs : LR.DirectCtorArgsDefEq IH args args' rargs
  majorType : IH.TyDefEq legacy.pair.domain legacy.pair.domain
    legacy.majorTypeShape
  majorRel : IH.DefEq legacy.majorX legacy.majorY legacy.pair.domain
    legacy.majorShape legacy.majorTypeShape
  pi : LR.DirectPiDefEq IH legacy.pair.domain legacy.pair.codomain
    legacy.pair.codomain legacy.majorTypeShape legacy.resultTypeShape

/-- The registered constant type at the exact guarded root shape used by
the direct application spine.

The semantic witness and guarded type relation are deliberately indexed by
the same literal `WShape`.  A reached pattern leaf may therefore inspect the
registered type telescope without pairing an independently selected semantic
typing with the direct Pi decomposition that generated its captures. -/
structure LR.DirectRegisteredTypeRoot (Γ : List SExpr) (ρ : Valuation)
    (headType : SExpr) : Type where
  level : Nat
  domain : WShape level
  codomain : WShapeFun level
  witness : LE_Interp.Witness ρ
    (WShape.forallE domain codomain).T headType
  related : (LRD Γ).TyDefEq headType headType
    (.forallE domain codomain)

/-- The registered type decomposition followed by the direct constant
evaluator, with every application layer retained at the exact shapes used by
that evaluator.

The argument level is fixed by the registered root.  The type observation
has its own level: the root Pi lives one level above its domain, while later
Pi observations may be exposed at the common argument level and therefore
lift their domains before accepting the next argument.  The result syntax is
kept as an explicit index because the right rectangle row is transported to
the evaluator's left-oriented dependent result rather than being
definitionally `F.inst y`. -/
inductive LR.DirectRegisteredTypeTrace (Γ : List SExpr) (ρ : Valuation)
    (headType : SExpr) :
    {argLevel : Nat} →
      List SExpr → List SExpr → List (WShape argLevel) → SExpr →
      {typeLevel : Nat} → WShape typeLevel → Type where
  | nil (registered : LR.DirectRegisteredTypeRoot Γ ρ headType) :
      LR.DirectRegisteredTypeTrace Γ ρ headType
        (argLevel := registered.level)
        [] [] [] headType
        (.forallE registered.domain registered.codomain)
  | cons
      {argLevel domainLevel : Nat}
      {xs ys : List SExpr} {ps : List (WShape argLevel)}
      {A B F result x y : SExpr}
      {domain : WShape domainLevel} {codomain : WShapeFun domainLevel}
      {p : WShape argLevel} {u vX vY : SLevel}
      (levelLE : domainLevel ≤ argLevel)
      (previous : LR.DirectRegisteredTypeTrace Γ ρ headType
        xs ys ps A (.forallE domain codomain))
      (path : TypeDefEqPath Γ A (.forallE B F) u)
      (hasType : p.HasType (domain.lift argLevel))
      (typeRelatedLegacy : (LR Γ).TyDefEq B B (domain.lift argLevel))
      (typeRelatedDirect : (LRD Γ).TyDefEq B B (domain.lift argLevel))
      (defeq : IsDefEq Γ x y B)
      (relatedLegacy : (LR Γ).DefEq x y B p (domain.lift argLevel))
      (relatedDirect : (LRD Γ).DefEq x y B p (domain.lift argLevel))
      (resultX : IsDefEq Γ (F.inst x) result (.sort vX))
      (resultY : IsDefEq Γ (F.inst y) result (.sort vY))
      (resultRelated : (LRD Γ).TyDefEq result result
        ((codomain.lift argLevel).app p)) :
      LR.DirectRegisteredTypeTrace Γ ρ headType
        (x :: xs) (y :: ys) (p :: ps) result
        ((codomain.lift argLevel).app p)

/-- Add an application whose Pi domain already lives at the trace's common
argument level.  This is the registered root step; the general constructor
above handles later Pi observations whose domains require a canonical
lift. -/
noncomputable def LR.DirectRegisteredTypeTrace.consSelf
    {n : Nat} {xs ys : List SExpr} {ps : List (WShape n)}
    {A B F result x y : SExpr} {domain : WShape n}
    {codomain : WShapeFun n} {p : WShape n} {u vX vY : SLevel}
    (previous : LR.DirectRegisteredTypeTrace Γ ρ headType
      xs ys ps A (.forallE domain codomain))
    (path : TypeDefEqPath Γ A (.forallE B F) u)
    (hasType : p.HasType domain)
    (typeRelatedLegacy : (LR Γ).TyDefEq B B domain)
    (typeRelatedDirect : (LRD Γ).TyDefEq B B domain)
    (defeq : IsDefEq Γ x y B)
    (relatedLegacy : (LR Γ).DefEq x y B p domain)
    (relatedDirect : (LRD Γ).DefEq x y B p domain)
    (resultX : IsDefEq Γ (F.inst x) result (.sort vX))
    (resultY : IsDefEq Γ (F.inst y) result (.sort vY))
    (resultRelated : (LRD Γ).TyDefEq result result (codomain.app p)) :
    LR.DirectRegisteredTypeTrace Γ ρ headType
      (x :: xs) (y :: ys) (p :: ps) result (codomain.app p) := by
  have hasType' : p.HasType (domain.lift n) := by
    simpa only [WShape.lift_self] using hasType
  have typeRelatedLegacy' : (LR Γ).TyDefEq B B (domain.lift n) := by
    simpa only [WShape.lift_self] using typeRelatedLegacy
  have typeRelatedDirect' : (LRD Γ).TyDefEq B B (domain.lift n) := by
    simpa only [WShape.lift_self] using typeRelatedDirect
  have relatedLegacy' : (LR Γ).DefEq x y B p (domain.lift n) := by
    simpa only [WShape.lift_self] using relatedLegacy
  have relatedDirect' : (LRD Γ).DefEq x y B p (domain.lift n) := by
    simpa only [WShape.lift_self] using relatedDirect
  have resultRelated' : (LRD Γ).TyDefEq result result
      ((codomain.lift n).app p) := by
    simpa only [WShapeFun.lift_self] using resultRelated
  simpa only [WShapeFun.lift_self] using
    LR.DirectRegisteredTypeTrace.cons (Nat.le_refl n) previous path
      hasType' typeRelatedLegacy' typeRelatedDirect' defeq relatedLegacy'
      relatedDirect' resultX resultY resultRelated'

/-- Recover the exact registered root retained by an application trace. -/
noncomputable def LR.DirectRegisteredTypeTrace.registeredRoot
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType xs ys ps A outTy) :
    LR.DirectRegisteredTypeRoot Γ ρ headType := by
  induction H with
  | nil registered => exact registered
  | cons _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- The exact semantic witness at an empty registered trace.  Unlike
`registeredRoot`, this projection keeps the trace's terminal type-shape index
in its result, which is essential when a consumer peels the registered Pi
telescope without reselecting a root observation. -/
def LR.DirectRegisteredTypeTrace.nilWitness
    {argLevel typeLevel : Nat} {A : SExpr} {outTy : WShape typeLevel}
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType
      (argLevel := argLevel)
      [] [] [] A outTy) :
    LE_Interp.Witness ρ outTy.T A := by
  cases H with
  | nil registered => exact registered.witness

/-- An empty registered trace has not changed the registered type syntax. -/
theorem LR.DirectRegisteredTypeTrace.nilResult_eq
    {argLevel typeLevel : Nat} {A : SExpr} {outTy : WShape typeLevel}
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType
      (argLevel := argLevel) [] [] [] A outTy) :
    A = headType := by
  cases H
  rfl

/-- Forget a registered-type trace to its synchronized direct argument
payload. -/
theorem LR.DirectRegisteredTypeTrace.directArgs
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType xs ys ps A outTy) :
    LR.DirectCtorArgsDefEq (LRD Γ) xs ys ps := by
  induction H with
  | nil _ => exact .nil
  | cons _ _ _ hp htyLegacy htyDirect hxy hvLegacy hvDirect _ _ _ ih =>
      exact .cons hp htyLegacy htyDirect hxy hvLegacy hvDirect ih

/-- Keep the left endpoint of every exact registered-type application
layer.  Both dependent result transports reuse the left result edge, so the
trace keeps its original left-oriented terminal type. -/
noncomputable def LR.DirectRegisteredTypeTrace.left
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType xs ys ps A outTy) :
    LR.DirectRegisteredTypeTrace Γ ρ headType xs xs ps A outTy := by
  induction H with
  | nil registered => exact .nil registered
  | cons levelLE previous path hp htyLegacy htyDirect hxy hvLegacy hvDirect
      resultX resultY resultRelated ih =>
    exact .cons levelLE ih path hp htyLegacy htyDirect hxy.hasType.1
      ((LR Γ).left hvLegacy) (LRD.DefEq.left hvDirect)
      resultX resultX resultRelated

/-- Keep the right endpoint of every exact registered-type application
layer while retaining the evaluator's left-oriented terminal type through
the stored right-to-result conversion. -/
noncomputable def LR.DirectRegisteredTypeTrace.right
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType xs ys ps A outTy) :
    LR.DirectRegisteredTypeTrace Γ ρ headType ys ys ps A outTy := by
  induction H with
  | nil registered => exact .nil registered
  | cons levelLE previous path hp htyLegacy htyDirect hxy hvLegacy hvDirect
      resultX resultY resultRelated ih =>
    exact .cons levelLE ih path hp htyLegacy htyDirect hxy.hasType.2
      ((LR Γ).left ((LR Γ).symm hvLegacy))
      (LRD.DefEq.left (LRD.DefEq.symm hvDirect))
      resultY resultY resultRelated

/-- Data-valued inversion of one nonempty registered-type application
trace.  Unlike inversion through the proposition-valued argument relation,
this view preserves the literal Pi domain which accepted the head argument
and the previous trace which produced that Pi observation. -/
structure LR.DirectRegisteredTypeTrace.ConsView
    (Γ : List SExpr) (ρ : Valuation) (headType : SExpr)
    {n outLevel : Nat} (x y : SExpr) (xs ys : List SExpr)
    (p : WShape n) (ps : List (WShape n)) (result : SExpr)
    (outTy : WShape outLevel)
    (_H : LR.DirectRegisteredTypeTrace Γ ρ headType
      (x :: xs) (y :: ys) (p :: ps) result outTy) where
  domainLevel : Nat
  previousType : SExpr
  domainExpr : SExpr
  bodyExpr : SExpr
  domain : WShape domainLevel
  codomain : WShapeFun domainLevel
  pathSort : SLevel
  resultSortX : SLevel
  resultSortY : SLevel
  levelLE : domainLevel ≤ n
  previous : LR.DirectRegisteredTypeTrace Γ ρ headType
    xs ys ps previousType (.forallE domain codomain)
  path : TypeDefEqPath Γ previousType
    (.forallE domainExpr bodyExpr) pathSort
  hasType : p.HasType (domain.lift n)
  typeRelatedLegacy : (LR Γ).TyDefEq domainExpr domainExpr
    (domain.lift n)
  typeRelatedDirect : (LRD Γ).TyDefEq domainExpr domainExpr
    (domain.lift n)
  defeq : IsDefEq Γ x y domainExpr
  relatedLegacy : (LR Γ).DefEq x y domainExpr p (domain.lift n)
  relatedDirect : (LRD Γ).DefEq x y domainExpr p (domain.lift n)
  resultX : IsDefEq Γ (bodyExpr.inst x) result (.sort resultSortX)
  resultY : IsDefEq Γ (bodyExpr.inst y) result (.sort resultSortY)
  resultRelated : (LRD Γ).TyDefEq result result
    ((codomain.lift n).app p)
  outLevel_eq : outLevel = n
  outTy_eq : outTy.T = ((codomain.lift n).app p).T

/-- A nonempty registered-type trace has a proof-relevant one-layer view.
The proposition-valued existence proof is the safe elimination boundary for
the indexed trace; `consView` below chooses its data-valued representative. -/
theorem LR.DirectRegisteredTypeTrace.consView_nonempty
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType
      (x :: xs) (y :: ys) (p :: ps) result outTy) :
    Nonempty (LR.DirectRegisteredTypeTrace.ConsView
      Γ ρ headType x y xs ys p ps result outTy H) := by
  cases H with
  | cons levelLE previous path hp htyLegacy htyDirect hxy hvLegacy
      hvDirect resultX resultY resultRelated =>
    exact ⟨{
      domainLevel := _
      previousType := _
      domainExpr := _
      bodyExpr := _
      domain := _
      codomain := _
      pathSort := _
      resultSortX := _
      resultSortY := _
      levelLE
      previous
      path
      hasType := hp
      typeRelatedLegacy := htyLegacy
      typeRelatedDirect := htyDirect
      defeq := hxy
      relatedLegacy := hvLegacy
      relatedDirect := hvDirect
      resultX
      resultY
      resultRelated
      outLevel_eq := rfl
      outTy_eq := rfl }⟩

/-- Peel one exact application layer from a nonempty registered-type trace. -/
noncomputable def LR.DirectRegisteredTypeTrace.consView
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType
      (x :: xs) (y :: ys) (p :: ps) result outTy) :
    LR.DirectRegisteredTypeTrace.ConsView
      Γ ρ headType x y xs ys p ps result outTy H :=
  Classical.choice H.consView_nonempty

/-- Reuse one exact registered application layer as a guarded capture at
the literal argument/domain shapes retained by the trace.  Only the semantic
pattern bound is supplied by the caller; every typing and relational field
comes from the registered Pi application itself. -/
theorem LR.DirectRegisteredTypeTrace.ConsView.captureAtShapes
    {Γ : List SExpr} {ρ : Valuation} {headType : SExpr}
    {n outLevel : Nat} {x y result : SExpr} {xs ys : List SExpr}
    {p : WShape n} {ps : List (WShape n)} {outTy : WShape outLevel}
    {trace : LR.DirectRegisteredTypeTrace Γ ρ headType
      (x :: xs) (y :: ys) (p :: ps) result outTy}
    {m : TShape}
    (H : LR.DirectRegisteredTypeTrace.ConsView
      (n := n) (outLevel := outLevel)
      Γ ρ headType x y xs ys p ps result outTy trace)
    (hshape : m ≤ p.T) :
    LR.DirectCaptureDefEqAligned.AtShapes (n := n) (LRD Γ)
      m x y H.domainExpr p (H.domain.lift n) :=
  ⟨hshape, H.hasType, H.typeRelatedLegacy, H.typeRelatedDirect,
    H.defeq, H.relatedLegacy, H.relatedDirect⟩

/-- Follow one registered Pi layer semantically after lifting it to a larger
argument level.  The caller may supply any argument above the trace's
selected one; monotonicity of the registered codomain then lowers the body
witness to the lifted exact output retained by the trace. -/
noncomputable def LR.DirectRegisteredTypeTrace.ConsView.bodyWitnessLift
    {Γ : List SExpr} {traceρ ρ : Valuation} {headType : SExpr}
    {n outLevel targetLevel : Nat}
    {x y result : SExpr} {xs ys : List SExpr}
    {p : WShape n} {ps : List (WShape n)} {outTy : WShape outLevel}
    {trace : LR.DirectRegisteredTypeTrace Γ traceρ headType
      (x :: xs) (y :: ys) (p :: ps) result outTy}
    (H : LR.DirectRegisteredTypeTrace.ConsView
      (n := n) (outLevel := outLevel)
      Γ traceρ headType x y xs ys p ps result outTy trace)
    (levelLE : n ≤ targetLevel)
    {B F : SExpr}
    (root : LE_Interp.Witness ρ
      (WShape.forallE (H.domain.lift targetLevel)
        (H.codomain.lift targetLevel)).T
      (.forallE B F))
    (q : WShape targetLevel) (hpq : p.lift targetLevel ≤ q) :
    LE_Interp.Witness (ρ.push q.T) (outTy.lift targetLevel).T F := by
  have houtLevelLE : outLevel ≤ targetLevel := by
    rw [H.outLevel_eq]
    exact levelLE
  have hdomainLevelLE : H.domainLevel ≤ targetLevel :=
    Nat.le_trans H.levelLE levelLE
  have hselected : (outTy.lift targetLevel).T ≤
      ((H.codomain.lift targetLevel).app (p.lift targetLevel)).T := by
    refine (TShape.lift_eqv (a := outTy.T) houtLevelLE).1 |>.trans ?_
    have houtEq : outTy.T ≤ ((H.codomain.lift n).app p).T := by
      rw [H.outTy_eq]
      exact TShape.LE.rfl
    refine houtEq.trans ?_
    have happLevelLE : (((H.codomain.lift n).app p).T).1 ≤ targetLevel := by
      exact levelLE
    refine (TShape.lift_eqv
      (a := ((H.codomain.lift n).app p).T) happLevelLE).2.trans ?_
    rw [WShapeFun.lift_app levelLE,
      WShapeFun.lift_lift (.inl H.levelLE)]
    exact TShape.LE.rfl
  exact (root.forallE_inv'.2 q).mono
    (hselected.trans (WShapeFun.app_mono_r hpq).T)

/-- Follow one registered Pi layer at the trace's existing argument level.
This exact-level form packages the `lift_self` transports needed by
`bodyWitnessLift`. -/
noncomputable def LR.DirectRegisteredTypeTrace.ConsView.bodyWitnessSelf
    {Γ : List SExpr} {traceρ ρ : Valuation} {headType : SExpr}
    {n outLevel : Nat}
    {x y result : SExpr} {xs ys : List SExpr}
    {p : WShape n} {ps : List (WShape n)} {outTy : WShape outLevel}
    {trace : LR.DirectRegisteredTypeTrace Γ traceρ headType
      (x :: xs) (y :: ys) (p :: ps) result outTy}
    (H : LR.DirectRegisteredTypeTrace.ConsView
      (n := n) (outLevel := outLevel)
      Γ traceρ headType x y xs ys p ps result outTy trace)
    {B F : SExpr}
    (root : LE_Interp.Witness ρ
      (WShape.forallE (H.domain.lift n)
        (H.codomain.lift n)).T
      (.forallE B F))
    (q : WShape n) (hpq : p ≤ q) :
    LE_Interp.Witness (ρ.push q.T) outTy.T F := by
  have houtLevel_eq : outLevel = n := H.outLevel_eq
  subst outLevel
  have hpq' : p.lift n ≤ q := by
    simpa only [WShape.lift_self] using hpq
  simpa only [WShape.lift_self] using
    H.bodyWitnessLift (Nat.le_refl n) root q hpq'

/-- Short name for the exact one-layer view of a nonempty trace. -/
abbrev LR.DirectRegisteredTypeTrace.HeadView
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType
      (x :: xs) (y :: ys) (p :: ps) result outTy) : Type :=
  LR.DirectRegisteredTypeTrace.ConsView
    Γ ρ headType x y xs ys p ps result outTy H

/-- Four exact applications above a registered Pi root.  Nat recursor
leaves have precisely this shape: the constructor major is the newest
layer, followed by the successor minor, zero minor, and motive. -/
structure LR.DirectRegisteredTypeTrace.FourView
    {n outLevel : Nat}
    {x₄ x₃ x₂ x₁ y₄ y₃ y₂ y₁ result : SExpr}
    {p₄ p₃ p₂ p₁ : WShape n} {outTy : WShape outLevel}
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType
      [x₄, x₃, x₂, x₁] [y₄, y₃, y₂, y₁]
      [p₄, p₃, p₂, p₁] result outTy) where
  fourth : LR.DirectRegisteredTypeTrace.HeadView H
  third : LR.DirectRegisteredTypeTrace.HeadView fourth.previous
  second : LR.DirectRegisteredTypeTrace.HeadView third.previous
  first : LR.DirectRegisteredTypeTrace.HeadView second.previous

/-- The four registered application layers as one explicitly listed direct
argument payload.  Every type expression and type shape is the literal Pi
domain retained by the corresponding `ConsView`. -/
def LR.DirectRegisteredTypeTrace.FourView.directArgsListed
    {n outLevel : Nat}
    {x₄ x₃ x₂ x₁ y₄ y₃ y₂ y₁ resultExpr : SExpr}
    {p₄ p₃ p₂ p₁ : WShape n} {outTy : WShape outLevel}
    {H : LR.DirectRegisteredTypeTrace Γ ρ headType
      [x₄, x₃, x₂, x₁] [y₄, y₃, y₂, y₁]
      [p₄, p₃, p₂, p₁] resultExpr outTy}
    (view : LR.DirectRegisteredTypeTrace.FourView H) :
    LR.DirectCtorArgsDefEqListed (LRD Γ)
      [x₄, x₃, x₂, x₁] [y₄, y₃, y₂, y₁]
      [view.fourth.domainExpr, view.third.domainExpr,
        view.second.domainExpr, view.first.domainExpr]
      [p₄, p₃, p₂, p₁]
      [view.fourth.domain.lift n, view.third.domain.lift n,
        view.second.domain.lift n, view.first.domain.lift n] :=
  .cons view.fourth.hasType view.fourth.typeRelatedLegacy
    view.fourth.typeRelatedDirect view.fourth.defeq
    view.fourth.relatedLegacy view.fourth.relatedDirect <|
  .cons view.third.hasType view.third.typeRelatedLegacy
    view.third.typeRelatedDirect view.third.defeq
    view.third.relatedLegacy view.third.relatedDirect <|
  .cons view.second.hasType view.second.typeRelatedLegacy
    view.second.typeRelatedDirect view.second.defeq
    view.second.relatedLegacy view.second.relatedDirect <|
  .cons view.first.hasType view.first.typeRelatedLegacy
    view.first.typeRelatedDirect view.first.defeq
    view.first.relatedLegacy view.first.relatedDirect .nil

/-- The three recursor-prefix layers of a registered four-application trace,
dropping only the newest constructor major.  For Nat these are, newest first,
the successor minor, zero minor, and motive. -/
def LR.DirectRegisteredTypeTrace.FourView.recArgsListed
    {n outLevel : Nat}
    {x₄ x₃ x₂ x₁ y₄ y₃ y₂ y₁ resultExpr : SExpr}
    {p₄ p₃ p₂ p₁ : WShape n} {outTy : WShape outLevel}
    {H : LR.DirectRegisteredTypeTrace Γ ρ headType
      [x₄, x₃, x₂, x₁] [y₄, y₃, y₂, y₁]
      [p₄, p₃, p₂, p₁] resultExpr outTy}
    (view : LR.DirectRegisteredTypeTrace.FourView H) :
    LR.DirectCtorArgsDefEqListed (LRD Γ)
      [x₃, x₂, x₁] [y₃, y₂, y₁]
      [view.third.domainExpr, view.second.domainExpr,
        view.first.domainExpr]
      [p₃, p₂, p₁]
      [view.third.domain.lift n, view.second.domain.lift n,
        view.first.domain.lift n] :=
  .cons view.third.hasType view.third.typeRelatedLegacy
    view.third.typeRelatedDirect view.third.defeq
    view.third.relatedLegacy view.third.relatedDirect <|
  .cons view.second.hasType view.second.typeRelatedLegacy
    view.second.typeRelatedDirect view.second.defeq
    view.second.relatedLegacy view.second.relatedDirect <|
  .cons view.first.hasType view.first.typeRelatedLegacy
    view.first.typeRelatedDirect view.first.defeq
    view.first.relatedLegacy view.first.relatedDirect .nil

/-- The sparse three-binder telescope selected by the oldest three layers
of a four-application registered trace.  Each retained branch is lifted just
far enough to contain the already-built inner telescope; the supplied result
is the observation obtained after specializing the fourth (major) layer. -/
def LR.DirectRegisteredTypeTrace.FourView.sparsePrefix
    {n outLevel : Nat}
    {x₄ x₃ x₂ x₁ y₄ y₃ y₂ y₁ resultExpr : SExpr}
    {p₄ p₃ p₂ p₁ : WShape n} {outTy : WShape outLevel}
    {H : LR.DirectRegisteredTypeTrace Γ ρ headType
      [x₄, x₃, x₂, x₁] [y₄, y₃, y₂, y₁]
      [p₄, p₃, p₂, p₁] resultExpr outTy}
    (view : LR.DirectRegisteredTypeTrace.FourView H)
    (result : WShape n) : WShape (n + 3) :=
  .forallE (view.first.domain.lift (n + 2))
    (.single (p₁.lift (n + 2)) <|
      .forallE (view.second.domain.lift (n + 1))
        (.single (p₂.lift (n + 1)) <|
          .forallE (view.third.domain.lift n)
            (.single p₃ result)))

/-- Peel all four layers of an exact four-argument registered-type trace. -/
noncomputable def LR.DirectRegisteredTypeTrace.fourView
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType
      [x₄, x₃, x₂, x₁] [y₄, y₃, y₂, y₁]
      [p₄, p₃, p₂, p₁] result outTy) :
    LR.DirectRegisteredTypeTrace.FourView H := by
  let fourth := H.consView
  let third := fourth.previous.consView
  let second := third.previous.consView
  let first := second.previous.consView
  exact { fourth, third, second, first }

/-- Eliminate a trace whose tail lists all have length three into its four
literal newest-first layers.  The continuation form performs the dependent
list substitutions once, exposing both the transported trace and its exact
four-layer view without storing equality casts in later native-site data. -/
theorem LR.DirectRegisteredTypeTrace.fourViewElim_of_tail_lengths
    {n outLevel : Nat} {x₄ y₄ result : SExpr}
    {xs ys : List SExpr} {p₄ : WShape n} {ps : List (WShape n)}
    {outTy : WShape outLevel}
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType
      (x₄ :: xs) (y₄ :: ys) (p₄ :: ps) result outTy)
    (hxs : xs.length = 3) (hys : ys.length = 3)
    (hps : ps.length = 3) {C : Prop}
    (K : ∀ (x₃ x₂ x₁ y₃ y₂ y₁ : SExpr)
        (p₃ p₂ p₁ : WShape n),
      ∀ H' : LR.DirectRegisteredTypeTrace Γ ρ headType
        [x₄, x₃, x₂, x₁] [y₄, y₃, y₂, y₁]
        [p₄, p₃, p₂, p₁] result outTy,
        LR.DirectRegisteredTypeTrace.FourView H' → C) : C := by
  obtain ⟨x₃, x₂, x₁, rfl⟩ : ∃ x₃ x₂ x₁, xs = [x₃, x₂, x₁] :=
    ⟨xs[0], xs[1], xs[2], List.eq_getElem_of_length_eq_three xs hxs⟩
  obtain ⟨y₃, y₂, y₁, rfl⟩ : ∃ y₃ y₂ y₁, ys = [y₃, y₂, y₁] :=
    ⟨ys[0], ys[1], ys[2], List.eq_getElem_of_length_eq_three ys hys⟩
  obtain ⟨p₃, p₂, p₁, rfl⟩ : ∃ p₃ p₂ p₁, ps = [p₃, p₂, p₁] :=
    ⟨ps[0], ps[1], ps[2], List.eq_getElem_of_length_eq_three ps hps⟩
  exact K x₃ x₂ x₁ y₃ y₂ y₁ p₃ p₂ p₁ H H.fourView

/-- Keep the related final majors while using the left direct recursor prefix
at both endpoints.  The proof rebuilds the dependent legacy package so the
guarded major and Pi fields remain literally indexed by the same pair. -/
def LR.DirectPatternLeafSpine.leftPrefixes
    {majorX majorY : SExpr} {recXs recYs : List SExpr}
    {majorShape : WShape n} {recShapes : List (WShape n)}
    (H : LR.DirectPatternLeafSpine Γ (LRD Γ) Head
      (majorX :: recXs) (majorY :: recYs)
      (majorShape :: recShapes) A out outTy) :
    LR.DirectPatternLeafSpine Γ (LRD Γ) Head
      (majorX :: recXs) (majorY :: recXs)
      (majorShape :: recShapes) A out outTy := by
  rcases H with ⟨legacy, directArgs, hmajorTypeD, hmajorRelD, hpiD⟩
  rcases legacy with
    ⟨mx, rxs, my, rys, ms, rss, mts, rs, rts,
      hargs, hargs', hrargs, hout, houtTy, pair,
      hmsty, hrty, hmty, hmrel, haligned, hpi⟩
  simp only [List.cons.injEq] at hargs hargs' hrargs
  rcases hargs with ⟨rfl, rfl⟩
  rcases hargs' with ⟨rfl, rfl⟩
  rcases hrargs with ⟨rfl, rfl⟩
  exact {
    legacy := {
      majorX := majorX
      recXs := recXs
      majorY := majorY
      recYs := recXs
      majorShape := majorShape
      recShapes := recShapes
      majorTypeShape := mts
      resultShape := rs
      resultTypeShape := rts
      args_eq := rfl
      args'_eq := rfl
      rargs_eq := rfl
      out_eq := hout
      outTy_eq := houtTy
      pair := pair.leftPrefixes
      majorHasType := hmsty
      resultType := hrty
      majorType := hmty
      majorRel := hmrel
      aligned := haligned.leftPrefixes
      pi := hpi }
    directArgs := directArgs.leftPrefixes
    majorType := hmajorTypeD
    majorRel := hmajorRelD
    pi := hpiD }

/-- Keep the related final majors while using the right direct recursor
prefix at both endpoints. -/
def LR.DirectPatternLeafSpine.rightPrefixes
    {majorX majorY : SExpr} {recXs recYs : List SExpr}
    {majorShape : WShape n} {recShapes : List (WShape n)}
    (H : LR.DirectPatternLeafSpine Γ (LRD Γ) Head
      (majorX :: recXs) (majorY :: recYs)
      (majorShape :: recShapes) A out outTy) :
    LR.DirectPatternLeafSpine Γ (LRD Γ) Head
      (majorX :: recYs) (majorY :: recYs)
      (majorShape :: recShapes) A out outTy := by
  rcases H with ⟨legacy, directArgs, hmajorTypeD, hmajorRelD, hpiD⟩
  rcases legacy with
    ⟨mx, rxs, my, rys, ms, rss, mts, rs, rts,
      hargs, hargs', hrargs, hout, houtTy, pair,
      hmsty, hrty, hmty, hmrel, haligned, hpi⟩
  simp only [List.cons.injEq] at hargs hargs' hrargs
  rcases hargs with ⟨rfl, rfl⟩
  rcases hargs' with ⟨rfl, rfl⟩
  rcases hrargs with ⟨rfl, rfl⟩
  exact {
    legacy := {
      majorX := majorX
      recXs := recYs
      majorY := majorY
      recYs := recYs
      majorShape := majorShape
      recShapes := recShapes
      majorTypeShape := mts
      resultShape := rs
      resultTypeShape := rts
      args_eq := rfl
      args'_eq := rfl
      rargs_eq := rfl
      out_eq := hout
      outTy_eq := houtTy
      pair := pair.rightPrefixes
      majorHasType := hmsty
      resultType := hrty
      majorType := hmty
      majorRel := hmrel
      aligned := haligned.rightPrefixes
      pi := hpi }
    directArgs := directArgs.rightPrefixes
    majorType := hmajorTypeD
    majorRel := hmajorRelD
    pi := hpiD }

theorem LR.DirectPatternLeafSpine.of_cons_path
    {Γ : List SExpr} {n : Nat} {IH : LR.DirectRelBase Γ n}
    {Head A B F x y : SExpr} {xs ys : List SExpr}
    {p a : WShape n} {ps : List (WShape n)}
    {g f : WShapeFun n} {u v : SLevel}
    (prefixX : SExpr.SpineWF Γ Head xs.reverse A)
    (prefixY : SExpr.SpineWF Γ Head ys.reverse A)
    (aligned : LRS.CtorSpineDefEq (LR Γ) Head xs ys ps A)
    (directArgs : LR.DirectCtorArgsDefEq IH xs ys ps)
    (path : TypeDefEqPath Γ A (.forallE B F) u)
    (hp : p.HasType a)
    (htpi : WShape.HasTypePi f a true)
    (hBLegacy : (LR Γ).TyDefEq B B a)
    (hBDirect : IH.TyDefEq B B a)
    (hxy : IsDefEq Γ x y B)
    (hrelLegacy : (LR Γ).DefEq x y B p a)
    (hrelDirect : IH.DefEq x y B p a)
    (hresult : IsDefEq Γ (F.inst y) (F.inst x) (.sort v))
    (hPiLegacy : LRS.PiDefEq (LR Γ) B F F a f)
    (hPiDirect : LR.DirectPiDefEq IH B F F a f) :
    Nonempty (LR.DirectPatternLeafSpine Γ IH Head
      (x :: xs) (y :: ys) (p :: ps) (F.inst x)
      (g.app p) (f.app p)) := by
  obtain ⟨w, hPiTy⟩ := path.rightType
  exact ⟨{
    legacy := {
      majorX := x
      recXs := xs
      majorY := y
      recYs := ys
      majorShape := p
      recShapes := ps
      majorTypeShape := a
      resultShape := g
      resultTypeShape := f
      args_eq := rfl
      args'_eq := rfl
      rargs_eq := rfl
      out_eq := rfl
      outTy_eq := rfl
      pair := {
        prefixType := .forallE B F
        domain := B
        codomain := F
        piSort := w
        resultSortX := v
        resultSortY := v
        prefixX := SpineWF.ret_path path prefixX
        prefixY := SpineWF.ret_path path prefixY
        pi := hPiTy
        major := hxy
        resultX := hresult.hasType.2
        resultY := hresult }
      majorHasType := hp
      resultType := htpi
      majorType := hBLegacy
      majorRel := hrelLegacy
      aligned := aligned.cons_path path hp hBLegacy hxy hrelLegacy hresult
      pi := hPiLegacy }
    directArgs := .cons hp hBLegacy hBDirect hxy
      hrelLegacy hrelDirect directArgs
    majorType := hBDirect
    majorRel := hrelDirect
    pi := hPiDirect }⟩

/--
info: 'Lean4Lean.SExpr.LR.DirectPatternLeafSpine.of_cons_path' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectPatternLeafSpine.of_cons_path

/-- Forget the final-Pi alignment back to the ordinary related argument
spine consumed by the structural constant cases. -/
theorem LR.PatternLeafSpine.args
    (H : LR.PatternLeafSpine Γ IH Head xs ys rargs A out outTy) :
    LRS.CtorArgsDefEq IH xs ys rargs := H.aligned.args

/-- Recover the common raw type of the two majors from an externally
decomposed nonempty leaf.  Destructing the package before transporting its
major equality avoids dependent rewrites through the `LastPair` projection. -/
theorem LR.PatternLeafSpine.majorDefEq
    (H : LR.PatternLeafSpine Γ IH Head (x :: xs) (y :: ys)
      rargs A out outTy) :
    ∃ D, IsDefEq Γ x y D := by
  rcases H with ⟨mx, _, my, _, _, _, _, _, _, hx, hy, _, _, _, pair, _, _⟩
  have hmx : x = mx := (List.cons.inj hx).1
  have hmy : y = my := (List.cons.inj hy).1
  subst mx
  subst my
  exact ⟨pair.domain, pair.major⟩

/-- A packaged final application is definitionally nonempty. -/
theorem LR.PatternLeafSpine.nonempty
    (H : LR.PatternLeafSpine Γ IH Head xs ys rargs A out outTy) :
    rargs ≠ [] := by
  rw [H.rargs_eq]
  simp

/-- Keep the left concrete spine at both endpoints.  The final application
certificate was deliberately designed to retain both prefix and major
self-relations, so this operation is structural. -/
def LR.PatternLeafSpine.left
    (H : LR.PatternLeafSpine Γ IH Head xs ys rargs A out outTy) :
    LR.PatternLeafSpine Γ IH Head xs xs rargs A out outTy :=
  { H with
    majorY := H.majorX
    recYs := H.recXs
    args'_eq := H.args_eq
    pair := H.pair.leftPrefixes.leftMajors
    majorRel := IH.left H.majorRel
    aligned := H.aligned.left }

/-- Keep the right concrete spine at both endpoints. -/
def LR.PatternLeafSpine.right
    (H : LR.PatternLeafSpine Γ IH Head xs ys rargs A out outTy) :
    LR.PatternLeafSpine Γ IH Head ys ys rargs A out outTy :=
  { H with
    majorX := H.majorY
    recXs := H.recYs
    args_eq := H.args'_eq
    pair := H.pair.rightPrefixes.rightMajors
    majorRel := IH.left (IH.symm H.majorRel)
    aligned := H.aligned.right }

/-- Keep the related final majors while using the left recursor prefix at
both endpoints.  This is the left row of the synchronized iota rectangle;
unlike `left`, it does not replace the right major by the left major. -/
def LR.PatternLeafSpine.leftPrefixes
    {majorX majorY : SExpr} {recXs recYs : List SExpr}
    {majorShape : WShape n} {recShapes : List (WShape n)}
    (H : LR.PatternLeafSpine Γ IH Head
      (majorX :: recXs) (majorY :: recYs)
      (majorShape :: recShapes) A out outTy) :
    LR.PatternLeafSpine Γ IH Head
      (majorX :: recXs) (majorY :: recXs)
      (majorShape :: recShapes) A out outTy := by
  rcases H with
    ⟨mx, rxs, my, rys, ms, rss, mts, rs, rts,
      hargs, hargs', hrargs, hout, houtTy, pair,
      hmsty, hrty, hmty, hmrel, haligned, hpi⟩
  simp only [List.cons.injEq] at hargs hargs' hrargs
  rcases hargs with ⟨rfl, rfl⟩
  rcases hargs' with ⟨rfl, rfl⟩
  rcases hrargs with ⟨rfl, rfl⟩
  exact {
    majorX := majorX
    recXs := recXs
    majorY := majorY
    recYs := recXs
    majorShape := majorShape
    recShapes := recShapes
    majorTypeShape := mts
    resultShape := rs
    resultTypeShape := rts
    args_eq := rfl
    args'_eq := rfl
    rargs_eq := rfl
    out_eq := hout
    outTy_eq := houtTy
    pair := pair.leftPrefixes
    majorHasType := hmsty
    resultType := hrty
    majorType := hmty
    majorRel := hmrel
    aligned := haligned.leftPrefixes
    pi := hpi }

/-- Keep the related final majors while using the right recursor prefix at
both endpoints.  This is the right row of the synchronized iota rectangle. -/
def LR.PatternLeafSpine.rightPrefixes
    {majorX majorY : SExpr} {recXs recYs : List SExpr}
    {majorShape : WShape n} {recShapes : List (WShape n)}
    (H : LR.PatternLeafSpine Γ IH Head
      (majorX :: recXs) (majorY :: recYs)
      (majorShape :: recShapes) A out outTy) :
    LR.PatternLeafSpine Γ IH Head
      (majorX :: recYs) (majorY :: recYs)
      (majorShape :: recShapes) A out outTy := by
  rcases H with
    ⟨mx, rxs, my, rys, ms, rss, mts, rs, rts,
      hargs, hargs', hrargs, hout, houtTy, pair,
      hmsty, hrty, hmty, hmrel, haligned, hpi⟩
  simp only [List.cons.injEq] at hargs hargs' hrargs
  rcases hargs with ⟨rfl, rfl⟩
  rcases hargs' with ⟨rfl, rfl⟩
  rcases hrargs with ⟨rfl, rfl⟩
  exact {
    majorX := majorX
    recXs := recYs
    majorY := majorY
    recYs := recYs
    majorShape := majorShape
    recShapes := recShapes
    majorTypeShape := mts
    resultShape := rs
    resultTypeShape := rts
    args_eq := rfl
    args'_eq := rfl
    rargs_eq := rfl
    out_eq := hout
    outTy_eq := houtTy
    pair := pair.rightPrefixes
    majorHasType := hmsty
    resultType := hrty
    majorType := hmty
    majorRel := hmrel
    aligned := haligned.rightPrefixes
    pi := hpi }

/-- Swap both concrete spines while retaining the left-oriented result type. -/
def LR.PatternLeafSpine.symm
    (H : LR.PatternLeafSpine Γ IH Head xs ys rargs A out outTy) :
    LR.PatternLeafSpine Γ IH Head ys xs rargs A out outTy :=
  { H with
    majorX := H.majorY
    recXs := H.recYs
    majorY := H.majorX
    recYs := H.recXs
    args_eq := H.args'_eq
    args'_eq := H.args_eq
    pair := H.pair.symm
    majorRel := IH.symm H.majorRel
    aligned := H.aligned.symm }

/-- Transport a packaged final application through the same lift equivalence
used by a normalized constructor frame. -/
def LR.PatternLeafSpine.lift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (E : LogRel.LiftEquiv IH IH' le)
    (H : LR.PatternLeafSpine Γ IH Head xs ys rargs A out outTy) :
    LR.PatternLeafSpine Γ IH' Head xs ys (rargs.map (.lift n')) A
      (out.lift n') (outTy.lift n') := by
  have hmajorType : IH'.TyDefEq H.pair.domain H.pair.domain
      (H.majorTypeShape.lift n') :=
    (E.ty H.majorHasType.isType).2 H.majorType
  have hmajorRel : IH'.DefEq H.majorX H.majorY H.pair.domain
      (H.majorShape.lift n') (H.majorTypeShape.lift n') :=
    (E.term H.majorHasType).2 H.majorRel
  exact {
    majorX := H.majorX
    recXs := H.recXs
    majorY := H.majorY
    recYs := H.recYs
    majorShape := H.majorShape.lift n'
    recShapes := H.recShapes.map (.lift n')
    majorTypeShape := H.majorTypeShape.lift n'
    resultShape := H.resultShape.lift n'
    resultTypeShape := H.resultTypeShape.lift n'
    args_eq := H.args_eq
    args'_eq := H.args'_eq
    rargs_eq := by simpa only [H.rargs_eq, List.map_cons]
    out_eq := by simpa only [H.out_eq, WShapeFun.lift_app le]
    outTy_eq := by simpa only [H.outTy_eq, WShapeFun.lift_app le]
    pair := H.pair
    majorHasType := (WShape.HasType.lift le).2 H.majorHasType
    resultType := (WShape.HasTypePi.lift le).2 H.resultType
    majorType := hmajorType
    majorRel := hmajorRel
    aligned := H.aligned.lift le E.ty E.term
    pi := (LRS.PiDefEq.liftEquiv le H.resultType E).2 H.pi }

/-- The remaining consumer obligation at a reached nonempty pattern leaf. -/
def LR.PatternLeafDefEq (Γ₀ : List SExpr) (c : Name) (ls : List SLevel)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ {n : Nat} {rargs : List (WShape n)}
      {p : Pattern} {r : p.RHS × p.Check} {mcap : p.Path → TShape}
      {xs ys : List SExpr} {CHead A : SExpr} {out outTy : WShape n},
      Params.Pat p r →
      LE_Interp.Matches (n := n) p c rargs mcap →
      LE_Interp.RHS ls mcap R out.T r.1 →
      LR.PatternLeafSpine Γ₀ (LR Γ₀) CHead xs ys rargs A out outTy →
      Γ₀ ⊢
        (xs.foldr (fun a f => f.app a) (.const c ls)) ≡
        (ys.foldr (fun a f => f.app a) (.const c ls)) : A →
      (∃ u, Γ₀ ⊢ A : .sort u) →
      Γ₀ ⊢ .const c ls : CHead →
      SExpr.SpineWF Γ₀ CHead xs.reverse A →
      SExpr.SpineWF Γ₀ CHead ys.reverse A →
      out.HasType outTy →
      (LR Γ₀).TyDefEq A A outTy →
      (LR Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy

/-- The nonempty leaf contract after eliminating the impossible definition
case.  Its pattern is definitionally an iota pattern, so consumers can invert
the semantic match into recursor and constructor spines without another
shape oracle. -/
def LR.IotaLeafDefEq (Γ₀ : List SExpr) (c : Name) (ls : List SLevel)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ {n : Nat} {rargs : List (WShape n)}
      {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
      {xs ys : List SExpr} {CHead A : SExpr} {out outTy : WShape n},
      Params.Pat (RecursorIotaPattern rec major ctor arity) r →
      LE_Interp.Matches (n := n) (RecursorIotaPattern rec major ctor arity)
        c rargs mcap →
      LE_Interp.RHS ls mcap R out.T r.1 →
      LR.PatternLeafSpine Γ₀ (LR Γ₀) CHead xs ys rargs A out outTy →
      Γ₀ ⊢
        (xs.foldr (fun a f => f.app a) (.const c ls)) ≡
        (ys.foldr (fun a f => f.app a) (.const c ls)) : A →
      (∃ u, Γ₀ ⊢ A : .sort u) →
      Γ₀ ⊢ .const c ls : CHead →
      SExpr.SpineWF Γ₀ CHead xs.reverse A →
      SExpr.SpineWF Γ₀ CHead ys.reverse A →
      out.HasType outTy →
      (LR Γ₀).TyDefEq A A outTy →
      (LR Γ₀).DefEq
      (xs.foldr (fun a f => f.app a) (.const c ls))
      (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy

/-- One reached iota leaf at an explicit logical argument-spine level. -/
def LR.IotaLeafDefEqAt (Γ₀ : List SExpr) (level : Nat)
    (c : Name) (ls : List SLevel)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ {rargs : List (WShape level)}
      {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
      {xs ys : List SExpr} {CHead A : SExpr}
      {out outTy : WShape level},
      Params.Pat (RecursorIotaPattern rec major ctor arity) r →
      LE_Interp.Matches (n := level)
        (RecursorIotaPattern rec major ctor arity) c rargs mcap →
      LE_Interp.RHS ls mcap R out.T r.1 →
      LR.PatternLeafSpine Γ₀ (LR Γ₀) CHead xs ys rargs A out outTy →
      Γ₀ ⊢
        (xs.foldr (fun a f => f.app a) (.const c ls)) ≡
        (ys.foldr (fun a f => f.app a) (.const c ls)) : A →
      (∃ u, Γ₀ ⊢ A : .sort u) →
      Γ₀ ⊢ .const c ls : CHead →
      SExpr.SpineWF Γ₀ CHead xs.reverse A →
      SExpr.SpineWF Γ₀ CHead ys.reverse A →
      out.HasType outTy →
      (LR Γ₀).TyDefEq A A outTy →
      (LR Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy

/-- The structural pattern-leaf contract at one explicit spine level. -/
def LR.PatternLeafDefEqAt (Γ₀ : List SExpr) (level : Nat)
    (c : Name) (ls : List SLevel)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ {rargs : List (WShape level)}
      {p : Pattern} {r : p.RHS × p.Check} {mcap : p.Path → TShape}
      {xs ys : List SExpr} {CHead A : SExpr}
      {out outTy : WShape level},
      Params.Pat p r →
      LE_Interp.Matches (n := level) p c rargs mcap →
      LE_Interp.RHS ls mcap R out.T r.1 →
      LR.PatternLeafSpine Γ₀ (LR Γ₀) CHead xs ys rargs A out outTy →
      Γ₀ ⊢
        (xs.foldr (fun a f => f.app a) (.const c ls)) ≡
        (ys.foldr (fun a f => f.app a) (.const c ls)) : A →
      (∃ u, Γ₀ ⊢ A : .sort u) →
      Γ₀ ⊢ .const c ls : CHead →
      SExpr.SpineWF Γ₀ CHead xs.reverse A →
      SExpr.SpineWF Γ₀ CHead ys.reverse A →
      out.HasType outTy →
      (LR Γ₀).TyDefEq A A outTy →
      (LR Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy

/-- Guarded counterpart of the structural pattern-leaf contract.  The
ordinary and direct spine evidence share literal endpoints, while the
ordinary result remains explicit because guarded argument quantification
cannot manufacture its legacy projection. -/
def LRD.PatternLeafDefEqAt (Γ₀ : List SExpr) (level : Nat)
    (c : Name) (ls : List SLevel)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ {rargs : List (WShape level)}
      {p : Pattern} {r : p.RHS × p.Check} {mcap : p.Path → TShape}
      {xs ys : List SExpr} {CHead A : SExpr}
      {out outTy : WShape level},
      Params.Pat p r →
      LE_Interp.Matches (n := level) p c rargs mcap →
      LE_Interp.RHS ls mcap R out.T r.1 →
      LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀)
        CHead xs ys rargs A out outTy →
      IsDefEq Γ₀
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A →
      (∃ u, IsDefEq Γ₀ A A (.sort u)) →
      IsDefEq Γ₀ (.const c ls) (.const c ls) CHead →
      SExpr.SpineWF Γ₀ CHead xs.reverse A →
      SExpr.SpineWF Γ₀ CHead ys.reverse A →
      out.HasType outTy →
      (LR Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy →
      (LRD Γ₀).TyDefEq A A outTy →
      (LRD Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy

/-- Guarded nonempty iota-leaf contract at one explicit application-spine
level.  As in the structural guarded contract, the established result is an
explicit input while the paired spine retains the direct major and Pi
actions needed to rebuild the informative output. -/
def LRD.IotaLeafDefEqAt (Γ₀ : List SExpr) (level : Nat)
    (c : Name) (ls : List SLevel)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ {rargs : List (WShape level)}
      {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
      {xs ys : List SExpr} {CHead A : SExpr}
      {out outTy : WShape level},
      Params.Pat (RecursorIotaPattern rec major ctor arity) r →
      LE_Interp.Matches (n := level)
        (RecursorIotaPattern rec major ctor arity) c rargs mcap →
      LE_Interp.RHS ls mcap R out.T r.1 →
      LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀)
        CHead xs ys rargs A out outTy →
      IsDefEq Γ₀
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A →
      (∃ u, IsDefEq Γ₀ A A (.sort u)) →
      IsDefEq Γ₀ (.const c ls) (.const c ls) CHead →
      SExpr.SpineWF Γ₀ CHead xs.reverse A →
      SExpr.SpineWF Γ₀ CHead ys.reverse A →
      out.HasType outTy →
      (LR Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy →
      (LRD Γ₀).TyDefEq A A outTy →
      (LRD Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy

/-- A guarded structural leaf carrying the exact registered-type
application trace which produced its direct argument spine.  This is the
proof-relevant evaluator boundary used by the typed constant callback; the
ordinary leaf contract remains available for consumers that do not inspect
the registered telescope. -/
def LRD.RegisteredPatternLeafDefEqAt (Γ₀ : List SExpr) (ρ : Valuation)
    (headType : SExpr) (level : Nat) (c : Name) (ls : List SLevel)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ {rargs : List (WShape level)}
      {p : Pattern} {r : p.RHS × p.Check} {mcap : p.Path → TShape}
      {xs ys : List SExpr} {A : SExpr}
      {out outTy : WShape level},
      Params.Pat p r →
      LE_Interp.Matches (n := level) p c rargs mcap →
      LE_Interp.RHS ls mcap R out.T r.1 →
      LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀)
        headType xs ys rargs A out outTy →
      LR.DirectRegisteredTypeTrace Γ₀ ρ headType
        xs ys rargs A outTy →
      IsDefEq Γ₀
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A →
      (∃ u, IsDefEq Γ₀ A A (.sort u)) →
      IsDefEq Γ₀ (.const c ls) (.const c ls) headType →
      SExpr.SpineWF Γ₀ headType xs.reverse A →
      SExpr.SpineWF Γ₀ headType ys.reverse A →
      out.HasType outTy →
      (LR Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy →
      (LRD Γ₀).TyDefEq A A outTy →
      (LRD Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy

/-- Iota-specialized registered leaf contract.  The selected pattern and
the exact registered-type trace are retained in one implication chain, so a
native leaf may eliminate both without choosing a second application
telescope. -/
def LRD.RegisteredIotaLeafDefEqAt (Γ₀ : List SExpr) (ρ : Valuation)
    (headType : SExpr) (level : Nat) (c : Name) (ls : List SLevel)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ {rargs : List (WShape level)}
      {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
      {xs ys : List SExpr} {A : SExpr}
      {out outTy : WShape level},
      Params.Pat (RecursorIotaPattern rec major ctor arity) r →
      LE_Interp.Matches (n := level)
        (RecursorIotaPattern rec major ctor arity) c rargs mcap →
      LE_Interp.RHS ls mcap R out.T r.1 →
      LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀)
        headType xs ys rargs A out outTy →
      LR.DirectRegisteredTypeTrace Γ₀ ρ headType
        xs ys rargs A outTy →
      IsDefEq Γ₀
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A →
      (∃ u, IsDefEq Γ₀ A A (.sort u)) →
      IsDefEq Γ₀ (.const c ls) (.const c ls) headType →
      SExpr.SpineWF Γ₀ headType xs.reverse A →
      SExpr.SpineWF Γ₀ headType ys.reverse A →
      out.HasType outTy →
      (LR Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy →
      (LRD Γ₀).TyDefEq A A outTy →
      (LRD Γ₀).DefEq
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy

/-- Argument-count rigidity of a semantic `varN` match: the matched list
has exactly the pattern's arity. -/
theorem LE_Interp.Matches.varN_length
    {c c' : Name} {k : Nat} : ∀ {n : Nat} {rargs : List (WShape n)}
      {m : (Pattern.varN (.const c) k).Path → TShape},
    LE_Interp.Matches (Pattern.varN (.const c) k) c' rargs m →
    rargs.length = k := by
  induction k with
  | zero =>
    intro n rargs m H
    cases H
    rfl
  | succ k ih =>
    intro n rargs m H
    cases H with
    | var H => simpa using ih H

/-- The remaining guarded major-chain action at one reached iota site.

The selected recursor and constructor matches, semantic RHS, paired direct
leaf, and its normalized final-Pi record are all retained literally.  A
producer must return one guarded rectangle for every framed native link of
the constructor-major closure; `iotaLeafDefEqAt_of_majorLinkStep` performs
the surrounding match inversion and chain fold. -/
def LRD.IotaMajorLinkStepAt (Γ₀ : List SExpr) (level : Nat)
    (c : Name) (recLs : List SLevel)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ {n : Nat} {rec ctor : Name} {major arity : Nat}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const rec) major).Path → TShape}
      {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {majorX majorY : SExpr} {recXs recYs : List SExpr}
      {CHead A : SExpr} {out outTy : WShape (n + 1)},
    level = n + 1 →
    c = rec →
    Ctx.WF Γ₀ →
    Params.Pat (RecursorIotaPattern rec major ctor arity) r →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor →
    LE_Interp.RHS recLs (Sum.elim mrec mctor) R out.T r.1 →
    (hleaf : LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀) CHead
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ctor ctorShapes.reverse) :: recShapes) A out outTy) →
    (pair : SExpr.SpineWF.LastPair Γ₀ CHead
      recXs recYs majorX majorY A) →
    IsDefEq Γ₀ (.const rec recLs) (.const rec recLs) CHead →
    out.HasType outTy →
    (LRD Γ₀).TyDefEq A A outTy →
    LR.DirectMajorLinkRectAt Γ₀
      (.ctor' ctor ctorShapes.reverse) pair.domain
      rec recLs recXs recYs majorX A out outTy

/-- A fixed-site guarded major-link producer closes the complete reached
iota leaf.  The executable match determines the recursor/constructor split;
the direct leaf then supplies the constructor closure and the final typed Pi
site.  Only `IotaMajorLinkStepAt` remains after the root constructor closure
is folded by `iotaDefEq_of_ctorDefEqAt`. -/
theorem LRD.iotaLeafDefEqAt_of_majorLinkStep
    (hΓ : Ctx.WF Γ₀)
    (anchor : LR.MajorChainAnchorStep Γ₀)
    (site : LRD.IotaMajorLinkStepAt Γ₀ level c ls R) :
    LRD.IotaLeafDefEqAt Γ₀ level c ls R := by
  intro rargs rec major ctor arity r mcap xs ys CHead A out outTy
    hpat hmatch hrhs hleaf hterm hAType hhead hspineX hspineY hout
    hlegacy hA
  cases hmatch with
  | @app fPat nCtor head recShapes mrec aPat ctorHead
      ctorShapes mctor hmf hma =>
    have hleafRoot := hleaf
    rcases hleaf.legacy with
      ⟨majorX, recXs, majorY, recYs, majorShape, recShapes',
        majorTypeShape, resultShape, resultTypeShape,
        hxs, hys, hrargs, houtEq, houtTyEq, hpair,
        hmajorHasType, hresultType, hmajorType, hmajorRel,
        haligned, hpi⟩
    subst xs
    subst ys
    simp only [List.cons.injEq] at hrargs
    rcases hrargs with ⟨hmajorShape, hrecShapes⟩
    subst recShapes'
    subst out
    subst outTy
    have hctorHead : ctor = ctorHead := hma.varN_const_head
    subst ctorHead
    have hctorClass : Params.classify ctor =
        some (.ctor ctorShapes.reverse.length) := by
      simpa using hma.head_wf_eq (Params.pat_wf hpat).2
    subst majorShape
    have hrecHead : rec = c := hmf.varN_const_head
    subst c
    have hrecShapesLen : recShapes.length = major := hmf.varN_length
    have hrecargs : LRS.CtorArgsDefEq (LR Γ₀)
        recXs recYs recShapes := hleafRoot.legacy.aligned.args.tail
    obtain ⟨hXlen, hYlen⟩ := hrecargs.lengths
    have hmajorPremX : IsMajorPremise
        (recXs.foldr (fun a f => f.app a) (.const rec ls)) := by
      have hlen : recXs.length = major := hXlen.trans hrecShapesLen
      obtain ⟨m2, hm2⟩ :=
        hlen ▸ Pattern.varN_const_matchesS rec ls recXs
      exact ⟨_, ⟨r, hpat⟩, _, _, .refl, ls, m2, hm2⟩
    have hmajorPremY : IsMajorPremise
        (recYs.foldr (fun a f => f.app a) (.const rec ls)) := by
      have hlen : recYs.length = major := hYlen.trans hrecShapesLen
      obtain ⟨m2, hm2⟩ :=
        hlen ▸ Pattern.varN_const_matchesS rec ls recYs
      exact ⟨_, ⟨r, hpat⟩, _, _, .refl, ls, m2, hm2⟩
    have hmajorCtor := LR.DefEq.ctor'_inv hctorClass
      hmajorHasType hmajorRel
    have hlink : LR.DirectMajorLinkRectAt Γ₀
        (.ctor' ctor ctorShapes.reverse) hpair.domain
        rec ls recXs recYs majorX A
        (resultShape.app (.ctor' ctor ctorShapes.reverse))
        (resultTypeShape.app (.ctor' ctor ctorShapes.reverse)) :=
      site rfl rfl hΓ hpat hmf hma hrhs
        hleafRoot hpair hhead hout hA
    exact LRD.iotaDefEq_of_ctorDefEqAt anchor hmajorCtor.2 hpair
      hhead hmajorPremX hmajorPremY hA hlink

/--
info: 'Lean4Lean.SExpr.LRD.IotaMajorLinkStepAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.IotaMajorLinkStepAt

/--
info: 'Lean4Lean.SExpr.LRD.iotaLeafDefEqAt_of_majorLinkStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaLeafDefEqAt_of_majorLinkStep

/-- Registered counterpart of `LRD.IotaMajorLinkStepAt`.  The fixed-site
producer receives the exact registered-type application trace in addition to
the normalized direct leaf, so its native Nat branch can derive capture
domains from the same Pi decomposition used by constant evaluation. -/
def LRD.RegisteredIotaMajorLinkStepAt (Γ₀ : List SExpr)
    (ρ : Valuation) (headType : SExpr) (level : Nat)
    (c : Name) (recLs : List SLevel)
    (R : TShape → SExpr → Prop) : Prop :=
  ∀ {n : Nat} {rec ctor : Name} {major arity : Nat}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const rec) major).Path → TShape}
      {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {majorX majorY : SExpr} {recXs recYs : List SExpr}
      {A : SExpr} {out outTy : WShape (n + 1)},
    level = n + 1 →
    c = rec →
    Ctx.WF Γ₀ →
    Params.Pat (RecursorIotaPattern rec major ctor arity) r →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor →
    LE_Interp.RHS recLs (Sum.elim mrec mctor) R out.T r.1 →
    (hleaf : LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀) headType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ctor ctorShapes.reverse) :: recShapes) A out outTy) →
    LR.DirectRegisteredTypeTrace Γ₀ ρ headType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ctor ctorShapes.reverse) :: recShapes) A outTy →
    (pair : SExpr.SpineWF.LastPair Γ₀ headType
      recXs recYs majorX majorY A) →
    IsDefEq Γ₀ (.const rec recLs) (.const rec recLs) headType →
    out.HasType outTy →
    (LRD Γ₀).TyDefEq A A outTy →
    LR.DirectMajorLinkRectAt Γ₀
      (.ctor' ctor ctorShapes.reverse) pair.domain
      rec recLs recXs recYs majorX A out outTy

/-- Fold a registered fixed-site callback through the executable iota match
while preserving the exact registered-type trace at the reached site. -/
theorem LRD.registeredIotaLeafDefEqAt_of_majorLinkStep
    (hΓ : Ctx.WF Γ₀)
    (anchor : LR.MajorChainAnchorStep Γ₀)
    (site : LRD.RegisteredIotaMajorLinkStepAt
      Γ₀ ρ headType level c ls R) :
    LRD.RegisteredIotaLeafDefEqAt
      Γ₀ ρ headType level c ls R := by
  intro rargs rec major ctor arity r mcap xs ys A out outTy
    hpat hmatch hrhs hleaf trace hterm hAType hhead hspineX hspineY
    hout hlegacy hA
  cases hmatch with
  | @app fPat nCtor head recShapes mrec aPat ctorHead
      ctorShapes mctor hmf hma =>
    have hleafRoot := hleaf
    rcases hleaf.legacy with
      ⟨majorX, recXs, majorY, recYs, majorShape, recShapes',
        majorTypeShape, resultShape, resultTypeShape,
        hxs, hys, hrargs, houtEq, houtTyEq, hpair,
        hmajorHasType, hresultType, hmajorType, hmajorRel,
        haligned, hpi⟩
    subst xs
    subst ys
    simp only [List.cons.injEq] at hrargs
    rcases hrargs with ⟨hmajorShape, hrecShapes⟩
    subst recShapes'
    subst out
    subst outTy
    have hctorHead : ctor = ctorHead := hma.varN_const_head
    subst ctorHead
    have hctorClass : Params.classify ctor =
        some (.ctor ctorShapes.reverse.length) := by
      simpa using hma.head_wf_eq (Params.pat_wf hpat).2
    subst majorShape
    have hrecHead : rec = c := hmf.varN_const_head
    subst c
    have hrecShapesLen : recShapes.length = major := hmf.varN_length
    have hrecargs : LRS.CtorArgsDefEq (LR Γ₀)
        recXs recYs recShapes := hleafRoot.legacy.aligned.args.tail
    obtain ⟨hXlen, hYlen⟩ := hrecargs.lengths
    have hmajorPremX : IsMajorPremise
        (recXs.foldr (fun a f => f.app a) (.const rec ls)) := by
      have hlen : recXs.length = major := hXlen.trans hrecShapesLen
      obtain ⟨m2, hm2⟩ :=
        hlen ▸ Pattern.varN_const_matchesS rec ls recXs
      exact ⟨_, ⟨r, hpat⟩, _, _, .refl, ls, m2, hm2⟩
    have hmajorPremY : IsMajorPremise
        (recYs.foldr (fun a f => f.app a) (.const rec ls)) := by
      have hlen : recYs.length = major := hYlen.trans hrecShapesLen
      obtain ⟨m2, hm2⟩ :=
        hlen ▸ Pattern.varN_const_matchesS rec ls recYs
      exact ⟨_, ⟨r, hpat⟩, _, _, .refl, ls, m2, hm2⟩
    have hmajorCtor := LR.DefEq.ctor'_inv hctorClass
      hmajorHasType hmajorRel
    have hlink : LR.DirectMajorLinkRectAt Γ₀
        (.ctor' ctor ctorShapes.reverse) hpair.domain
        rec ls recXs recYs majorX A
        (resultShape.app (.ctor' ctor ctorShapes.reverse))
        (resultTypeShape.app (.ctor' ctor ctorShapes.reverse)) :=
      site rfl rfl hΓ hpat hmf hma hrhs hleafRoot trace
        hpair hhead hout hA
    exact LRD.iotaDefEq_of_ctorDefEqAt anchor hmajorCtor.2 hpair
      hhead hmajorPremX hmajorPremY hA hlink

/--
info: 'Lean4Lean.SExpr.LRD.registeredIotaLeafDefEqAt_of_majorLinkStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LRD.registeredIotaLeafDefEqAt_of_majorLinkStep

/-- A fixed-level iota handler discharges the corresponding structural
nonempty pattern leaf. -/
theorem LR.PatternLeafDefEqAt.of_iota
    (H : LR.IotaLeafDefEqAt Γ₀ level c ls R) :
    LR.PatternLeafDefEqAt Γ₀ level c ls R := by
  intro rargs p r mcap xs ys CHead A out outTy
    hpat hmatch hrhs hleaf hterm hAType hhead hspineX hspineY hout hA
  obtain ⟨rec, major, ctor, arity, rfl⟩ :=
    hmatch.iota_of_pat_nonempty hpat hleaf.nonempty
  exact H hpat hmatch hrhs hleaf hterm hAType hhead
    hspineX hspineY hout hA

/-- A guarded fixed-level iota handler discharges the corresponding
structural leaf after executable matching proves that its nonempty argument
spine cannot be a definitional pattern. -/
theorem LRD.PatternLeafDefEqAt.of_iota
    (H : LRD.IotaLeafDefEqAt Γ₀ level c ls R) :
    LRD.PatternLeafDefEqAt Γ₀ level c ls R := by
  intro rargs p r mcap xs ys CHead A out outTy
    hpat hmatch hrhs hleaf hterm hAType hhead hspineX hspineY hout
    hlegacy hA
  obtain ⟨rec, major, ctor, arity, rfl⟩ :=
    hmatch.iota_of_pat_nonempty hpat hleaf.legacy.nonempty
  exact H hpat hmatch hrhs hleaf hterm hAType hhead
    hspineX hspineY hout hlegacy hA

/-- An ordinary guarded leaf remains a registered leaf consumer when it
does not need to inspect the synchronized type trace. -/
theorem LRD.PatternLeafDefEqAt.toRegistered
    (H : LRD.PatternLeafDefEqAt Γ₀ level c ls R) :
    LRD.RegisteredPatternLeafDefEqAt Γ₀ ρ headType level c ls R := by
  intro rargs p r mcap xs ys A out outTy hpat hmatch hrhs hleaf _trace
    hterm hAType hhead hspineX hspineY hout hlegacy hA
  exact H hpat hmatch hrhs hleaf hterm hAType hhead
    hspineX hspineY hout hlegacy hA

/-- An ordinary guarded iota handler is likewise a registered handler which
ignores the additional exact evaluator trace. -/
theorem LRD.IotaLeafDefEqAt.toRegistered
    (H : LRD.IotaLeafDefEqAt Γ₀ level c ls R) :
    LRD.RegisteredIotaLeafDefEqAt Γ₀ ρ headType level c ls R := by
  intro rargs rec major ctor arity r mcap xs ys A out outTy
    hpat hmatch hrhs hleaf _trace hterm hAType hhead hspineX hspineY
    hout hlegacy hA
  exact H hpat hmatch hrhs hleaf hterm hAType hhead
    hspineX hspineY hout hlegacy hA

/-- A registered fixed-level iota handler discharges the corresponding
registered structural leaf without forgetting its exact type trace. -/
theorem LRD.RegisteredPatternLeafDefEqAt.of_iota
    (H : LRD.RegisteredIotaLeafDefEqAt
      Γ₀ ρ headType level c ls R) :
    LRD.RegisteredPatternLeafDefEqAt
      Γ₀ ρ headType level c ls R := by
  intro rargs p r mcap xs ys A out outTy hpat hmatch hrhs hleaf trace
    hterm hAType hhead hspineX hspineY hout hlegacy hA
  obtain ⟨rec, major, ctor, arity, rfl⟩ :=
    hmatch.iota_of_pat_nonempty hpat hleaf.legacy.nonempty
  exact H hpat hmatch hrhs hleaf trace hterm hAType hhead
    hspineX hspineY hout hlegacy hA

/--
info: 'Lean4Lean.SExpr.LRD.PatternLeafDefEqAt.of_iota' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.PatternLeafDefEqAt.of_iota

/-- The witness-aware iota obligation at the exact constant-argument level. -/
def LR.IotaWitnessStepAt (Γ₀ : List SExpr) (level : Nat) : Prop :=
  Ctx.WF Γ₀ →
  ∀ {ρ : Valuation} {c : Name} {ls : List SLevel}
      {R : TShape → SExpr → Prop},
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LR.IotaLeafDefEqAt Γ₀ level c ls (LE_Interp.Lower R)

/-- The sole recursive semantic input needed by the nonempty iota leaf.

Keeping this boundary separate from derivation induction lets the joint
level construction provide predecessor uniqueness and fixed-head recursion
without assuming the polymorphic adequacy theorem being assembled. -/
def LR.IotaWitnessStep (Γ₀ : List SExpr) : Prop :=
  Ctx.WF Γ₀ →
  ∀ {ρ : Valuation} {c : Name} {ls : List SLevel}
      {R : TShape → SExpr → Prop},
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LR.IotaLeafDefEq Γ₀ c ls (LE_Interp.Lower R)

/-- The depth-indexed joint-leaf obligation.  At rung `depth` of the
stratified adequacy fixpoint, the recursive constructor-major leaf may
consume every strictly smaller contextual adequacy rung; the fixpoint
itself never assembles a predecessor inversion or uniqueness package on
the leaf's behalf.  Shape levels stay polymorphic inside the produced
`IotaWitnessStep`: only the adequacy rung is indexed, so no
level-indexed obligation is reintroduced.

The strict predecessor family is stated in exactly the shape of the two
prepared consumers at a successor rung:
`JointStratifiedPathInversionAt.of_predecessorAdequacy` at the
predecessor depth, and `SelfAdequateDefeqStepAt.of_lowerAdequacy` at any
interior depth of the coherent construction. -/
def LR.IotaWitnessStepAtDepth (Γ₀ : List SExpr) (depth : Nat) : Prop :=
  (∀ d', d' < depth → LR.ContextualAdequacyAtDepth d') →
  LR.IotaWitnessStep Γ₀

/-- The depth-indexed joint-leaf obligation uniformly over target
contexts.  `Ctx.WF Γ₀` is already the first argument of the produced
`IotaWitnessStep`, so no separate well-formedness hypothesis is repeated
here. -/
def LR.ContextualIotaWitnessStepAtDepth (depth : Nat) : Prop :=
  ∀ {Γ₀ : List SExpr}, LR.IotaWitnessStepAtDepth Γ₀ depth

/-- The synchronized producer certificate for one generated fixed-head
application chain.

The `TypedTelescope` component records the semantic term spine, its dependent
type spine, and the exact terminal type observation.  `Captures` pins every
application layer to the same aligned logical-relation representative used
as its semantic upper bound and as its typed domain argument.  This is the
non-erasing boundary required before the fixed-head application fold: none
of the three components may independently reselect an existential capture. -/
def LR.FixedHeadTelescope (Γ₀ : List SExpr)
    {p : Pattern} {mcap : p.Path → TShape}
    (mx my captureType : p.Path → SExpr)
    {head out headTy outTy : TShape} {paths : List p.Path}
    (spine : LE_Interp.RHS.ShapeSpine mcap head paths out) : Prop :=
  LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures
    (m2 := mcap)
    (fun {n} path (elemShape typeShape : WShape n) =>
      LRS.CaptureDefEqAligned.AtShapes (LR Γ₀)
        (mcap path) (mx path) (my path) (captureType path)
        elemShape typeShape)
    head paths out headTy outTy

/-- One application layer of the synchronized peel (the N1 core, ported
verbatim from the proved probe `probeB.peelLayerProved`).  Given the next
layer's synchronized lower endpoint below `g.app aSp`, an aligned capture
bound `aSp ≤ argCap` typed in the literal domain, and the layer's lambda
typing, produce the synchronized lower endpoint one layer earlier: a
singleton lambda at the typed fire point, typed by the singleton Pi at
that same fire point, below the literal `forallE tyDom tyFun`
observation.  `hgle` and `hty` are unused by this layer's algebra but fix
the interface of the spine recursion that will consume it. -/
theorem WShape.HasTypeLam.peelLayer
    {n : Nat} {g g' : WShapeFun n}
    {tyDom : WShape n} {tyFun : WShapeFun n}
    (hgle : g ≤ g')
    (hty : WShape.HasTypeLam g' tyDom tyFun)
    {aSp argCap : WShape n}
    (hargCap : aSp ≤ argCap)
    (hcapDom : argCap.HasType tyDom)
    {next nextTy : WShape n}
    (hnext : next ≤ g.app aSp)
    (hnextTy : next.HasType nextTy)
    (hnextLe : nextTy ≤ tyFun.app argCap) :
    ∃ elem elemTy : WShape (n + 1),
      elem ≤ .lam' g ∧ elem.HasType elemTy ∧
        elemTy ≤ .forallE tyDom tyFun := by
  refine ⟨.lam' (.single argCap next), .forallE tyDom (.single argCap nextTy),
    ?_, ?_, ?_⟩
  · -- elem ≤ lam' g : one dominating pair of g at the typed fire point
    apply WShape.lam'_le_lam'.2
    obtain ⟨x', hx', hmem⟩ := g.app_eq argCap
    exact WShapeFun.single_le.2
      ⟨x', _, hmem, hx', hnext.trans (WShapeFun.app_mono_r hargCap)⟩
  · -- elem.HasType elemTy : singleton lambda typing at the REAL domain
    apply WShape.HasType.lam
    refine WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
    · refine WShape.HasTypePi.def.2
        ⟨WShape.HasDom.single.2 (.inl hcapDom), ?_⟩
      intro x y hxy
      obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ := WShapeFun.mem_single.1 hxy
      · exact hnextTy.isType
      · exact .bot' .sort
    · exact WShape.HasDom.single.2 (.inl hcapDom)
    · simp only [WShapeFun.single_app]
      split <;> [exact hnextTy; exact .bot' (.bot' .sort)]
  · -- elemTy ≤ forallE tyDom tyFun : domain is literal; fun by one pair
    apply WShape.forallE_le_forallE.2
    refine ⟨.rfl, ?_⟩
    obtain ⟨x', hx', hmem⟩ := tyFun.app_eq argCap
    exact WShapeFun.single_le.2 ⟨x', _, hmem, hx', hnextLe⟩

/-- Empty fixed-head telescope.  Its initial and terminal type observations
are definitionally the supplied result type. -/
theorem LR.FixedHeadTelescope.nil
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr} {head outTy : TShape}
    (htyped : head.HasType outTy) :
    LR.FixedHeadTelescope (headTy := outTy) (outTy := outTy)
      Γ₀ mx my captureType
      (LE_Interp.RHS.ShapeSpine.nil (m2 := mcap) (head := head)) := by
  exact LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.nil htyped

/-- Prepend one synchronized application layer.

The aligned capture's exact element shape is reused as `argCap`; hence the
semantic spine argument lies below it, it is typed in the literal domain of
the constructed Pi observation, and the logical capture relation remains
indexed by that same pair. -/
theorem LR.FixedHeadTelescope.cons
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {n : Nat} {f : WShape (n + 1)} {a : WShape n}
    {m out : TShape} {path : p.Path} {paths : List p.Path}
    (harg : a.T ≤ mcap path) (happ : m ≤ (f.app a).T)
    (rest : LE_Interp.RHS.ShapeSpine mcap m paths out)
    {tyDom : WShape n} {tyFun : WShapeFun n} {argCap : WShape n}
    {outTy : TShape}
    (capture : LRS.CaptureDefEqAligned.AtShapes (LR Γ₀)
      (mcap path) (mx path) (my path) (captureType path)
      argCap tyDom)
    (tail : LR.FixedHeadTelescope
      (headTy := (tyFun.app argCap).T) (outTy := outTy)
      Γ₀ mx my captureType rest) :
    LR.FixedHeadTelescope
      (headTy := (WShape.forallE tyDom tyFun).T) (outTy := outTy)
      Γ₀ mx my captureType
      (LE_Interp.RHS.ShapeSpine.cons harg happ rest) := by
  have hargCap : a ≤ argCap :=
    WShape.LE.T_iff.1 (harg.trans capture.1)
  exact LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.cons
    harg happ hargCap capture.2.1 capture tail

/-- Forget the logical capture payload and recover the synchronized lower
head selected by the ordered term/type telescope. -/
theorem LR.FixedHeadTelescope.lowerHead
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (H : LR.FixedHeadTelescope (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine) :
    spine.TypedLowerHead headTy := by
  simpa only using H.telescope.lowerHead

/-- The joint certificate lands at the caller-specified result type shape. -/
theorem LR.FixedHeadTelescope.outHasType
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (H : LR.FixedHeadTelescope (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine) :
    out.HasType outTy := by
  exact H.telescope.outHasType

/-- Add the registered-type witness to the synchronized lower endpoint
without projecting semantic structure through a function-shape inequality. -/
theorem LR.FixedHeadTelescope.withWitness
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (H : LR.FixedHeadTelescope (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine)
    (hTy : LE_Interp.Witness ρ headTy B) :
    ∃ headElem headElemTy : TShape,
      headElem ≤ head ∧ headElem.HasType headElemTy ∧
        Nonempty (LE_Interp.Witness ρ headElemTy B) :=
  (LR.FixedHeadTelescope.lowerHead H).withWitness hTy

/-- The packed producer returns the synchronized lower endpoint and its
logical application chain in one elimination.  The type bound belongs to the
same recursive choices as the chain, so lowering `hTy` cannot be paired with
an independently reconstructed capture telescope. -/
theorem LR.FixedHeadTelescope.withWitnessAndChain
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    (H : LR.FixedHeadTelescope
      (headTy := headTy) (outTy := outTy.T)
      Γ₀ mx my captureType spine)
    (hTy : LE_Interp.Witness ρ headTy B)
    (houtNonbot : ¬out.T ≤ TShape.bot) :
    ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
      headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
        Nonempty (LE_Interp.Witness ρ headElemTy.T B) ∧
        LR.FixedHeadShapeChain Γ₀ mcap mx my captureType
          paths headElem headElemTy out outTy := by
  obtain ⟨headLevel, headElem, headElemTy, hhead, htyped,
    hheadTy, _hheadNonbot, chain⟩ :=
    LE_Interp.RHS.ShapeSpine.TypedTelescope.fixedHeadShapeChain
      H rfl rfl houtNonbot
  exact ⟨headLevel, headElem, headElemTy, hhead, htyped,
    ⟨hTy.mono hheadTy⟩, chain⟩

/-! ### The monotone fixed-head telescope

`LR.FixedHeadTelescope`'s terminal index is an *equality* index: its base
constructor identifies the observation the ordered type peel reaches with the
result observation the telescope is read at.  Those two are independently
determined — the reached observation is a function of the registered type and
the aligned capture shapes, while the result observation `outTy` is an input of
`LR.constDefEq`, fixed by the adequacy caller before any pattern is matched and
threaded verbatim to the leaf.  Identifying them is not merely unproved, it is
refutable (`LR.FixedHeadTerminalRetarget.not_general`).

`LR.FixedHeadTelescopeLE` replaces that equality by the single comparison
`outTy ≤ reached` at the base.  Every consumer below is the same theorem with
the same proof: the terminal index is read exactly twice — once for the
caller's own `out.HasType outTy`, which the monotone base records directly, and
once for the returned `headElemTy.T ≤ headTy` bound, which now travels through
the comparison. -/

/-- The synchronized producer certificate with a monotone terminal index. -/
def LR.FixedHeadTelescopeLE (Γ₀ : List SExpr)
    {p : Pattern} {mcap : p.Path → TShape}
    (mx my captureType : p.Path → SExpr)
    {head out headTy outTy : TShape} {paths : List p.Path}
    (spine : LE_Interp.RHS.ShapeSpine mcap head paths out) : Prop :=
  LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
    (m2 := mcap)
    (fun {n} path (elemShape typeShape : WShape n) =>
      LRS.CaptureDefEqAligned.AtShapes (LR Γ₀)
        (mcap path) (mx path) (my path) (captureType path)
        elemShape typeShape)
    head paths out headTy outTy

/-- Faithfulness: an exact telescope is a monotone one at the reflexive
comparison, so every existing producer still supplies the weakened premise. -/
theorem LR.FixedHeadTelescope.toLE
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (H : LR.FixedHeadTelescope (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine) :
    LR.FixedHeadTelescopeLE (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine :=
  LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.toLE H

/-- **THE O1 REPAIR AT THE TELESCOPE.**  Read a finished telescope at the
caller's own result observation, given the caller's own result typing and the
one comparison against the observation the peel reached.

This is what `LR.FixedHeadTerminalRetarget` tried and could not be: the
retarget demanded the two observations be *equal*, which is `HasType`
functionality at the terminal head and is false.  Here they are merely
compared, and the direction is the one every consumer needs — the head
observation is used only as an upper bound. -/
theorem LR.FixedHeadTelescope.retarget
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy reachedTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (H : LR.FixedHeadTelescope (headTy := headTy) (outTy := reachedTy)
      Γ₀ mx my captureType spine)
    (htyped : out.HasType outTy) (hle : outTy ≤ reachedTy) :
    LR.FixedHeadTelescopeLE (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine :=
  LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.retarget H htyped hle

/-- Empty monotone telescope: the caller's result typing plus the base
comparison. -/
theorem LR.FixedHeadTelescopeLE.nil
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr} {head headTy outTy : TShape}
    (htyped : head.HasType outTy) (hle : outTy ≤ headTy) :
    LR.FixedHeadTelescopeLE (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType
      (LE_Interp.RHS.ShapeSpine.nil (m2 := mcap) (head := head)) :=
  LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.nil htyped hle

/-- Prepend one synchronized application layer to a monotone telescope.
Verbatim `LR.FixedHeadTelescope.cons`; only the base differs. -/
theorem LR.FixedHeadTelescopeLE.cons
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {n : Nat} {f : WShape (n + 1)} {a : WShape n}
    {m out : TShape} {path : p.Path} {paths : List p.Path}
    (harg : a.T ≤ mcap path) (happ : m ≤ (f.app a).T)
    (rest : LE_Interp.RHS.ShapeSpine mcap m paths out)
    {tyDom : WShape n} {tyFun : WShapeFun n} {argCap : WShape n}
    {outTy : TShape}
    (capture : LRS.CaptureDefEqAligned.AtShapes (LR Γ₀)
      (mcap path) (mx path) (my path) (captureType path)
      argCap tyDom)
    (tail : LR.FixedHeadTelescopeLE
      (headTy := (tyFun.app argCap).T) (outTy := outTy)
      Γ₀ mx my captureType rest) :
    LR.FixedHeadTelescopeLE
      (headTy := (WShape.forallE tyDom tyFun).T) (outTy := outTy)
      Γ₀ mx my captureType
      (LE_Interp.RHS.ShapeSpine.cons harg happ rest) := by
  have hargCap : a ≤ argCap :=
    WShape.LE.T_iff.1 (harg.trans capture.1)
  exact LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.cons
    harg happ hargCap capture.2.1 capture tail

/-- The monotone certificate still lands at the caller's exact result type
shape — that is now recorded by its base rather than derived from an index
equality. -/
theorem LR.FixedHeadTelescopeLE.outHasType
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (H : LR.FixedHeadTelescopeLE (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine) :
    out.HasType outTy :=
  LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.outHasType H

/-- Forget the logical capture payload of a monotone telescope. -/
theorem LR.FixedHeadTelescopeLE.lowerHead
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (H : LR.FixedHeadTelescopeLE (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine) :
    spine.TypedLowerHead headTy := by
  simpa only using
    LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.lowerHead H

/-- Add the registered-type witness to a monotone telescope's synchronized
lower endpoint. -/
theorem LR.FixedHeadTelescopeLE.withWitness
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (H : LR.FixedHeadTelescopeLE (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine)
    (hTy : LE_Interp.Witness ρ headTy B) :
    ∃ headElem headElemTy : TShape,
      headElem ≤ head ∧ headElem.HasType headElemTy ∧
        Nonempty (LE_Interp.Witness ρ headElemTy B) :=
  (LR.FixedHeadTelescopeLE.lowerHead H).withWitness hTy

/-- The packed producer for the monotone telescope: same conclusion, same
proof, one comparison instead of one index equality. -/
theorem LR.FixedHeadTelescopeLE.withWitnessAndChain
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    (H : LR.FixedHeadTelescopeLE
      (headTy := headTy) (outTy := outTy.T)
      Γ₀ mx my captureType spine)
    (hTy : LE_Interp.Witness ρ headTy B)
    (houtNonbot : ¬out.T ≤ TShape.bot) :
    ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
      headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
        Nonempty (LE_Interp.Witness ρ headElemTy.T B) ∧
        LR.FixedHeadShapeChain Γ₀ mcap mx my captureType
          paths headElem headElemTy out outTy := by
  obtain ⟨headLevel, headElem, headElemTy, hhead, htyped,
    hheadTy, _hheadNonbot, chain⟩ :=
    LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.fixedHeadShapeChain
      H rfl rfl houtNonbot
  exact ⟨headLevel, headElem, headElemTy, hhead, htyped,
    ⟨hTy.mono hheadTy⟩, chain⟩

/-- Everything the fixed-head application consumer needs after the ordered
producer has finished.

The lower term/type pair is shared literally by self-adequacy and the
logical application chain.  The registered-type witness is retained at that
exact type observation, so the consumer never projects typing backwards
through a function-shape inequality or reselects an existential capture. -/
def LR.FixedHeadApplication (Γ₀ : List SExpr)
    {rho root X} (hX : LE_Interp.Witness rho root X) (depth : Nat)
    {p : Pattern} (mcap : p.Path → TShape)
    (mx my captureType : p.Path → SExpr)
    (paths : List p.Path) (headType resultType : SExpr)
    (head : TShape) {outLevel : Nat}
    (out outTy : WShape outLevel) : Prop :=
  ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
    headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
      Nonempty (LE_Interp.Witness rho headElemTy.T headType) ∧
      (LR Γ₀).DefEq X X headType headElem headElemTy ∧
      LR.FixedHeadExposedChain Γ₀ mcap mx my captureType
        paths headType resultType headElem headElemTy out outTy

/-- Use heterogeneous depth-bounded adequacy to validate a closed fixed
head at its registered displayed type.

Heterogeneous `AdequacyAtDepth` supplies the term relation directly, so no
raw type-uniqueness theorem or cast is needed for that half.  The exact
registered-type stratification separately supplies its `isType` derivation;
adequacy at the preceding type rung then validates the same lower type
observation.  Closedness removes the surrounding substitution after both
relations have been produced. -/
theorem LR.AdequacyAtDepth.closedHeadSelf
    (adequacy : LR.AdequacyAtDepth Γ₀ depth)
    (hstrong : IsDefEqStrong Δ X X headType)
    (hstrat : HasTypeStratifiedS Δ X headType core depth)
    (W : LR.SubstWF Γ₀ σ σ' Δ rho)
    (hXClosed : X.ClosedN) (hTypeClosed : headType.ClosedN)
    {n : Nat} {headElem headElemTy : WShape n}
    (hX : LE_Interp.Witness rho headElem.T X)
    (hTy : LE_Interp.Witness rho headElemTy.T headType)
    (htyped : headElem.HasType headElemTy) :
    (LR Γ₀).DefEq X X headType headElem headElemTy ∧
      (LR Γ₀).TyDefEq headType headType headElemTy := by
  have hrel :=
    ((adequacy hstrong hstrat hX.toInterp hTy.toInterp htyped).1 W).1
  rw [hXClosed.subst_eq .zero, hXClosed.subst_eq .zero,
    hTypeClosed.subst_eq .zero] at hrel
  obtain ⟨u, hTypeStrat⟩ := hstrat.isType
  have hTypeStrong : IsDefEqStrong Δ
      headType headType (.sort u) := hTypeStrat.strong
  obtain ⟨n', typeElem, sortElem, le_n, le_type,
      hTypeInterp, hSortInterp, hTypeTyped⟩ :=
    (LE_Interp.sound hTypeStrong W.left.fits).2 hTy.toInterp |>.out
  have hTypeAdequate :=
    (adequacy hTypeStrong (hTypeStrat.mono (Nat.sub_le depth 1))
      hTypeInterp hSortInterp hTypeTyped).2 W.left
  simp only [SExpr.subst] at hTypeAdequate
  rw [hTypeClosed.subst_eq .zero] at hTypeAdequate
  exact ⟨hrel, LR.toValTy le_n le_type htyped.isType
    hSortInterp hTypeTyped hTypeAdequate⟩

/-- Depth-bounded adequacy is contravariant in its depth index: a rung that
accepts every certificate of depth `depth` accepts every smaller one after
`HasTypeStratifiedS.mono`.  Larger index means strictly more admissible
inputs, hence a strictly stronger package. -/
theorem LR.AdequacyAtDepth.of_le {d depth : Nat} (hle : d ≤ depth)
    (adequacy : LR.AdequacyAtDepth Γ₀ depth) :
    LR.AdequacyAtDepth Γ₀ d := by
  intro n Γ ρ M N A B core m a H hstrat hM hA hmem
  exact adequacy H (hstrat.mono hle) hM hA hmem

/-- THE TYPE-RUNG RESIDUAL of the fixed-head application fold.

`LR.AdequacyAtDepth.closedHeadSelf` returns two components and consumes the
one `adequacy` hypothesis twice.  The two calls are *not* at the same rung:

* the term call has subject `X` and certificate `hstrat` at `depth` — that
  instance is literally an instance of `LR.SelfAdequateAt Γ₀ hX depth`, which
  the coherent algebra already holds at the same witness and depth;
* the type call has subject `headType` and certificate `hstrat.isType`, whose
  index is `depth - 1` (`HasTypeStratifiedS.isType`).  `closedHeadSelf` raises
  it back with `mono` only so that a single hypothesis can serve both calls.

This Prop isolates the second call.  Its depth index is the rung's, but the
adequacy it consumes is at `depth - 1`; see `of_predecessorAdequacy`, which
is a strict predecessor exactly when `0 < depth` (`of_lowerAdequacy`).
Nothing here is manufactured inside the induction: the demand is an interface
hypothesis of `LR.CoherentFixedHeadStep.of_steps`. -/
def LR.FixedHeadTypeValidStep (Γ₀ : List SExpr) (depth : Nat) : Prop :=
  ∀ {Δ : List SExpr} {ρ : Valuation} {σ σ' : Subst}
      {X headType : SExpr} {core : Bool}
      {n : Nat} {headElem headElemTy : WShape n},
    LR.SubstWF Γ₀ σ σ' Δ ρ →
    HasTypeStratifiedS Δ X headType core depth →
    headType.ClosedN →
    headElem.HasType headElemTy →
    LE_Interp.Witness ρ headElemTy.T headType →
    (LR Γ₀).TyDefEq headType headType headElemTy

/-- The type rung is discharged by adequacy at `depth - 1`, with no `mono`
anywhere: `HasTypeStratifiedS.isType` already lands there.  This is the exact
depth arithmetic of the fixed-head application fold. -/
theorem LR.FixedHeadTypeValidStep.of_predecessorAdequacy
    (adequacy : LR.AdequacyAtDepth Γ₀ (depth - 1)) :
    LR.FixedHeadTypeValidStep Γ₀ depth := by
  intro Δ ρ σ σ' X headType core n headElem headElemTy W hstrat
    hTypeClosed htyped hTy
  obtain ⟨u, hTypeStrat⟩ := hstrat.isType
  have hTypeStrong : IsDefEqStrong Δ headType headType (.sort u) :=
    hTypeStrat.strong
  obtain ⟨n', typeElem, sortElem, le_n, le_type,
      hTypeInterp, hSortInterp, hTypeTyped⟩ :=
    (LE_Interp.sound hTypeStrong W.left.fits).2 hTy.toInterp |>.out
  have hTypeAdequate :=
    (adequacy hTypeStrong hTypeStrat hTypeInterp hSortInterp hTypeTyped).2
      W.left
  simp only [SExpr.subst] at hTypeAdequate
  rw [hTypeClosed.subst_eq .zero] at hTypeAdequate
  exact LR.toValTy le_n le_type htyped.isType
    hSortInterp hTypeTyped hTypeAdequate

/-- Faithfulness: the same-rung package `closedHeadSelf` used to demand still
discharges the isolated type rung. -/
theorem LR.FixedHeadTypeValidStep.of_adequacyAtDepth
    (adequacy : LR.AdequacyAtDepth Γ₀ depth) :
    LR.FixedHeadTypeValidStep Γ₀ depth :=
  LR.FixedHeadTypeValidStep.of_predecessorAdequacy
    (adequacy.of_le (Nat.sub_le depth 1))

/-- The strict-predecessor form, stated so the decrease is visible.  At
`depth = 0` truncated subtraction collapses `depth - 1` onto the rung itself,
so this producer deliberately requires `0 < depth`: the depth-zero rung is
where the demand stops being a predecessor demand. -/
theorem LR.FixedHeadTypeValidStep.of_lowerAdequacy
    (hΓ₀ : Ctx.WF Γ₀) {depth : Nat} (hdepth : 0 < depth)
    (lower : ∀ d, d < depth → LR.ContextualAdequacyAtDepth d) :
    LR.FixedHeadTypeValidStep Γ₀ depth :=
  LR.FixedHeadTypeValidStep.of_predecessorAdequacy
    (lower (depth - 1) (Nat.sub_lt hdepth Nat.one_pos) hΓ₀)

/-- The conversion transport consumed while zipping the fixed-head
application chain, named rather than left as an anonymous callback.

It is *not* an instance of `LR.TyDefEq.of_defeq_of_stratifiedInversion`: that
lemma also demands the right endpoint's own validity `(LR Γ₀).TyDefEq B B a`,
which the chain zip has no producer for.  Recorded as a separate obligation
because `LR.FixedHeadTelescope.toApplicationWith` has always required it and
`LR.FixedHeadShapeChain.pathSemantics` fixes its shape.

**What it unfolds to** (corrected 2026-08-15 from
`plans/probes/probeW-disjointness.lean`; the previous account, on
`LR.FixedHeadConvertRightValid` below, was wrong in both directions).  The
conclusion is `TyDefEq A B a`, not `TyDefEq B B a`, so at `a = .sort r` the
step additionally demands that `A` and `B` reach the **same** sort.  Unfolded,
that is discharged from exactly three inputs — none of them `LRS.TypeWHNFEx`:
transport (`LRS.SortHeadNorm`, SLR), subject reduction (`LRS.SubjectRedS`, a
CR-ladder item), and sort injectivity (`LRS.SortInv`).  See
`LR.fixedHeadConvertStep_sort_of_parts` below.

**G4 (rung-0 consumption).**  This Prop is depth-free, so it has to hold at
rung `0` too — and there its sort observation would consume a `LRS.SortInv`
that is itself produced at rung `0`
(`LRS.SortInv.of_adequacyAtDepth_zero`).  That is a same-rung consumption at
exactly that rung, and it is not papered over: `LR.FixedHeadConvertStepAt`
below is the depth-indexed variant, modelled on `LR.SelfAdequateDefeqStepAt`,
which is vacuous at rung `0` (`LR.FixedHeadConvertStepAt.zero`) and at every
positive rung takes its `LRS.SortInv` from the *strictly lower* family
(`LR.fixedHeadConvertStepAt_sort_of_lowerAdequacy`).  The consumers still
demand the depth-free form; migrating them is a separate step, because the
`conv`/`ret` edges of `SExpr.PathSpineWF` carry no certificate to index on. -/
def LR.FixedHeadConvertStep (Γ₀ : List SExpr) : Prop :=
  ∀ {n : Nat} {A B : SExpr} {u : SLevel} {a : WShape n},
    IsDefEq Γ₀ A B (.sort u) →
    (LR Γ₀).TyDefEq A A a →
    (LR Γ₀).TyDefEq A B a

/-- The legacy fixed-head conversion contract is definitionally the legacy
half consumed by guarded completion.  This bridge lets the existing CR-ladder
producers feed the direct path zipper without restating their interface. -/
theorem LRD.FixedHeadLegacyConvertStep.of_legacy
    (legacy : LR.FixedHeadConvertStep Γ₀) :
    LRD.FixedHeadLegacyConvertStep Γ₀ :=
  legacy

/-- Package an existing legacy fixed-head conversion together with guarded
validity of its right endpoint into the conversion contract used by the direct
path zipper. -/
theorem LRD.FixedHeadConvertStep.of_legacy_and_right
    (legacy : LR.FixedHeadConvertStep Γ₀)
    (right : LRD.FixedHeadConvertRightValidStep Γ₀) :
    LRD.FixedHeadConvertStep Γ₀ :=
  LRD.FixedHeadConvertStep.of_parts
    (LRD.FixedHeadLegacyConvertStep.of_legacy legacy) right

/--
info: 'Lean4Lean.SExpr.LRD.FixedHeadLegacyConvertStep.of_legacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.FixedHeadLegacyConvertStep.of_legacy

/--
info: 'Lean4Lean.SExpr.LRD.FixedHeadConvertStep.of_legacy_and_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LRD.FixedHeadConvertStep.of_legacy_and_right

/-- THE ONE MISSING INPUT of `LR.FixedHeadConvertStep`: a raw type conversion
transports validity to its right endpoint at the *same* observation.

Naming it is what makes the recorded dead end usable.
`LR.TyDefEq.of_defeq_of_stratifiedInversion` (ADQ:1168) was rejected because
it additionally demands `(LR Γ₀).TyDefEq B B a`; that demand is exactly this
Prop, so the convert step is one line away from it (`of_rightValid` below)
rather than out of reach.

It is not leaf-local, and the reason is visible by unfolding the goal at each
observation.

**Corrected 2026-08-15** (`plans/probes/probeW-disjointness.lean`, Part 5).
The previous account here claimed the residual is `PiHeadNorm` =
`TypeWHNFEx` + `PiHeadStable`.  That is wrong in *both* directions, and
`LRS.TypeWHNFEx` never arises at all: this Prop carries `TyDefEq A A a` as a
**hypothesis**, so the left endpoint's weak-head normal form is *given*, not
manufactured.  What the two observations really are:

* At `a = .sort r`, `LogRel.sort_iff_ty` makes the obligation *exactly* the
  sort analogue of `LRS.PiHeadNorm`, namely `LRS.SortHeadNorm` (SLR) — a pure
  transport, nothing existential.  Machine-checked in **both** directions:
  `LR.fixedHeadConvertRightValid_sort_of_transport` (transport ⟹ obligation)
  and `LRS.SortHeadNorm.of_fixedHeadConvertRightValid` (obligation ⟹
  transport).  So nothing weaker suffices and nothing stronger is demanded.
* At `a = .forallE b f`, `LRS.TyDefEq.forallE_iff` unfolds the goal to
  `LRS.ValTyPi2` (`LR.tyDefEq_forallE_unfold`, SLR), whose first two conjuncts
  are the two weak-head reductions — that half *is* `LRS.PiHeadNorm`, and the
  CR ladder covers it — but whose remaining four conjuncts
  (`TypeDefEqPath` ×2, `TyDefEq B₁ B₂ b`, `LRS.PiDefEq`) are *semantic
  component* data the CR ladder does not produce.  That half is isolated as
  `LR.PiComponentTransport` (SLR); see
  `LR.fixedHeadConvertRightValid_forallE_of_parts`.

So the CR route covers the head-shape half at both observations and does not
cover the component half at the Pi observation.  Nothing weaker is available at
the consumer either: `SExpr.PathSpineWF`'s `conv`/`ret` edges carry a bare
`IsDefEq` and no shape, witness, or endpoint validity at all — the G5 gap in
its exact position. -/
def LR.FixedHeadConvertRightValid (Γ₀ : List SExpr) : Prop :=
  ∀ {n : Nat} {A B : SExpr} {u : SLevel} {a : WShape n},
    IsDefEq Γ₀ A B (.sort u) →
    (LR Γ₀).TyDefEq A A a →
    (LR Γ₀).TyDefEq B B a

/-- The convert step from the right-endpoint residual.  Recorded so the
inventory names the honest obligation: `FixedHeadConvertStep` is not an extra
gap beside the inversion package, it is that package plus validity transport.

**Read the price honestly** (corrected 2026-08-15).  The docstring on
`LR.FixedHeadConvertRightValid` above used to say the convert step is "one
line away" from `LR.TyDefEq.of_defeq_of_stratifiedInversion`.  The *line* is
one line; the *input* is not.  `inv` here is the full, uncollapsed
`JointStratifiedInversion`: its `sortInv` field is unbounded-depth sort
injectivity, and its `forallEInv` field is `IsDefEq`-valued — i.e. already
collapsed — Pi inversion with endpoint stratification bookkeeping at `n - 1`,
which is strictly stronger than the path-valued `LRS.PiPathInv` the rest of
the development charges.  So this route buys the convert step at the price of
the whole inversion package, path collapse included.  The per-observation
theorems below buy the same observations at CR-ladder prices instead. -/
theorem LR.FixedHeadConvertStep.of_rightValid
    (inv : JointStratifiedInversion) (hΓ₀ : Ctx.WF Γ₀)
    (right : LR.FixedHeadConvertRightValid Γ₀) :
    LR.FixedHeadConvertStep Γ₀ := by
  intro n A B u a hEq hAA
  exact LR.TyDefEq.of_defeq_of_stratifiedInversion inv hΓ₀ hEq hAA
    (right hEq hAA)

/-! #### The two observations, at CR-ladder prices

Ported from `plans/probes/probeW-disjointness.lean` Part 5.  The generic
unfoldings (`LR.tyDefEq_sort_self_iff`, `LR.tyDefEq_sort_iff`,
`LR.tyDefEq_forallE_unfold`) and the two named residuals (`LRS.SortHeadNorm`,
`LR.PiComponentTransport`) live in `ShapeLogRel.lean`; what is here is what
names the ADQ obligations. -/

omit [Params.Semantic] in
/-- **The caveat, half one.**  The sort observation of
`LR.FixedHeadConvertRightValid` follows from a pure *transport*. -/
theorem LR.fixedHeadConvertRightValid_sort_of_transport {Γ₀ : List SExpr}
    (hΓ₀ : Ctx.WF Γ₀) (norm : LRS.SortHeadNorm) {n : Nat} {A B : SExpr}
    {u : SLevel} {r : Bool}
    (hEq : IsDefEq Γ₀ A B (.sort u))
    (hAA : (LR Γ₀ : LogRel Γ₀ n).TyDefEq A A (.sort r)) :
    (LR Γ₀ : LogRel Γ₀ n).TyDefEq B B (.sort r) := by
  obtain ⟨w, hred⟩ := LR.tyDefEq_sort_self_iff.1 hAA
  obtain ⟨w', hred'⟩ := norm hΓ₀ hEq hred
  exact LR.tyDefEq_sort_self_iff.2 ⟨w', hred'⟩

omit [Params.Semantic] in
/-- **The caveat, half two.**  Conversely, the sort observation of
`LR.FixedHeadConvertRightValid` *is* that transport: nothing weaker suffices,
and nothing stronger is demanded.  In particular `LRS.TypeWHNFEx` is neither
needed nor implied. -/
theorem LRS.SortHeadNorm.of_fixedHeadConvertRightValid
    (right : ∀ Γ₀ : List SExpr, LR.FixedHeadConvertRightValid Γ₀) :
    LRS.SortHeadNorm := by
  intro Γ X Y w s _ hEq hred
  have hXX : (LR Γ : LogRel Γ 0).TyDefEq X X (WShape.sort true) :=
    LR.tyDefEq_sort_self_iff.2 ⟨w, hred⟩
  exact LR.tyDefEq_sort_self_iff.1 (right Γ hEq hXX)

omit [Params.Semantic] in
/-- **The Pi observation, split.**  `LRS.PiHeadNorm` supplies the head-shape
half, which the CR ladder covers; `LR.PiComponentTransport` supplies the rest,
which it does not. -/
theorem LR.fixedHeadConvertRightValid_forallE_of_parts {Γ₀ : List SExpr}
    (hΓ₀ : Ctx.WF Γ₀) (norm : LRS.PiHeadNorm) (comp : LR.PiComponentTransport Γ₀)
    {n : Nat} {A B : SExpr} {u : SLevel} {b : WShape n} {f : WShapeFun n}
    (hEq : IsDefEq Γ₀ A B (.sort u))
    (hAA : (LR Γ₀ : LogRel Γ₀ (n+1)).TyDefEq A A (.forallE b f)) :
    (LR Γ₀ : LogRel Γ₀ (n+1)).TyDefEq B B (.forallE b f) := by
  obtain ⟨B₁, F₁, _, _, _, _, hred, _, _, _, _, _⟩ :=
    LR.tyDefEq_forallE_unfold.1 hAA
  obtain ⟨B₂, F₂, hredB⟩ := norm hΓ₀ hEq hred
  obtain ⟨u', v', hdom, hcod, hty, hpi⟩ := comp hEq hAA hredB hredB
  exact LR.tyDefEq_forallE_unfold.2
    ⟨B₂, F₂, B₂, F₂, u', v', hredB, hredB, hdom, hcod, hty, hpi⟩

omit [Params.Semantic] in
/-- **The step itself, not just its right-endpoint residual.**
`LR.FixedHeadConvertStep` concludes `TyDefEq A B a`, so its sort case
additionally demands that `A` and `B` reach the *same* sort.  Discharged from
three inputs, none of which is `LRS.TypeWHNFEx`: transport
(`LRS.SortHeadNorm`), subject reduction (`LRS.SubjectRedS`, a CR-ladder item),
and sort injectivity (`LRS.SortInv`, the depth-0 item). -/
theorem LR.fixedHeadConvertStep_sort_of_parts {Γ₀ : List SExpr}
    (hΓ₀ : Ctx.WF Γ₀) (sr : LRS.SubjectRedS) (norm : LRS.SortHeadNorm)
    (sinv : LRS.SortInv) {n : Nat} {A B : SExpr} {u : SLevel} {r : Bool}
    (hEq : IsDefEq Γ₀ A B (.sort u))
    (hAA : (LR Γ₀ : LogRel Γ₀ n).TyDefEq A A (.sort r)) :
    (LR Γ₀ : LogRel Γ₀ n).TyDefEq A B (.sort r) := by
  obtain ⟨w, hredA⟩ := LR.tyDefEq_sort_self_iff.1 hAA
  obtain ⟨w', hredB⟩ := norm hΓ₀ hEq hredA
  have hA' : IsDefEq Γ₀ A (.sort w) (.sort u) := sr hΓ₀ hredA hEq.hasType.1
  have hB' : IsDefEq Γ₀ B (.sort w') (.sort u) := sr hΓ₀ hredB hEq.hasType.2
  cases sinv hΓ₀ (hA'.symm.trans (hEq.trans hB'))
  exact LR.tyDefEq_sort_iff.2 ⟨w, hredA, hredB⟩

/-! #### The convert step, discharged (2026-08-15)

The account above stops at "the CR route covers the head-shape half at both
observations and does not cover the component half at the Pi observation".
That is a correct reading of *one* unfolding, and a wrong reading of the
obligation.  `plans/probes/probeR12-picomponent.lean` and `LR.convertStepAt_all`
(SLR) show why: **the component half at the Pi observation is the same
statement one shape level down**, so `LR.FixedHeadConvertStep` is not a
fixed set of residuals but an induction on the shape level, and
`LR.PiComponentTransport` is its inductive step rather than a new input.

The two theorems below are the consequence, stated against the ADQ `Prop`s.
The induction is on the *shape level*, which is orthogonal to the adequacy
rung, so the G4 note in the next subsection is untouched: `LRS.SortInv` is
still consumed at the sort observation at every level, exactly as before, and
`LR.FixedHeadConvertStepAt` remains the right mitigation. -/

/-- **HEADLINE.**  `LR.FixedHeadConvertStep` — recorded above as "THE ONE
MISSING INPUT" — from the CR ladder, `LRS.SortInv` (adequacy rung `0`) and one
new head-form transport.

Of the six inputs, four are CR-ladder rungs (`LRS.SubjectRedS`,
`LRS.SortHeadNorm`, `LRS.PiHeadNorm`, `LRS.PiEdgeInv`), one is the depth-0
adequacy item `LRS.SortInv` that the sort observation already charged, and one
is new: `LRS.IndTyHeadNorm`, the `indTy` analogue of the other two head-form
transports.  Nothing here is `LRS.TypeWHNFEx`, path collapse, or
`JointStratifiedInversion`; in particular this route does *not* pay the price
that `LR.FixedHeadConvertStep.of_rightValid` pays.

**What the ladder rungs cost** (2026-08-15).  `LRS.PiEdgeInv` and
`LRS.PiHeadNorm` are inside the loop recorded on
`LRS.crComplete_is_the_last_input` (SLR) — they are interderivable with
`LRS.PiPathInv`, the 16C′ leaf.  So the correct reading of this theorem is not
"the convert step is now free" but the sharper and still valuable one: **the
convert step demands nothing beyond the leaf itself**, plus `LRS.SortInv` at
rung `0` and one genuinely new head-form transport.  It was recorded as a
separate, unrelated obligation; it is not one. -/
theorem LR.FixedHeadConvertStep.of_crLadder {Γ₀ : List SExpr}
    (hΓ₀ : Ctx.WF Γ₀) (sr : LRS.SubjectRedS) (snorm : LRS.SortHeadNorm)
    (sinv : LRS.SortInv) (norm : LRS.PiHeadNorm) (inv : LRS.PiEdgeInv)
    (ind : LRS.IndTyHeadNorm) : LR.FixedHeadConvertStep Γ₀ :=
  fun {n} => LR.convertStepAt_all hΓ₀ sr snorm sinv norm inv ind n

/-- And hence the right-endpoint residual, by `symm_ty ∘ left_ty`. -/
theorem LR.FixedHeadConvertRightValid.of_crLadder {Γ₀ : List SExpr}
    (hΓ₀ : Ctx.WF Γ₀) (sr : LRS.SubjectRedS) (snorm : LRS.SortHeadNorm)
    (sinv : LRS.SortInv) (norm : LRS.PiHeadNorm) (inv : LRS.PiEdgeInv)
    (ind : LRS.IndTyHeadNorm) : LR.FixedHeadConvertRightValid Γ₀ :=
  fun hEq hAA => (LR Γ₀).left_ty ((LR Γ₀).symm_ty
    (LR.FixedHeadConvertStep.of_crLadder hΓ₀ sr snorm sinv norm inv ind hEq hAA))

/-- The same with `LRS.PiEdgeInv` discharged by rung R11
(`LRS.PiEdgeInv.of_crLadder_noAdequacy`, SLR) and `LRS.PiHeadNorm` by
`LRS.PiHeadNorm.of_crLadder_noAdequacy`, so that only rungs with no producer
remain visible.  Four inputs: three CR-ladder rungs, `LRS.SortInv` at adequacy
rung `0`, and the one new head-form transport. -/
theorem LR.FixedHeadConvertStep.of_crLadder_R11 {Γ₀ : List SExpr}
    (hΓ₀ : Ctx.WF Γ₀) (srp : LRS.ParRedSDefeq) (cr : LRS.CRComplete)
    (std : LRS.PiStandard) (snorm : LRS.SortHeadNorm) (sinv : LRS.SortInv)
    (ind : LRS.IndTyHeadNorm) : LR.FixedHeadConvertStep Γ₀ :=
  have sr : LRS.SubjectRedS := LRS.SubjectRedS.of_parRedSDefeq srp
  LR.FixedHeadConvertStep.of_crLadder hΓ₀ sr snorm sinv
    (LRS.PiHeadNorm.of_crLadder_noAdequacy sr cr std)
    (LRS.PiEdgeInv.of_crLadder_noAdequacy srp cr) ind

/-! #### G4: the depth-indexed convert step

`LR.FixedHeadConvertStep` is depth-free, so it must hold at rung `0`, and its
sort observation there would consume a `LRS.SortInv` produced at rung `0` —
same-rung, at exactly that rung.  The mitigation is the one
`LR.SelfAdequateDefeqStepAt` already uses: index the Prop by the rung, and gate
it on a stratification certificate for the left endpoint at a *strictly*
smaller depth.  The index has one job, and the arithmetic makes it explicit:
`depth < outerDepth` forces `0 < outerDepth`, which is exactly what puts rung
`0` inside the strictly-lower family.

Landed **beside** the depth-free Prop rather than replacing it.  Migrating the
consumers is not a one-step change: `convert` is spent inside
`LR.FixedHeadShapeChain.pathSemantics` while zipping a `SExpr.PathSpineWF`,
whose `conv`/`ret` edges carry a bare `IsDefEq` and no stratification
certificate to index on.  Supplying one there is the G5 gap, not this one. -/

/-- Depth-indexed `LR.FixedHeadConvertStep`, shaped like
`LR.SelfAdequateDefeqStepAt`: the left endpoint arrives with a stratification
certificate strictly below the rung. -/
def LR.FixedHeadConvertStepAt (Γ₀ : List SExpr) (outerDepth : Nat) : Prop :=
  ∀ {n : Nat} {A B : SExpr} {u : SLevel} {a : WShape n}
      {core : Bool} {depth : Nat},
    depth < outerDepth →
    HasTypeStratifiedS Γ₀ A (.sort u) core depth →
    IsDefEq Γ₀ A B (.sort u) →
    (LR Γ₀).TyDefEq A A a →
    (LR Γ₀).TyDefEq A B a

omit [Params.Semantic] in
/-- The indexed form is a weakening of the depth-free one, so demanding it can
never demand more than the current interface does. -/
theorem LR.FixedHeadConvertStep.at (h : LR.FixedHeadConvertStep Γ₀)
    (outerDepth : Nat) : LR.FixedHeadConvertStepAt Γ₀ outerDepth :=
  fun _ _ hEq hAA => h hEq hAA

omit [Params.Semantic] in
/-- **The G4 mitigation, stated.**  At rung `0` the indexed step is
unconditional, so the rung that *produces* `LRS.SortInv` consumes nothing from
itself.  The same-rung consumption exists only for the depth-free Prop. -/
theorem LR.FixedHeadConvertStepAt.zero :
    LR.FixedHeadConvertStepAt Γ₀ 0 :=
  fun hdepth _ _ _ => absurd hdepth (Nat.not_lt_zero _)

/-- **The G4 mitigation, discharged at every positive rung.**  The sort
observation of the indexed step takes its `LRS.SortInv` from the strictly
lower adequacy family, because the certificate's `depth < outerDepth` already
forces `0 < outerDepth` and `LRS.SortInv` is produced at rung `0`.  Nothing is
consumed at the rung being built. -/
theorem LR.fixedHeadConvertStepAt_sort_of_lowerAdequacy {Γ₀ : List SExpr}
    (hΓ₀ : Ctx.WF Γ₀) (sr : LRS.SubjectRedS) (norm : LRS.SortHeadNorm)
    {outerDepth : Nat}
    (lower : ∀ d, d < outerDepth → LR.ContextualAdequacyAtDepth d)
    {n : Nat} {A B : SExpr} {u : SLevel} {r : Bool}
    {core : Bool} {depth : Nat}
    (hdepth : depth < outerDepth)
    (_hstrat : HasTypeStratifiedS Γ₀ A (.sort u) core depth)
    (hEq : IsDefEq Γ₀ A B (.sort u))
    (hAA : (LR Γ₀ : LogRel Γ₀ n).TyDefEq A A (.sort r)) :
    (LR Γ₀ : LogRel Γ₀ n).TyDefEq A B (.sort r) :=
  LR.fixedHeadConvertStep_sort_of_parts hΓ₀ sr norm
    (LRS.SortInv.of_lowerAdequacy
      (Nat.lt_of_le_of_lt (Nat.zero_le depth) hdepth) lower) hEq hAA

/-! ##### Vacuity check for `LR.FixedHeadConvertStepAt`

Standing policy: every new `Prop` exhibits an inhabitant or an attempted
derivation of `False`.  `LR.FixedHeadConvertStepAt Γ₀ 0` is inhabited
vacuously (`.zero`), and that alone would be a weak certificate, so the lemma
below checks a *positive* rung: at `outerDepth = 1` every hypothesis of the
Prop is simultaneously satisfiable **and** the conclusion holds there.  So the
Prop is neither empty-hypothesis vacuous nor refutable at the one instance
that can be computed outright.  No derivation of `False` was found; the Prop is
also implied by the depth-free one (`LR.FixedHeadConvertStep.at`), which
`LR.FixedHeadConvertStep.of_rightValid` already produces from
`JointStratifiedInversion`. -/

omit [Params.Semantic] in
/-- Non-vacuity at a positive rung: the five components below are, in order,
the depth gate, the stratification certificate, the type equality, the left
validity — i.e. all four hypotheses of `LR.FixedHeadConvertStepAt Γ₀ 1` — and
then its conclusion, all met at once by a syntactic sort. -/
theorem LR.fixedHeadConvertStepAt_nonvacuous {Γ₀ : List SExpr} {w : SLevel}
    {r : Bool} :
    (0 : Nat) < 1 ∧
      HasTypeStratifiedS Γ₀ (.sort w) (.sort w.succ) true 0 ∧
      IsDefEq Γ₀ (.sort w) (.sort w) (.sort w.succ) ∧
      (LR Γ₀ : LogRel Γ₀ 0).TyDefEq (.sort w) (.sort w) (WShape.sort r) ∧
      (LR Γ₀ : LogRel Γ₀ 0).TyDefEq (.sort w) (.sort w) (WShape.sort r) :=
  ⟨Nat.one_pos, HasTypeStratifiedS.sort_zero, .sort,
    LR.tyDefEq_sort_self_iff.2 ⟨w, .rfl⟩,
    LR.tyDefEq_sort_self_iff.2 ⟨w, .rfl⟩⟩

/-- Finish a fixed-head application package from one packed telescope and
the semantic type equalities justified at the caller's derivation-aware
boundary.

`headSelf` is invoked only for the literal lower head/type/witness triple
returned by `withWitnessAndChain`.  Likewise, `convert` is used only while
zipping the supplied `PathSpineWF`; it is never promoted to an ambient
conversion oracle.  This keeps the proof-relevant endpoint choice inside
one elimination while leaving the well-founded source of the type
equalities explicit in the producer's signature. -/
theorem LR.FixedHeadTelescope.toApplicationWith
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    {headType resultType : SExpr}
    {hX : LE_Interp.Witness rho root X} {depth : Nat}
    (H : LR.FixedHeadTelescope
      (headTy := headTy) (outTy := outTy.T)
      Γ₀ mx my captureType spine)
    (hTy : LE_Interp.Witness rho headTy headType)
    (houtNonbot : ¬out.T ≤ TShape.bot)
    (raw : SExpr.PathSpineWF Γ₀ mx captureType
      headType paths resultType)
    (resultRel : (LR Γ₀).TyDefEq
      resultType resultType outTy)
    (convert : ∀ {n : Nat} {A B : SExpr} {u : SLevel}
        {a : WShape n},
      IsDefEq Γ₀ A B (.sort u) →
      (LR Γ₀).TyDefEq A A a →
      (LR Γ₀).TyDefEq A B a)
    (headSelf : ∀ {headLevel : Nat}
        {headElem headElemTy : WShape headLevel},
      headElem.T ≤ head →
      headElem.HasType headElemTy →
      LE_Interp.Witness rho headElemTy.T headType →
      (LR Γ₀).DefEq X X headType headElem headElemTy ∧
        (LR Γ₀).TyDefEq headType headType headElemTy) :
    LR.FixedHeadApplication Γ₀ hX depth
      mcap mx my captureType paths headType resultType head out outTy := by
  obtain ⟨headLevel, headElem, headElemTy, hhead, htyped,
    ⟨hheadTy⟩, chain⟩ :=
    H.withWitnessAndChain hTy houtNonbot
  have ⟨hheadTermRel, hheadRel⟩ :=
    headSelf hhead htyped hheadTy
  have semantics : LR.FixedHeadPathSemantics Γ₀
      mcap mx my captureType chain raw :=
    chain.pathSemantics raw hheadRel resultRel convert
  exact ⟨headLevel, headElem, headElemTy, hhead, htyped,
    ⟨hheadTy⟩, hheadTermRel, semantics.exposed⟩

/-- The same fold for the monotone telescope.  Every input is unchanged,
including `resultRel` — the caller's `hA`, at the caller's own `outTy`, which
is where the terminal observation was always going to have to be reconciled. -/
theorem LR.FixedHeadTelescopeLE.toApplicationWith
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    {headType resultType : SExpr}
    {hX : LE_Interp.Witness rho root X} {depth : Nat}
    (H : LR.FixedHeadTelescopeLE
      (headTy := headTy) (outTy := outTy.T)
      Γ₀ mx my captureType spine)
    (hTy : LE_Interp.Witness rho headTy headType)
    (houtNonbot : ¬out.T ≤ TShape.bot)
    (raw : SExpr.PathSpineWF Γ₀ mx captureType
      headType paths resultType)
    (resultRel : (LR Γ₀).TyDefEq
      resultType resultType outTy)
    (convert : ∀ {n : Nat} {A B : SExpr} {u : SLevel}
        {a : WShape n},
      IsDefEq Γ₀ A B (.sort u) →
      (LR Γ₀).TyDefEq A A a →
      (LR Γ₀).TyDefEq A B a)
    (headSelf : ∀ {headLevel : Nat}
        {headElem headElemTy : WShape headLevel},
      headElem.T ≤ head →
      headElem.HasType headElemTy →
      LE_Interp.Witness rho headElemTy.T headType →
      (LR Γ₀).DefEq X X headType headElem headElemTy ∧
        (LR Γ₀).TyDefEq headType headType headElemTy) :
    LR.FixedHeadApplication Γ₀ hX depth
      mcap mx my captureType paths headType resultType head out outTy := by
  obtain ⟨headLevel, headElem, headElemTy, hhead, htyped,
    ⟨hheadTy⟩, chain⟩ :=
    H.withWitnessAndChain hTy houtNonbot
  have ⟨hheadTermRel, hheadRel⟩ :=
    headSelf hhead htyped hheadTy
  have semantics : LR.FixedHeadPathSemantics Γ₀
      mcap mx my captureType chain raw :=
    chain.pathSemantics raw hheadRel resultRel convert
  exact ⟨headLevel, headElem, headElemTy, hhead, htyped,
    ⟨hheadTy⟩, hheadTermRel, semantics.exposed⟩

/-- Finish the packed fixed-head application using the exact registered-head
typing at one strictly earlier adequacy rung.

This is the conversion-safe producer adapter.  Heterogeneous
`AdequacyAtDepth` validates the exact lower head selected by the packed
telescope without a raw type cast; the registered derivation validates that
same lower type observation.  Both relations are retained in
`FixedHeadApplication`. -/
theorem LR.FixedHeadTelescope.toApplicationWithAdequacyAtDepth
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    {headType resultType : SExpr}
    {hX : LE_Interp.Witness rho root X} {depth : Nat}
    (H : LR.FixedHeadTelescope
      (headTy := headTy) (outTy := outTy.T)
      Γ₀ mx my captureType spine)
    (hTy : LE_Interp.Witness rho headTy headType)
    (houtNonbot : ¬out.T ≤ TShape.bot)
    (raw : SExpr.PathSpineWF Γ₀ mx captureType
      headType paths resultType)
    (resultRel : (LR Γ₀).TyDefEq
      resultType resultType outTy)
    (convert : ∀ {n : Nat} {A B : SExpr} {u : SLevel}
        {a : WShape n},
      IsDefEq Γ₀ A B (.sort u) →
      (LR Γ₀).TyDefEq A A a →
      (LR Γ₀).TyDefEq A B a)
    (adequacy : LR.AdequacyAtDepth Γ₀ depth)
    (hhead : head ≤ root)
    (hstrong : IsDefEqStrong Δ X X headType)
    (hstrat : HasTypeStratifiedS Δ X headType core depth)
    (W : LR.SubstWF Γ₀ σ σ' Δ rho)
    (hXClosed : X.ClosedN) (hTypeClosed : headType.ClosedN) :
    LR.FixedHeadApplication Γ₀ hX depth
      mcap mx my captureType paths headType resultType head out outTy := by
  apply H.toApplicationWith hTy houtNonbot raw resultRel convert
  intro headLevel headElem headElemTy helem htyped hheadTy
  exact adequacy.closedHeadSelf hstrong hstrat W hXClosed hTypeClosed
    (hX.mono (helem.trans hhead)) hheadTy htyped

/-- The proof-independent result required from one exact fixed RHS head.
It consumes the rule's semantic `ShapeSpine`, the two typed capture spines,
and aligned capture relations to produce the generated RHS relation. -/
def LR.FixedHeadResult (Γ₀ : List SExpr)
    (hX : LE_Interp.Witness ρ root X) : Prop :=
  ∀ {Δ : List SExpr} {σ σ' : Subst},
    LR.SubstWF Γ₀ σ σ' Δ ρ →
    ∀ {n : Nat}
      {rec ctor : Name} {major arity : Nat}
      {recLs : List SLevel}
      {mrec : (Pattern.varN (.const rec) major).Path → TShape}
      {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
      {head headTy : TShape}
      {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {A : SExpr} {outTy : WShape (n + 1)},
    X = SExpr.mkInst recLs rule.df.rhs →
    head ≤ root →
    IsDefEqStrong Δ X X (SExpr.mkInst recLs rule.df.type) →
    ∀ hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
      head rule.capturePaths out.T,
    LR.FixedHeadTelescopeLE (headTy := headTy) (outTy := outTy.T)
      Γ₀ mx my captureType hshape →
    LE_Interp.Witness ρ headTy (SExpr.mkInst recLs rule.df.type) →
    SExpr.PathSpineWF Γ₀ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    SExpr.PathSpineWF Γ₀ my captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LRS.CaptureDefEqAligned (LR (n := n + 1) Γ₀) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned (LR (n := n) Γ₀) (mctor p)
          (mx path) (my path) (captureType path)) →
    out.HasType outTy →
    (LR (n := n + 1) Γ₀).TyDefEq A A outTy →
    (LR (n := n + 1) Γ₀).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy

/-- The fixed-head result at one explicit stratified typing depth.

The proof-relevant semantic recursion is Nat-first: conversion may restart
from an arbitrary witness only after the typing depth decreases.  Retaining
the depth here prevents a same-witness producer from silently consuming the
depth-polymorphic result it is still constructing.  The public
`FixedHeadResult` is recovered below only after this predicate has been
constructed at every depth. -/
def LR.FixedHeadResultAt (Γ₀ : List SExpr)
    (hX : LE_Interp.Witness ρ root X) (depth : Nat) : Prop :=
  ∀ {Δ : List SExpr} {σ σ' : Subst},
    LR.SubstWF Γ₀ σ σ' Δ ρ →
    ∀ {n : Nat}
      {rec ctor : Name} {major arity : Nat}
      {recLs : List SLevel}
      {mrec : (Pattern.varN (.const rec) major).Path → TShape}
      {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
      {head headTy : TShape}
      {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {A : SExpr} {outTy : WShape (n + 1)},
    X = SExpr.mkInst recLs rule.df.rhs →
    head ≤ root →
    IsDefEqStrong Δ X X (SExpr.mkInst recLs rule.df.type) →
    HasTypeStratifiedS Δ X (SExpr.mkInst recLs rule.df.type) true depth →
    ∀ hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
      head rule.capturePaths out.T,
    LR.FixedHeadTelescopeLE (headTy := headTy) (outTy := outTy.T)
      Γ₀ mx my captureType hshape →
    LE_Interp.Witness ρ headTy (SExpr.mkInst recLs rule.df.type) →
    SExpr.PathSpineWF Γ₀ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    SExpr.PathSpineWF Γ₀ my captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LRS.CaptureDefEqAligned (LR (n := n + 1) Γ₀) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned (LR (n := n) Γ₀) (mctor p)
          (mx path) (my path) (captureType path)) →
    out.HasType outTy →
    (LR (n := n + 1) Γ₀).TyDefEq A A outTy →
    (LR (n := n + 1) Γ₀).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy

/-- Forget the explicit stratification certificate when an already-complete
fixed-head result is available. -/
theorem LR.FixedHeadResult.at
    (H : LR.FixedHeadResult Γ₀ hX) (depth : Nat) :
    LR.FixedHeadResultAt Γ₀ hX depth := by
  intro Δ σ σ' W n rec ctor major arity recLs mrec mctor r rule out head
    headTy mx my captureType A outTy hsyntax hhead hstrong _hstrat hshape
    htel hTyReg hspineX hspineY hcap hout hA
  exact H W hsyntax hhead hstrong hshape htel hTyReg
    hspineX hspineY hcap hout hA

/-- Recover the proof-independent API once the Nat-first recursion has
constructed its depth-indexed result for every stratification depth. -/
theorem LR.FixedHeadResult.of_forall_at
    (H : ∀ depth, LR.FixedHeadResultAt Γ₀ hX depth) :
    LR.FixedHeadResult Γ₀ hX := by
  intro Δ σ σ' W n rec ctor major arity recLs mrec mctor r rule out head
    headTy mx my captureType A outTy hsyntax hhead hstrong hshape
    htel hTyReg hspineX hspineY hcap hout hA
  obtain ⟨depth, hleft, _⟩ := hstrong.stratify
  exact H depth W hsyntax hhead hstrong hleft hshape htel hTyReg
    hspineX hspineY hcap hout hA

theorem LR.FixedHeadResultAt.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LR.FixedHeadResultAt Γ₀ hX depth) :
    LR.FixedHeadResultAt Γ₀ (hX.mono hle) depth := by
  intro Δ σ σ' W n rec ctor major arity recLs mrec mctor r rule out head
    headTy mx my captureType A outTy hsyntax hhead hstrong hstrat hshape
    htel hTyReg hspineX hspineY hcap hout hA
  exact H W hsyntax (hhead.trans hle) hstrong hstrat hshape htel hTyReg
    hspineX hspineY hcap hout hA

theorem LR.FixedHeadResult.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LR.FixedHeadResult Γ₀ hX) :
    LR.FixedHeadResult Γ₀ (hX.mono hle) := by
  intro Δ σ σ' W n rec ctor major arity recLs mrec mctor r rule out head
    headTy mx my captureType A outTy hsyntax hhead hstrong hshape
    htel hTyReg hspineX hspineY hcap hout hA
  exact H W hsyntax (hhead.trans hle) hstrong hshape htel hTyReg
    hspineX hspineY hcap hout hA

theorem LR.FixedHeadResult.bot
    {nroot : Nat} {X : SExpr} :
    LR.FixedHeadResult Γ₀
      (LE_Interp.Witness.bot (ρ := ρ) (n := nroot) (M := X)) := by
  intro Δ σ σ' W n rec ctor major arity recLs mrec mctor r rule out head
    headTy mx my captureType A outTy hsyntax hhead hstrong hshape
    htel hTyReg hspineX hspineY hcap hout hA
  have hheadBot : head ≤ TShape.bot :=
    hhead.trans TShape.bot_eqv.1
  have houtBot : out.T ≤ TShape.bot := hshape.le_bot hheadBot
  have houtEq : out = .bot := TShape.le_bot.1 houtBot
  subst out
  exact (LR Γ₀).bot hout.isType

/-- A bound variable cannot be the closed registered fixed head of an iota
rule.  This constructor is therefore discharged before inspecting either
the semantic application spine or any logical capture evidence. -/
theorem LR.FixedHeadResult.bvar
    {ρ : Valuation} {root : TShape} {i : Nat}
    (hle : root ≤ ρ i) :
    LR.FixedHeadResult Γ₀ (LE_Interp.Witness.bvar hle) := by
  intro Δ σ σ' W n rec ctor major arity recLs mrec mctor r rule out head
    headTy mx my captureType A outTy hsyntax hhead hstrong hshape
    htel hTyReg hspineX hspineY hcap hout hA
  have hclosed : (SExpr.bvar i).ClosedN 0 := by
    rw [hsyntax]
    exact rule.rhsClosed.mkInstS
  simp [SExpr.ClosedN] at hclosed

/-- A fixed sort head either remains a sort when the generated capture
spine is empty or collapses to bottom at its first application.  This is the
first constructor of the canonical fixed-head algebra; it is independent of
semantic recursion because sorts have no ordinary or abstract children. -/
theorem LR.FixedHeadResult.sort
    (hroot : root ≤ TShape.sort (decide (l ≠ SLevel.zero))) :
    LR.FixedHeadResult Γ₀
      (LE_Interp.Witness.sort (ρ := ρ) (l := l) hroot) := by
  intro Δ σ σ' W n rec ctor major arity recLs mrec mctor r rule out head
    headTy mx my captureType A outTy hsyntax hhead hstrong hshape
    htel hTyReg hspineX hspineY hcap hout hA
  generalize hpaths : rule.capturePaths = paths at hshape hspineX hspineY
  cases hshape with
  | nil =>
    have hrhsX : r.1.applyS recLs mx = .sort l := by
      rw [← rule.rhsApply, hpaths]
      simpa only [List.map_nil, List.foldl_nil] using hsyntax.symm
    have hrhsY : r.1.applyS recLs my = .sort l := by
      rw [← rule.rhsApply, hpaths]
      simpa only [List.map_nil, List.foldl_nil] using hsyntax.symm
    rw [hrhsX, hrhsY]
    have houtSortT : out.T ≤ TShape.sort (decide (l ≠ SLevel.zero)) :=
      hhead.trans hroot
    have houtSort : out ≤ .sort (decide (l ≠ SLevel.zero)) := by
      simpa [TShape.sort, WShape.lift_sort] using
        (TShape.LE.lift_r (Nat.zero_le (n + 1))).1 houtSortT
    obtain rfl | rfl := WShape.le_sort.1 houtSort
    · exact (LR Γ₀).bot hout.isType
    · have houtTy : outTy = .type := by
        ext1
        simp only [WShape.HasType, WShape.sort] at hout
        generalize outTy.val = outTyVal at hout
        let .sort := Shape.HasType.unfold_iff.1 hout
        rfl
      subst outTy
      exact (LR Γ₀).sort_iff.2 ⟨l, .rfl, .rfl⟩
  | @cons n' f arg m out' path paths harg happ hrest =>
    have hfSortT : f.T ≤ TShape.sort (decide (l ≠ SLevel.zero)) :=
      hhead.trans hroot
    have hfSort : f ≤ .sort (decide (l ≠ SLevel.zero)) := by
      simpa [TShape.sort, WShape.lift_sort] using
        (TShape.LE.lift_r (Nat.zero_le (n' + 1))).1 hfSortT
    have hfapp : f.app arg = .bot := by
      obtain rfl | rfl := WShape.le_sort.1 hfSort
      · exact WShape.bot_app
      · rfl
    have hmBot : m ≤ TShape.bot := by
      rw [hfapp] at happ
      exact happ.trans TShape.bot_eqv.1
    have houtBot : out.T ≤ TShape.bot := hrest.le_bot hmBot
    have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact (LR Γ₀).bot hout.isType

/-! ### The ordered telescope producer

`WShape.HasTypeLam.peelLayer` is the TERM side of the peel; the recursion
itself is driven by the TYPE side, and the lemma that moves a registered-type
witness across one binder in lockstep with `LR.FixedHeadTelescope.cons`'s
codomain index is `LE_Interp.Witness.forallE_inst`.  That coincidence is the
producer: `cons` demands its tail at `(tyFun.app argCap).T`, and
`forallE_inst` delivers the next registered-type witness at exactly that
observation, instantiated at the same `argCap` the capture is aligned at.

Everything is continuation-passing.  No component of a layer is
existentially re-chosen and no `Nonempty` appears, which is what keeps the
`Type`-valued witness usable (N2 decision (ii)). -/

/-- The per-layer input of the ordered peel.

The equation `headTy = (WShape.forallE tyDom tyFun).T` is the capture-domain
link proper: the registered type's observation at this layer *is* a Pi
observation whose domain is the shape the aligned capture is indexed by, at
the semantic layer's own level.  `B = .forallE Bdom Bbody` is carried as part
of the layer datum rather than derived, because `PathSpineWF` reaches the
syntactic Pi form only through `conv`/`ret` edges carrying bare `IsDefEq`
(the G5 gap); keeping it a datum leaves that cost visible and outside the
fold. -/
def LR.FixedHeadOrderedLink (Γ₀ : List SExpr) (ρ : Valuation) {p : Pattern}
    (mcap : p.Path → TShape) (mx my captureType : p.Path → SExpr) : Prop :=
  ∀ {C : Prop} {n : Nat} (path : p.Path) (a : WShape n)
      (headTy : TShape) (B : SExpr),
    a.T ≤ mcap path →
    LE_Interp.Witness ρ headTy B →
    (∀ (tyDom : WShape n) (tyFun : WShapeFun n) (argCap : WShape n)
        (Bdom Bbody : SExpr),
      headTy = (WShape.forallE tyDom tyFun).T →
      B = .forallE Bdom Bbody →
      a ≤ argCap →
      LRS.CaptureDefEqAligned.AtShapes (LR Γ₀) (mcap path)
        (mx path) (my path) (captureType path) argCap tyDom →
      LE_Interp.Witness ρ argCap.T (mx path) → C) → C

/-- The terminal input of the first ordered peel: at the observation the peel
reaches, the semantic result of the spine is typed.

**REFUTED — see `LR.FixedHeadTerminalLink.not_nonbot` below.**  It quantifies
over *every* observation carrying a witness, and `LE_Interp.Witness.bot` is a
witness of every syntax at `TShape.bot`, so the Prop forces `out ≤ TShape.bot`.
Every consumer of the ordered peel holds `¬out.T ≤ TShape.bot`, so no consumer
can ever supply it.  This is the same disease as
`LR.FixedHeadTerminalRetarget`: a terminal fact stated as a *law over
observations* rather than as a datum at the observation actually reached.
`LR.FixedHeadTelescopeLE.ofOrderedLink` is the repaired peel — it takes no
terminal law at all and hands the reached observation back to its caller. -/
def LR.FixedHeadTerminalLink (ρ : Valuation) (out : TShape) : Prop :=
  ∀ (headTy : TShape) (B : SExpr),
    LE_Interp.Witness ρ headTy B → out.HasType headTy

/-- **`LR.FixedHeadTerminalLink` FORCES ITS SUBJECT TO BE BOTTOM.**
`LE_Interp.Witness.bot` (SLR:3928) is a witness of an arbitrary syntax at
`TShape.bot`, and `TShape.HasType.bot_r` (SLR:3120) turns the resulting typing
into `out ≤ TShape.bot`. -/
theorem LR.FixedHeadTerminalLink.le_bot {ρ : Valuation} {out : TShape}
    (H : LR.FixedHeadTerminalLink ρ out) : out ≤ TShape.bot :=
  TShape.HasType.bot_r
    (H TShape.bot (.sort .zero) (LE_Interp.Witness.bot (n := 0)))

/-- **THE ORDERED PEEL'S TERMINAL LAW IS ALSO REFUTABLE**, independently of
`LR.FixedHeadTerminalRetarget`.  Every consumer of the fixed-head fold carries
`houtNonbot : ¬out.T ≤ TShape.bot` — the bottom result shape is discharged
before the telescope is ever consumed — so this Prop is false exactly where it
would be used.  `LR.FixedHeadProducer.of_orderedLink` is therefore vacuous for
two independent reasons, and neither is repairable at the leaf. -/
theorem LR.FixedHeadTerminalLink.not_nonbot {ρ : Valuation} {out : TShape}
    (hnonbot : ¬out ≤ TShape.bot) : ¬ LR.FixedHeadTerminalLink ρ out :=
  fun H => hnonbot H.le_bot

/-- One ordered layer step, returning the telescope layer and the peeled
registered-type witness from ONE declaration.

Returning both halves together is the non-erasing form: a caller cannot pair
this telescope layer with a type witness peeled at some other domain.
`peelLayer`'s `hcapDom` is `capture.2.1` here, taken at the domain of the
very observation the type witness is peeled at. -/
noncomputable def LR.FixedHeadTelescope.consPeel
    {Γ₀ : List SExpr} {ρ : Valuation}
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {n : Nat} {f : WShape (n + 1)} {a : WShape n}
    {m out : TShape} {path : p.Path} {paths : List p.Path}
    (harg : a.T ≤ mcap path) (happ : m ≤ (f.app a).T)
    (rest : LE_Interp.RHS.ShapeSpine mcap m paths out)
    {tyDom : WShape n} {tyFun : WShapeFun n} {argCap : WShape n}
    {outTy : TShape} {Bdom Bbody : SExpr}
    (capture : LRS.CaptureDefEqAligned.AtShapes (LR Γ₀)
      (mcap path) (mx path) (my path) (captureType path) argCap tyDom)
    (hTy : LE_Interp.Witness ρ (WShape.forallE tyDom tyFun).T
      (.forallE Bdom Bbody))
    (hArg : LE_Interp.Witness ρ argCap.T (mx path))
    (tail : LR.FixedHeadTelescope
      (headTy := (tyFun.app argCap).T) (outTy := outTy)
      Γ₀ mx my captureType rest) :
    PProd
      (LR.FixedHeadTelescope
        (headTy := (WShape.forallE tyDom tyFun).T) (outTy := outTy)
        Γ₀ mx my captureType
        (LE_Interp.RHS.ShapeSpine.cons harg happ rest))
      (LE_Interp.Witness ρ (tyFun.app argCap).T (Bbody.inst (mx path))) :=
  ⟨LR.FixedHeadTelescope.cons harg happ rest capture tail,
    hTy.forallE_inst hArg⟩

/-- THE ORDERED PRODUCER.  Peel the head's binder layers in order: at every
layer the registered type's witness is instantiated at the very `argCap` the
aligned capture is indexed by, so the telescope's captures line up with the
pattern's ordered path list by construction.

Continuation-passing keeps the produced `outTy` index and the produced
registered-type witness attached to the same telescope, so the changed third
premise of `LR.FixedHeadResult` is discharged in one elimination. -/
theorem LR.FixedHeadTelescope.ofOrderedLink
    {Γ₀ : List SExpr} {ρ : Valuation}
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head out : TShape}
    (spine : LE_Interp.RHS.ShapeSpine mcap head paths out)
    (link : LR.FixedHeadOrderedLink Γ₀ ρ mcap mx my captureType)
    (term : LR.FixedHeadTerminalLink ρ out) :
    ∀ {C : Prop} {headTy : TShape} {B : SExpr},
      LE_Interp.Witness ρ headTy B →
      (∀ outTy : TShape,
        LR.FixedHeadTelescope (headTy := headTy) (outTy := outTy)
          Γ₀ mx my captureType spine → C) → C := by
  induction spine with
  | @nil head0 =>
    intro C headTy B hTy K
    exact K headTy (LR.FixedHeadTelescope.nil (term headTy B hTy))
  | @cons n f a m out path paths harg happ rest ih =>
    intro C headTy B hTy K
    refine link path a headTy B harg hTy ?_
    intro tyDom tyFun argCap Bdom Bbody hheadTy hB hargCap capture hArg
    subst hheadTy
    subst hB
    refine ih term (hTy.forallE_inst hArg) ?_
    intro outTy tail
    exact K outTy (LR.FixedHeadTelescope.cons harg happ rest capture tail)

/-- **THE REPAIRED ORDERED PRODUCER.**  Peel the head's binder layers in order,
taking no terminal law whatsoever, and hand the caller both the observation the
peel actually reached (with its witness) and a *factory* that builds the
telescope at any result observation the caller can type and compare.

Two things move relative to `LR.FixedHeadTelescope.ofOrderedLink`.

* `LR.FixedHeadTerminalLink` is gone.  It was a law quantified over every
  observation carrying a witness, and `LE_Interp.Witness.bot` refutes every such
  law (`LR.FixedHeadTerminalLink.not_nonbot`).  The peel never needed it: the
  base typing it was used for is the caller's own `out.HasType outTy`.
* The terminal index is no longer existentially produced and then retargeted.
  It is an *argument of the factory*, so the caller supplies it — which is the
  only place `hout`/`hA` are available, since they are inputs of
  `LR.constDefEq` fixed before any pattern is matched.

What is left over is exactly one comparison, `outTy ≤ reachedTy`, at an
observation the caller now holds.  That is the entire residual content of
obstruction O1. -/
theorem LR.FixedHeadTelescopeLE.ofOrderedLink
    {Γ₀ : List SExpr} {ρ : Valuation}
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head out : TShape}
    (spine : LE_Interp.RHS.ShapeSpine mcap head paths out)
    (link : LR.FixedHeadOrderedLink Γ₀ ρ mcap mx my captureType) :
    ∀ {C : Prop} {headTy : TShape} {B : SExpr},
      LE_Interp.Witness ρ headTy B →
      (∀ (reachedTy : TShape) (Bend : SExpr),
        LE_Interp.Witness ρ reachedTy Bend →
        (∀ outTy : TShape, out.HasType outTy → outTy ≤ reachedTy →
          LR.FixedHeadTelescopeLE (headTy := headTy) (outTy := outTy)
            Γ₀ mx my captureType spine) → C) → C := by
  induction spine with
  | @nil head0 =>
    intro C headTy B hTy K
    exact K headTy B hTy
      (fun _ htyped hle => LR.FixedHeadTelescopeLE.nil htyped hle)
  | @cons n f a m out path paths harg happ rest ih =>
    intro C headTy B hTy K
    refine link path a headTy B harg hTy ?_
    intro tyDom tyFun argCap Bdom Bbody hheadTy hB hargCap capture hArg
    subst hheadTy
    subst hB
    refine ih (hTy.forallE_inst hArg) ?_
    intro reachedTy Bend hEnd factory
    exact K reachedTy Bend hEnd
      (fun outTy htyped hle =>
        LR.FixedHeadTelescopeLE.cons harg happ rest capture
          (factory outTy htyped hle))

/-- The exact interface the changed third premise of `LR.FixedHeadResult`
consumes: one elimination delivering the ordered capture telescope AND the
registered type's own semantic witness at ONE shape index, at the caller's
own result-type observation `outTy.T`.

Continuation-passing is load-bearing.  `LE_Interp.Witness` is `Type`-valued,
so an existential package would need `Nonempty` and would re-choose the
index; here no component of the pair is chosen twice, and the telescope and
the witness provably come from the same peel. -/
def LR.FixedHeadProducer (Γ₀ : List SExpr) (ρ : Valuation)
    {n : Nat} {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) {out : WShape (n + 1)} {head : TShape}
    (mx my captureType :
      (RecursorIotaPattern rec major ctor arity).Path → SExpr)
    {outTy : WShape (n + 1)}
    (hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
      head rule.capturePaths out.T) : Prop :=
  ∀ {C : Prop},
    (∀ headTy : TShape,
      LR.FixedHeadTelescopeLE (headTy := headTy) (outTy := outTy.T)
        Γ₀ mx my captureType hshape →
      LE_Interp.Witness ρ headTy (SExpr.mkInst recLs rule.df.type) → C) → C

/-- Closedness of a registered iota rule's *displayed type*.

`Pattern.IotaRule` carries `rhsClosed` and no `typeClosed` field, but the fact
is available anyway and needs no new field: the environment's own ordering
invariant `VEnv.Ordered.closed` closes all three components of every
registered `VDefEq`.  This discharges the side condition recorded when the
nil-valuation fixed-head producer was landed. -/
theorem _root_.Lean4Lean.Pattern.IotaRule.typeClosed
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) (ls : List SLevel) :
    (SExpr.mkInst ls rule.df.type).ClosedN :=
  (Params.henv.closed.2 rule.registered).2.2.mkInstS

/-- THE ISOLATED O1 RESIDUAL: read a finished fixed-head telescope at the
caller's own result-type observation instead of the one the peel reached.

`WithCaptures.nil` identifies the telescope's two type indices, so the peel's
terminal observation is a function of the registered type and the aligned
capture shapes, whereas `outTy` is an *input* of the constant-evaluation fold.
`LR.constDefEq` receives `hout`/`hA`; it recomputes them only at an
application layer, and hands them to the pattern leaf unchanged in its `pat`
branch; `LR.PatternLeafDefEq.of_iota`, `LR.IotaLeafDefEq` and
`LRS.IotaRHSDefEq` then thread them verbatim.  So `outTy` is already fixed
before any pattern is matched, and producing `hout`/`hA` "from the peel" is
not available anywhere at or below the matched leaf.  The whole gap is this
one retarget, and it is not a lemma: `WithCaptures` has no terminal-index
monotonicity (the same absence O2 records for its level index), and the
retarget is an equality of indices, not a comparison.

Its natural producer is a uniqueness statement, not a construction: the peel's
terminal witness observes the syntactic spine result `A` (the right endpoint
of `SExpr.PathSpineWF`), and the caller's `hA : (LR Γ₀).TyDefEq A A outTy`
observes the same `A` at `outTy`. -/
def LR.FixedHeadTerminalRetarget (Γ₀ : List SExpr)
    {p : Pattern} {mcap : p.Path → TShape}
    (mx my captureType : p.Path → SExpr)
    {head out : TShape} {paths : List p.Path}
    (spine : LE_Interp.RHS.ShapeSpine mcap head paths out)
    (outTy : TShape) : Prop :=
  ∀ {headTy reachedTy : TShape},
    LR.FixedHeadTelescope (headTy := headTy) (outTy := reachedTy)
      Γ₀ mx my captureType spine →
    LR.FixedHeadTelescope (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine

/-- **`LR.FixedHeadTerminalRetarget` IS `HasType`-functionality at the
telescope's terminal head shape**, which is what makes it unprovable as
stated rather than merely open.

`WithCaptures.nil` (SLR:3661) identifies the two type indices, so at a
nil-terminated spine the retarget says: every type of `head` equals the
caller's `outTy`.  `WithCaptures.cons` threads `outTy` unchanged, so on a
longer spine the same demand simply reappears at the base. -/
theorem LR.FixedHeadTerminalRetarget.hasType_functional
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr} {head outTy : TShape}
    (H : LR.FixedHeadTerminalRetarget Γ₀ mx my captureType
      (LE_Interp.RHS.ShapeSpine.nil (m2 := mcap) (head := head)) outTy)
    {headTy : TShape} (htyped : head.HasType headTy) :
    headTy = outTy := by
  have tel := H (LR.FixedHeadTelescope.nil (Γ₀ := Γ₀) (mx := mx) (my := my)
    (captureType := captureType) (mcap := mcap) htyped)
  cases tel
  rfl

/-- **THE O1 RESIDUAL AS NAMED IS REFUTABLE.**  `TShape.HasType.bot`
(SLR:3135) types `.bot` at every sort, so the functionality forced above
fails outright.

This closes the O1 question in the negative and redirects it: no producer can
discharge `LR.FixedHeadTerminalRetarget`, because there is nothing to
discharge — the statement is false.  The previous session's suggested
"uniqueness statement" producer is refuted along with the Prop.

**REPAIRED.**  The terminal-index monotonicity is
`LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE` (SLR), landed as an
additive parallel structure; the retarget as a *comparison* is
`LR.FixedHeadTelescope.retarget`, and the residual it leaves is
`LR.FixedHeadTerminalDominance`.  The other candidate route — letting
`LR.FixedHeadShapeChain.pathSemantics` consume a chain at the reached
observation plus a semantic bridge to `outTy` — is not available: the chain's
terminal index feeds `LR.FixedHeadApplication` and thence the conclusion of
`LR.FixedHeadResult` verbatim, so it must literally be the caller's `outTy`,
and `resultRel` (which is the caller's `hA`) is already consumed there. -/
theorem LR.FixedHeadTerminalRetarget.not_general
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr} {outTy : TShape} :
    ¬ LR.FixedHeadTerminalRetarget Γ₀ mx my captureType
        (LE_Interp.RHS.ShapeSpine.nil (m2 := mcap)
          (head := TShape.bot)) outTy := by
  intro H
  have h1 := LR.FixedHeadTerminalRetarget.hasType_functional H
    (TShape.HasType.bot' (TShape.HasType.sort (r := true)))
  have h2 := LR.FixedHeadTerminalRetarget.hasType_functional H
    (TShape.HasType.bot' (TShape.HasType.sort (r := false)))
  have hEq : TShape.sort true = TShape.sort false := h1.trans h2.symm
  simp [TShape, WShape, TShape.sort, WShape.T, WShape.sort] at hEq
  have h0 : Shape0.sort true = Shape0.sort false := hEq
  injection h0 with hb
  exact absurd hb (by decide)

/-- **VACUOUS TWICE OVER — kept only as the reference statement.**  Two of its
four inputs are refutable: `term` by `LR.FixedHeadTerminalLink.not_nonbot` (at
every non-bottom result shape, i.e. wherever the fold runs) and `retarget` by
`LR.FixedHeadTerminalRetarget.not_general`.  It must not be counted as progress
toward the four leaf-local `producer` hypotheses.

`LR.FixedHeadProducer.of_dominance` below is the live replacement, and
`LR.FixedHeadTelescopeLE.ofOrderedLink` is the repaired peel it rests on. -/
theorem LR.FixedHeadProducer.of_orderedLink
    {Γ₀ : List SExpr} {ρ : Valuation}
    {n : Nat} {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)} {head : TShape}
    {mx my captureType :
      (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {outTy : WShape (n + 1)}
    {hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
      head rule.capturePaths out.T}
    {headTy : TShape}
    (hTyReg : LE_Interp.Witness ρ headTy (SExpr.mkInst recLs rule.df.type))
    (link : LR.FixedHeadOrderedLink Γ₀ ρ (Sum.elim mrec mctor)
      mx my captureType)
    (term : LR.FixedHeadTerminalLink ρ out.T)
    (retarget : LR.FixedHeadTerminalRetarget Γ₀ mx my captureType
      hshape outTy.T) :
    LR.FixedHeadProducer Γ₀ ρ rule mx my captureType hshape
      (recLs := recLs) (outTy := outTy) := by
  intro C K
  refine LR.FixedHeadTelescope.ofOrderedLink hshape link term hTyReg ?_
  intro _reachedTy tel
  exact K headTy (retarget tel).toLE hTyReg

/-- **THE O1 RESIDUAL, CORRECTLY STATED.**  Some run of the ordered peel
terminates at an observation that *dominates* the caller's result observation.

This is what survives after the two refutations.  Compare what it replaces:

* `LR.FixedHeadTerminalRetarget` demanded the two observations be *equal*.  That
  is `HasType`-functionality at the terminal head, and `TShape.HasType.bot`
  refutes it (`.not_general`).
* `LR.FixedHeadTerminalLink` demanded a typing at *every* witnessed
  observation.  `LE_Interp.Witness.bot` refutes it (`.not_nonbot`).

Both failed for the same structural reason: they are laws quantified over
observations, and the observation lattice has a bottom that every syntax is
witnessed at.  This Prop is instead *existential in the reached observation* —
continuation-passing, so the peel's own choice is what is compared — and is
therefore not refutable by that argument.  `.of_exact` shows it is strictly
weaker than the demand it replaces; `.nil` inhabits it at exactly the instance
where the retarget is false. -/
def LR.FixedHeadTerminalDominance (Γ₀ : List SExpr)
    {p : Pattern} {mcap : p.Path → TShape}
    (mx my captureType : p.Path → SExpr)
    {head out : TShape} {paths : List p.Path}
    (spine : LE_Interp.RHS.ShapeSpine mcap head paths out)
    (headTy outTy : TShape) : Prop :=
  ∀ {C : Prop},
    (∀ reachedTy : TShape, outTy ≤ reachedTy →
      LR.FixedHeadTelescope (headTy := headTy) (outTy := reachedTy)
        Γ₀ mx my captureType spine → C) → C

/-- Faithfulness: the old (exact) demand implies the dominance, at the
reflexive comparison.  So nothing that used to discharge the producer stops
discharging it. -/
theorem LR.FixedHeadTerminalDominance.of_exact
    {Γ₀ : List SExpr} {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (H : LR.FixedHeadTelescope (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine) :
    LR.FixedHeadTerminalDominance Γ₀ mx my captureType spine headTy outTy :=
  fun K => K outTy TShape.LE.rfl H

/-- **THE NON-VACUITY CERTIFICATE.**  At the empty capture spine the dominance
is inhabited from the caller's own result typing alone — including at
`head = .bot`, which is the very instance at which
`LR.FixedHeadTerminalRetarget.not_general` derives `False`.  So the replacement
Prop is genuinely satisfiable where its predecessor was refutable. -/
theorem LR.FixedHeadTerminalDominance.nil
    {Γ₀ : List SExpr} {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr} {head outTy : TShape}
    (htyped : head.HasType outTy) :
    LR.FixedHeadTerminalDominance Γ₀ mx my captureType
      (LE_Interp.RHS.ShapeSpine.nil (m2 := mcap) (head := head))
      outTy outTy :=
  fun K => K outTy TShape.LE.rfl (LR.FixedHeadTelescope.nil htyped)

/-- Level rigidity of the packed telescopes, type side: any monotone packed
telescope has at least as many sigma-levels in its head-type observation as
it has capture paths.  Each `cons` locks its layer's element, domain, and
function shapes to one sigma-level `n` with the head observation at `n + 1`,
and the type-side index chain descends by exactly one level per path. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.paths_le_headTyLevel
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
      (m2 := m2) Cap head paths out headTy outTy) :
    paths.length ≤ headTy.1 := by
  induction H with
  | nil _ _ => exact Nat.zero_le _
  | cons _ _ _ _ _ _ ih => simpa using Nat.succ_le_succ ih

/-- Any monotone packed telescope bounds its path count by the sigma-level
of the *head term* observation as well (at a nonempty path list the head and
head-type observations are locked to the same constructor level). -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.paths_le_headLevel
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
      (m2 := m2) Cap head paths out headTy outTy) :
    paths.length ≤ head.1 := by
  cases H with
  | nil _ _ => exact Nat.zero_le _
  | cons _ _ _ _ _ tail => simpa using Nat.succ_le_succ tail.paths_le_headTyLevel

/-- The exact packed telescope satisfies the same bound (it is the reflexive
case of the monotone one). -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.paths_le_headLevel
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures
      (m2 := m2) Cap head paths out headTy outTy) :
    paths.length ≤ head.1 :=
  H.toLE.paths_le_headLevel

/-- **The necessary level-adequacy precondition of the concrete spine
instance.**  Any inhabitant of `LR.FixedHeadProducer` forces the head
observation's sigma-level to be at least the rule's capture-path count.
Nothing at the leaf callback bounds the abstract evaluator's head
observation from below (the `R`-evaluator may observe the registered RHS
shallowly), so this bound — or the head witness it follows from — is a
genuine input of any producer discharge, not bookkeeping. -/
theorem LR.FixedHeadProducer.forces_headLevel
    {Γ₀ : List SExpr} {ρ : Valuation}
    {n : Nat} {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)} {head : TShape}
    {mx my captureType :
      (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {outTy : WShape (n + 1)}
    {hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
      head rule.capturePaths out.T}
    (P : LR.FixedHeadProducer Γ₀ ρ rule mx my captureType hshape
      (recLs := recLs) (outTy := outTy)) :
    rule.capturePaths.length ≤ head.1 := by
  refine P ?_
  intro headTy htel _hTyReg
  exact LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.paths_le_headLevel
    htel

/-- The same bound is forced by any dominance value at the spine, so the
concrete-spine producer below cannot be stated for an arbitrary spine head:
level adequacy is a genuine premise of its layer package. -/
theorem LR.FixedHeadTerminalDominance.forces_headLevel
    {Γ₀ : List SExpr}
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    {headTy outTy : TShape}
    (D : LR.FixedHeadTerminalDominance Γ₀ mx my captureType
      spine headTy outTy) :
    paths.length ≤ head.1 :=
  D fun _reachedTy _hle tel =>
    LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.paths_le_headLevel tel

/-- Transport a caller typing to a level-`n` representative of the type
observation.  This is the only fact needed to canonicalize the terminal
datum of the concrete-spine dominance to `w := outTy.2.lift n` whenever the
caller's observation fits below the innermost layer level. -/
theorem TShape.HasType.liftTy {out outTy : TShape} {n : Nat}
    (h : out.HasType outTy) (hfit : outTy.1 ≤ n) :
    out.HasType (outTy.2.lift n).T := by
  have h1 : out.1 ≤ max out.1 n := Nat.le_max_left ..
  have h2 : outTy.1 ≤ max out.1 n :=
    Nat.le_trans hfit (Nat.le_max_right ..)
  have hW := (TShape.HasType.def h1 h2).1 h
  refine (TShape.HasType.def h1 (Nat.le_max_right ..)).2 ?_
  rwa [WShape.lift_lift (.inl hfit)]

/-- The concrete-spine dominance layers: one aligned capture per spine step,
at consecutive descending sigma-levels, closed by the terminal datum
`(w, out.HasType w.T, outTy ≤ w.T)` at the observation actually reached.

Per layer the singleton Pi tower is chosen from the aligned capture itself:
the domain is the capture's own `typeShape`, the function is
`WShapeFun.single` at the capture's `elemShape`, and the accumulated tower
rides in the last index.  The terminal fact is a *datum* at the reached
observation — never a law quantified over observations — and `.nil`'s
comparison `outTy ≤ w.T` is the single point where the caller's result-type
observation enters. -/
inductive LR.FixedHeadDominanceSpine (Γ₀ : List SExpr) {p : Pattern}
    (mcap : p.Path → TShape) (mx my captureType : p.Path → SExpr)
    (outTy : TShape) :
    {n : Nat} → TShape → List p.Path → TShape → WShape n → Prop where
  | nil {n : Nat} {out : TShape} {w : WShape n}
      (hw : out.HasType w.T) (hle : outTy ≤ w.T) :
      FixedHeadDominanceSpine Γ₀ mcap mx my captureType outTy out [] out w
  | cons {n : Nat} {f : WShape (n + 1)} {a argCap tyDom inner : WShape n}
      {m out : TShape} {path : p.Path} {paths : List p.Path}
      (harg : a.T ≤ mcap path) (happ : m ≤ (f.app a).T)
      (capture : LRS.CaptureDefEqAligned.AtShapes (LR Γ₀)
        (mcap path) (mx path) (my path) (captureType path) argCap tyDom)
      (tail : FixedHeadDominanceSpine Γ₀ mcap mx my captureType outTy
        m paths out inner) :
      FixedHeadDominanceSpine Γ₀ mcap mx my captureType outTy
        f.T (path :: paths) out (.forallE tyDom (.single argCap inner))

/-- Recover the semantic application spine retained by a layer package. -/
theorem LR.FixedHeadDominanceSpine.spine
    {Γ₀ : List SExpr} {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {outTy head out : TShape} {paths : List p.Path}
    {n : Nat} {tower : WShape n}
    (H : LR.FixedHeadDominanceSpine Γ₀ mcap mx my captureType outTy
      head paths out tower) :
    LE_Interp.RHS.ShapeSpine mcap head paths out := by
  induction H with
  | nil _ _ => exact .nil
  | cons harg happ _ _ ih => exact .cons harg happ ih

/-- The level-fitted terminal layer: when the caller's `outTy` fits at the
innermost layer level, the terminal datum is canonical
(`w := outTy.2.lift n`) and the package base needs only the caller's own
typing — exactly the data the leaf callback holds. -/
theorem LR.FixedHeadDominanceSpine.nilFit
    {Γ₀ : List SExpr} {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {out outTy : TShape} {n : Nat}
    (houtTy : out.HasType outTy) (hfit : outTy.1 ≤ n) :
    LR.FixedHeadDominanceSpine Γ₀ mcap mx my captureType outTy
      out [] out (outTy.2.lift n) :=
  .nil (houtTy.liftTy hfit) (TShape.lift_eqv hfit).2

/-- **The general concrete-spine producer**, strictly between `.nil` (empty
spine) and `.of_exact` (exact terminal index): a layer package produces the
terminal dominance at its own singleton Pi tower observation, for any
semantic spine over the same head, paths, and result indices.  Each `cons`
folds one `LR.FixedHeadTelescope.cons` with one `WShapeFun.single_app`
rewrite; the base reads the terminal datum. -/
theorem LR.FixedHeadTerminalDominance.of_layers
    {Γ₀ : List SExpr} {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {outTy head out : TShape} {paths : List p.Path}
    {n : Nat} {tower : WShape n}
    (H : LR.FixedHeadDominanceSpine Γ₀ mcap mx my captureType outTy
      head paths out tower)
    (spine : LE_Interp.RHS.ShapeSpine mcap head paths out) :
    LR.FixedHeadTerminalDominance Γ₀ mx my captureType spine tower.T outTy := by
  induction H with
  | nil hw hle =>
    intro C K
    exact K _ hle (LR.FixedHeadTelescope.nil hw)
  | @cons n f a argCap tyDom inner m out path paths harg happ capture tail ih =>
    intro C K
    refine ih tail.spine ?_
    intro reachedTy hle tel
    refine K reachedTy hle ?_
    have happEq : (WShapeFun.single argCap inner).app argCap = inner := by
      rw [WShapeFun.single_app]; exact if_pos WShape.LE.rfl
    refine LR.FixedHeadTelescope.cons harg happ tail.spine capture ?_
    rw [happEq]
    exact tel

/-- Non-vacuity of the concrete-spine producer at a *nonempty* spine — the
certificate the landed `.nil` producer (empty spine) does not provide:
pattern `(.const c).var` (path `none`), capture `x = y = .sort 0` aligned at
element shape `.bot` / type shape `.sort true`, head observation
`.lam' (single .bot (.sort true))`, result observation `sort true`. -/
theorem LR.fixedHeadTerminalDominance_cons_nonvacuous (c : Name) :
    ∃ spine : LE_Interp.RHS.ShapeSpine
        (p := Pattern.varN (.const c) 1)
        (fun _ => (WShape.bot (n := 0)).T)
        (WShape.lam' (WShapeFun.single (WShape.bot (n := 0))
          (WShape.sort (n := 0) true))).T
        [(none : Option Empty)]
        (WShape.sort (n := 0) true).T,
      LR.FixedHeadTerminalDominance []
        (fun _ => SExpr.sort .zero) (fun _ => SExpr.sort .zero)
        (fun _ => SExpr.sort (.succ .zero))
        spine
        (WShape.forallE (WShape.sort (n := 0) true)
          (WShapeFun.single (WShape.bot (n := 0))
            (WShape.sort (n := 0) true))).T
        (WShape.sort (n := 0) true).T := by
  have happ : (WShape.sort (n := 0) true).T ≤
      ((WShape.lam' (WShapeFun.single (WShape.bot (n := 0))
        (WShape.sort (n := 0) true))).app (WShape.bot (n := 0))).T := by
    simp only [WShape.lam'_app, WShapeFun.single_app, WShape.bot_le,
      if_pos]
    exact TShape.LE.rfl
  have capture : LRS.CaptureDefEqAligned.AtShapes (LR [])
      ((WShape.bot (n := 0)).T) (SExpr.sort .zero) (SExpr.sort .zero)
      (SExpr.sort (.succ .zero)) (WShape.bot (n := 0))
      (WShape.sort (n := 0) true) := by
    refine ⟨TShape.LE.rfl, .bot' .sort, ?_, .sort, (LR []).bot .sort⟩
    exact (LR []).sort_iff_ty.2 ⟨_, .rfl, .rfl⟩
  have hw : (WShape.sort (n := 0) true).T.HasType
      (WShape.sort (n := 0) true).T :=
    WShape.HasType.T (WShape.HasType.sort (n := 0) (r := true))
  have harg : (WShape.bot (n := 0)).T ≤
      (fun _ : (Pattern.varN (.const c) 1).Path =>
        (WShape.bot (n := 0)).T) none :=
    TShape.LE.rfl
  exact ⟨.cons harg happ .nil,
    LR.FixedHeadTerminalDominance.of_layers
      (.cons harg happ capture (.nil hw TShape.LE.rfl))
      (.cons harg happ .nil)⟩

/-- The four leaf-local `producer` hypotheses reduce to the registered type's
own observation, the caller's own result typing, and the terminal dominance.

Everything else the ordered peel needs is proved:
`LR.FixedHeadTelescopeLE.ofOrderedLink` runs the layers from `link` alone, and
`LR.FixedHeadTelescope.retarget` moves the finished telescope down to the
caller's observation.  Contrast `LR.FixedHeadProducer.of_orderedLink`, which is
vacuous twice over. -/
theorem LR.FixedHeadProducer.of_dominance
    {Γ₀ : List SExpr} {ρ : Valuation}
    {n : Nat} {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)} {head : TShape}
    {mx my captureType :
      (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {outTy : WShape (n + 1)}
    {hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
      head rule.capturePaths out.T}
    {headTy : TShape}
    (hTyReg : LE_Interp.Witness ρ headTy (SExpr.mkInst recLs rule.df.type))
    (hout : out.HasType outTy)
    (dom : LR.FixedHeadTerminalDominance Γ₀ mx my captureType
      hshape headTy outTy.T) :
    LR.FixedHeadProducer Γ₀ ρ rule mx my captureType hshape
      (recLs := recLs) (outTy := outTy) := by
  intro C K
  refine dom ?_
  intro reachedTy hle tel
  exact K headTy (tel.retarget hout.T hle) hTyReg

/-- Logical-relation congruence for one generated iota RHS at adjacent
stratification levels.  The two endpoints share the rule's ordered paths and
one exact capture-type map; each variable leaf is therefore related at the
very domain used by both dependent application spines.  The eventual
constructor proves the fixed-tower case by `LE_Interp.recR`; no environment
or reduction oracle appears in this contract. -/
def LRS.IotaRHSDefEq
    (IH : LogRel Γ n) (R : TShape → SExpr → Prop)
    {rec ctor : Name} {major arity : Nat}
    (recLs : List SLevel)
    (mrec : (Pattern.varN (.const rec) major).Path → TShape)
    (mctor : (Pattern.varN (.const ctor) arity).Path → TShape)
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check)
    (rule : Pattern.IotaRule r)
    (out : WShape (n + 1)) : Prop :=
  LE_Interp.RHS recLs (Sum.elim mrec mctor) R out.T r.1 →
  ∀ {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {A : SExpr} {outTy : WShape (n + 1)},
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    SExpr.PathSpineWF Γ my captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LRS.CaptureDefEqAligned (LRS IH) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned IH (mctor p)
          (mx path) (my path) (captureType path)) →
    out.HasType outTy →
    (LRS IH).TyDefEq A A outTy →
    (LRS IH).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy

/-- Build the full generated-RHS contract from its only nontrivial case.
`RHS.bot` is discharged uniformly; the continuation receives the semantic
fixed head, its environment-derived strong self-typing, and the exact ordered
application chain extracted from the rule.  It also receives a typed lower
approximation of that head.  This last witness is the admissible argument to
the surrounding `LE_Interp.recR` induction: capture materialization supplies
logical witnesses only at the selected arguments, and therefore cannot by
itself manufacture validity of the registered head's universally quantified
type. -/
theorem LRS.IotaRHSDefEq.of_nonbot
    {IH : LogRel Γ n} {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    (H : ∀ {head : TShape}
        {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {captureType :
          (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {A : SExpr} {outTy : WShape (n + 1)},
      LE_Interp.RHS (p := RecursorIotaPattern rec major ctor arity)
        recLs (Sum.elim mrec mctor) R head
        (.fixed rule.df.rhs rule.rhsClosed) →
      IsDefEqStrong Γ (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) →
      LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T →
      (∃ headElem headTy : TShape,
        headElem ≤ head ∧ headElem.HasType headTy) →
      SExpr.PathSpineWF Γ mx captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      SExpr.PathSpineWF Γ my captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LRS.CaptureDefEqAligned (LRS IH) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned IH (mctor p)
            (mx path) (my path) (captureType path)) →
      out.HasType outTy →
      (LRS IH).TyDefEq A A outTy →
      (LRS IH).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy) :
    LRS.IotaRHSDefEq IH R recLs mrec mctor r rule out := by
  intro hrhs mx my captureType A outTy hspineX hspineY hcap hout hA
  obtain hbot | ⟨head, hhead, hshapeSpine⟩ := rule.rhsShapeSpine hrhs
  · have houtBot : out = .bot := TShape.le_bot.1 hbot
    subst out
    exact (LRS IH).bot hout.isType
  · have hcapTyped : ∀ path,
        ∃ elem elemTy : TShape,
          Sum.elim mrec mctor path ≤ elem ∧ elem.HasType elemTy := by
      intro path
      cases path with
      | inl path =>
        obtain ⟨elem, elemTy, hshape, htype, _⟩ := hcap (.inl path)
        exact ⟨elem.T, elemTy.T, hshape, htype.T⟩
      | inr path =>
        obtain ⟨elem, elemTy, hshape, htype, _⟩ := hcap (.inr path)
        exact ⟨elem.T, elemTy.T, hshape, htype.T⟩
    have hheadTyped := hshapeSpine.typedLowerHead hcapTyped hout.T
    exact H hhead (rule.rhsStrong recLs) hshapeSpine hheadTyped
      hspineX hspineY hcap hout hA

/-- Witness-aware form of `IotaRHSDefEq.of_nonbot` for a constant evaluator
using `LE_Interp.Lower R`.  The callback receives the exact proof-relevant
fixed-head witness selected by the enclosing constant's `R` callback; no
propositional derivation identity has to survive this boundary. -/
theorem LRS.IotaRHSDefEq.of_nonbotWitness
    {IH : LogRel Γ n} {R : TShape → SExpr → Prop}
    {ρ : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (H : ∀ {head : TShape}
        {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {captureType :
          (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {A : SExpr} {outTy : WShape (n + 1)},
      LE_Interp.Witness ρ head (SExpr.mkInst recLs rule.df.rhs) →
      IsDefEqStrong Γ (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) →
      LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T →
      (∃ headElem headTy : TShape,
        headElem ≤ head ∧ headElem.HasType headTy) →
      SExpr.PathSpineWF Γ mx captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      SExpr.PathSpineWF Γ my captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LRS.CaptureDefEqAligned (LRS IH) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned IH (mctor p)
            (mx path) (my path) (captureType path)) →
      out.HasType outTy →
      (LRS IH).TyDefEq A A outTy →
      (LRS IH).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy) :
    LRS.IotaRHSDefEq IH (LE_Interp.Lower R)
      recLs mrec mctor r rule out := by
  apply LRS.IotaRHSDefEq.of_nonbot
  intro head mx my captureType A outTy hhead hstrong hshape htyped
    hspineX hspineY hcap hout hA
  exact H (hhead.fixedLowerWitness hR) hstrong hshape htyped
    hspineX hspineY hcap hout hA

/-- Recursive-result-preserving form of `of_nonbotWitness`.

The fixed head is selected from an abstract `R` edge of the enclosing
constant.  Its recursive hypothesis must be selected at the same time: a
second proof-relevant witness with identical public indices may carry a
different abstract relation.  `hmono` transports that hypothesis through
the root-only lowering performed by `LE_Interp.Lower`. -/
theorem LRS.IotaRHSDefEq.of_nonbotWitnessResult
    {IH : LogRel Γ n} {R : TShape → SExpr → Prop}
    {ρ : Valuation}
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hP : ∀ {m M} (hr : R m M), P (hR hr))
    (hmono : ∀ {m m' M} (hle : m ≤ m')
      (hM : LE_Interp.Witness ρ m' M), P hM → P (hM.mono hle))
    (H : ∀ {head : TShape}
        {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {captureType :
          (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {A : SExpr} {outTy : WShape (n + 1)}
        (hhead : LE_Interp.Witness ρ head
          (SExpr.mkInst recLs rule.df.rhs)),
      P hhead →
      IsDefEqStrong Γ (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) →
      LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T →
      (∃ headElem headTy : TShape,
        headElem ≤ head ∧ headElem.HasType headTy) →
      SExpr.PathSpineWF Γ mx captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      SExpr.PathSpineWF Γ my captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LRS.CaptureDefEqAligned (LRS IH) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned IH (mctor p)
            (mx path) (my path) (captureType path)) →
      out.HasType outTy →
      (LRS IH).TyDefEq A A outTy →
      (LRS IH).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy) :
    LRS.IotaRHSDefEq IH (LE_Interp.Lower R)
      recLs mrec mctor r rule out := by
  intro hrhs mx my captureType A outTy hspineX hspineY hcap hout hA
  by_cases houtBot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact (LRS IH).bot hout.isType
  obtain hbot | ⟨head, hhead, hshapeSpine⟩ := rule.rhsShapeSpine hrhs
  · exact (houtBot hbot).elim
  have hheadNonbot : ¬head ≤ TShape.bot := by
    intro hbot
    exact houtBot (hshapeSpine.le_bot hbot)
  have hcapTyped : ∀ path,
      ∃ elem elemTy : TShape,
        Sum.elim mrec mctor path ≤ elem ∧ elem.HasType elemTy := by
    intro path
    cases path with
    | inl path =>
      obtain ⟨elem, elemTy, hshape, htype, _⟩ := hcap (.inl path)
      exact ⟨elem.T, elemTy.T, hshape, htype.T⟩
    | inr path =>
      obtain ⟨elem, elemTy, hshape, htype, _⟩ := hcap (.inr path)
      exact ⟨elem.T, elemTy.T, hshape, htype.T⟩
  have hheadTyped := hshapeSpine.typedLowerHead hcapTyped hout.T
  let headResult :=
    hhead.fixedLowerWitnessResult hR hP hmono hheadNonbot
  exact H headResult.1 headResult.2 (rule.rhsStrong recLs)
    hshapeSpine hheadTyped hspineX hspineY hcap hout hA

/-- The exact constructor case of iota materialization with explicit typing
certificates for the reached contraction sites.  Keeping these certificates
as callbacks lets native leaves discharge them by reflexivity, while callers
with genuinely reducing majors may derive them through their chosen subject-
reduction theorem. -/
theorem LR.iotaActions_of_exactEqAt
    {n : Nat} {IH : LogRel Γ₀ n} {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrecargs : LRS.CtorArgsDefEq (LRS IH) recXs recYs recShapes)
    (hctorargs : LRS.CtorArgsDefEq IH ctorXs ctorYs ctorShapes)
    (hMajorX : Γ₀ ⊢ majorX ⤳*
      ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs))
    (hMajorY : Γ₀ ⊢ majorY ⤳*
      ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs'))
    (hsiteTypeX : ∀ (_ : Γ₀ ⊢
      (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorX ⤳*
        (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs))),
      Γ₀ ⊢
        (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)) : A)
    (hsiteTypeY : ∀ (_ : Γ₀ ⊢
      (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorY ⤳*
        (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs'))),
      Γ₀ ⊢
        (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')) : A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    {recHeadType ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      majorType : SExpr}
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hrecSpineX : SExpr.SpineWF Γ₀ recHeadType
      (recXs.reverse ++ [majorX]) A)
    (hrecSpineY : SExpr.SpineWF Γ₀ recHeadType
      (recYs.reverse ++ [majorY]) A)
    (hctorHeadX : Γ₀ ⊢ .const ctor ctorLs : ctorHeadTypeX)
    (hctorHeadY : Γ₀ ⊢ .const ctor ctorLs' : ctorHeadTypeY)
    (hctorSpineX : SExpr.SpineWF Γ₀ ctorHeadTypeX
      ctorXs.reverse ctorResultX)
    (hctorSpineY : SExpr.SpineWF Γ₀ ctorHeadTypeY
      ctorYs.reverse ctorResultY)
    (hMajorEqX : Γ₀ ⊢ majorX ≡
      ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs) : majorType)
    (hMajorEqY : Γ₀ ⊢ majorY ≡
      ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs') : majorType) :
    ∃ (mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (captureTypingX : Pattern.CaptureTyping Γ₀ mx captureType)
      (captureTypingY : Pattern.CaptureTyping Γ₀ my captureType)
      (rule : Pattern.IotaRule r)
      (siteX : Pattern.IotaReductionSite Γ₀ r rule recLs ctorLs
        recXs ctorXs majorX A mx captureType captureTypingX)
      (siteY : Pattern.IotaReductionSite Γ₀ r rule recLs ctorLs'
        recYs ctorYs majorY A my captureType captureTypingY),
      ∃ actionX : Pattern.Action Γ₀ r
        ((recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)))
        recLs mx A,
      ∃ actionY : Pattern.Action Γ₀ r
        ((recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')))
        recLs my A,
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LRS.CaptureDefEqAligned (LRS IH) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned IH (mctor p)
            (mx path) (my path) (captureType path)) ∧
      Γ₀ ⊢
        (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorX ⤳*
          r.1.applyS recLs mx ∧
      Γ₀ ⊢
        (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app majorY ⤳*
          r.1.applyS recLs my := by
  obtain ⟨mx, my, hmatchX, hmatchY, hcap, hredX, hredY⟩ :=
    LE_Interp.Matches.iota_materialize_exactAt hpat hmf hma
      hrecargs hctorargs hMajorX hMajorY
  let typingX : Pattern.IotaTyping Γ₀ rec ctor recLs ctorLs
      recXs ctorXs majorX A := {
    recHeadType := recHeadType
    ctorHeadType := ctorHeadTypeX
    ctorResultType := ctorResultX
    majorType := majorType
    recHead := hrecHead
    recSpine := hrecSpineX
    ctorHead := hctorHeadX
    ctorSpine := hctorSpineX
    majorEq := hMajorEqX }
  let typingY : Pattern.IotaTyping Γ₀ rec ctor recLs ctorLs'
      recYs ctorYs majorY A := {
    recHeadType := recHeadType
    ctorHeadType := ctorHeadTypeY
    ctorResultType := ctorResultY
    majorType := majorType
    recHead := hrecHead
    recSpine := hrecSpineY
    ctorHead := hctorHeadY
    ctorSpine := hctorSpineY
    majorEq := hMajorEqY }
  classical
  let captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr :=
    fun path => match path with
      | Sum.inl p => (LRS.CaptureDefEqAt.witness (hcap (Sum.inl p))).typeExpr
      | Sum.inr p => (LRS.CaptureDefEqAt.witness (hcap (Sum.inr p))).typeExpr
  let captureTypingX : Pattern.CaptureTyping Γ₀ mx captureType := {
    typed := by
      intro path
      cases path with
      | inl p =>
        exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inl p))).defeq.hasType.1
      | inr p =>
        exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inr p))).defeq.hasType.1 }
  let captureTypingY : Pattern.CaptureTyping Γ₀ my captureType := {
    typed := by
      intro path
      cases path with
      | inl p =>
        exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inl p))).defeq.hasType.2
      | inr p =>
        exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inr p))).defeq.hasType.2 }
  let rule := Params.Semantic.iotaRule hpat
  let siteX := Params.Semantic.iotaSite rule captureType captureTypingX hΓ.reify
    typingX hmatchX
    (hsiteTypeX hredX) hAType
  let siteY := Params.Semantic.iotaSite rule captureType captureTypingY hΓ.reify
    typingY hmatchY
    (hsiteTypeY hredY) hAType
  let actionX := siteX.action
  let actionY := siteY.action
  have hcapAligned : ∀ path :
      (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LRS.CaptureDefEqAligned (LRS IH) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned IH (mctor p)
          (mx path) (my path) (captureType path) := by
    intro path
    cases path with
    | inl p =>
      exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inl p))).aligned
    | inr p =>
      exact (LRS.CaptureDefEqAt.witness (hcap (Sum.inr p))).aligned
  exact ⟨mx, my, captureType, captureTypingX, captureTypingY,
    rule, siteX, siteY, actionX, actionY, hcapAligned,
    .tail hredX (.extra actionX), .tail hredY (.extra actionY)⟩

/-- Generated-iota-RHS congruence in the guarded relation.  Recursor
captures retain paired direct evidence at level `n + 1`; constructor fields
remain in the established predecessor relation at level `n`.  Concrete
families may upgrade exactly the constructor captures their RHS uses. -/
def LRD.IotaRHSDefEq
    {Γ : List SExpr} {n : Nat} (R : TShape → SExpr → Prop)
    {rec ctor : Name} {major arity : Nat}
    (recLs : List SLevel)
    (mrec : (Pattern.varN (.const rec) major).Path → TShape)
    (mctor : (Pattern.varN (.const ctor) arity).Path → TShape)
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check)
    (rule : Pattern.IotaRule r)
    (out : WShape (n + 1)) : Prop :=
  LE_Interp.RHS recLs (Sum.elim mrec mctor) R out.T r.1 →
  ∀ {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {A : SExpr} {outTy : WShape (n + 1)},
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    SExpr.PathSpineWF Γ my captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LR.DirectCaptureDefEqAligned
          (n := n + 1) (LRD Γ) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor p) (mx path) (my path) (captureType path)) →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    (LRD Γ).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy

/-- Guarded iota-RHS congruence with the recursor-prefix captures retained at
their literal materialized shapes.

This is a conservative strengthening of `LRD.IotaRHSDefEq`: constructor
fields still use the predecessor relation, while every recursor path also
exposes the exact element/type shape pair from the direct argument spine.
Concrete registered leaves can therefore synchronize a generated RHS tower
without reopening an existential capture witness. -/
def LRD.IotaRHSDefEqAlignedRec
    {Γ : List SExpr} {n : Nat} (R : TShape → SExpr → Prop)
    {rec ctor : Name} {major arity : Nat}
    (recLs : List SLevel)
    (mrec : (Pattern.varN (.const rec) major).Path → TShape)
    (mctor : (Pattern.varN (.const ctor) arity).Path → TShape)
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check)
    (recXs recYs : List SExpr) (recShapes : List (WShape (n + 1)))
    (rule : Pattern.IotaRule r)
    (out : WShape (n + 1)) : Prop :=
  LE_Interp.RHS recLs (Sum.elim mrec mctor) R out.T r.1 →
  ∀ {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {recElemShape recTypeShape :
        (Pattern.varN (.const rec) major).Path → WShape (n + 1)}
      {A : SExpr} {outTy : WShape (n + 1)},
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    SExpr.PathSpineWF Γ my captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LR.DirectCaptureDefEqAligned
          (n := n + 1) (LRD Γ) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor p) (mx path) (my path) (captureType path)) →
    (∀ path : (Pattern.varN (.const rec) major).Path,
      LR.DirectCaptureDefEqAligned.AtShapes
        (n := n + 1) (LRD Γ) (mrec path)
        (mx (.inl path)) (my (.inl path)) (captureType (.inl path))
        (recElemShape path) (recTypeShape path)) →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => mx (.inl path)) = recXs.reverse →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => my (.inl path)) = recYs.reverse →
    (Pattern.varNPaths (.const rec) major).map recElemShape =
      recShapes.reverse →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    (LRD Γ).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy

/-- Forget the exact recursor shape maps when an ordinary guarded RHS
consumer already suffices. -/
theorem LRD.IotaRHSDefEq.toAlignedRec
    {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {recXs recYs : List SExpr} {recShapes : List (WShape (n + 1))}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    (H : LRD.IotaRHSDefEq (Γ := Γ) R recLs
      mrec mctor r rule out) :
    LRD.IotaRHSDefEqAlignedRec (Γ := Γ) R recLs
      mrec mctor r recXs recYs recShapes rule out := by
  intro hrhs mx my captureType recElemShape recTypeShape A outTy
    hspineX hspineY hcap _hcapRec _hrecXs _hrecYs _hrecShapes hout hA
  exact H hrhs hspineX hspineY hcap hout hA

/-- Fully listed guarded iota-RHS congruence.  This is the registered-leaf
boundary: all recursor capture maps are tied to explicit newest-first lists
of syntax, raw types, element shapes, and type shapes. -/
def LRD.IotaRHSDefEqListedRec
    {Γ : List SExpr} {n : Nat} (R : TShape → SExpr → Prop)
    {rec ctor : Name} {major arity : Nat}
    (recLs : List SLevel)
    (mrec : (Pattern.varN (.const rec) major).Path → TShape)
    (mctor : (Pattern.varN (.const ctor) arity).Path → TShape)
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check)
    (recXs recYs recTypes : List SExpr)
    (recShapes recTypeShapes : List (WShape (n + 1)))
    (rule : Pattern.IotaRule r) (out : WShape (n + 1)) : Prop :=
  LE_Interp.RHS recLs (Sum.elim mrec mctor) R out.T r.1 →
  ∀ {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {recElemShape recTypeShape :
        (Pattern.varN (.const rec) major).Path → WShape (n + 1)}
      {A : SExpr} {outTy : WShape (n + 1)},
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    SExpr.PathSpineWF Γ my captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LR.DirectCaptureDefEqAligned
          (n := n + 1) (LRD Γ) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor p) (mx path) (my path) (captureType path)) →
    (∀ path : (Pattern.varN (.const rec) major).Path,
      LR.DirectCaptureDefEqAligned.AtShapes
        (n := n + 1) (LRD Γ) (mrec path)
        (mx (.inl path)) (my (.inl path)) (captureType (.inl path))
        (recElemShape path) (recTypeShape path)) →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => mx (.inl path)) = recXs.reverse →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => my (.inl path)) = recYs.reverse →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => captureType (.inl path)) = recTypes.reverse →
    (Pattern.varNPaths (.const rec) major).map recElemShape =
      recShapes.reverse →
    (Pattern.varNPaths (.const rec) major).map recTypeShape =
      recTypeShapes.reverse →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    (LRD Γ).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy

/-- Fixed-result form of the listed guarded RHS contract.

The native exact leaf already fixes `A`, `out`, and `outTy` before it
materializes an iota action.  Retaining those indices here lets a registered
consumer reuse the exact terminal observation of its application trace; a
contract universally quantified over an unrelated output type would demand
the false type-functionality principle that the dominance design avoids. -/
def LRD.IotaRHSDefEqListedRecAt
    {Γ : List SExpr} {n : Nat} (R : TShape → SExpr → Prop)
    {rec ctor : Name} {major arity : Nat}
    (recLs : List SLevel)
    (mrec : (Pattern.varN (.const rec) major).Path → TShape)
    (mctor : (Pattern.varN (.const ctor) arity).Path → TShape)
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check)
    (recXs recYs recTypes : List SExpr)
    (recShapes recTypeShapes : List (WShape (n + 1)))
    (rule : Pattern.IotaRule r) (A : SExpr)
    (out outTy : WShape (n + 1)) : Prop :=
  LE_Interp.RHS recLs (Sum.elim mrec mctor) R out.T r.1 →
  ∀ {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {recElemShape recTypeShape :
        (Pattern.varN (.const rec) major).Path → WShape (n + 1)},
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    SExpr.PathSpineWF Γ my captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LR.DirectCaptureDefEqAligned
          (n := n + 1) (LRD Γ) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor p) (mx path) (my path) (captureType path)) →
    (∀ path : (Pattern.varN (.const rec) major).Path,
      LR.DirectCaptureDefEqAligned.AtShapes
        (n := n + 1) (LRD Γ) (mrec path)
        (mx (.inl path)) (my (.inl path)) (captureType (.inl path))
        (recElemShape path) (recTypeShape path)) →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => mx (.inl path)) = recXs.reverse →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => my (.inl path)) = recYs.reverse →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => captureType (.inl path)) = recTypes.reverse →
    (Pattern.varNPaths (.const rec) major).map recElemShape =
      recShapes.reverse →
    (Pattern.varNPaths (.const rec) major).map recTypeShape =
      recTypeShapes.reverse →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    (LRD Γ).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy

/-- Fixed-result generated-RHS contract with both sides of the iota split
fully listed and guarded.

The ordinary listed contract intentionally leaves constructor captures in
the predecessor legacy relation.  A framed non-nullary constructor instead
rebuilds those fields at the root relation from strict recursive evidence;
this refinement records their raw types, element shapes, and type shapes so
the RHS consumes precisely that rebuilt payload. -/
def LRD.IotaRHSDefEqDirectListedRecAt
    {Γ : List SExpr} {n : Nat} (R : TShape → SExpr → Prop)
    {rec ctor : Name} {major arity : Nat}
    (recLs : List SLevel)
    (mrec : (Pattern.varN (.const rec) major).Path → TShape)
    (mctor : (Pattern.varN (.const ctor) arity).Path → TShape)
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check)
    (recXs recYs recTypes : List SExpr)
    (recShapes recTypeShapes : List (WShape (n + 1)))
    (ctorXs ctorYs ctorTypes : List SExpr)
    (ctorShapes ctorTypeShapes : List (WShape n))
    (rule : Pattern.IotaRule r) (A : SExpr)
    (out outTy : WShape (n + 1)) : Prop :=
  LE_Interp.RHS recLs (Sum.elim mrec mctor) R out.T r.1 →
  ∀ {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {recElemShape recTypeShape :
        (Pattern.varN (.const rec) major).Path → WShape (n + 1)}
      {ctorElemShape ctorTypeShape :
        (Pattern.varN (.const ctor) arity).Path → WShape n},
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    SExpr.PathSpineWF Γ my captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
    (∀ path : (Pattern.varN (.const rec) major).Path,
      LR.DirectCaptureDefEqAligned.AtShapes
        (n := n + 1) (LRD Γ) (mrec path)
        (mx (.inl path)) (my (.inl path)) (captureType (.inl path))
        (recElemShape path) (recTypeShape path)) →
    (∀ path : (Pattern.varN (.const ctor) arity).Path,
      LR.DirectCaptureDefEqAligned.AtShapes
        (n := n) (LRD Γ) (mctor path)
        (mx (.inr path)) (my (.inr path)) (captureType (.inr path))
        (ctorElemShape path) (ctorTypeShape path)) →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => mx (.inl path)) = recXs.reverse →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => my (.inl path)) = recYs.reverse →
    (Pattern.varNPaths (.const rec) major).map
      (fun path => captureType (.inl path)) = recTypes.reverse →
    (Pattern.varNPaths (.const rec) major).map recElemShape =
      recShapes.reverse →
    (Pattern.varNPaths (.const rec) major).map recTypeShape =
      recTypeShapes.reverse →
    (Pattern.varNPaths (.const ctor) arity).map
      (fun path => mx (.inr path)) = ctorXs.reverse →
    (Pattern.varNPaths (.const ctor) arity).map
      (fun path => my (.inr path)) = ctorYs.reverse →
    (Pattern.varNPaths (.const ctor) arity).map
      (fun path => captureType (.inr path)) = ctorTypes.reverse →
    (Pattern.varNPaths (.const ctor) arity).map ctorElemShape =
      ctorShapes.reverse →
    (Pattern.varNPaths (.const ctor) arity).map ctorTypeShape =
      ctorTypeShapes.reverse →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    (LRD Γ).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy

/-- Specialize a universally listed RHS consumer to the terminal indices of
one exact leaf. -/
theorem LRD.IotaRHSDefEqListedRec.toAt
    {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {recXs recYs recTypes : List SExpr}
    {recShapes recTypeShapes : List (WShape (n + 1))}
    {rule : Pattern.IotaRule r} {A : SExpr} {out outTy : WShape (n + 1)}
    (H : LRD.IotaRHSDefEqListedRec (Γ := Γ) R recLs mrec mctor r
      recXs recYs recTypes recShapes recTypeShapes rule out) :
    LRD.IotaRHSDefEqListedRecAt (Γ := Γ) R recLs mrec mctor r
      recXs recYs recTypes recShapes recTypeShapes rule A out outTy := by
  intro hrhs mx my captureType recElemShape recTypeShape
    hspineX hspineY hcap hcapRec hrecXs hrecYs hrecTypes
    hrecShapes hrecTypeShapes hout hA
  exact H hrhs hspineX hspineY hcap hcapRec hrecXs hrecYs hrecTypes
    hrecShapes hrecTypeShapes hout hA

/-- An ordinary guarded RHS consumer can ignore all five listed recursor
readbacks. -/
theorem LRD.IotaRHSDefEq.toListedRec
    {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {recXs recYs recTypes : List SExpr}
    {recShapes recTypeShapes : List (WShape (n + 1))}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    (H : LRD.IotaRHSDefEq (Γ := Γ) R recLs
      mrec mctor r rule out) :
    LRD.IotaRHSDefEqListedRec (Γ := Γ) R recLs mrec mctor r
      recXs recYs recTypes recShapes recTypeShapes rule out := by
  intro hrhs mx my captureType recElemShape recTypeShape A outTy
    hspineX hspineY hcap _hcapRec _hrecXs _hrecYs _hrecTypes
    _hrecShapes _hrecTypeShapes hout hA
  exact H hrhs hspineX hspineY hcap hout hA

/-- Reduce the guarded generated-RHS contract to its non-bottom fixed-head
case.  Recursor-prefix captures keep their paired guarded evidence, while
constructor captures contribute the predecessor relation used to reconstruct
the semantic head's typed lower approximation. -/
theorem LRD.IotaRHSDefEq.of_nonbot
    {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    (H : ∀ {head : TShape}
        {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {captureType :
          (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {A : SExpr} {outTy : WShape (n + 1)},
      LE_Interp.RHS (p := RecursorIotaPattern rec major ctor arity)
        recLs (Sum.elim mrec mctor) R head
        (.fixed rule.df.rhs rule.rhsClosed) →
      IsDefEqStrong Γ (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) →
      LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T →
      (∃ headElem headTy : TShape,
        headElem ≤ head ∧ headElem.HasType headTy) →
      SExpr.PathSpineWF Γ mx captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      SExpr.PathSpineWF Γ my captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LR.DirectCaptureDefEqAligned
            (n := n + 1) (LRD Γ) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
            (mctor p) (mx path) (my path) (captureType path)) →
      out.HasType outTy →
      (LRD Γ).TyDefEq A A outTy →
      (LRD Γ).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy) :
    LRD.IotaRHSDefEq (Γ := Γ) R recLs
      mrec mctor r rule out := by
  intro hrhs mx my captureType A outTy hspineX hspineY hcap hout hA
  obtain hbot | ⟨head, hhead, hshapeSpine⟩ := rule.rhsShapeSpine hrhs
  · have houtBot : out = .bot := TShape.le_bot.1 hbot
    subst out
    exact LRD.DefEq.bot hout.isType
  · have hcapTyped : ∀ path,
        ∃ elem elemTy : TShape,
          Sum.elim mrec mctor path ≤ elem ∧ elem.HasType elemTy := by
      intro path
      cases path with
      | inl path =>
        obtain ⟨elem, elemTy, hshape, htype, _⟩ := hcap (.inl path)
        exact ⟨elem.T, elemTy.T, hshape, htype.T⟩
      | inr path =>
        obtain ⟨elem, elemTy, hshape, htype, _⟩ := hcap (.inr path)
        exact ⟨elem.T, elemTy.T, hshape, htype.T⟩
    have hheadTyped := hshapeSpine.typedLowerHead hcapTyped hout.T
    exact H hhead (rule.rhsStrong recLs) hshapeSpine hheadTyped
      hspineX hspineY hcap hout hA

/-- Proof-relevant guarded fixed-head form.  The callback receives the exact
semantic witness selected by the enclosing RHS derivation, so a recursive
successor result cannot be silently reselected at the same public indices. -/
theorem LRD.IotaRHSDefEq.of_nonbotWitness
    {R : TShape → SExpr → Prop} {ρ : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (H : ∀ {head : TShape}
        {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {captureType :
          (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {A : SExpr} {outTy : WShape (n + 1)},
      LE_Interp.Witness ρ head (SExpr.mkInst recLs rule.df.rhs) →
      IsDefEqStrong Γ (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) →
      LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T →
      (∃ headElem headTy : TShape,
        headElem ≤ head ∧ headElem.HasType headTy) →
      SExpr.PathSpineWF Γ mx captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      SExpr.PathSpineWF Γ my captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LR.DirectCaptureDefEqAligned
            (n := n + 1) (LRD Γ) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
            (mctor p) (mx path) (my path) (captureType path)) →
      out.HasType outTy →
      (LRD Γ).TyDefEq A A outTy →
      (LRD Γ).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy) :
    LRD.IotaRHSDefEq (Γ := Γ) (LE_Interp.Lower R) recLs
      mrec mctor r rule out := by
  apply LRD.IotaRHSDefEq.of_nonbot
  intro head mx my captureType A outTy hhead hstrong hshape htyped
    hspineX hspineY hcap hout hA
  exact H (hhead.fixedLowerWitness hR) hstrong hshape htyped
    hspineX hspineY hcap hout hA

/-- Recursive-result-preserving guarded form of `of_nonbotWitness`.

The fixed head and its attached predicate are selected together through
`fixedLowerWitnessResult`.  This is the proof-relevant boundary needed by a
guarded coherent leaf: retained evaluator seeds, child trees, or semantic
typing data cannot be silently paired with a second witness at the same
public indices. -/
theorem LRD.IotaRHSDefEq.of_nonbotWitnessResult
    {R : TShape → SExpr → Prop} {ρ : Valuation}
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hP : ∀ {m M} (hr : R m M), P (hR hr))
    (hmono : ∀ {m m' M} (hle : m ≤ m')
      (hM : LE_Interp.Witness ρ m' M), P hM → P (hM.mono hle))
    (H : ∀ {head : TShape}
        {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {captureType :
          (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {A : SExpr} {outTy : WShape (n + 1)}
        (hhead : LE_Interp.Witness ρ head
          (SExpr.mkInst recLs rule.df.rhs)),
      P hhead →
      IsDefEqStrong Γ (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) →
      LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T →
      (∃ headElem headTy : TShape,
        headElem ≤ head ∧ headElem.HasType headTy) →
      SExpr.PathSpineWF Γ mx captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      SExpr.PathSpineWF Γ my captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LR.DirectCaptureDefEqAligned
            (n := n + 1) (LRD Γ) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
            (mctor p) (mx path) (my path) (captureType path)) →
      out.HasType outTy →
      (LRD Γ).TyDefEq A A outTy →
      (LRD Γ).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy) :
    LRD.IotaRHSDefEq (Γ := Γ) (LE_Interp.Lower R) recLs
      mrec mctor r rule out := by
  intro hrhs mx my captureType A outTy hspineX hspineY hcap hout hA
  by_cases houtBot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact LRD.DefEq.bot hout.isType
  obtain hbot | ⟨head, hhead, hshapeSpine⟩ := rule.rhsShapeSpine hrhs
  · exact (houtBot hbot).elim
  have hheadNonbot : ¬head ≤ TShape.bot := by
    intro hbot
    exact houtBot (hshapeSpine.le_bot hbot)
  have hcapTyped : ∀ path,
      ∃ elem elemTy : TShape,
        Sum.elim mrec mctor path ≤ elem ∧ elem.HasType elemTy := by
    intro path
    cases path with
    | inl path =>
      obtain ⟨elem, elemTy, hshape, htype, _⟩ := hcap (.inl path)
      exact ⟨elem.T, elemTy.T, hshape, htype.T⟩
    | inr path =>
      obtain ⟨elem, elemTy, hshape, htype, _⟩ := hcap (.inr path)
      exact ⟨elem.T, elemTy.T, hshape, htype.T⟩
  have hheadTyped := hshapeSpine.typedLowerHead hcapTyped hout.T
  let headResult :=
    hhead.fixedLowerWitnessResult hR hP hmono hheadNonbot
  exact H headResult.1 headResult.2 (rule.rhsStrong recLs)
    hshapeSpine hheadTyped hspineX hspineY hcap hout hA

/--
info: 'Lean4Lean.SExpr.LRD.IotaRHSDefEq.of_nonbotWitnessResult' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.IotaRHSDefEq.of_nonbotWitnessResult

/-- Guarded exact iota action materialization.  Recursor-prefix captures
retain paired legacy/direct evidence at one selected type; constructor-field
captures stay in the predecessor legacy relation.  The theorem also builds
the registered reduction actions and returns the complete contractions. -/
theorem LRD.iotaActions_of_exactEqAt
    {n : Nat} {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrecargs : LR.DirectCtorArgsDefEq (LRD Γ₀)
      recXs recYs recShapes)
    (hctorargs : LRS.CtorArgsDefEq (LR Γ₀)
      ctorXs ctorYs ctorShapes)
    (hMajorX : WHRedS Γ₀ majorX
      (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)))
    (hMajorY : WHRedS Γ₀ majorY
      (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')))
    (hsiteTypeX : ∀ (_ : WHRedS Γ₀
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs)))),
      Γ₀ ⊢
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) : A)
    (hsiteTypeY : ∀ (_ : WHRedS Γ₀
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs')))),
      Γ₀ ⊢
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) : A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    {recHeadType ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      majorType : SExpr}
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hrecSpineX : SExpr.SpineWF Γ₀ recHeadType
      (recXs.reverse ++ [majorX]) A)
    (hrecSpineY : SExpr.SpineWF Γ₀ recHeadType
      (recYs.reverse ++ [majorY]) A)
    (hctorHeadX : Γ₀ ⊢ .const ctor ctorLs : ctorHeadTypeX)
    (hctorHeadY : Γ₀ ⊢ .const ctor ctorLs' : ctorHeadTypeY)
    (hctorSpineX : SExpr.SpineWF Γ₀ ctorHeadTypeX
      ctorXs.reverse ctorResultX)
    (hctorSpineY : SExpr.SpineWF Γ₀ ctorHeadTypeY
      ctorYs.reverse ctorResultY)
    (hMajorEqX : IsDefEq Γ₀ majorX
      (ctorXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs)) majorType)
    (hMajorEqY : IsDefEq Γ₀ majorY
      (ctorYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs')) majorType) :
    ∃ (mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (recElemShape recTypeShape :
        (Pattern.varN (.const rec) major).Path → WShape (n + 1))
      (captureTypingX : Pattern.CaptureTyping Γ₀ mx captureType)
      (captureTypingY : Pattern.CaptureTyping Γ₀ my captureType)
      (rule : Pattern.IotaRule r)
      (siteX : Pattern.IotaReductionSite Γ₀ r rule recLs ctorLs
        recXs ctorXs majorX A mx captureType captureTypingX)
      (siteY : Pattern.IotaReductionSite Γ₀ r rule recLs ctorLs'
        recYs ctorYs majorY A my captureType captureTypingY),
      ∃ actionX : Pattern.Action Γ₀ r
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) recLs mx A,
      ∃ actionY : Pattern.Action Γ₀ r
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) recLs my A,
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LR.DirectCaptureDefEqAligned
            (n := n + 1) (LRD Γ₀) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ₀)
            (mctor p) (mx path) (my path) (captureType path)) ∧
      (∀ path : (Pattern.varN (.const rec) major).Path,
        LR.DirectCaptureDefEqAligned.AtShapes
          (n := n + 1) (LRD Γ₀) (mrec path)
          (mx (.inl path)) (my (.inl path)) (captureType (.inl path))
          (recElemShape path) (recTypeShape path)) ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => mx (.inl path)) = recXs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => my (.inl path)) = recYs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map recElemShape =
        recShapes.reverse ∧
      WHRedS Γ₀
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorX)
        (r.1.applyS recLs mx) ∧
      WHRedS Γ₀
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorY)
        (r.1.applyS recLs my) := by
  obtain ⟨mx, my, captureType, recElemShape, recTypeShape,
      hmatchX, hmatchY, hrecXsPaths, hrecYsPaths, hrecShapePaths,
      hcapRec, hcapCtor, hredX, hredY⟩ :=
    LE_Interp.Matches.iota_materializeDirectRecAlignedAt hpat hmf hma
      hrecargs hctorargs hMajorX hMajorY
  let typingX : Pattern.IotaTyping Γ₀ rec ctor recLs ctorLs
      recXs ctorXs majorX A := {
    recHeadType := recHeadType
    ctorHeadType := ctorHeadTypeX
    ctorResultType := ctorResultX
    majorType := majorType
    recHead := hrecHead
    recSpine := hrecSpineX
    ctorHead := hctorHeadX
    ctorSpine := hctorSpineX
    majorEq := hMajorEqX }
  let typingY : Pattern.IotaTyping Γ₀ rec ctor recLs ctorLs'
      recYs ctorYs majorY A := {
    recHeadType := recHeadType
    ctorHeadType := ctorHeadTypeY
    ctorResultType := ctorResultY
    majorType := majorType
    recHead := hrecHead
    recSpine := hrecSpineY
    ctorHead := hctorHeadY
    ctorSpine := hctorSpineY
    majorEq := hMajorEqY }
  classical
  let captureTypingX : Pattern.CaptureTyping Γ₀ mx captureType := {
    typed := by
      intro path
      cases path with
      | inl p =>
        exact (hcapRec p).2.2.2.2.1.hasType.1
      | inr p =>
        exact (LRS.CaptureDefEqAligned.witness
          (hcapCtor p)).defeq.hasType.1 }
  let captureTypingY : Pattern.CaptureTyping Γ₀ my captureType := {
    typed := by
      intro path
      cases path with
      | inl p =>
        exact (hcapRec p).2.2.2.2.1.hasType.2
      | inr p =>
        exact (LRS.CaptureDefEqAligned.witness
          (hcapCtor p)).defeq.hasType.2 }
  let rule := Params.Semantic.iotaRule hpat
  let siteX := Params.Semantic.iotaSite rule captureType captureTypingX
    hΓ.reify typingX hmatchX (hsiteTypeX hredX) hAType
  let siteY := Params.Semantic.iotaSite rule captureType captureTypingY
    hΓ.reify typingY hmatchY (hsiteTypeY hredY) hAType
  let actionX := siteX.action
  let actionY := siteY.action
  have hcapAligned : ∀ path :
      (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LR.DirectCaptureDefEqAligned
          (n := n + 1) (LRD Γ₀) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ₀)
          (mctor p) (mx path) (my path) (captureType path) := by
    intro path
    cases path with
    | inl p =>
      exact ⟨recElemShape p, recTypeShape p, hcapRec p⟩
    | inr p => exact hcapCtor p
  exact ⟨mx, my, captureType, recElemShape, recTypeShape,
    captureTypingX, captureTypingY,
    rule, siteX, siteY, actionX, actionY, hcapAligned, hcapRec,
    hrecXsPaths, hrecYsPaths, hrecShapePaths,
    .tail hredX (.extra actionX), .tail hredY (.extra actionY)⟩

/-- Guarded iota action materialization from an explicitly listed recursor
prefix.  The resulting sites and contractions retain canonical readback
equations for syntax, capture types, element shapes, and type shapes. -/
theorem LRD.iotaActions_of_exactListedAt
    {n : Nat} {rec ctor : Name} {major arity : Nat}
    {recShapes recTypeShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs recTypes ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrecargs : LR.DirectCtorArgsDefEqListed (LRD Γ₀)
      recXs recYs recTypes recShapes recTypeShapes)
    (hctorargs : LRS.CtorArgsDefEq (LR Γ₀)
      ctorXs ctorYs ctorShapes)
    (hMajorX : WHRedS Γ₀ majorX
      (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)))
    (hMajorY : WHRedS Γ₀ majorY
      (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')))
    (hsiteTypeX : ∀ (_ : WHRedS Γ₀
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs)))),
      Γ₀ ⊢
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) : A)
    (hsiteTypeY : ∀ (_ : WHRedS Γ₀
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs')))),
      Γ₀ ⊢
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) : A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    {recHeadType ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      majorType : SExpr}
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hrecSpineX : SExpr.SpineWF Γ₀ recHeadType
      (recXs.reverse ++ [majorX]) A)
    (hrecSpineY : SExpr.SpineWF Γ₀ recHeadType
      (recYs.reverse ++ [majorY]) A)
    (hctorHeadX : Γ₀ ⊢ .const ctor ctorLs : ctorHeadTypeX)
    (hctorHeadY : Γ₀ ⊢ .const ctor ctorLs' : ctorHeadTypeY)
    (hctorSpineX : SExpr.SpineWF Γ₀ ctorHeadTypeX
      ctorXs.reverse ctorResultX)
    (hctorSpineY : SExpr.SpineWF Γ₀ ctorHeadTypeY
      ctorYs.reverse ctorResultY)
    (hMajorEqX : IsDefEq Γ₀ majorX
      (ctorXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs)) majorType)
    (hMajorEqY : IsDefEq Γ₀ majorY
      (ctorYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs')) majorType) :
    ∃ (mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (recElemShape recTypeShape :
        (Pattern.varN (.const rec) major).Path → WShape (n + 1))
      (captureTypingX : Pattern.CaptureTyping Γ₀ mx captureType)
      (captureTypingY : Pattern.CaptureTyping Γ₀ my captureType)
      (rule : Pattern.IotaRule r)
      (siteX : Pattern.IotaReductionSite Γ₀ r rule recLs ctorLs
        recXs ctorXs majorX A mx captureType captureTypingX)
      (siteY : Pattern.IotaReductionSite Γ₀ r rule recLs ctorLs'
        recYs ctorYs majorY A my captureType captureTypingY),
      ∃ actionX : Pattern.Action Γ₀ r
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) recLs mx A,
      ∃ actionY : Pattern.Action Γ₀ r
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) recLs my A,
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LR.DirectCaptureDefEqAligned
            (n := n + 1) (LRD Γ₀) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ₀)
            (mctor p) (mx path) (my path) (captureType path)) ∧
      (∀ path : (Pattern.varN (.const rec) major).Path,
        LR.DirectCaptureDefEqAligned.AtShapes
          (n := n + 1) (LRD Γ₀) (mrec path)
          (mx (.inl path)) (my (.inl path)) (captureType (.inl path))
          (recElemShape path) (recTypeShape path)) ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => mx (.inl path)) = recXs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => my (.inl path)) = recYs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => captureType (.inl path)) = recTypes.reverse ∧
      (Pattern.varNPaths (.const rec) major).map recElemShape =
        recShapes.reverse ∧
      (Pattern.varNPaths (.const rec) major).map recTypeShape =
        recTypeShapes.reverse ∧
      WHRedS Γ₀
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorX)
        (r.1.applyS recLs mx) ∧
      WHRedS Γ₀
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorY)
        (r.1.applyS recLs my) := by
  obtain ⟨mx, my, captureType, recElemShape, recTypeShape,
      hmatchX, hmatchY, hrecXsPaths, hrecYsPaths, hrecTypePaths,
      hrecShapePaths, hrecTypeShapePaths, hcapRec, hcapCtor,
      hredX, hredY⟩ :=
    LE_Interp.Matches.iota_materializeDirectRecListedAt hpat hmf hma
      hrecargs hctorargs hMajorX hMajorY
  let typingX : Pattern.IotaTyping Γ₀ rec ctor recLs ctorLs
      recXs ctorXs majorX A := {
    recHeadType := recHeadType
    ctorHeadType := ctorHeadTypeX
    ctorResultType := ctorResultX
    majorType := majorType
    recHead := hrecHead
    recSpine := hrecSpineX
    ctorHead := hctorHeadX
    ctorSpine := hctorSpineX
    majorEq := hMajorEqX }
  let typingY : Pattern.IotaTyping Γ₀ rec ctor recLs ctorLs'
      recYs ctorYs majorY A := {
    recHeadType := recHeadType
    ctorHeadType := ctorHeadTypeY
    ctorResultType := ctorResultY
    majorType := majorType
    recHead := hrecHead
    recSpine := hrecSpineY
    ctorHead := hctorHeadY
    ctorSpine := hctorSpineY
    majorEq := hMajorEqY }
  classical
  let captureTypingX : Pattern.CaptureTyping Γ₀ mx captureType := {
    typed := by
      intro path
      cases path with
      | inl p => exact (hcapRec p).2.2.2.2.1.hasType.1
      | inr p =>
        exact (LRS.CaptureDefEqAligned.witness
          (hcapCtor p)).defeq.hasType.1 }
  let captureTypingY : Pattern.CaptureTyping Γ₀ my captureType := {
    typed := by
      intro path
      cases path with
      | inl p => exact (hcapRec p).2.2.2.2.1.hasType.2
      | inr p =>
        exact (LRS.CaptureDefEqAligned.witness
          (hcapCtor p)).defeq.hasType.2 }
  let rule := Params.Semantic.iotaRule hpat
  let siteX := Params.Semantic.iotaSite rule captureType captureTypingX
    hΓ.reify typingX hmatchX (hsiteTypeX hredX) hAType
  let siteY := Params.Semantic.iotaSite rule captureType captureTypingY
    hΓ.reify typingY hmatchY (hsiteTypeY hredY) hAType
  let actionX := siteX.action
  let actionY := siteY.action
  have hcapAligned : ∀ path :
      (RecursorIotaPattern rec major ctor arity).Path,
      match path with
      | Sum.inl p => LR.DirectCaptureDefEqAligned
          (n := n + 1) (LRD Γ₀) (mrec p)
          (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ₀)
          (mctor p) (mx path) (my path) (captureType path) := by
    intro path
    cases path with
    | inl p => exact ⟨recElemShape p, recTypeShape p, hcapRec p⟩
    | inr p => exact hcapCtor p
  exact ⟨mx, my, captureType, recElemShape, recTypeShape,
    captureTypingX, captureTypingY, rule, siteX, siteY,
    actionX, actionY, hcapAligned, hcapRec,
    hrecXsPaths, hrecYsPaths, hrecTypePaths,
    hrecShapePaths, hrecTypeShapePaths,
    .tail hredX (.extra actionX), .tail hredY (.extra actionY)⟩

/-- Materialize the registered actions while retaining fully listed paired
guarded captures on both sides of the recursor/constructor split. -/
theorem LRD.iotaActions_of_exactDirectListedAt
    {n : Nat} {rec ctor : Name} {major arity : Nat}
    {recShapes recTypeShapes : List (WShape (n + 1))}
    {ctorShapes ctorTypeShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs recTypes ctorXs ctorYs ctorTypes : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrecargs : LR.DirectCtorArgsDefEqListed (LRD Γ₀)
      recXs recYs recTypes recShapes recTypeShapes)
    (hctorargs : LR.DirectCtorArgsDefEqListed (LRD Γ₀)
      ctorXs ctorYs ctorTypes ctorShapes ctorTypeShapes)
    (hMajorX : WHRedS Γ₀ majorX
      (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)))
    (hMajorY : WHRedS Γ₀ majorY
      (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')))
    (hsiteTypeX : ∀ (_ : WHRedS Γ₀
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs)))),
      Γ₀ ⊢
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) : A)
    (hsiteTypeY : ∀ (_ : WHRedS Γ₀
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs')))),
      Γ₀ ⊢
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) : A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    {recHeadType ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      majorType : SExpr}
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hrecSpineX : SExpr.SpineWF Γ₀ recHeadType
      (recXs.reverse ++ [majorX]) A)
    (hrecSpineY : SExpr.SpineWF Γ₀ recHeadType
      (recYs.reverse ++ [majorY]) A)
    (hctorHeadX : Γ₀ ⊢ .const ctor ctorLs : ctorHeadTypeX)
    (hctorHeadY : Γ₀ ⊢ .const ctor ctorLs' : ctorHeadTypeY)
    (hctorSpineX : SExpr.SpineWF Γ₀ ctorHeadTypeX
      ctorXs.reverse ctorResultX)
    (hctorSpineY : SExpr.SpineWF Γ₀ ctorHeadTypeY
      ctorYs.reverse ctorResultY)
    (hMajorEqX : IsDefEq Γ₀ majorX
      (ctorXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs)) majorType)
    (hMajorEqY : IsDefEq Γ₀ majorY
      (ctorYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs')) majorType) :
    ∃ (mx my captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (recElemShape recTypeShape :
        (Pattern.varN (.const rec) major).Path → WShape (n + 1))
      (ctorElemShape ctorTypeShape :
        (Pattern.varN (.const ctor) arity).Path → WShape n)
      (captureTypingX : Pattern.CaptureTyping Γ₀ mx captureType)
      (captureTypingY : Pattern.CaptureTyping Γ₀ my captureType)
      (rule : Pattern.IotaRule r)
      (siteX : Pattern.IotaReductionSite Γ₀ r rule recLs ctorLs
        recXs ctorXs majorX A mx captureType captureTypingX)
      (siteY : Pattern.IotaReductionSite Γ₀ r rule recLs ctorLs'
        recYs ctorYs majorY A my captureType captureTypingY),
      ∃ actionX : Pattern.Action Γ₀ r
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) recLs mx A,
      ∃ actionY : Pattern.Action Γ₀ r
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs'))) recLs my A,
      (∀ path : (Pattern.varN (.const rec) major).Path,
        LR.DirectCaptureDefEqAligned.AtShapes
          (n := n + 1) (LRD Γ₀) (mrec path)
          (mx (.inl path)) (my (.inl path)) (captureType (.inl path))
          (recElemShape path) (recTypeShape path)) ∧
      (∀ path : (Pattern.varN (.const ctor) arity).Path,
        LR.DirectCaptureDefEqAligned.AtShapes
          (n := n) (LRD Γ₀) (mctor path)
          (mx (.inr path)) (my (.inr path)) (captureType (.inr path))
          (ctorElemShape path) (ctorTypeShape path)) ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => mx (.inl path)) = recXs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => my (.inl path)) = recYs.reverse ∧
      (Pattern.varNPaths (.const rec) major).map
        (fun path => captureType (.inl path)) = recTypes.reverse ∧
      (Pattern.varNPaths (.const rec) major).map recElemShape =
        recShapes.reverse ∧
      (Pattern.varNPaths (.const rec) major).map recTypeShape =
        recTypeShapes.reverse ∧
      (Pattern.varNPaths (.const ctor) arity).map
        (fun path => mx (.inr path)) = ctorXs.reverse ∧
      (Pattern.varNPaths (.const ctor) arity).map
        (fun path => my (.inr path)) = ctorYs.reverse ∧
      (Pattern.varNPaths (.const ctor) arity).map
        (fun path => captureType (.inr path)) = ctorTypes.reverse ∧
      (Pattern.varNPaths (.const ctor) arity).map ctorElemShape =
        ctorShapes.reverse ∧
      (Pattern.varNPaths (.const ctor) arity).map ctorTypeShape =
        ctorTypeShapes.reverse ∧
      WHRedS Γ₀
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorX)
        (r.1.applyS recLs mx) ∧
      WHRedS Γ₀
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app majorY)
        (r.1.applyS recLs my) := by
  obtain ⟨mx, my, captureType, recElemShape, recTypeShape,
      ctorElemShape, ctorTypeShape, hmatchX, hmatchY,
      hrecXsPaths, hrecYsPaths, hrecTypePaths,
      hrecShapePaths, hrecTypeShapePaths,
      hctorXsPaths, hctorYsPaths, hctorTypePaths,
      hctorShapePaths, hctorTypeShapePaths,
      hcapRec, hcapCtor, hredX, hredY⟩ :=
    LE_Interp.Matches.iota_materializeDirectListedAt hpat hmf hma
      hrecargs hctorargs hMajorX hMajorY
  let typingX : Pattern.IotaTyping Γ₀ rec ctor recLs ctorLs
      recXs ctorXs majorX A := {
    recHeadType := recHeadType
    ctorHeadType := ctorHeadTypeX
    ctorResultType := ctorResultX
    majorType := majorType
    recHead := hrecHead
    recSpine := hrecSpineX
    ctorHead := hctorHeadX
    ctorSpine := hctorSpineX
    majorEq := hMajorEqX }
  let typingY : Pattern.IotaTyping Γ₀ rec ctor recLs ctorLs'
      recYs ctorYs majorY A := {
    recHeadType := recHeadType
    ctorHeadType := ctorHeadTypeY
    ctorResultType := ctorResultY
    majorType := majorType
    recHead := hrecHead
    recSpine := hrecSpineY
    ctorHead := hctorHeadY
    ctorSpine := hctorSpineY
    majorEq := hMajorEqY }
  let captureTypingX : Pattern.CaptureTyping Γ₀ mx captureType := {
    typed := by
      intro path
      cases path with
      | inl p => exact (hcapRec p).2.2.2.2.1.hasType.1
      | inr p => exact (hcapCtor p).2.2.2.2.1.hasType.1 }
  let captureTypingY : Pattern.CaptureTyping Γ₀ my captureType := {
    typed := by
      intro path
      cases path with
      | inl p => exact (hcapRec p).2.2.2.2.1.hasType.2
      | inr p => exact (hcapCtor p).2.2.2.2.1.hasType.2 }
  let rule := Params.Semantic.iotaRule hpat
  let siteX := Params.Semantic.iotaSite rule captureType captureTypingX
    hΓ.reify typingX hmatchX (hsiteTypeX hredX) hAType
  let siteY := Params.Semantic.iotaSite rule captureType captureTypingY
    hΓ.reify typingY hmatchY (hsiteTypeY hredY) hAType
  let actionX := siteX.action
  let actionY := siteY.action
  exact ⟨mx, my, captureType, recElemShape, recTypeShape,
    ctorElemShape, ctorTypeShape, captureTypingX, captureTypingY,
    rule, siteX, siteY, actionX, actionY, hcapRec, hcapCtor,
    hrecXsPaths, hrecYsPaths, hrecTypePaths,
    hrecShapePaths, hrecTypeShapePaths,
    hctorXsPaths, hctorYsPaths, hctorTypePaths,
    hctorShapePaths, hctorTypeShapePaths,
    .tail hredX (.extra actionX), .tail hredY (.extra actionY)⟩

/-- Consume explicitly listed iota-site data after the constructor leaf has
already been normalized.  This is the data-level core of the exact-leaf
handler: it needs only the two raw constructor spines and their finite field
relation, so a nullary constructor can be reused across a `CtorFrame`
without transporting the frame's ambient logical relation. -/
theorem LRD.iotaDefEq_of_exactListedDataAt
    {n : Nat} {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recShapes recTypeShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs recTypes ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      R out.T r.1)
    (hrecargs : LR.DirectCtorArgsDefEqListed (LRD Γ₀)
      recXs recYs recTypes recShapes recTypeShapes)
    (hctorargs : LRS.CtorArgsDefEq (LR Γ₀)
      ctorXs ctorYs ctorShapes)
    (hMajorRedX : WHRedS Γ₀ majorX
      (ctorXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs)))
    (hMajorRedY : WHRedS Γ₀ majorY
      (ctorYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs')))
    (hsiteTypeX : Γ₀ ⊢
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs))) : A)
    (hsiteTypeY : Γ₀ ⊢
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs'))) : A)
    (hsiteEqX : IsDefEq Γ₀
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs))) A)
    (hsiteEqY : IsDefEq Γ₀
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs'))) A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    {recHeadType ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      majorType : SExpr}
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hrecSpineX : SExpr.SpineWF Γ₀ recHeadType
      (recXs.reverse ++ [majorX]) A)
    (hrecSpineY : SExpr.SpineWF Γ₀ recHeadType
      (recYs.reverse ++ [majorY]) A)
    (hctorHeadX : Γ₀ ⊢ .const ctor ctorLs : ctorHeadTypeX)
    (hctorHeadY : Γ₀ ⊢ .const ctor ctorLs' : ctorHeadTypeY)
    (hctorSpineX : SExpr.SpineWF Γ₀ ctorHeadTypeX
      ctorXs.reverse ctorResultX)
    (hctorSpineY : SExpr.SpineWF Γ₀ ctorHeadTypeY
      ctorYs.reverse ctorResultY)
    (hMajorEqX : IsDefEq Γ₀ majorX
      (ctorXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs)) majorType)
    (hMajorEqY : IsDefEq Γ₀ majorY
      (ctorYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs')) majorType)
    (hout : out.HasType outTy)
    (hA : (LRD Γ₀).TyDefEq A A outTy)
    (rhsDefEq : ∀ rule : Pattern.IotaRule r,
      LRD.IotaRHSDefEqListedRecAt (Γ := Γ₀) R recLs mrec mctor r
        recXs recYs recTypes recShapes recTypeShapes rule A out outTy) :
    (LRD Γ₀).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  obtain ⟨mx, my, captureType, recElemShape, recTypeShape,
      captureTypingX, captureTypingY, rule, siteX, siteY,
      actionX, actionY, hcap, hcapRec,
      hrecXsPaths, hrecYsPaths, hrecTypePaths,
      hrecShapePaths, hrecTypeShapePaths, hredX, hredY⟩ :=
    LRD.iotaActions_of_exactListedAt hΓ hpat hmf hma
      hrecargs hctorargs hMajorRedX hMajorRedY
      (fun _ => hsiteTypeX) (fun _ => hsiteTypeY)
      hAType hrecHead hrecSpineX hrecSpineY
      hctorHeadX hctorHeadY hctorSpineX hctorSpineY
      hMajorEqX hMajorEqY
  have hrhsDefEq : (LRD Γ₀).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy :=
    rhsDefEq rule hrhs siteX.captureSpine siteY.captureSpine
      hcap hcapRec hrecXsPaths hrecYsPaths hrecTypePaths
      hrecShapePaths hrecTypeShapePaths hout hA
  have htypedX : TypedWHRedS Γ₀
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      (r.1.applyS recLs mx) A :=
    ⟨hsiteEqX.trans actionX.sound, hredX⟩
  have htypedY : TypedWHRedS Γ₀
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      (r.1.applyS recLs my) A :=
    ⟨hsiteEqY.trans actionY.sound, hredY⟩
  exact (LRD.DefEq.whr hA htypedX htypedY).2 hrhsDefEq

/-- Consume explicitly listed iota-site data when the normalized constructor
fields have already been rebuilt in the paired guarded root relation. -/
theorem LRD.iotaDefEq_of_exactDirectListedDataAt
    {n : Nat} {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recShapes recTypeShapes : List (WShape (n + 1))}
    {ctorShapes ctorTypeShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs recTypes ctorXs ctorYs ctorTypes : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      R out.T r.1)
    (hrecargs : LR.DirectCtorArgsDefEqListed (LRD Γ₀)
      recXs recYs recTypes recShapes recTypeShapes)
    (hctorargs : LR.DirectCtorArgsDefEqListed (LRD Γ₀)
      ctorXs ctorYs ctorTypes ctorShapes ctorTypeShapes)
    (hMajorRedX : WHRedS Γ₀ majorX
      (ctorXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs)))
    (hMajorRedY : WHRedS Γ₀ majorY
      (ctorYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs')))
    (hsiteTypeX : Γ₀ ⊢
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs))) : A)
    (hsiteTypeY : Γ₀ ⊢
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs'))) : A)
    (hsiteEqX : IsDefEq Γ₀
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs))) A)
    (hsiteEqY : IsDefEq Γ₀
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a)
            (.const ctor ctorLs'))) A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    {recHeadType ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      majorType : SExpr}
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hrecSpineX : SExpr.SpineWF Γ₀ recHeadType
      (recXs.reverse ++ [majorX]) A)
    (hrecSpineY : SExpr.SpineWF Γ₀ recHeadType
      (recYs.reverse ++ [majorY]) A)
    (hctorHeadX : Γ₀ ⊢ .const ctor ctorLs : ctorHeadTypeX)
    (hctorHeadY : Γ₀ ⊢ .const ctor ctorLs' : ctorHeadTypeY)
    (hctorSpineX : SExpr.SpineWF Γ₀ ctorHeadTypeX
      ctorXs.reverse ctorResultX)
    (hctorSpineY : SExpr.SpineWF Γ₀ ctorHeadTypeY
      ctorYs.reverse ctorResultY)
    (hMajorEqX : IsDefEq Γ₀ majorX
      (ctorXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs)) majorType)
    (hMajorEqY : IsDefEq Γ₀ majorY
      (ctorYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ctor ctorLs')) majorType)
    (hout : out.HasType outTy)
    (hA : (LRD Γ₀).TyDefEq A A outTy)
    (rhsDefEq : ∀ rule : Pattern.IotaRule r,
      LRD.IotaRHSDefEqDirectListedRecAt (Γ := Γ₀) R
        recLs mrec mctor r recXs recYs recTypes recShapes recTypeShapes
        ctorXs ctorYs ctorTypes ctorShapes ctorTypeShapes
        rule A out outTy) :
    (LRD Γ₀).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  obtain ⟨mx, my, captureType, recElemShape, recTypeShape,
      ctorElemShape, ctorTypeShape, captureTypingX, captureTypingY,
      rule, siteX, siteY, actionX, actionY, hcapRec, hcapCtor,
      hrecXsPaths, hrecYsPaths, hrecTypePaths,
      hrecShapePaths, hrecTypeShapePaths,
      hctorXsPaths, hctorYsPaths, hctorTypePaths,
      hctorShapePaths, hctorTypeShapePaths, hredX, hredY⟩ :=
    LRD.iotaActions_of_exactDirectListedAt hΓ hpat hmf hma
      hrecargs hctorargs hMajorRedX hMajorRedY
      (fun _ => hsiteTypeX) (fun _ => hsiteTypeY)
      hAType hrecHead hrecSpineX hrecSpineY
      hctorHeadX hctorHeadY hctorSpineX hctorSpineY
      hMajorEqX hMajorEqY
  have hrhsDefEq : (LRD Γ₀).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy :=
    rhsDefEq rule hrhs siteX.captureSpine siteY.captureSpine
      hcapRec hcapCtor
      hrecXsPaths hrecYsPaths hrecTypePaths
      hrecShapePaths hrecTypeShapePaths
      hctorXsPaths hctorYsPaths hctorTypePaths
      hctorShapePaths hctorTypeShapePaths hout hA
  have htypedX : TypedWHRedS Γ₀
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      (r.1.applyS recLs mx) A :=
    ⟨hsiteEqX.trans actionX.sound, hredX⟩
  have htypedY : TypedWHRedS Γ₀
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      (r.1.applyS recLs my) A :=
    ⟨hsiteEqY.trans actionY.sound, hredY⟩
  exact (LRD.DefEq.whr hA htypedX htypedY).2 hrhsDefEq

/-- Consume one native constructor leaf using an explicitly listed recursor
prefix.  The generated-RHS callback receives the five canonical readbacks
from the registered Pi domains used to build its reduction sites. -/
theorem LRD.iotaDefEq_of_ctorExactListedAt
    {n : Nat} {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recShapes recTypeShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs recTypes : List SExpr} {recLs : List SLevel}
    {majorX majorY recHeadType A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    {hwf : IsStruct ctor → WShape.ListNonZero ctorShapes.reverse}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      R out.T r.1)
    (leaf : LRS.CtorExact Γ₀ (LR Γ₀) majorX majorY
      (.ctor ctor ctorShapes.reverse hwf))
    (hleaf : LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ctor ctorShapes.reverse hwf) :: recShapes) A out outTy)
    (hrecargs : LR.DirectCtorArgsDefEqListed (LRD Γ₀)
      recXs recYs recTypes recShapes recTypeShapes)
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hout : out.HasType outTy)
    (hA : (LRD Γ₀).TyDefEq A A outTy)
    (rhsDefEq : ∀ rule : Pattern.IotaRule r,
      LRD.IotaRHSDefEqListedRecAt (Γ := Γ₀) R recLs mrec mctor r
        recXs recYs recTypes recShapes recTypeShapes rule A out outTy) :
    (LRD Γ₀).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  generalize hm : WShape.ctor ctor ctorShapes.reverse hwf = m at leaf
  cases leaf with
  | @intro _ ctorLeafShapes _ ctorLs ctorLs' ctorXs ctorYs
      ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      hctorClass hctorLenX hctorLenY hctorLevels hctorHeadX hctorHeadY
      hctorSpineX hctorSpineY hctorArgs hctorAligned hctorMirror =>
    subst ctorLs'
    obtain ⟨rfl, hctorShapes⟩ := WShape.ctor.inj.1 hm
    have hctorShapes' : ctorShapes = ctorLeafShapes := by
      exact List.reverse_inj.1 hctorShapes
    subst ctorShapes
    have hterm : Γ₀ ⊢
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) ≡
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) : A := by
      simpa only [List.foldl_reverse, List.foldr_cons] using
        hleaf.legacy.aligned.spine.congr hrecHead
    have hAType : ∃ u, Γ₀ ⊢ A : .sort u :=
      ⟨hleaf.legacy.pair.resultSortX,
        hleaf.legacy.pair.resultX.hasType.2⟩
    have hrecSpineX := hleaf.legacy.pair.fullX
    rw [← hleaf.legacy.args_eq] at hrecSpineX
    simp only [List.reverse_cons] at hrecSpineX
    have hrecSpineY := hleaf.legacy.pair.fullY
    rw [← hleaf.legacy.args'_eq] at hrecSpineY
    simp only [List.reverse_cons] at hrecSpineY
    obtain ⟨_, hmajor⟩ := hleaf.legacy.majorDefEq
    obtain ⟨mx, my, captureType, recElemShape, recTypeShape,
        captureTypingX, captureTypingY, rule, siteX, siteY,
        actionX, actionY, hcap, hcapRec,
        hrecXsPaths, hrecYsPaths, hrecTypePaths,
        hrecShapePaths, hrecTypeShapePaths, hredX, hredY⟩ :=
      LRD.iotaActions_of_exactListedAt hΓ hpat hmf hma
        hrecargs hctorArgs .rfl .rfl
        (fun _ => hterm.hasType.1) (fun _ => hterm.hasType.2)
        hAType hrecHead hrecSpineX hrecSpineY
        hctorHeadX hctorHeadY hctorSpineX hctorSpineY
        hmajor.hasType.1 hmajor.hasType.2
    have hrhsDefEq : (LRD Γ₀).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy :=
      rhsDefEq rule hrhs siteX.captureSpine siteY.captureSpine
        hcap hcapRec hrecXsPaths hrecYsPaths hrecTypePaths
        hrecShapePaths hrecTypeShapePaths hout hA
    have htypedX : TypedWHRedS Γ₀
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs)))
        (r.1.applyS recLs mx) A := ⟨actionX.sound, hredX⟩
    have htypedY : TypedWHRedS Γ₀
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs)))
        (r.1.applyS recLs my) A := ⟨actionY.sound, hredY⟩
    exact (LRD.DefEq.whr hA htypedX htypedY).2 hrhsDefEq

/-- Consume one native constructor leaf while exposing the exact materialized
recursor capture shapes to the generated-RHS consumer.  The registered
actions themselves provide the typed equalities for both contractions, so
guarded weak-head transport needs no external subject-reduction theorem. -/
theorem LRD.iotaDefEq_of_ctorExactAlignedAt
    {n : Nat} {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs : List SExpr} {recLs : List SLevel}
    {majorX majorY recHeadType A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    {hwf : IsStruct ctor → WShape.ListNonZero ctorShapes.reverse}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      R out.T r.1)
    (leaf : LRS.CtorExact Γ₀ (LR Γ₀) majorX majorY
      (.ctor ctor ctorShapes.reverse hwf))
    (hleaf : LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ctor ctorShapes.reverse hwf) :: recShapes) A out outTy)
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hout : out.HasType outTy)
    (hA : (LRD Γ₀).TyDefEq A A outTy)
    (rhsDefEq : ∀ rule : Pattern.IotaRule r,
      LRD.IotaRHSDefEqAlignedRec (Γ := Γ₀) R recLs
        mrec mctor r recXs recYs recShapes rule out) :
    (LRD Γ₀).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  generalize hm : WShape.ctor ctor ctorShapes.reverse hwf = m at leaf
  cases leaf with
  | @intro _ ctorLeafShapes _ ctorLs ctorLs' ctorXs ctorYs
      ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      hctorClass hctorLenX hctorLenY hctorLevels hctorHeadX hctorHeadY
      hctorSpineX hctorSpineY hctorArgs hctorAligned hctorMirror =>
    subst ctorLs'
    obtain ⟨rfl, hctorShapes⟩ := WShape.ctor.inj.1 hm
    have hctorShapes' : ctorShapes = ctorLeafShapes := by
      exact List.reverse_inj.1 hctorShapes
    subst ctorShapes
    have hterm : Γ₀ ⊢
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) ≡
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) : A := by
      simpa only [List.foldl_reverse, List.foldr_cons] using
        hleaf.legacy.aligned.spine.congr hrecHead
    have hAType : ∃ u, Γ₀ ⊢ A : .sort u :=
      ⟨hleaf.legacy.pair.resultSortX,
        hleaf.legacy.pair.resultX.hasType.2⟩
    have hrecSpineX := hleaf.legacy.pair.fullX
    rw [← hleaf.legacy.args_eq] at hrecSpineX
    simp only [List.reverse_cons] at hrecSpineX
    have hrecSpineY := hleaf.legacy.pair.fullY
    rw [← hleaf.legacy.args'_eq] at hrecSpineY
    simp only [List.reverse_cons] at hrecSpineY
    obtain ⟨_, hmajor⟩ := hleaf.legacy.majorDefEq
    obtain ⟨mx, my, captureType, recElemShape, recTypeShape,
        captureTypingX, captureTypingY, rule, siteX, siteY,
        actionX, actionY, hcap, hcapRec,
        hrecXsPaths, hrecYsPaths, hrecShapePaths, hredX, hredY⟩ :=
      LRD.iotaActions_of_exactEqAt hΓ hpat hmf hma
        hleaf.directArgs.tail hctorArgs .rfl .rfl
        (fun _ => hterm.hasType.1) (fun _ => hterm.hasType.2)
        hAType hrecHead hrecSpineX hrecSpineY
        hctorHeadX hctorHeadY hctorSpineX hctorSpineY
        hmajor.hasType.1 hmajor.hasType.2
    have hrhsDefEq : (LRD Γ₀).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy :=
      rhsDefEq rule hrhs siteX.captureSpine siteY.captureSpine
        hcap hcapRec hrecXsPaths hrecYsPaths hrecShapePaths hout hA
    have htypedX : TypedWHRedS Γ₀
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs)))
        (r.1.applyS recLs mx) A := ⟨actionX.sound, hredX⟩
    have htypedY : TypedWHRedS Γ₀
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs)))
        (r.1.applyS recLs my) A := ⟨actionY.sound, hredY⟩
    exact (LRD.DefEq.whr hA htypedX htypedY).2 hrhsDefEq

/-- Consume one native constructor leaf in the guarded relation.  This
compatibility wrapper forgets the exact recursor shape maps exposed by
`iotaDefEq_of_ctorExactAlignedAt`. -/
theorem LRD.iotaDefEq_of_ctorExactAt
    {n : Nat} {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs : List SExpr} {recLs : List SLevel}
    {majorX majorY recHeadType A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    {hwf : IsStruct ctor → WShape.ListNonZero ctorShapes.reverse}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      R out.T r.1)
    (leaf : LRS.CtorExact Γ₀ (LR Γ₀) majorX majorY
      (.ctor ctor ctorShapes.reverse hwf))
    (hleaf : LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ctor ctorShapes.reverse hwf) :: recShapes) A out outTy)
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hout : out.HasType outTy)
    (hA : (LRD Γ₀).TyDefEq A A outTy)
    (rhsDefEq : ∀ rule : Pattern.IotaRule r,
      LRD.IotaRHSDefEq (Γ := Γ₀) R recLs
        mrec mctor r rule out) :
    (LRD Γ₀).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  exact LRD.iotaDefEq_of_ctorExactAlignedAt hΓ hpat hmf hma hrhs
    leaf hleaf hrecHead hout hA
    (fun rule => (rhsDefEq rule).toAlignedRec
      (recXs := recXs) (recYs := recYs) (recShapes := recShapes))

/--
info: 'Lean4Lean.SExpr.LR.DirectCtorArgsDefEq.tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCtorArgsDefEq.tail

/--
info: 'Lean4Lean.SExpr.LR.DirectCaptureDefEqAt.Witness.aligned' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.DirectCaptureDefEqAt.Witness.aligned

/--
info: 'Lean4Lean.SExpr.LRD.IotaRHSDefEq.toAlignedRec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.IotaRHSDefEq.toAlignedRec

/--
info: 'Lean4Lean.SExpr.LRD.IotaRHSDefEqListedRec.toAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.IotaRHSDefEqListedRec.toAt

/--
info: 'Lean4Lean.SExpr.LRD.IotaRHSDefEq.toListedRec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.IotaRHSDefEq.toListedRec

/--
info: 'Lean4Lean.SExpr.LRD.iotaActions_of_exactEqAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaActions_of_exactEqAt

/--
info: 'Lean4Lean.SExpr.LRD.iotaActions_of_exactListedAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaActions_of_exactListedAt

/--
info: 'Lean4Lean.SExpr.LRD.iotaActions_of_exactDirectListedAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaActions_of_exactDirectListedAt

/--
info: 'Lean4Lean.SExpr.LRD.iotaDefEq_of_exactListedDataAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaDefEq_of_exactListedDataAt

/--
info: 'Lean4Lean.SExpr.LRD.iotaDefEq_of_exactDirectListedDataAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaDefEq_of_exactDirectListedDataAt

/--
info: 'Lean4Lean.SExpr.LRD.iotaDefEq_of_ctorExactAlignedAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaDefEq_of_ctorExactAlignedAt

/--
info: 'Lean4Lean.SExpr.LRD.iotaDefEq_of_ctorExactListedAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaDefEq_of_ctorExactListedAt

/--
info: 'Lean4Lean.SExpr.LRD.iotaDefEq_of_ctorExactAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaDefEq_of_ctorExactAt

/-- Consume one native constructor leaf as a synchronized guarded iota
rectangle.  The two row edges retain the original related majors and choose
the left or right direct recursor prefix; the cross edge is the original
paired leaf.  All three calls therefore share the exact result observation
and the registered actions' typed contractions. -/
theorem LRD.iotaDefEqRect_of_ctorExactAt
    {n : Nat} {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs : List SExpr} {recLs : List SLevel}
    {majorX majorY recHeadType A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    {hwf : IsStruct ctor → WShape.ListNonZero ctorShapes.reverse}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      R out.T r.1)
    (leaf : LRS.CtorExact Γ₀ (LR Γ₀) majorX majorY
      (.ctor ctor ctorShapes.reverse hwf))
    (hleaf : LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ctor ctorShapes.reverse hwf) :: recShapes) A out outTy)
    (hrecHead : IsDefEq Γ₀ (.const rec recLs) (.const rec recLs)
      recHeadType)
    (hout : out.HasType outTy)
    (hA : (LRD Γ₀).TyDefEq A A outTy)
    (rhsDefEq : ∀ rule : Pattern.IotaRule r,
      LRD.IotaRHSDefEq (Γ := Γ₀) R recLs
        mrec mctor r rule out) :
    LR.DirectDefEqRect (LRD Γ₀)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  refine ⟨?_, ?_, ?_⟩
  · exact LRD.iotaDefEq_of_ctorExactAt hΓ hpat hmf hma hrhs leaf
      hleaf.leftPrefixes hrecHead hout hA rhsDefEq
  · exact LRD.iotaDefEq_of_ctorExactAt hΓ hpat hmf hma hrhs leaf
      hleaf.rightPrefixes hrecHead hout hA rhsDefEq
  · exact LRD.iotaDefEq_of_ctorExactAt hΓ hpat hmf hma hrhs leaf
      hleaf hrecHead hout hA rhsDefEq

/--
info: 'Lean4Lean.SExpr.LRD.iotaDefEqRect_of_ctorExactAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.iotaDefEqRect_of_ctorExactAt

/-- Consume a native exact constructor leaf without appealing to generic
weak-head subject reduction.

At this boundary both majors already *are* their classified constructor
spines.  `CtorExact` supplies the constructor head/spine certificates and
related fields, while `PatternLeafSpine` supplies the recursor spine, its
last Pi, and the majors' common domain typing.  Both majors' weak-head
observations are reflexive here and every remaining typing is projected
from those two certificates.  This is the exact handler used after a
`CtorFrame` has reached its native leaf. -/
theorem LRS.iotaDefEq_of_ctorExactAt
    {n : Nat} {IH : LogRel Γ₀ n}
    {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs : List SExpr} {recLs : List SLevel}
    {majorX majorY recHeadType A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    {hwf : IsStruct ctor → WShape.ListNonZero ctorShapes.reverse}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      R out.T r.1)
    (leaf : LRS.CtorExact Γ₀ IH majorX majorY
      (.ctor ctor ctorShapes.reverse hwf))
    (hleaf : LR.PatternLeafSpine Γ₀ (LRS IH) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ctor ctorShapes.reverse hwf) :: recShapes) A out outTy)
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hout : out.HasType outTy)
    (hA : (LRS IH).TyDefEq A A outTy)
    (rhsDefEq : ∀ rule : Pattern.IotaRule r,
      LRS.IotaRHSDefEq IH R recLs mrec mctor r rule out) :
    (LRS IH).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  generalize hm : WShape.ctor ctor ctorShapes.reverse hwf = m at leaf
  cases leaf with
  | @intro _ ctorLeafShapes _ ctorLs ctorLs' ctorXs ctorYs
      ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      hctorClass hctorLenX hctorLenY hctorLevels hctorHeadX hctorHeadY
      hctorSpineX hctorSpineY hctorArgs hctorAligned hctorMirror =>
    subst ctorLs'
    obtain ⟨rfl, hctorShapes⟩ := WShape.ctor.inj.1 hm
    have hctorShapes' : ctorShapes = ctorLeafShapes := by
      exact List.reverse_inj.1 hctorShapes
    subst ctorShapes
    have hterm : Γ₀ ⊢
        ((recXs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) ≡
        ((recYs.foldr (fun (a f : SExpr) => f.app a)
          (.const rec recLs)).app
            (ctorYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ctor ctorLs))) : A := by
      simpa only [List.foldl_reverse, List.foldr_cons] using
        hleaf.aligned.spine.congr hrecHead
    have hAType : ∃ u, Γ₀ ⊢ A : .sort u :=
      ⟨hleaf.pair.resultSortX, hleaf.pair.resultX.hasType.2⟩
    have hrecSpineX := hleaf.pair.fullX
    rw [← hleaf.args_eq] at hrecSpineX
    simp only [List.reverse_cons] at hrecSpineX
    have hrecSpineY := hleaf.pair.fullY
    rw [← hleaf.args'_eq] at hrecSpineY
    simp only [List.reverse_cons] at hrecSpineY
    obtain ⟨_, hmajor⟩ := hleaf.majorDefEq
    obtain ⟨mx, my, captureType, captureTypingX, captureTypingY,
        rule, siteX, siteY, actionX, actionY, hcap, hredX, hredY⟩ :=
      LR.iotaActions_of_exactEqAt (IH := IH) hΓ hpat hmf hma
        hleaf.args.tail hctorArgs .rfl .rfl
        (fun _ => hterm.hasType.1) (fun _ => hterm.hasType.2)
        hAType hrecHead
      hrecSpineX hrecSpineY
      hctorHeadX hctorHeadY hctorSpineX hctorSpineY
      hmajor.hasType.1 hmajor.hasType.2
    have hrhsDefEq : (LRS IH).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy :=
      rhsDefEq rule hrhs siteX.captureSpine siteY.captureSpine hcap hout hA
    exact ((LRS IH).whr hredX hredY).2 hrhsDefEq

/-- Consume one native constructor leaf as a synchronized iota rectangle.

The two row edges reuse respectively the left and right recursor prefixes
while keeping the original related constructor majors.  The diagonal reuses
the original cross-prefix leaf.  Thus all three contractions have one result
shape and one left-oriented dependent result type, which is the invariant
needed by normalized-chain composition. -/
theorem LRS.iotaDefEqRect_of_ctorExactAt
    {n : Nat} {IH : LogRel Γ₀ n}
    {R : TShape → SExpr → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs : List SExpr} {recLs : List SLevel}
    {majorX majorY recHeadType A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    {hwf : IsStruct ctor → WShape.ListNonZero ctorShapes.reverse}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      R out.T r.1)
    (leaf : LRS.CtorExact Γ₀ IH majorX majorY
      (.ctor ctor ctorShapes.reverse hwf))
    (hleaf : LR.PatternLeafSpine Γ₀ (LRS IH) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ctor ctorShapes.reverse hwf) :: recShapes) A out outTy)
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hout : out.HasType outTy)
    (hA : (LRS IH).TyDefEq A A outTy)
    (rhsDefEq : ∀ rule : Pattern.IotaRule r,
      LRS.IotaRHSDefEq IH R recLs mrec mctor r rule out) :
    LogRel.DefEqRect (LRS IH)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  refine ⟨?_, ?_, ?_⟩
  · exact LRS.iotaDefEq_of_ctorExactAt hΓ hpat hmf hma hrhs leaf
      hleaf.leftPrefixes hrecHead hout hA rhsDefEq
  · exact LRS.iotaDefEq_of_ctorExactAt hΓ hpat hmf hma hrhs leaf
      hleaf.rightPrefixes hrecHead hout hA rhsDefEq
  · exact LRS.iotaDefEq_of_ctorExactAt hΓ hpat hmf hma hrhs leaf
      hleaf hrecHead hout hA rhsDefEq

/-- Close one native exact iota leaf from proof-relevant fixed-head results.

The semantic `R` callback and its recursive result are selected together,
so lowering the reached head cannot silently reselect a different constant
evaluator.  This is the exact-leaf half of the final normalized consumer:
constructor materialization remains local, while the generated RHS is
discharged by the proof-independent canonical `FixedHeadResult`.

`producer` carries the caller's own result typing `out.HasType outTyP`:
without that premise the ∀-quantified `outTyP` could be instantiated at
`.bot`, and `LR.FixedHeadTelescopeLE.outHasType` would force `out.T ≤ ⊥` —
an undischargeable demand, since every invocation below runs strictly after
the bottom result shape has been discharged. -/
theorem LRS.iotaDefEq_of_ctorExactAt_fixedHead
    {n : Nat}
    {R : TShape → SExpr → Prop} {ρ : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs : List SExpr} {recLs : List SLevel}
    {majorX majorY recHeadType A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    {hwf : IsStruct ctor → WShape.ListNonZero ctorShapes.reverse}
    {Δ : List SExpr} {σ σ' : Subst}
    (W : LR.SubstWF Γ₀ σ σ' Δ ρ)
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T r.1)
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hP : ∀ {m M} (hr : R m M), LR.FixedHeadResult Γ₀ (hR hr))
    (producer : ∀ (rule : Pattern.IotaRule r) {head : TShape}
      (mx my captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      {outTyP : WShape (n + 1)}
      (houtP : out.HasType outTyP)
      (hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T),
      LR.FixedHeadProducer Γ₀ ρ rule mx my captureType hshape
        (recLs := recLs) (outTy := outTyP))
    (leaf : LRS.CtorExact Γ₀ (LR Γ₀) majorX majorY
      (.ctor ctor ctorShapes.reverse hwf))
    (hleaf : LR.PatternLeafSpine Γ₀ (LR Γ₀) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ctor ctorShapes.reverse hwf) :: recShapes) A out outTy)
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hout : out.HasType outTy)
    (hA : (LR Γ₀).TyDefEq A A outTy) :
    (LR Γ₀).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  apply LRS.iotaDefEq_of_ctorExactAt hΓ hpat hmf hma hrhs leaf hleaf
    hrecHead hout hA
  intro rule
  apply LRS.IotaRHSDefEq.of_nonbotWitnessResult
    (P := fun h => LR.FixedHeadResult Γ₀ h) hR hP
  · intro m m' M hle hM H
    exact LR.FixedHeadResult.mono (ρ := ρ) (hX := hM) hle H
  · intro head mx my captureType A outTy hhead hfixed _hstrong hshape
      _htyped hspineX hspineY hcap hout hA
    refine producer rule mx my captureType hout hshape (outTyP := outTy) ?_
    intro headTy htel hTyReg
    exact hfixed W rfl .rfl (rule.rhsStrong recLs) hshape htel hTyReg
      hspineX hspineY hcap hout hA

/-- Close one native exact iota leaf from closed-valuation fixed-head
results.

`FixedHeadResult` is consumed through `LR.SubstWF`, whose only closed
constructor pins the valuation to `Valuation.nil`, while an abstract
constant evaluator observes its registered fixed heads at an arbitrary
caller valuation with no fits certificate.  The registered RHS is closed,
so the selected head witness is transported to `Valuation.nil` at the same
root shape before its fixed-head result is consumed at the identity
substitution.  Nothing is truncated by this move: the semantic spine, the
typed lower head, both raw capture telescopes, and the aligned logical
captures are already valuation-free, and `Witness.closedAt` preserves the
entire evaluator tree of the selected witness rather than reselecting a
public interpretation.

`producer` carries the caller's own result typing `out.HasType outTyP`; see
`iotaDefEq_of_ctorExactAt_fixedHead` for why the premise is required. -/
theorem LRS.iotaDefEq_of_ctorExactAt_closedFixedHead
    {n : Nat}
    {R : TShape → SExpr → Prop} {ρ : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs : List SExpr} {recLs : List SLevel}
    {majorX majorY recHeadType A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    {hwf : IsStruct ctor → WShape.ListNonZero ctorShapes.reverse}
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T r.1)
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (fixedHead : ∀ {root : TShape} {X : SExpr}
      (hX : LE_Interp.Witness Valuation.nil root X),
      LR.FixedHeadResult Γ₀ hX)
    (producer : ∀ (rule : Pattern.IotaRule r) {head : TShape}
      (mx my captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      {outTyP : WShape (n + 1)}
      (houtP : out.HasType outTyP)
      (hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T),
      LR.FixedHeadProducer Γ₀ Valuation.nil rule mx my captureType hshape
        (recLs := recLs) (outTy := outTyP))
    (leaf : LRS.CtorExact Γ₀ (LR Γ₀) majorX majorY
      (.ctor ctor ctorShapes.reverse hwf))
    (hleaf : LR.PatternLeafSpine Γ₀ (LR Γ₀) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ctor ctorShapes.reverse hwf) :: recShapes) A out outTy)
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hout : out.HasType outTy)
    (hA : (LR Γ₀).TyDefEq A A outTy) :
    (LR Γ₀).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  apply LRS.iotaDefEq_of_ctorExactAt hΓ hpat hmf hma hrhs leaf hleaf
    hrecHead hout hA
  intro rule
  apply LRS.IotaRHSDefEq.of_nonbotWitness hR
  intro head mx my captureType A' outTy' hhead hstrong hshape
    _htyped hspineX hspineY hcap hout' hA'
  have hclosed : (SExpr.mkInst recLs rule.df.rhs).ClosedN :=
    rule.rhsClosed.mkInstS
  refine producer rule mx my captureType hout' hshape (outTyP := outTy') ?_
  intro headTy htel hTyReg
  exact fixedHead (hhead.closedAt hclosed) LR.SubstWF.id rfl .rfl
    hstrong hshape htel hTyReg hspineX hspineY hcap hout' hA'

/-- A proof of the iota-only leaf contract discharges every nonempty simple
pattern leaf. -/
theorem LR.PatternLeafDefEq.of_iota
    (H : LR.IotaLeafDefEq Γ₀ c ls R) :
    LR.PatternLeafDefEq Γ₀ c ls R := by
  intro n rargs p r mcap xs ys CHead A out outTy
    hpat hmatch hrhs hleaf hterm hAType hhead hspineX hspineY hout hA
  obtain ⟨rec, major, ctor, arity, rfl⟩ :=
    hmatch.iota_of_pat_nonempty hpat hleaf.nonempty
  exact H hpat hmatch hrhs hleaf hterm hAType hhead hspineX hspineY hout hA

/-- Evaluate a semantic constant using exact related syntax for its accumulated
application spine.  All structural cases are discharged here; a caller only
supplies the finite, proof-carrying action at a reached pattern leaf.  The
extra `rargs'` layer is essential: recursive semantic function layers may
change shape depth, while the already accumulated spine must only be lifted
or enlarged, never projected. -/
theorem LR.constDefEq
    {c : Name} {ls : List SLevel} {R : TShape → SExpr → Prop}
    (piInv : LRS.PiPathInv) (hΓ₀ : Ctx.WF Γ₀)
    (hRmono : ∀ {m m' M}, m ≤ m' → R m' M → R m M)
    {n : Nat} {rargs : List (WShape n)} {mout : TShape}
    (hC : LE_Interp.Const c ls R rargs mout)
    {n' : Nat} {rargs' : List (WShape n')}
    {xs ys : List SExpr} {CHead A : SExpr} {out outTy : WShape n'}
    (evalPat : LR.PatternLeafDefEqAt Γ₀ n' c ls R)
    (hargle : List.Forall₂ (fun x y => x.T ≤ y.T) rargs rargs')
    (hleaf : LR.PatternLeafSpine Γ₀ (LR Γ₀)
      CHead xs ys rargs' A out outTy)
    (hterm : Γ₀ ⊢
      (xs.foldr (fun a f => f.app a) (.const c ls)) ≡
      (ys.foldr (fun a f => f.app a) (.const c ls)) : A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    (hhead : Γ₀ ⊢ .const c ls : CHead)
    (hspineX : SExpr.SpineWF Γ₀ CHead xs.reverse A)
    (hspineY : SExpr.SpineWF Γ₀ CHead ys.reverse A)
    (hout : out.HasType outTy)
    (hA : (LR Γ₀).TyDefEq A A outTy)
    (houtle : out.T ≤ mout) :
    (LR Γ₀).DefEq
      (xs.foldr (fun a f => f.app a) (.const c ls))
      (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy := by
  induction hC generalizing rargs' xs ys A out outTy with
  | bot =>
    have hb : out.T ≤ TShape.bot := houtle.trans TShape.bot_eqv.1
    have heq : out = .bot := TShape.le_bot.1 hb
    subst out
    exact (LR Γ₀).bot hout.isType
  | pat hpat hmatch hrhs =>
    obtain ⟨mcap', hmatch', hcap⟩ :=
      hmatch.mono_lT (Params.pat_wf hpat) hargle
    have hrhs' : LE_Interp.RHS ls mcap' R out.T _ :=
      (hrhs.mono_l hcap).mono (R' := R) houtle
        (fun le hr => hRmono le hr)
    exact evalPat hpat hmatch' hrhs' hleaf hterm hAType
      hhead hspineX hspineY hout hA
  | @lam f rargs mout hrec hlam ih =>
    have hlam₀ := houtle.trans hlam
    have hlam' := hlam₀
    cases hout.unfold with
    | bot hm => exact (LR Γ₀).bot hm
    | sort => exact (TShape.sort_not_le_lam' hlam').elim
    | forallE => exact (TShape.forallE_not_le_lam' hlam').elim
    | @lam q g a₁ a₂ htm =>
      rw [LR_succ] at hA ⊢
      unfold WShape.lam' at hlam' ⊢
      split at hlam' <;> rename_i hg
      · obtain ⟨B₁, F₁, B₂, F₂, u, v, rA, _, hB, hF, hValB, hPi₀⟩ := hA
        have hPi := LRS.PiDefEq.left hPi₀
        have evalChild : ∀ {K : Nat}, K = q + 1 → ∀
            {x y : SExpr} {p : WShape K} {x₀ y₀ : WShape n}
            {zs zs' : List SExpr},
            LRS.CtorSpineDefEq (LR Γ₀) CHead zs zs' rargs' A →
            Γ₀ ⊢
              (zs.foldr (fun a f => f.app a) (.const c ls)) ≡
              (zs'.foldr (fun a f => f.app a) (.const c ls)) : A →
            SExpr.SpineWF Γ₀ CHead zs.reverse A →
            SExpr.SpineWF Γ₀ CHead zs'.reverse A →
            p.HasType (a₁.lift K) →
            Γ₀ ⊢ x ≡ y : B₁ →
            (LR Γ₀).DefEq x y B₁ p (a₁.lift K) →
            (x₀, y₀) ∈ f → x₀.T ≤ p.T →
            ((g.lift K).app p).T ≤ y₀.T →
            (LR Γ₀).DefEq
              ((zs.foldr (fun a (acc : SExpr) => acc.app a) (SExpr.const c ls)).app x)
              ((zs'.foldr (fun a (acc : SExpr) => acc.app a) (SExpr.const c ls)).app y)
              (F₁.inst x) ((g.lift K).app p)
                ((a₂.lift K).app p) := by
          intro K hK
          subst K
          intro x y p x₀ y₀ zs zs' htailAligned htailTerm
            htailSpineX htailSpineY hp hxy hv hmem hx hy
          have hchildLe : List.Forall₂ (fun x y => x.T ≤ y.T)
              (x₀ :: rargs) (p :: rargs') := by
            exact .cons hx hargle
          have hBK : (LR Γ₀).TyDefEq B₁ B₁ (a₁.lift (q + 1)) :=
            (LR.TyDefEq.lift (Nat.le_succ q)
              (WShape.HasTypePi.iff.1 htm.1).1.isType).2
              ((LR Γ₀).left_ty hValB)
          have htmK : WShape.HasTypeLam (g.lift (q + 1))
              (a₁.lift (q + 1)) (a₂.lift (q + 1)) :=
            (WShape.HasTypeLam.lift (Nat.le_succ q)).2 htm
          have houtK : ((g.lift (q + 1)).app p).HasType
              ((a₂.lift (q + 1)).app p) :=
            (WShape.HasTypeLam.iff.1 htmK).2.2 p hp
          have hPiK : LRS.PiDefEq (LR Γ₀) B₁ F₁ F₁
              (a₁.lift (q + 1)) (a₂.lift (q + 1)) :=
            (LRS.PiDefEq.lift (Nat.le_succ q) htm.1).2 hPi
          have hAK : (LR Γ₀).TyDefEq (F₁.inst x) (F₁.inst x)
              ((a₂.lift (q + 1)).app p) :=
            hPiK.2 hp hxy.hasType.1 ((LR Γ₀).left hv)
          obtain ⟨uA, hAType⟩ := hAType
          have hAeqPi : Γ₀ ⊢ A ≡ .forallE B₁ F₁ : .sort uA :=
            rA.defeq_of_piPathInv piInv hΓ₀ hAType
          have htailPi : Γ₀ ⊢
              (zs.foldr (fun a f => f.app a) (.const c ls)) ≡
              (zs'.foldr (fun a f => f.app a) (.const c ls)) :
                .forallE B₁ F₁ :=
            hAeqPi.defeqDF htailTerm
          have hchildTerm : Γ₀ ⊢
              (zs.foldr (fun a (f : SExpr) => f.app a) (SExpr.const c ls)).app x ≡
              (zs'.foldr (fun a (f : SExpr) => f.app a) (SExpr.const c ls)).app y :
                F₁.inst x :=
            .appDF htailPi hxy
          have hchildType : Γ₀ ⊢ F₁.inst x : .sort v :=
            (IsDefEq.beta hF.leftType hxy.hasType.1).hasType.2
          have hchildSpineX : SExpr.SpineWF Γ₀ CHead
              (x :: zs).reverse (F₁.inst x) := by
            simpa only [List.reverse_cons] using
              htailSpineX.snoc hAeqPi hxy.hasType.1
          obtain ⟨_, hCodomain⟩ := (hPiK.1 hp hxy hv).leftDefEq
          have hchildAligned : LRS.CtorSpineDefEq (LR Γ₀) CHead
              (x :: zs) (y :: zs')
              (p :: rargs') (F₁.inst x) :=
            .cons htailAligned hAeqPi hp hBK hxy hv hCodomain.symm
          have hchildSpineY : SExpr.SpineWF Γ₀ CHead
              (y :: zs').reverse (F₁.inst x) := by
            have hspine := htailSpineY.snoc hAeqPi hxy.hasType.2
            simpa only [List.reverse_cons] using
              SExpr.SpineWF.ret hspine hCodomain.symm
          let hchildPair : SExpr.SpineWF.LastPair Γ₀ CHead
              zs zs' x y (F₁.inst x) := {
              prefixType := A
              domain := B₁
              codomain := F₁
              piSort := uA
              resultSortX := v
              resultSortY := _
              prefixX := htailSpineX
              prefixY := htailSpineY
              pi := hAeqPi
              major := hxy
              resultX := hchildType
              resultY := hCodomain.symm }
          have hchildLeaf : LR.PatternLeafSpine Γ₀ (LR Γ₀) CHead
              (x :: zs) (y :: zs') (p :: rargs')
              (F₁.inst x) ((g.lift (q + 1)).app p)
                ((a₂.lift (q + 1)).app p) := {
            majorX := x
            recXs := zs
            majorY := y
            recYs := zs'
            majorShape := p
            recShapes := rargs'
            majorTypeShape := a₁.lift (q + 1)
            resultShape := g.lift (q + 1)
            resultTypeShape := a₂.lift (q + 1)
            args_eq := rfl
            args'_eq := rfl
            rargs_eq := rfl
            out_eq := rfl
            outTy_eq := rfl
            pair := hchildPair
            majorHasType := hp
            resultType := htmK.1
            majorType := hBK
            majorRel := hv
            aligned := hchildAligned
            pi := hPiK }
          simpa only [List.foldr_cons] using
            ih x₀ y₀ hmem hchildLe hchildLeaf
              hchildTerm ⟨v, hchildType⟩ hchildSpineX hchildSpineY
              houtK hAK hy
        rw [dif_pos hg]
        refine (LRS.DefEq.lam_forallE
          (M := xs.foldr (fun a f => f.app a) (.const c ls))
          (N := ys.foldr (fun a f => f.app a) (.const c ls))
          (A := A) (f := g) (hf := hg) (a₁ := a₁) (a₂ := a₂)
          (LR Γ₀)).2 ?_
        refine ⟨B₁, F₁, u, v, rA, hB.leftType,
          (LR Γ₀).left_ty hValB, hF.leftType, hPi, ?_⟩
        exact LR.constLamDefEq (hf := hg) (nArgs := q + 1) htm hlam₀
          (fun {_ _ _ _ _} hp hxy hv hmem hx hy => ⟨
            evalChild (Nat.max_eq_right (Nat.le_succ q))
              hleaf.aligned.left hterm.hasType.1
              hspineX hspineX hp hxy hv hmem hx hy,
            evalChild (Nat.max_eq_right (Nat.le_succ q))
              hleaf.aligned.right hterm.hasType.2
              hspineY hspineY hp hxy hv hmem hx hy,
            evalChild (Nat.max_eq_right (Nat.le_succ q))
              hleaf.aligned hterm hspineX hspineY
              hp hxy hv hmem hx hy⟩)
      · rw [dif_neg hg]
        exact (LR Γ₀).bot hout.isType
    | ctor => exact (TShape.ctor_not_le_lam' hlam').elim
    | indTy => exact (TShape.indTy_not_le_lam' hlam').elim
  | @ctor semOut semArgs hcl hctor =>
    have hlen : semArgs.length = rargs'.length := by
      simpa using Lean4Lean.List.Forall₂.length_eq hargle
    have hcl' : Params.classify c = some (.ctor rargs'.length) := hlen ▸ hcl
    let K := max n n'
    have hnK : n ≤ K := Nat.le_max_left ..
    have hn'K : n' ≤ K := Nat.le_max_right ..
    have hargsK := WShape.forall₂_liftT hnK hn'K hargle
    have hctorT : (WShape.ctor' c semArgs.reverse).T ≤
        (WShape.ctor' c rargs'.reverse).T := by
      apply (TShape.LE.def (Nat.succ_le_succ hnK)
        (Nat.succ_le_succ hn'K)).2
      rw [WShape.lift_ctor' hnK, WShape.lift_ctor' hn'K,
        List.map_reverse, List.map_reverse]
      exact WShape.ctor'_le_ctor' (List.Forall₂.reverse.2 hargsK)
    have hctor' := houtle.trans (hctor.trans hctorT)
    cases hout.unfold with
    | bot hm => exact (LR Γ₀).bot hm
    | sort => exact (TShape.sort_not_le_ctor' hctor').elim
    | forallE => exact (TShape.forallE_not_le_ctor' hctor').elim
    | lam htm =>
      unfold WShape.lam' at hctor' ⊢
      split at hctor' <;> rename_i hnonzero
      · exact (TShape.lam_not_le_ctor' hctor').elim
      · simpa [hnonzero] using (LR Γ₀).bot hout.isType
    | @ctor q c' fields hwf =>
      have hIndHead : LRS.IndTyHead Γ₀ A := by
        simpa only [LR_succ, LRS.TyDefEq.indTy_m] using hA.1
      rw [LR_succ]
      change LRS.IndDefEq Γ₀ (LR Γ₀)
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A
        (WShape.ctor c' fields hwf)
      exact ⟨hIndHead, LRS.CtorDefEq.of_exact_ctor_spines
        hleaf.args hleaf.aligned hleaf.aligned.symm hcl' rfl hhead hhead
        hspineX hspineY hctor'⟩
    | indTy => exact (TShape.indTy_not_le_ctor' hctor').elim
  | @indTy semOut semArgs hcl hind =>
    have hlen : semArgs.length = rargs'.length := by
      simpa using Lean4Lean.List.Forall₂.length_eq hargle
    have hcl' : Params.classify c = some (.indTy rargs'.length) := hlen ▸ hcl
    have hind' := houtle.trans hind
    cases hout.unfold with
    | bot hm => exact (LR Γ₀).bot hm
    | sort => exact (TShape.sort_not_le_indTy hind').elim
    | forallE => exact (TShape.forallE_not_le_indTy hind').elim
    | lam htm =>
      unfold WShape.lam' at hind' ⊢
      split at hind' <;> rename_i hnonzero
      · exact (TShape.lam_not_le_indTy hind').elim
      · simpa [hnonzero] using (LR Γ₀).bot hout.isType
    | ctor => exact (TShape.ctor_not_le_indTy hind').elim
    | indTy =>
      rw [LR_succ]
      change LRS.IndTyHead Γ₀
          (xs.foldr (fun a f => f.app a) (.const c ls)) ∧
        LRS.IndTyHead Γ₀
          (ys.foldr (fun a f => f.app a) (.const c ls))
      exact ⟨⟨c, ls, xs, hleaf.args.lengths.1.symm ▸ hcl', .rfl⟩,
        ⟨c, ls, ys, hleaf.args.lengths.2.symm ▸ hcl', .rfl⟩⟩

/-- Direct constant evaluation.  This is the recursive counterpart of
`LR.constDefEq`: the result type arrives as `DirectTyDefEq`, so every Pi
layer supplies both its own path-typed root and the next instantiated
codomain observation.  No `PiPathInv` or subject-reduction callback appears
in the interface. -/
theorem LR.constDefEqDirect
    {c : Name} {ls : List SLevel} {R : TShape → SExpr → Prop}
    (hRmono : ∀ {m m' M}, m ≤ m' → R m' M → R m M)
    {n : Nat} {rargs : List (WShape n)} {mout : TShape}
    (hC : LE_Interp.Const c ls R rargs mout)
    {n' : Nat} {rargs' : List (WShape n')}
    {xs ys : List SExpr} {CHead A : SExpr} {out outTy : WShape n'}
    (evalPat : LR.PatternLeafDefEqAt Γ₀ n' c ls R)
    (hargle : List.Forall₂ (fun x y => x.T ≤ y.T) rargs rargs')
    (hleaf : LR.PatternLeafSpine Γ₀ (LR Γ₀)
      CHead xs ys rargs' A out outTy)
    (hterm : Γ₀ ⊢
      (xs.foldr (fun a f => f.app a) (.const c ls)) ≡
      (ys.foldr (fun a f => f.app a) (.const c ls)) : A)
    (hAType : ∃ u, Γ₀ ⊢ A : .sort u)
    (hhead : Γ₀ ⊢ .const c ls : CHead)
    (hspineX : SExpr.SpineWF Γ₀ CHead xs.reverse A)
    (hspineY : SExpr.SpineWF Γ₀ CHead ys.reverse A)
    (hout : out.HasType outTy)
    (hADirect : LR.DirectTyDefEq Γ₀ A A outTy)
    (houtle : out.T ≤ mout) :
    (LR Γ₀).DefEq
      (xs.foldr (fun a f => f.app a) (.const c ls))
      (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy := by
  induction hC generalizing rargs' xs ys A out outTy with
  | bot =>
    have hb : out.T ≤ TShape.bot := houtle.trans TShape.bot_eqv.1
    have heq : out = .bot := TShape.le_bot.1 hb
    subst out
    exact (LR Γ₀).bot hout.isType
  | pat hpat hmatch hrhs =>
    obtain ⟨mcap', hmatch', hcap⟩ :=
      hmatch.mono_lT (Params.pat_wf hpat) hargle
    have hrhs' : LE_Interp.RHS ls mcap' R out.T _ :=
      (hrhs.mono_l hcap).mono (R' := R) houtle
        (fun le hr => hRmono le hr)
    exact evalPat hpat hmatch' hrhs' hleaf hterm hAType
      hhead hspineX hspineY hout hADirect.toTyDefEq
  | @lam f rargs mout hrec hlam ih =>
    have hlam₀ := houtle.trans hlam
    have hlam' := hlam₀
    cases hout.unfold with
    | bot hm => exact (LR Γ₀).bot hm
    | sort => exact (TShape.sort_not_le_lam' hlam').elim
    | forallE => exact (TShape.forallE_not_le_lam' hlam').elim
    | @lam q g a₁ a₂ htm =>
      rw [LR_succ]
      unfold WShape.lam' at hlam' ⊢
      split at hlam' <;> rename_i hg
      · obtain ⟨B₁, F₁, B₂, F₂, u, v, rootA, _rootA₂,
          hB, hF, hValB, hPi₀, hDirectPi⟩ :=
          hADirect.toValTyPi2DirectRec
        obtain ⟨uA, rootPath, rootRed⟩ := rootA
        have hPi := LRS.PiDefEq.left hPi₀
        have evalChild : ∀ {K : Nat}, K = q + 1 → ∀
            {x y : SExpr} {p : WShape K} {x₀ y₀ : WShape n}
            {zs zs' : List SExpr},
            LRS.CtorSpineDefEq (LR Γ₀) CHead zs zs' rargs' A →
            Γ₀ ⊢
              (zs.foldr (fun a f => f.app a) (.const c ls)) ≡
              (zs'.foldr (fun a f => f.app a) (.const c ls)) : A →
            SExpr.SpineWF Γ₀ CHead zs.reverse A →
            SExpr.SpineWF Γ₀ CHead zs'.reverse A →
            p.HasType (a₁.lift K) →
            Γ₀ ⊢ x ≡ y : B₁ →
            (LR Γ₀).DefEq x y B₁ p (a₁.lift K) →
            (x₀, y₀) ∈ f → x₀.T ≤ p.T →
            ((g.lift K).app p).T ≤ y₀.T →
            (LR Γ₀).DefEq
              ((zs.foldr (fun a (acc : SExpr) => acc.app a) (SExpr.const c ls)).app x)
              ((zs'.foldr (fun a (acc : SExpr) => acc.app a) (SExpr.const c ls)).app y)
              (F₁.inst x) ((g.lift K).app p)
                ((a₂.lift K).app p) := by
          intro K hK
          subst K
          intro x y p x₀ y₀ zs zs' htailAligned htailTerm
            htailSpineX htailSpineY hp hxy hv hmem hx hy
          have hchildLe : List.Forall₂ (fun x y => x.T ≤ y.T)
              (x₀ :: rargs) (p :: rargs') := by
            exact .cons hx hargle
          have hBK : (LR Γ₀).TyDefEq B₁ B₁ (a₁.lift (q + 1)) :=
            (LR.TyDefEq.lift (Nat.le_succ q)
              (WShape.HasTypePi.iff.1 htm.1).1.isType).2
              hValB.left.toTyDefEq
          have htmK : WShape.HasTypeLam (g.lift (q + 1))
              (a₁.lift (q + 1)) (a₂.lift (q + 1)) :=
            (WShape.HasTypeLam.lift (Nat.le_succ q)).2 htm
          have houtK : ((g.lift (q + 1)).app p).HasType
              ((a₂.lift (q + 1)).app p) :=
            (WShape.HasTypeLam.iff.1 htmK).2.2 p hp
          have hPiK : LRS.PiDefEq (LR Γ₀) B₁ F₁ F₁
              (a₁.lift (q + 1)) (a₂.lift (q + 1)) :=
            (LRS.PiDefEq.lift (Nat.le_succ q) htm.1).2 hPi
          have hAK : LR.DirectTyDefEq Γ₀ (F₁.inst x) (F₁.inst x)
              ((a₂.lift (q + 1)).app p) :=
            (hDirectPi (Nat.le_succ q) hp hxy.hasType.1
              ((LR Γ₀).left hv)).left
          have htailPi : Γ₀ ⊢
              (zs.foldr (fun a f => f.app a) (.const c ls)) ≡
              (zs'.foldr (fun a f => f.app a) (.const c ls)) :
                .forallE B₁ F₁ :=
            rootPath.defeqDF htailTerm
          have hchildTerm : Γ₀ ⊢
              (zs.foldr (fun a (f : SExpr) => f.app a) (SExpr.const c ls)).app x ≡
              (zs'.foldr (fun a (f : SExpr) => f.app a) (SExpr.const c ls)).app y :
                F₁.inst x :=
            .appDF htailPi hxy
          have hchildType : Γ₀ ⊢ F₁.inst x : .sort v :=
            (IsDefEq.beta hF.leftType hxy.hasType.1).hasType.2
          have hchildSpineX : SExpr.SpineWF Γ₀ CHead
              (x :: zs).reverse (F₁.inst x) := by
            simpa only [List.reverse_cons] using
              htailSpineX.snoc_path rootPath hxy.hasType.1
          obtain ⟨_, hCodomain⟩ := (hPiK.1 hp hxy hv).leftDefEq
          have hchildSpineY : SExpr.SpineWF Γ₀ CHead
              (y :: zs').reverse (F₁.inst x) := by
            have hspine := htailSpineY.snoc_path rootPath hxy.hasType.2
            simpa only [List.reverse_cons] using
              SExpr.SpineWF.ret hspine hCodomain.symm
          obtain ⟨hchildLeaf⟩ := LR.PatternLeafSpine.of_cons_path
            (g := g.lift (q + 1)) (f := a₂.lift (q + 1))
            htailSpineX htailSpineY htailAligned rootPath hp htmK.1 hBK
            hxy hv hCodomain.symm hPiK
          simpa only [List.foldr_cons] using
            ih x₀ y₀ hmem hchildLe hchildLeaf
              hchildTerm ⟨v, hchildType⟩ hchildSpineX hchildSpineY
              houtK hAK hy
        rw [dif_pos hg]
        refine (LRS.DefEq.lam_forallE
          (M := xs.foldr (fun a f => f.app a) (.const c ls))
          (N := ys.foldr (fun a f => f.app a) (.const c ls))
          (A := A) (f := g) (hf := hg) (a₁ := a₁) (a₂ := a₂)
          (LR Γ₀)).2 ?_
        refine ⟨B₁, F₁, u, v, rootRed, hB.leftType,
          hValB.left.toTyDefEq, hF.leftType, hPi, ?_⟩
        exact LR.constLamDefEq (hf := hg) (nArgs := q + 1) htm hlam₀
          (fun {_ _ _ _ _} hp hxy hv hmem hx hy => ⟨
            evalChild (Nat.max_eq_right (Nat.le_succ q))
              hleaf.aligned.left hterm.hasType.1
              hspineX hspineX hp hxy hv hmem hx hy,
            evalChild (Nat.max_eq_right (Nat.le_succ q))
              hleaf.aligned.right hterm.hasType.2
              hspineY hspineY hp hxy hv hmem hx hy,
            evalChild (Nat.max_eq_right (Nat.le_succ q))
              hleaf.aligned hterm hspineX hspineY
              hp hxy hv hmem hx hy⟩)
      · rw [dif_neg hg]
        exact (LR Γ₀).bot hout.isType
    | ctor => exact (TShape.ctor_not_le_lam' hlam').elim
    | indTy => exact (TShape.indTy_not_le_lam' hlam').elim
  | @ctor semOut semArgs hcl hctor =>
    have hlen : semArgs.length = rargs'.length := by
      simpa using Lean4Lean.List.Forall₂.length_eq hargle
    have hcl' : Params.classify c = some (.ctor rargs'.length) := hlen ▸ hcl
    let K := max n n'
    have hnK : n ≤ K := Nat.le_max_left ..
    have hn'K : n' ≤ K := Nat.le_max_right ..
    have hargsK := WShape.forall₂_liftT hnK hn'K hargle
    have hctorT : (WShape.ctor' c semArgs.reverse).T ≤
        (WShape.ctor' c rargs'.reverse).T := by
      apply (TShape.LE.def (Nat.succ_le_succ hnK)
        (Nat.succ_le_succ hn'K)).2
      rw [WShape.lift_ctor' hnK, WShape.lift_ctor' hn'K,
        List.map_reverse, List.map_reverse]
      exact WShape.ctor'_le_ctor' (List.Forall₂.reverse.2 hargsK)
    have hctor' := houtle.trans (hctor.trans hctorT)
    cases hout.unfold with
    | bot hm => exact (LR Γ₀).bot hm
    | sort => exact (TShape.sort_not_le_ctor' hctor').elim
    | forallE => exact (TShape.forallE_not_le_ctor' hctor').elim
    | lam htm =>
      unfold WShape.lam' at hctor' ⊢
      split at hctor' <;> rename_i hnonzero
      · exact (TShape.lam_not_le_ctor' hctor').elim
      · simpa [hnonzero] using (LR Γ₀).bot hout.isType
    | @ctor q c' fields hwf =>
      have hIndHead : LRS.IndTyHead Γ₀ A := by
        simpa only [LR_succ, LRS.TyDefEq.indTy_m] using
          hADirect.toTyDefEq.1
      rw [LR_succ]
      change LRS.IndDefEq Γ₀ (LR Γ₀)
        (xs.foldr (fun a f => f.app a) (.const c ls))
        (ys.foldr (fun a f => f.app a) (.const c ls)) A
        (WShape.ctor c' fields hwf)
      exact ⟨hIndHead, LRS.CtorDefEq.of_exact_ctor_spines
        hleaf.args hleaf.aligned hleaf.aligned.symm hcl' rfl hhead hhead
        hspineX hspineY hctor'⟩
    | indTy => exact (TShape.indTy_not_le_ctor' hctor').elim
  | @indTy semOut semArgs hcl hind =>
    have hlen : semArgs.length = rargs'.length := by
      simpa using Lean4Lean.List.Forall₂.length_eq hargle
    have hcl' : Params.classify c = some (.indTy rargs'.length) := hlen ▸ hcl
    have hind' := houtle.trans hind
    cases hout.unfold with
    | bot hm => exact (LR Γ₀).bot hm
    | sort => exact (TShape.sort_not_le_indTy hind').elim
    | forallE => exact (TShape.forallE_not_le_indTy hind').elim
    | lam htm =>
      unfold WShape.lam' at hind' ⊢
      split at hind' <;> rename_i hnonzero
      · exact (TShape.lam_not_le_indTy hind').elim
      · simpa [hnonzero] using (LR Γ₀).bot hout.isType
    | ctor => exact (TShape.ctor_not_le_indTy hind').elim
    | indTy =>
      rw [LR_succ]
      change LRS.IndTyHead Γ₀
          (xs.foldr (fun a f => f.app a) (.const c ls)) ∧
        LRS.IndTyHead Γ₀
          (ys.foldr (fun a f => f.app a) (.const c ls))
      exact ⟨⟨c, ls, xs, hleaf.args.lengths.1.symm ▸ hcl', .rfl⟩,
        ⟨c, ls, ys, hleaf.args.lengths.2.symm ▸ hcl', .rfl⟩⟩

/--
info: 'Lean4Lean.SExpr.LR.constDefEqDirect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.constDefEqDirect
/-- Evaluate a semantic constant in the guarded relation.  The established
result is supplied explicitly for the additive first projection; every
informative function layer is rebuilt from typed roots, a retained direct Pi
action, and recursive guarded children.  Thus this evaluator itself has no
Pi-inversion or subject-reduction premise. -/
theorem LRD.constDefEq
    {c : Name} {ls : List SLevel} {R : TShape → SExpr → Prop}
    {ρ : Valuation}
    (hRmono : ∀ {m m' M}, m ≤ m' → R m' M → R m M)
    {n : Nat} {rargs : List (WShape n)} {mout : TShape}
    (hC : LE_Interp.Const c ls R rargs mout)
    {n' : Nat} {rargs' : List (WShape n')}
    {xs ys : List SExpr} {CHead A : SExpr}
    {out outTy : WShape n'}
    (evalPat : LRD.RegisteredPatternLeafDefEqAt
      Γ₀ ρ CHead n' c ls R)
    (hargle : List.Forall₂ (fun x y => x.T ≤ y.T) rargs rargs')
    (hleaf : LR.DirectPatternLeafSpine Γ₀ (LRD Γ₀)
      CHead xs ys rargs' A out outTy)
    (htrace : LR.DirectRegisteredTypeTrace Γ₀ ρ CHead
      xs ys rargs' A outTy)
    (hterm : IsDefEq Γ₀
      (xs.foldr (fun a f => f.app a) (.const c ls))
      (ys.foldr (fun a f => f.app a) (.const c ls)) A)
    (hAType : ∃ u, IsDefEq Γ₀ A A (.sort u))
    (hhead : IsDefEq Γ₀ (.const c ls) (.const c ls) CHead)
    (hspineX : SExpr.SpineWF Γ₀ CHead xs.reverse A)
    (hspineY : SExpr.SpineWF Γ₀ CHead ys.reverse A)
    (hout : out.HasType outTy)
    (hlegacy : (LR Γ₀).DefEq
      (xs.foldr (fun a f => f.app a) (.const c ls))
      (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy)
    (hADirect : (LRD Γ₀).TyDefEq A A outTy)
    (houtle : out.T ≤ mout) :
    (LRD Γ₀).DefEq
      (xs.foldr (fun a f => f.app a) (.const c ls))
      (ys.foldr (fun a f => f.app a) (.const c ls)) A out outTy := by
  induction hC generalizing rargs' xs ys A out outTy with
  | bot =>
    have hb : out.T ≤ TShape.bot := houtle.trans TShape.bot_eqv.1
    have heq : out = .bot := TShape.le_bot.1 hb
    subst out
    exact LRD.DefEq.bot hout.isType
  | pat hpat hmatch hrhs =>
    obtain ⟨mcap', hmatch', hcap⟩ :=
      hmatch.mono_lT (Params.pat_wf hpat) hargle
    have hrhs' : LE_Interp.RHS ls mcap' R out.T _ :=
      (hrhs.mono_l hcap).mono (R' := R) houtle
        (fun le hr => hRmono le hr)
    exact evalPat hpat hmatch' hrhs' hleaf htrace hterm hAType hhead
      hspineX hspineY hout hlegacy hADirect
  | @lam f rargs mout hrec hlam ih =>
    have hlam₀ := houtle.trans hlam
    have hlam' := hlam₀
    cases hout.unfold with
    | bot hm => exact LRD.DefEq.bot hm
    | sort => exact (TShape.sort_not_le_lam' hlam').elim
    | forallE => exact (TShape.forallE_not_le_lam' hlam').elim
    | @lam q g a₁ a₂ htm =>
      unfold WShape.lam' at hlam' ⊢
      split at hlam' <;> rename_i hg
      · rw [dif_pos hg]
        rw [LRD_succ] at hADirect
        obtain ⟨B₁, F₁, B₂, F₂, u, v, rootTyped, _rootA₂,
            hB, hF, hValB, hDirectPi⟩ :=
          hADirect.2.2 a₁ a₂ rfl
        have rootReduction := rootTyped.toWHRedS
        obtain ⟨uRoot, rootPath, rootRaw⟩ := rootTyped
        obtain ⟨BL, FL, BR, FR, uL, vL, rootLegacy, _rootLegacyR,
            hBL, hFL, hValBL, hPiLegacy⟩ := hADirect.1
        have hrootEq : SExpr.forallE BL FL = .forallE B₁ F₁ :=
          rootLegacy.determ .forallE rootReduction .forallE
        cases hrootEq
        have hPiLegacyLeft : LRS.PiDefEq (LR Γ₀)
            B₁ F₁ F₁ a₁ a₂ := LRS.PiDefEq.left hPiLegacy
        have hValBLeft : (LRD Γ₀).TyDefEq B₁ B₁ a₁ :=
          LRD.TyDefEq.left hValB
        have hDirectPiLeft : LR.DirectPiDefEq (LRD Γ₀)
            B₁ F₁ F₁ a₁ a₂ := by
          constructor
          · intro x y p hp hxy hv
            have h := hDirectPi.1 hp hxy hv
            exact ⟨h.leftTy, h.leftTy, h.leftDefEq, h.leftDefEq⟩
          · intro x p hp hxy hv
            exact (hDirectPi.1 hp hxy hv).leftTy
        have hlegacy' : (LR Γ₀).DefEq
            (xs.foldr (fun a f => f.app a) (.const c ls))
            (ys.foldr (fun a f => f.app a) (.const c ls)) A
            (.lam g hg) (.forallE a₁ a₂) := by
          simpa only [WShape.lam', dif_pos hg] using hlegacy
        have legacyRect : LogRel.DefEqRect (LR Γ₀)
            (xs.foldr (fun a f => f.app a) (.const c ls))
            (xs.foldr (fun a f => f.app a) (.const c ls))
            (ys.foldr (fun a f => f.app a) (.const c ls))
            (ys.foldr (fun a f => f.app a) (.const c ls)) A
            (.lam g hg) (.forallE a₁ a₂) :=
          ⟨(LR Γ₀).left hlegacy',
            (LR Γ₀).left ((LR Γ₀).symm hlegacy'), hlegacy'⟩
        have legacyChildren : ∀ {K : Nat}, K = q + 1 → ∀
            {x y : SExpr} {p : WShape K},
            p.HasType (a₁.lift K) →
            IsDefEq Γ₀ x y B₁ →
            (LRD Γ₀).DefEq x y B₁ p (a₁.lift K) →
            LogRel.DefEqRect (LR Γ₀)
              ((xs.foldr (fun a (acc : SExpr) => acc.app a)
                (SExpr.const c ls)).app x)
              ((xs.foldr (fun a (acc : SExpr) => acc.app a)
                (SExpr.const c ls)).app y)
              ((ys.foldr (fun a (acc : SExpr) => acc.app a)
                (SExpr.const c ls)).app x)
              ((ys.foldr (fun a (acc : SExpr) => acc.app a)
                (SExpr.const c ls)).app y)
              (F₁.inst x) ((g.lift K).app p)
                ((a₂.lift K).app p) := by
          intro K hK
          subst K
          intro x y p hp hxy hv
          have leq : q ≤ q + 1 := Nat.le_succ q
          have hgK : (g.lift (q + 1)).NonZero :=
            (WShapeFun.NonZero.lift_iff leq).2 hg
          have htmShape : (WShape.lam g hg).HasType
              (.forallE a₁ a₂) := by
            simpa only [WShape.lam', dif_pos hg] using
              WShape.HasType.lam htm
          have liftLegacy {P Q : SExpr}
              (H : (LR Γ₀).DefEq P Q A
                (.lam g hg) (.forallE a₁ a₂)) :
              (LR Γ₀).DefEq P Q A
                (.lam (g.lift (q + 1)) hgK)
                (.forallE (a₁.lift (q + 1))
                  (a₂.lift (q + 1))) := by
            simpa only [WShape.lift_lam leq,
              WShape.lift_forallE leq] using
              (LR.DefEq.lift (Nat.succ_le_succ leq)
                htmShape).2 H
          have legacyRectK : LogRel.DefEqRect (LR Γ₀)
              (xs.foldr (fun a f => f.app a) (.const c ls))
              (xs.foldr (fun a f => f.app a) (.const c ls))
              (ys.foldr (fun a f => f.app a) (.const c ls))
              (ys.foldr (fun a f => f.app a) (.const c ls)) A
              (.lam (g.lift (q + 1)) hgK)
              (.forallE (a₁.lift (q + 1))
                (a₂.lift (q + 1))) :=
            ⟨liftLegacy legacyRect.left, liftLegacy legacyRect.right,
              liftLegacy legacyRect.cross⟩
          obtain ⟨B, F, u', v', rootLegacyK, hBTy, hBRel,
              hFTy, hPiK, applyLegacy⟩ :=
            LRS.DefEqRect.app_exposed (x := x) (y := y)
              legacyRectK hp
          have hrootEq : SExpr.forallE B F = .forallE B₁ F₁ :=
            rootLegacyK.determ .forallE rootReduction .forallE
          cases hrootEq
          exact applyLegacy hxy (LRD.defLegacy hv)
        have evalChild : ∀ {K : Nat}, K = q + 1 → ∀
            {x y : SExpr} {p : WShape K} {x₀ y₀ : WShape n}
            {zs zs' : List SExpr},
            LRS.CtorSpineDefEq (LR Γ₀) CHead zs zs' rargs' A →
            LR.DirectCtorArgsDefEq (LRD Γ₀) zs zs' rargs' →
            LR.DirectRegisteredTypeTrace Γ₀ ρ CHead
              zs zs' rargs' A (.forallE a₁ a₂) →
            IsDefEq Γ₀
              (zs.foldr (fun a f => f.app a) (.const c ls))
              (zs'.foldr (fun a f => f.app a) (.const c ls)) A →
            SExpr.SpineWF Γ₀ CHead zs.reverse A →
            SExpr.SpineWF Γ₀ CHead zs'.reverse A →
            p.HasType (a₁.lift K) →
            IsDefEq Γ₀ x y B₁ →
            (LRD Γ₀).DefEq x y B₁ p (a₁.lift K) →
            (LR Γ₀).DefEq
              ((zs.foldr (fun a (acc : SExpr) => acc.app a)
                (SExpr.const c ls)).app x)
              ((zs'.foldr (fun a (acc : SExpr) => acc.app a)
                (SExpr.const c ls)).app y)
              (F₁.inst x) ((g.lift K).app p)
                ((a₂.lift K).app p) →
            (x₀, y₀) ∈ f → x₀.T ≤ p.T →
            ((g.lift K).app p).T ≤ y₀.T →
            (LRD Γ₀).DefEq
              ((zs.foldr (fun a (acc : SExpr) => acc.app a)
                (SExpr.const c ls)).app x)
              ((zs'.foldr (fun a (acc : SExpr) => acc.app a)
                (SExpr.const c ls)).app y)
              (F₁.inst x) ((g.lift K).app p)
                ((a₂.lift K).app p) := by
          intro K hK
          subst K
          intro x y p x₀ y₀ zs zs' htailAligned htailDirect htailTrace
            htailTerm htailSpineX htailSpineY hp hxy hv legacyEdge
            hmem hx hy
          have leq : q ≤ q + 1 := Nat.le_succ q
          have htmK : WShape.HasTypeLam (g.lift (q + 1))
              (a₁.lift (q + 1)) (a₂.lift (q + 1)) :=
            (WShape.HasTypeLam.lift leq).2 htm
          have hchildLe : List.Forall₂ (fun x y => x.T ≤ y.T)
              (x₀ :: rargs) (p :: rargs') := .cons hx hargle
          have hBKDirect : (LRD Γ₀).TyDefEq B₁ B₁
              (a₁.lift (q + 1)) :=
            (LRD.TyDefEq.lift leq
              (WShape.HasTypePi.iff.1 htm.1).1.isType).2 hValBLeft
          have hPiLegacyK : LRS.PiDefEq (LR Γ₀)
              B₁ F₁ F₁ (a₁.lift (q + 1))
                (a₂.lift (q + 1)) :=
            (LRS.PiDefEq.lift leq htm.1).2 hPiLegacyLeft
          have hPiDirectK : LR.DirectPiDefEq (LRD Γ₀)
              B₁ F₁ F₁ (a₁.lift (q + 1))
                (a₂.lift (q + 1)) :=
            (LR.DirectPiDefEq.lift leq htm.1).2 hDirectPiLeft
          have houtK : ((g.lift (q + 1)).app p).HasType
              ((a₂.lift (q + 1)).app p) :=
            (WShape.HasTypeLam.iff.1 htmK).2.2 p hp
          have hAK : (LRD Γ₀).TyDefEq
              (F₁.inst x) (F₁.inst x)
              ((a₂.lift (q + 1)).app p) :=
            LRD.TyDefEq.left
              (hPiDirectK.1 hp hxy hv).leftTy
          have hchildTerm : IsDefEq Γ₀
              ((zs.foldr (fun a (f : SExpr) => f.app a)
                (SExpr.const c ls)).app x)
              ((zs'.foldr (fun a (f : SExpr) => f.app a)
                (SExpr.const c ls)).app y) (F₁.inst x) :=
            .appDF (rootPath.defeqDF htailTerm) hxy
          obtain ⟨_, hCodomain⟩ :=
            (hPiLegacyK.1 hp hxy (LRD.defLegacy hv)).leftDefEq
          have hchildType : IsDefEq Γ₀ (F₁.inst x)
              (F₁.inst x) (.sort v) :=
            (IsDefEq.beta hF.leftType hxy.hasType.1).hasType.2
          have hchildSpineX : SExpr.SpineWF Γ₀ CHead
              (x :: zs).reverse (F₁.inst x) := by
            simpa only [List.reverse_cons] using
              htailSpineX.snoc_path rootPath hxy.hasType.1
          have hchildSpineY : SExpr.SpineWF Γ₀ CHead
              (y :: zs').reverse (F₁.inst x) := by
            have hspine :=
              htailSpineY.snoc_path rootPath hxy.hasType.2
            simpa only [List.reverse_cons] using
              SExpr.SpineWF.ret hspine hCodomain.symm
          obtain ⟨hchildLeaf⟩ :=
            LR.DirectPatternLeafSpine.of_cons_path
              htailSpineX htailSpineY htailAligned htailDirect
              rootPath hp htmK.1
              (LRD.tyLegacy hBKDirect) hBKDirect hxy
              (LRD.defLegacy hv) hv hCodomain.symm
              hPiLegacyK hPiDirectK
          have hchildTrace : LR.DirectRegisteredTypeTrace Γ₀ ρ CHead
              (x :: zs) (y :: zs') (p :: rargs') (F₁.inst x)
              ((a₂.lift (q + 1)).app p) :=
            .cons leq htailTrace rootPath hp
              (LRD.tyLegacy hBKDirect) hBKDirect hxy
              (LRD.defLegacy hv) hv hchildType hCodomain.symm hAK
          simpa only [List.foldr_cons] using
            ih x₀ y₀ hmem hchildLe hchildLeaf hchildTrace hchildTerm
              ⟨v, hchildType⟩ hchildSpineX hchildSpineY
              houtK legacyEdge hAK hy
        have action : LR.DirectLamDefEq (LRD Γ₀)
            (xs.foldr (fun a f => f.app a) (.const c ls))
            (ys.foldr (fun a f => f.app a) (.const c ls))
            B₁ F₁ g a₁ a₂ :=
          LRD.constLamDefEq (hf := hg) (nArgs := q + 1)
            htm hlam₀
            (fun hp hxy hv hmem hx hy => by
              have children := legacyChildren
                (Nat.max_eq_right (Nat.le_succ q)) hp hxy hv
              exact ⟨
                evalChild (Nat.max_eq_right (Nat.le_succ q))
                  hleaf.legacy.aligned.left hleaf.directArgs.left
                  htrace.left
                  hterm.hasType.1
                  hspineX hspineX hp hxy hv children.left hmem hx hy,
                evalChild (Nat.max_eq_right (Nat.le_succ q))
                  hleaf.legacy.aligned.right hleaf.directArgs.right
                  htrace.right
                  hterm.hasType.2
                  hspineY hspineY hp hxy hv children.right hmem hx hy,
                evalChild (Nat.max_eq_right (Nat.le_succ q))
                  hleaf.legacy.aligned hleaf.directArgs htrace hterm
                  hspineX hspineY
                  hp hxy hv children.cross hmem hx hy⟩)
        exact LRD.DefEq.lam hlegacy' <|
          ⟨B₁, F₁, u, v, ⟨uRoot, rootPath, rootRaw⟩,
            hB.leftType, hValBLeft,
            hF.leftType, hDirectPiLeft, action⟩
      · rw [dif_neg hg]
        exact LRD.DefEq.bot hout.isType
    | ctor => exact (TShape.ctor_not_le_lam' hlam').elim
    | indTy => exact (TShape.indTy_not_le_lam' hlam').elim
  | @ctor semOut semArgs hcl hctor =>
    have hlen : semArgs.length = rargs'.length := by
      simpa using Lean4Lean.List.Forall₂.length_eq hargle
    let K := max n n'
    have hnK : n ≤ K := Nat.le_max_left ..
    have hn'K : n' ≤ K := Nat.le_max_right ..
    have hargsK := WShape.forall₂_liftT hnK hn'K hargle
    have hctorT : (WShape.ctor' c semArgs.reverse).T ≤
        (WShape.ctor' c rargs'.reverse).T := by
      apply (TShape.LE.def (Nat.succ_le_succ hnK)
        (Nat.succ_le_succ hn'K)).2
      rw [WShape.lift_ctor' hnK, WShape.lift_ctor' hn'K,
        List.map_reverse, List.map_reverse]
      exact WShape.ctor'_le_ctor' (List.Forall₂.reverse.2 hargsK)
    have hctor' := houtle.trans (hctor.trans hctorT)
    cases hout.unfold with
    | bot hm => exact LRD.DefEq.bot hm
    | sort => exact (TShape.sort_not_le_ctor' hctor').elim
    | forallE => exact (TShape.forallE_not_le_ctor' hctor').elim
    | lam htm =>
      unfold WShape.lam' at hctor' ⊢
      split at hctor' <;> rename_i hnonzero
      · exact (TShape.lam_not_le_ctor' hctor').elim
      · rw [dif_neg hnonzero]
        exact LRD.DefEq.bot hout.isType
    | ctor => exact LRD.DefEq.of_legacy_indTy hlegacy
    | indTy => exact (TShape.indTy_not_le_ctor' hctor').elim
  | @indTy semOut semArgs hcl hind =>
    have hind' := houtle.trans hind
    cases hout.unfold with
    | bot hm => exact LRD.DefEq.bot hm
    | sort => exact (TShape.sort_not_le_indTy hind').elim
    | forallE => exact (TShape.forallE_not_le_indTy hind').elim
    | lam htm =>
      unfold WShape.lam' at hind' ⊢
      split at hind' <;> rename_i hnonzero
      · exact (TShape.lam_not_le_indTy hind').elim
      · rw [dif_neg hnonzero]
        exact LRD.DefEq.bot hout.isType
    | ctor => exact (TShape.ctor_not_le_indTy hind').elim
    | indTy => exact LRD.DefEq.of_legacy_indTy_type hlegacy

/--
info: 'Lean4Lean.SExpr.LRD.constDefEq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.constDefEq

/-- Package the root lambda layer of a semantic constant around the guarded
constant evaluator.  The ordinary root edge supplies the additive projection
and its synchronized child rectangle; the direct type observation supplies
the typed root and guarded Pi action used to seed each recursive paired
spine. -/
theorem LRD.constDefEqRootLam
    {c : Name} {ls : List SLevel} {R : TShape → SExpr → Prop}
    {ρ : Valuation}
    {n nsem : Nat} {f : WShapeFun n} {hf : f.NonZero}
    {a₁ : WShape n} {a₂ : WShapeFun n} {fsem : WShapeFun nsem}
    {A : SExpr}
    (htm : WShape.HasTypeLam f a₁ a₂)
    (hlam : (WShape.lam' f).T ≤ (WShape.lam' fsem).T)
    (hrec : ∀ x y : WShape nsem, (x, y) ∈ fsem →
      LE_Interp.Const c ls R [x] y.T)
    (hRmono : ∀ {m m' : TShape} {M : SExpr},
      m ≤ m' → R m' M → R m M)
    (evalPat : ∀ k,
      LRD.RegisteredPatternLeafDefEqAt Γ₀ ρ A k c ls R)
    (hhead : IsDefEq Γ₀ (.const c ls) (.const c ls) A)
    (hlegacy : (LR Γ₀).DefEq (.const c ls) (.const c ls) A
      (.lam f hf) (.forallE a₁ a₂))
    (hADirect : (LRD Γ₀).TyDefEq A A (.forallE a₁ a₂))
    (hRegistered : LE_Interp.Witness ρ
      (WShape.forallE a₁ a₂).T A) :
    (LRD Γ₀).DefEq (.const c ls) (.const c ls) A
      (.lam f hf) (.forallE a₁ a₂) := by
  rw [LRD_succ] at hADirect
  obtain ⟨B₁, F₁, B₂, F₂, u, v, rootTyped, _rootA₂,
      hB, hF, hValB, hDirectPi⟩ :=
    hADirect.2.2 a₁ a₂ rfl
  have rootReduction := rootTyped.toWHRedS
  obtain ⟨uRoot, rootPath, rootRaw⟩ := rootTyped
  obtain ⟨BL, FL, BR, FR, uL, vL, rootLegacy, _rootLegacyR,
      hBL, hFL, hValBL, hPiLegacy⟩ := hADirect.1
  have hrootEq : SExpr.forallE BL FL = .forallE B₁ F₁ :=
    rootLegacy.determ .forallE rootReduction .forallE
  cases hrootEq
  have hPiLegacyLeft : LRS.PiDefEq (LR Γ₀)
      B₁ F₁ F₁ a₁ a₂ := LRS.PiDefEq.left hPiLegacy
  have hValBLeft : (LRD Γ₀).TyDefEq B₁ B₁ a₁ :=
    LRD.TyDefEq.left hValB
  have hDirectPiLeft : LR.DirectPiDefEq (LRD Γ₀)
      B₁ F₁ F₁ a₁ a₂ := by
    constructor
    · intro x y p hp hxy hv
      have h := hDirectPi.1 hp hxy hv
      exact ⟨h.leftTy, h.leftTy, h.leftDefEq, h.leftDefEq⟩
    · intro x p hp hxy hv
      exact (hDirectPi.1 hp hxy hv).leftTy
  have legacyRect : LogRel.DefEqRect (LR Γ₀)
      (.const c ls) (.const c ls) (.const c ls) (.const c ls) A
      (.lam f hf) (.forallE a₁ a₂) :=
    LogRel.DefEqRect.diagonal hlegacy
  let registeredRoot : LR.DirectRegisteredTypeRoot Γ₀ ρ A := {
    level := n
    domain := a₁
    codomain := a₂
    witness := hRegistered
    related := hADirect }
  let registeredTrace : LR.DirectRegisteredTypeTrace Γ₀ ρ A
      ([] : List SExpr) [] [] A (.forallE a₁ a₂) :=
    .nil registeredRoot
  have eval : ∀ {K : Nat}, K = n → ∀
      {x y : SExpr} {p : WShape K} {x₀ y₀ : WShape nsem},
      p.HasType (a₁.lift K) →
      IsDefEq Γ₀ x y B₁ →
      (LRD Γ₀).DefEq x y B₁ p (a₁.lift K) →
      (x₀, y₀) ∈ fsem → x₀.T ≤ p.T →
      ((f.lift K).app p).T ≤ y₀.T →
      LR.DirectDefEqRect (LRD Γ₀)
        ((SExpr.const c ls).app x) ((SExpr.const c ls).app y)
        ((SExpr.const c ls).app x) ((SExpr.const c ls).app y)
        (F₁.inst x) ((f.lift K).app p) ((a₂.lift K).app p) := by
    intro K hK
    subst K
    intro x y p x₀ y₀ hp hxy hv hmem hx hy
    simp only [WShape.lift_self, WShapeFun.lift_self] at hp hv hy ⊢
    have htmK : WShape.HasTypeLam f a₁ a₂ := htm
    have hBKDirect : (LRD Γ₀).TyDefEq B₁ B₁ a₁ := hValBLeft
    have hPiLegacyK : LRS.PiDefEq (LR Γ₀)
        B₁ F₁ F₁ a₁ a₂ := hPiLegacyLeft
    have hPiDirectK : LR.DirectPiDefEq (LRD Γ₀)
        B₁ F₁ F₁ a₁ a₂ := hDirectPiLeft
    have hout : (f.app p).HasType (a₂.app p) :=
      (WShape.HasTypeLam.iff.1 htmK).2.2 p hp
    have hAK : (LRD Γ₀).TyDefEq (F₁.inst x) (F₁.inst x)
        (a₂.app p) :=
      LRD.TyDefEq.left (hPiDirectK.1 hp hxy hv).leftTy
    have hAppTerm : IsDefEq Γ₀ ((SExpr.const c ls).app x)
        ((SExpr.const c ls).app y) (F₁.inst x) :=
      .appDF (rootPath.defeqDF hhead) hxy
    obtain ⟨_, hCodomain⟩ :=
      (hPiLegacyK.1 hp hxy (LRD.defLegacy hv)).leftDefEq
    have hAppType : IsDefEq Γ₀ (F₁.inst x) (F₁.inst x) (.sort v) :=
      (IsDefEq.beta hF.leftType hxy.hasType.1).hasType.2
    have hAppSpineX : SExpr.SpineWF Γ₀ A [x] (F₁.inst x) := by
      simpa only [List.nil_append] using
        (SExpr.SpineWF.nil (Γ := Γ₀) (A := A)).snoc_path
          rootPath hxy.hasType.1
    have hAppSpineY : SExpr.SpineWF Γ₀ A [y] (F₁.inst x) := by
      have hspine :=
        (SExpr.SpineWF.nil (Γ := Γ₀) (A := A)).snoc_path
          rootPath hxy.hasType.2
      exact SExpr.SpineWF.ret hspine hCodomain.symm
    obtain ⟨hAppLeaf⟩ := LR.DirectPatternLeafSpine.of_cons_path
      (g := f) (f := a₂)
      (SExpr.SpineWF.nil (Γ := Γ₀) (A := A))
      (SExpr.SpineWF.nil (Γ := Γ₀) (A := A))
      (LRS.CtorSpineDefEq.nil (IH := LR Γ₀) (Head := A))
      (LR.DirectCtorArgsDefEq.nil (IH := LRD Γ₀))
      rootPath hp htmK.1 (LRD.tyLegacy hBKDirect) hBKDirect
      hxy (LRD.defLegacy hv) hv hCodomain.symm
      hPiLegacyK hPiDirectK
    have hAppTrace : LR.DirectRegisteredTypeTrace Γ₀ ρ A
        [x] [y] [p] (F₁.inst x) (a₂.app p) := by
      exact LR.DirectRegisteredTypeTrace.consSelf
        registeredTrace rootPath hp (LRD.tyLegacy hBKDirect)
        hBKDirect hxy (LRD.defLegacy hv) hv hAppType
        hCodomain.symm hAK
    obtain ⟨B, F, u', v', rootLegacyK, hBTy, hBRel,
        hFTy, hPiK, applyLegacy⟩ :=
      LRS.DefEqRect.app_exposed (x := x) (y := y) legacyRect hp
    have hrootEq : SExpr.forallE B F = .forallE B₁ F₁ :=
      rootLegacyK.determ .forallE rootReduction .forallE
    cases hrootEq
    have legacyChildren := applyLegacy hxy (LRD.defLegacy hv)
    have run (legacyEdge : (LR Γ₀).DefEq
        ((SExpr.const c ls).app x) ((SExpr.const c ls).app y)
        (F₁.inst x) (f.app p) (a₂.app p)) :
        (LRD Γ₀).DefEq
          ((SExpr.const c ls).app x) ((SExpr.const c ls).app y)
          (F₁.inst x) (f.app p) (a₂.app p) := by
      simpa only [List.foldr_cons, List.foldr_nil] using
        LRD.constDefEq (Γ₀ := Γ₀) (c := c) (ls := ls) (R := R)
          hRmono (hrec x₀ y₀ hmem) (evalPat n)
          (.cons hx .nil) hAppLeaf hAppTrace hAppTerm
          ⟨v, hAppType⟩ hhead
          hAppSpineX hAppSpineY hout legacyEdge hAK hy
    exact ⟨run legacyChildren.left, run legacyChildren.right,
      run legacyChildren.cross⟩
  exact LRD.DefEq.lam hlegacy <|
    ⟨B₁, F₁, u, v, ⟨uRoot, rootPath, rootRaw⟩,
      hB.leftType, hValBLeft, hF.leftType, hDirectPiLeft,
      LRD.constLamDefEq (hf := hf) (nArgs := 0) htm hlam
        (fun hp hxy hv hmem hx hy =>
          eval (Nat.max_eq_left (Nat.zero_le n))
            hp hxy hv hmem hx hy)⟩

/--
info: 'Lean4Lean.SExpr.LRD.constDefEqRootLam' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.constDefEqRootLam

/-- Package the root lambda layer of a semantic constant around
`LR.constDefEqDirect`.

This is the syntax-directed caller boundary used by the direct fundamental
constant case.  Its registered type arrives as a recursive direct
observation.  The selected root path authorizes the initial application
spine, and each recursive codomain observation is passed back to the direct
evaluator.  Consequently neither this caller nor the evaluator has a
`PiPathInv` or context-WF premise. -/
theorem LR.constDefEqDirectRootLam
    {c : Name} {ls : List SLevel} {R : TShape → SExpr → Prop}
    {n nsem : Nat} {f : WShapeFun n} {hf : f.NonZero}
    {a₁ : WShape n} {a₂ : WShapeFun n} {fsem : WShapeFun nsem}
    {A : SExpr}
    (htm : WShape.HasTypeLam f a₁ a₂)
    (hlam : (WShape.lam' f).T ≤ (WShape.lam' fsem).T)
    (hrec : ∀ x y : WShape nsem, (x, y) ∈ fsem →
      LE_Interp.Const c ls R [x] y.T)
    (hRmono : ∀ {m m' : TShape} {M : SExpr},
      m ≤ m' → R m' M → R m M)
    (evalPat : ∀ k, LR.PatternLeafDefEqAt Γ₀ k c ls R)
    (hhead : IsDefEq Γ₀ (.const c ls) (.const c ls) A)
    (hADirect : LR.DirectTyDefEq Γ₀ A A (.forallE a₁ a₂)) :
    (LR Γ₀).DefEq (.const c ls) (.const c ls) A
      (.lam f hf) (.forallE a₁ a₂) := by
  rw [LR_succ]
  obtain ⟨B₁, F₁, B₂, F₂, u₁, v, rootA, _rootA₂,
    hB, hF, hValB, hPi₀, hDirectPi⟩ :=
    hADirect.toValTyPi2DirectRec
  obtain ⟨_, rootPath, rootRed⟩ := rootA
  have hPi := LRS.PiDefEq.left hPi₀
  refine (LRS.DefEq.lam_forallE
    (M := .const c ls) (N := .const c ls) (A := A)
    (f := f) (hf := hf) (a₁ := a₁) (a₂ := a₂) (LR Γ₀)).2 ?_
  refine ⟨B₁, F₁, u₁, v, rootRed, hB.leftType,
    hValB.left.toTyDefEq, hF.leftType, hPi, ?_⟩
  have eval : ∀ {K : Nat}, K = n → ∀
      {x y : SExpr} {p : WShape K} {x₀ y₀ : WShape nsem},
      p.HasType (a₁.lift K) →
      IsDefEq Γ₀ x y B₁ →
      (LR Γ₀).DefEq x y B₁ p (a₁.lift K) →
      (x₀, y₀) ∈ fsem → x₀.T ≤ p.T →
      ((f.lift K).app p).T ≤ y₀.T →
      (LR Γ₀).DefEq ((SExpr.const c ls).app x)
        ((SExpr.const c ls).app y)
        (F₁.inst x) ((f.lift K).app p) ((a₂.lift K).app p) := by
    intro K hK
    subst K
    intro x y p x₀ y₀ hp hxy hv hmem hx hy
    have hn : n ≤ n := Nat.le_refl n
    have hBK : (LR Γ₀).TyDefEq B₁ B₁ (a₁.lift n) :=
      (LR.TyDefEq.lift hn
        (WShape.HasTypePi.iff.1 htm.1).1.isType).2
        hValB.left.toTyDefEq
    have htmK : WShape.HasTypeLam (f.lift n)
        (a₁.lift n) (a₂.lift n) :=
      (WShape.HasTypeLam.lift hn).2 htm
    have hout : ((f.lift n).app p).HasType ((a₂.lift n).app p) :=
      (WShape.HasTypeLam.iff.1 htmK).2.2 p hp
    have hPiK : LRS.PiDefEq (LR Γ₀) B₁ F₁ F₁
        (a₁.lift n) (a₂.lift n) :=
      (LRS.PiDefEq.lift hn htm.1).2 hPi
    have hAK : LR.DirectTyDefEq Γ₀ (F₁.inst x) (F₁.inst x)
        ((a₂.lift n).app p) :=
      (hDirectPi hn hp hxy.hasType.1 ((LR Γ₀).left hv)).left
    have hConstPi : IsDefEq Γ₀ (SExpr.const c ls) (SExpr.const c ls)
        (.forallE B₁ F₁) := rootPath.defeqDF hhead
    have hAppTerm : IsDefEq Γ₀ ((SExpr.const c ls).app x)
        ((SExpr.const c ls).app y) (F₁.inst x) :=
      .appDF hConstPi hxy
    have hAppType : IsDefEq Γ₀ (F₁.inst x) (F₁.inst x) (.sort v) :=
      (IsDefEq.beta hF.leftType hxy.hasType.1).hasType.2
    have hAppSpineX : SExpr.SpineWF Γ₀ A [x] (F₁.inst x) := by
      simpa only [List.nil_append] using
        (SExpr.SpineWF.nil (Γ := Γ₀) (A := A)).snoc_path
          rootPath hxy.hasType.1
    obtain ⟨_, hAppCodomain⟩ := (hPiK.1 hp hxy hv).leftDefEq
    have hAppSpineY : SExpr.SpineWF Γ₀ A [y] (F₁.inst x) := by
      have hspine :=
        (SExpr.SpineWF.nil (Γ := Γ₀) (A := A)).snoc_path
          rootPath hxy.hasType.2
      exact SExpr.SpineWF.ret hspine hAppCodomain.symm
    obtain ⟨hAppLeaf⟩ := LR.PatternLeafSpine.of_cons_path
      (g := f.lift n) (f := a₂.lift n)
      (SExpr.SpineWF.nil (Γ := Γ₀) (A := A))
      (SExpr.SpineWF.nil (Γ := Γ₀) (A := A))
      (LRS.CtorSpineDefEq.nil (IH := LR Γ₀) (Head := A))
      rootPath hp htmK.1 hBK hxy hv hAppCodomain.symm hPiK
    simpa only [List.foldr_cons, List.foldr_nil] using
      LR.constDefEqDirect (Γ₀ := Γ₀) (c := c) (ls := ls) (R := R)
        hRmono (hrec x₀ y₀ hmem) (evalPat n)
        (.cons hx .nil) hAppLeaf hAppTerm ⟨v, hAppType⟩ hhead
        hAppSpineX hAppSpineY hout hAK hy
  exact LR.constLamDefEq (hf := hf) (nArgs := 0) htm hlam
    (fun {_ _ _ _ _} hp hxy hv hmem hx hy =>
      LogRel.DefEqRect.diagonal
        (eval (Nat.max_eq_left (Nat.zero_le n))
          hp hxy hv hmem hx hy))

/--
info: 'Lean4Lean.SExpr.LR.constDefEqDirectRootLam' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.constDefEqDirectRootLam

/-- Adequacy is closed under dependent application once the function,
argument, and instantiated-result premises are available.  This isolates the
shape join needed by application from the induction that supplies those
three premises; in particular, proof-relevant fixed-head recursion can reuse
the same handoff without rebuilding the shape argument. -/
theorem LR.adequateApp
    {Γ : List SExpr} {A B F F' X X' : SExpr} {v : SLevel}
    {ρ : Valuation} {n : Nat} {m a : WShape n}
    (Hf : IsDefEqStrong Γ F F' (A.forallE B))
    (Ha : IsDefEqStrong Γ X X' A)
    (HBa : IsDefEqStrong Γ (B.inst X) (B.inst X') (.sort v))
    (hM : LE_Interp ρ m.T (.app F X))
    (hA : LE_Interp ρ a.T (B.inst X))
    (hmem : m.HasType a)
    (ihf : ∀ {n'} {mf af : WShape n'},
      LE_Interp ρ mf.T F → LE_Interp ρ af.T (.forallE A B) →
      mf.HasType af → Adequate Γ₀ Γ ρ F F' (.forallE A B) mf af)
    (iha : ∀ {n'} {ma aa : WShape n'},
      LE_Interp ρ ma.T X → LE_Interp ρ aa.T A → ma.HasType aa →
      Adequate Γ₀ Γ ρ X X' A ma aa)
    (ihBa : ∀ {n'} {mb av : WShape n'},
      LE_Interp ρ mb.T (B.inst X) → LE_Interp ρ av.T (.sort v) →
      mb.HasType av →
      Adequate Γ₀ Γ ρ (B.inst X) (B.inst X') (.sort v) mb av) :
    Adequate Γ₀ Γ ρ (.app F X) (.app F' X') (B.inst X) m a := by
  cases hM with
  | bot => exact .bot hmem.isType
  | @app _ nf_app f _ _ _ x hif hia le_m =>
    suffices ∀ {F F' X X' σ σ'}, SubstWF Γ₀ σ σ' Γ ρ →
        IsDefEqStrong Γ F F' (A.forallE B) →
        IsDefEqStrong Γ X X' A →
        IsDefEqStrong Γ (B.inst X) (B.inst X') (.sort v) →
        LE_Interp ρ f.T F → LE_Interp ρ x.T X →
        LE_Interp ρ a.T (B.inst X) →
        (∀ {n'} {mf af : WShape n'}, LE_Interp ρ mf.T F →
          LE_Interp ρ af.T (.forallE A B) → mf.HasType af →
          Adequate Γ₀ Γ ρ F F' (.forallE A B) mf af) →
        (∀ {n'} {ma aa : WShape n'}, LE_Interp ρ ma.T X →
          LE_Interp ρ aa.T A → ma.HasType aa →
          Adequate Γ₀ Γ ρ X X' A ma aa) →
        (∀ {n'} {mb av : WShape n'}, LE_Interp ρ mb.T (B.inst X) →
          LE_Interp ρ av.T (.sort v) → mb.HasType av →
          Adequate Γ₀ Γ ρ (B.inst X) (B.inst X') (.sort v) mb av) →
        (LR Γ₀).DefEq (.subst (.app F X) σ) (.subst (.app F' X') σ')
          (.subst (B.inst X) σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩,
        fun σ W => this W Hf Ha HBa hif hia hA ihf iha ihBa⟩
      · refine this W (Hf.trans Hf.symm) (Ha.trans Ha.symm)
          (HBa.trans HBa.symm) hif hia hA ?_ ?_ ?_
        · exact fun hf hPi hmf => (ihf hf hPi hmf).left
        · exact fun ha hA hma => (iha ha hA hma).left
        · exact fun hB hv hmb => (ihBa hB hv hmb).left
      · refine (LR _).conv ((LR _).symm_ty ?_) <| this W
          (Hf.symm.trans Hf) (Ha.symm.trans Ha) (HBa.symm.trans HBa)
          ((LE_Interp.sound Hf W.fits).1.1 hif)
          ((LE_Interp.sound Ha W.fits).1.1 hia)
          ((LE_Interp.sound HBa W.fits).1.1 hA)
          (fun hf hPi hmf => ?_) (fun ha hA hma => ?_)
          (fun hB hv hmb => ?_)
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.sound HBa W.fits).2 hA |>.out
          exact LR.toValTy le le' hmem.isType iv hmb
            ((ihBa iB iv hmb).2 W.left)
        · exact (ihf ((LE_Interp.sound Hf W.left.fits).1.2 hf)
            hPi hmf).symm.left
        · exact (iha ((LE_Interp.sound Ha W.left.fits).1.2 ha)
            hA hma).symm.left
        · exact (ihBa ((LE_Interp.sound HBa W.left.fits).1.2 hB)
            hv hmb).symm.left
    intro F F' X X' σ σ' W hF hX hBa hif hia hA ihf iha ihBa
    have ⟨_, mf, _, le_nf, le_mf, hf', hPi, hmf⟩ :=
      (LE_Interp.sound hF W.left.fits).2 hif |>.out
    have Af := ihf hf' hPi hmf
    by_cases hm0 : mf = .bot
    · simp only [hm0] at le_mf hmf
      refine (?_ : m = .bot) ▸ (LR _).bot hmem.isType
      cases show f = .bot from TShape.le_bot.1 (le_mf.trans TShape.bot_le')
      exact TShape.le_bot.1
        ((WShape.bot_app ▸ le_m).trans TShape.bot_eqv.1)
    cases hPi with
    | bot => cases hm0 hmf.bot_r
    | forallE haA hbA hd hiB le =>
      cases hmf.unfold with
      | bot => cases hm0 rfl
      | lam hg =>
        rename_i n₁ b₁' b₂' f' n₂ b₁ b₂ f
        simp at le_nf
        let k := max n (max n₁ n₂)
        have hk := Nat.max_le.1 (Nat.le_refl k)
        rw [Nat.max_le] at hk
        have le_nf_k : nf_app ≤ k := Nat.le_trans le_nf hk.2.2
        have hA' := hA.lift hk.1
        have ⟨_, le_x', hx'_a₁, hgx2⟩ :=
          WShape.HasDom.iff.1 hg.2.1 (x.lift _)
        have hia' := (hia.lift le_nf).mono le_x'.T
        have hax' := LE_Interp.forallE' haA hbA hd hiB
          |>.mono le |>.forallE_inv.2 hia'
        have hJ := TShape.Join.mk (hA.compat hax')
        have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
        have hk' := Nat.max_le.2 ⟨hk.1, hk.2.2⟩
        have hJ1' := (TShape.LE.def hk.1 hk').1 hJ1
        have hJ2' := (TShape.LE.def hk.2.2 hk').1 hJ2
        have hgx' := (WShape.HasTypeLam.iff.1 hg).2.2 _ hx'_a₁
        have hJ_t := TShape.HasType.sort_r.2 hmem.isType
          |>.join' hJ <| TShape.HasType.sort_r.2 hgx'.isType
        have hmem_k := (WShape.HasType.lift hk.1).2 hmem
        rw [subst_inst]
        have hJ_t' := TShape.HasType.sort_r.1 <|
          hJ_t.mono_l (TShape.lift_eqv hk').2 (TShape.lift_eqv hk').1
        refine (LR.DefEq.lift hk.1 hmem).1 <|
          (LR Γ₀).mono_r_2 hJ1' hmem_k hJ_t' ?_
        have hgx'' := (WShape.HasType.lift hk.2.2).2 hgx'
        refine (LR Γ₀).mono_l ?_
          (.mono_r hJ1' hJ_t' hmem_k)
          (.mono_r hJ2' hJ_t' hgx'') ?_
        · exact (TShape.LE.def hk.1 hk.2.2).1 <| le_m.trans <|
            (TShape.app_mono le_mf (TShape.lift_eqv le_nf).2).trans
              (WShape.lam'_app ▸ hgx2.T)
        refine (LR Γ₀).mono_r_1 hJ2' hgx''
          (.mono_r hJ2' hJ_t' hgx'') ?_ ?_
        · have ⟨_, _, _, le_j, le_j', hBj, hSj, hmj⟩ :=
            (LE_Interp.sound hBa W.left.fits).2
              (hA.join hJ hax') |>.out
          exact (LR Γ₀).left_ty <|
            (LR.TyDefEq.lift hk' (TShape.HasType.sort_r.1 hJ_t)).2 <|
              subst_inst ▸ LR.toValTy le_j le_j'
                (TShape.HasType.sort_r.1 hJ_t) hSj hmj
                ((ihBa hBj hSj hmj).2 W.left)
        · have hAf := (LR _).trans (Af.2 W.left) (Af.1 W).2
          dsimp only [LR, LRS] at hAf
          unfold WShape.lam' at hAf
          split at hAf
          · rw [LRS.DefEq.lam_forallE] at hAf
            obtain ⟨_, _, _, _, red, _, _, _, _, valPi⟩ := hAf
            cases WHNF.forallE.whRedS red
            have le' := (TShape.LE.def
              (Nat.succ_le_succ hk.2.2) (Nat.succ_le_succ hk.2.1)).1 le
            simp only [WShape.T, WShape.lift_forallE hk.2.2,
              WShape.lift_forallE hk.2.1,
              WShape.forallE_le_forallE] at le'
            have Aa := iha hia'
              (haA.mono ((TShape.LE.def hk.2.2 hk.2.1).2 le'.1)) hx'_a₁
            have harg := (LR _).trans (Aa.2 W.left) (Aa.1 W).2
            exact (LR.DefEq.lift hk.2.2 hgx').2 <| (LR _).trans
              (valPi.2 hx'_a₁ (hX.subst W.toSubstEq).hasType.1
                <| (LR _).left harg)
              (valPi.1 hx'_a₁ (hX.subst W.toSubstEq) harg).2
          · refine (hm0 ?_).elim
            unfold WShape.lam'
            simp_all
      | _ =>
        refine have le₂ := Nat.succ_le_succ (Nat.le_max_right ..)
          have hbad := (TShape.LE.def
            (Nat.le_succ_of_le (Nat.le_max_left ..)) le₂).1 le
          ?_
        simp only [WShape.lift_sort, WShape.LE.def,
          WShape.lift_val le₂] at hbad
        cases hbad

/-- Self-adequacy is closed under dependent product formation once the
domain and codomain self-adequacy premises are available.  The proof uses
the relational substitution itself below the binder, so retained-tree
recursion can consume strictly shallower domain and codomain packages without
re-entering the full adequacy induction. -/
theorem LR.adequateForallESelf
    {Γ : List SExpr} {A body : SExpr} {u v : SLevel}
    {ρ : Valuation} {n : Nat} {m a : WShape n}
    (HA : IsDefEqStrong Γ A A (.sort u))
    (HBody : IsDefEqStrong (A :: Γ) body body (.sort v))
    (hM : LE_Interp ρ m.T (.forallE A body))
    (hA : LE_Interp ρ a.T (.sort (.imax u v)))
    (hmem : m.HasType a)
    (ihA : ∀ {ρ n} {ma aa : WShape n},
      LE_Interp ρ ma.T A → LE_Interp ρ aa.T (.sort u) →
      ma.HasType aa → Adequate Γ₀ Γ ρ A A (.sort u) ma aa)
    (ihBody : ∀ {ρ n} {mb ab : WShape n},
      LE_Interp ρ mb.T body → LE_Interp ρ ab.T (.sort v) →
      mb.HasType ab →
      Adequate Γ₀ (A :: Γ) ρ body body (.sort v) mb ab) :
    Adequate Γ₀ Γ ρ (.forallE A body) (.forallE A body)
      (.sort (.imax u v)) m a := by
  cases hmem.unfold with
  | bot hm =>
    cases hm.unfold with
    | forallE =>
      let .sort h := hA
      cases (TShape.LE.lift_r (by simp [TShape.sort])).1 h
    | _ => exact .bot hmem.isType
  | sort =>
    cases n <;>
      have .forallE _ _ _ _ h := hM <;>
      cases TShape.sort_not_le_forallE h
  | @lam _ f₀ =>
    revert hM
    unfold WShape.lam'
    split <;> [skip; exact fun _ => .bot hmem.isType]
    intro | .forallE _ _ _ _ h => cases TShape.lam_not_le_forallE h
  | ctor =>
    have .forallE _ _ _ _ h := hM
    cases TShape.ctor_not_le_forallE h
  | indTy =>
    have .forallE _ _ _ _ h := hM
    cases TShape.indTy_not_le_forallE h
  | @forallE k a₂ a₁ r aty =>
    have aty := WShape.HasTypePi.iff.1 aty
    have hA1 := hM.forallE_inv.1
    have cons := Adequate.cons ihA HA
    refine .refl fun σ σ' W => ?_
    have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
    have HAσ := (HA.substCongr W.toSubstEq).1
    have S' := W.toSubstEq.lift HA.defeq.hasType.1
    refine ⟨A.subst σ, body.subst σ.lift,
      A.subst σ', body.subst σ'.lift, u, v,
      .rfl, .rfl, .single HAσ,
      .single (HBody.substCongr S').1, ?_, ?_⟩
    · exact LR.toValTy le_n le_a aty.1.isType hSort hmem'
        ((ihA hA' hSort hmem').1 W).1
    simp only [LRS.PiDefEq]
    constructor
    · intro x x' p hp ha hv
      have hB := hM.forallE_inv'.2 p
      have WL := cons hp hA1 ha hv W.left
      have ⟨_, _, _, leL, leL', iBL, ivL, hmbL⟩ :=
        (LE_Interp.sound HBody WL.fits).2 hB |>.out
      have semL : (LR Γ₀).TyDefEq
          ((body.subst σ.lift).inst x) ((body.subst σ.lift).inst x')
          (a₂.app p) := by
        simpa [inst_lift_cons] using
          LR.toValTy leL leL' (aty.2 _ hp).toType ivL hmbL
            ((ihBody iBL ivL hmbL).1 WL).1
      have valA := LR.toValTy le_n le_a aty.1.isType hSort hmem'
        ((ihA hA' hSort hmem').1 W).1
      have WR := cons hp hA1 (HAσ.defeqDF ha) ((LR Γ₀).conv valA hv)
        W.symm.left
      have ⟨_, _, _, leR, leR', iBR, ivR, hmbR⟩ :=
        (LE_Interp.sound HBody WR.fits).2 hB |>.out
      have semR : (LR Γ₀).TyDefEq
          ((body.subst σ'.lift).inst x) ((body.subst σ'.lift).inst x')
          (a₂.app p) := by
        simpa [inst_lift_cons] using
          LR.toValTy leR leR' (aty.2 _ hp).toType ivR hmbR
            ((ihBody iBR ivR hmbR).1 WR).1
      have rawL : Γ₀ ⊢
          (body.subst σ.lift).inst x ≡
            (body.subst σ.lift).inst x' : .sort v := by
        simpa only [inst_lift_cons, SExpr.subst] using
          (HBody.substCongr WL.toSubstEq).1
      have rawR : Γ₀ ⊢
          (body.subst σ'.lift).inst x ≡
            (body.subst σ'.lift).inst x' : .sort v := by
        simpa only [inst_lift_cons, SExpr.subst] using
          (HBody.substCongr WR.toSubstEq).1
      exact ⟨semL, semR, ⟨v, rawL⟩, ⟨v, rawR⟩⟩
    · intro x p hp ha hv
      have hB := hM.forallE_inv'.2 p
      have WX := cons hp hA1 ha.hasType.1 ((LR Γ₀).left hv) W
      have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
        (LE_Interp.sound HBody WX.fits).2 hB |>.out
      have hout : (LR Γ₀).TyDefEq
          ((body.subst σ.lift).inst x) ((body.subst σ'.lift).inst x)
          (a₂.app p) := by
        simpa [inst_lift_cons] using
          LR.toValTy le le' (aty.2 _ hp).toType iv hmb
            ((ihBody iB iv hmb).1 WX).1
      exact cast (by congr 1) hout

/-- Adequacy is closed under a displayed-type conversion once adequacy of
the type equality and of the term at its original type are available.  The
statement makes the one heterogeneous callback required by the retained
self-validity recursion explicit. -/
theorem LR.adequateDefeq
    {Γ : List SExpr} {A B e : SExpr} {u : SLevel}
    {ρ : Valuation} {n : Nat} {m b : WShape n}
    (Hty : IsDefEqStrong Γ A B (.sort u))
    (hM : LE_Interp ρ m.T e)
    (hB : LE_Interp ρ b.T B)
    (hmem : m.HasType b)
    (ihTy : ∀ {n'} {ma sa : WShape n'},
      LE_Interp ρ ma.T A → LE_Interp ρ sa.T (.sort u) → ma.HasType sa →
      Adequate Γ₀ Γ ρ A B (.sort u) ma sa)
    (ihE : ∀ {n'} {me ae : WShape n'},
      LE_Interp ρ me.T e → LE_Interp ρ ae.T A → me.HasType ae →
      Adequate Γ₀ Γ ρ e e A me ae) :
    Adequate Γ₀ Γ ρ e e B m b := by
  have tyConv {σ} (W : SubstWF Γ₀ σ σ Γ ρ) :=
    have hA := (LE_Interp.sound Hty W.fits).1.2 hB
    have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound Hty W.fits).2 hA |>.out
    LR.toValTy le_n le_a hmem.isType hSort hmem'
      ((ihTy hA' hSort hmem').2 W)
  refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
    have hA := (LE_Interp.sound Hty W.left.fits).1.2 hB
  · exact ⟨(LR Γ₀).conv (tyConv W.left) ((ihE hM hA hmem).1 W).1,
           (LR Γ₀).conv (tyConv W.left) ((ihE hM hA hmem).1 W).2⟩
  · exact (LR Γ₀).conv (tyConv W) ((ihE hM hA hmem).2 W)

/-- Guarded adequacy is closed under displayed-type conversion once the
strict predecessor supplies the heterogeneous guarded adequacy of the type
edge.  This is the direct analogue of `LR.adequateDefeq`: the proof uses the
retained direct substitution throughout and never collapses a type path or
invokes a semantic inversion package. -/
theorem LRD.adequateDefeq
    {Γ : List SExpr} {A B e : SExpr} {u : SLevel}
    {ρ : Valuation} {n : Nat} {m b : WShape n}
    (Hty : IsDefEqStrong Γ A B (.sort u))
    (hM : LE_Interp ρ m.T e)
    (hB : LE_Interp ρ b.T B)
    (hmem : m.HasType b)
    (ihTy : ∀ {n'} {ma sa : WShape n'},
      LE_Interp ρ ma.T A → LE_Interp ρ sa.T (.sort u) → ma.HasType sa →
      LRD.Adequate Γ₀ Γ ρ A B (.sort u) ma sa)
    (ihE : ∀ {n'} {me ae : WShape n'},
      LE_Interp ρ me.T e → LE_Interp ρ ae.T A → me.HasType ae →
      LRD.Adequate Γ₀ Γ ρ e e A me ae) :
    LRD.Adequate Γ₀ Γ ρ e e B m b := by
  have tyConv {σ} (W : LR.DirectSubstWF Γ₀ σ σ Γ ρ) :=
    have hA := (LE_Interp.sound Hty W.fits).1.2 hB
    have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound Hty W.fits).2 hA |>.out
    LRD.toValTy le_n le_a hmem.isType hSort hmem'
      ((ihTy hA' hSort hmem').2 W)
  refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
    have hA := (LE_Interp.sound Hty W.left.fits).1.2 hB
  · exact ⟨LRD.DefEq.conv (tyConv W.left) ((ihE hM hA hmem).1 W).1,
           LRD.DefEq.conv (tyConv W.left) ((ihE hM hA hmem).1 W).2⟩
  · exact LRD.DefEq.conv (tyConv W) ((ihE hM hA hmem).2 W)

/--
info: 'Lean4Lean.SExpr.LRD.adequateDefeq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.adequateDefeq

/-- Self-validity is closed under a displayed-type conversion using the
joint adequacy/uniqueness tower.

Unlike `adequateDefeq`, this form does not ask the recursive consumer for a
heterogeneous adequacy proof of `A ≡ B`.  It asks only for self-validity of
`A`, `B`, and `e : A`.  At every relational substitution,
`TyDefEq.of_defeq_of_jointBuilder` combines the substituted raw type equality
with the two self observations, after which ordinary logical conversion
finishes the term.  This is the conversion algebra needed by the retained
fixed-head recursion. -/
theorem LR.adequateDefeqSelf_of_stratifiedInversion
    {Γ : List SExpr} {A B e : SExpr} {u : SLevel}
    {ρ : Valuation} {n : Nat} {m b : WShape n}
    (inv : JointStratifiedInversion) (hΓ₀ : Ctx.WF Γ₀)
    (Hty : IsDefEqStrong Γ A B (.sort u))
    (hM : LE_Interp ρ m.T e)
    (hB : LE_Interp ρ b.T B)
    (hmem : m.HasType b)
    (ihA : ∀ {n'} {ma sa : WShape n'},
      LE_Interp ρ ma.T A → LE_Interp ρ sa.T (.sort u) → ma.HasType sa →
      Adequate Γ₀ Γ ρ A A (.sort u) ma sa)
    (ihB : ∀ {n'} {mb sb : WShape n'},
      LE_Interp ρ mb.T B → LE_Interp ρ sb.T (.sort u) → mb.HasType sb →
      Adequate Γ₀ Γ ρ B B (.sort u) mb sb)
    (ihE : ∀ {n'} {me ae : WShape n'},
      LE_Interp ρ me.T e → LE_Interp ρ ae.T A → me.HasType ae →
      Adequate Γ₀ Γ ρ e e A me ae) :
    Adequate Γ₀ Γ ρ e e B m b := by
  have tyConv {σ} (W : SubstWF Γ₀ σ σ Γ ρ) :=
    have hA := (LE_Interp.sound Hty W.fits).1.2 hB
    have ⟨_, a', s', le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound Hty W.fits).2 hA |>.out
    have hB' := (LE_Interp.sound Hty W.fits).1.1 hA'
    have hAA : (LR Γ₀).TyDefEq (A.subst σ) (A.subst σ) a' :=
      (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hSort.le_sort' hmem'
        (.mono_r hSort.le_sort' .sort hmem') .sort
        ((ihA hA' hSort hmem').2 W)
    have hBB : (LR Γ₀).TyDefEq (B.subst σ) (B.subst σ) a' :=
      (LR Γ₀).toType <| (LR Γ₀).mono_r_1 hSort.le_sort' hmem'
        (.mono_r hSort.le_sort' .sort hmem') .sort
        ((ihB hB' hSort hmem').2 W)
    have hAB : Γ₀ ⊢ A.subst σ ≡ B.subst σ : .sort u := by
      simpa only [SExpr.subst] using Hty.subst W.toSubstEq
    have hABsem : (LR Γ₀).TyDefEq (A.subst σ) (B.subst σ) a' :=
      LR.TyDefEq.of_defeq_of_stratifiedInversion inv hΓ₀ hAB hAA hBB
    have ha'Type : a'.HasType .type :=
      (WShape.HasType.mono_r hSort.le_sort' .sort hmem').toType
    (LR.TyDefEq.lift le_n hmem.isType).1 <|
      (LR Γ₀).mono_r_2_ty ((TShape.LE.lift_l le_n).1 le_a)
        (WShape.lift_type ▸ (WShape.HasType.lift le_n).2 hmem.isType)
        ha'Type hABsem
  refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
    have hA := (LE_Interp.sound Hty W.left.fits).1.2 hB
  · exact ⟨(LR Γ₀).conv (tyConv W.left) ((ihE hM hA hmem).1 W).1,
           (LR Γ₀).conv (tyConv W.left) ((ihE hM hA hmem).1 W).2⟩
  · exact (LR Γ₀).conv (tyConv W) ((ihE hM hA hmem).2 W)

/-- Compatibility wrapper for callers that already carry the completed
joint builder. -/
theorem LR.adequateDefeqSelf_of_jointBuilder
    {Γ : List SExpr} {A B e : SExpr} {u : SLevel}
    {ρ : Valuation} {n : Nat} {m b : WShape n}
    (J : LR.JointBuilder) (hΓ₀ : Ctx.WF Γ₀)
    (Hty : IsDefEqStrong Γ A B (.sort u))
    (hM : LE_Interp ρ m.T e)
    (hB : LE_Interp ρ b.T B)
    (hmem : m.HasType b)
    (ihA : ∀ {n'} {ma sa : WShape n'},
      LE_Interp ρ ma.T A → LE_Interp ρ sa.T (.sort u) → ma.HasType sa →
      Adequate Γ₀ Γ ρ A A (.sort u) ma sa)
    (ihB : ∀ {n'} {mb sb : WShape n'},
      LE_Interp ρ mb.T B → LE_Interp ρ sb.T (.sort u) → mb.HasType sb →
      Adequate Γ₀ Γ ρ B B (.sort u) mb sb)
    (ihE : ∀ {n'} {me ae : WShape n'},
      LE_Interp ρ me.T e → LE_Interp ρ ae.T A → me.HasType ae →
      Adequate Γ₀ Γ ρ e e A me ae) :
    Adequate Γ₀ Γ ρ e e B m b :=
  LR.adequateDefeqSelf_of_stratifiedInversion
    J.stratifiedInversion hΓ₀ Hty hM hB hmem ihA ihB ihE

/-- Depth-indexed self-adequacy for every lower observation of one exact
interpretation witness.  Lowering preserves the proof-relevant evaluator
tree, which is exactly the variance needed by a generated RHS
`ShapeSpine`: its fixed head is observed below the root selected by the
constant evaluator. -/
def LR.SelfAdequateAt (Γ₀ : List SExpr)
    {ρ root X} (hX : LE_Interp.Witness ρ root X)
    (depth : Nat) : Prop :=
  ∀ {n : Nat} {mx bx : WShape n} {Δ : List SExpr} {core : Bool}
      {B : SExpr},
    mx.T ≤ root →
    HasTypeStratifiedS Δ X B core depth →
    mx.HasType bx →
    LE_Interp.Witness ρ bx.T B →
    LR.Adequate Γ₀ Δ ρ X X B mx bx

/-- Guarded self-adequacy for every lower observation of one exact
interpretation witness.  This is the full term-and-type counterpart of
`LR.DirectSelfTypeAt`: it retains the level-guarded `LRD` action selected by
the caller rather than projecting immediately to the legacy relation. -/
def LRD.SelfAdequateAt (Γ₀ : List SExpr)
    {ρ root X} (hX : LE_Interp.Witness ρ root X)
    (depth : Nat) : Prop :=
  ∀ {n : Nat} {mx bx : WShape n} {Δ : List SExpr} {core : Bool}
      {B : SExpr},
    mx.T ≤ root →
    HasTypeStratifiedS Δ X B core depth →
    mx.HasType bx →
    LE_Interp.Witness ρ bx.T B →
    LRD.Adequate Γ₀ Δ ρ X X B mx bx

/-- Downward-closed direct validity for a term known syntactically to be a
type.  Unlike ordinary self-adequacy, this package does not choose a second
semantic observation for the displayed sort.  It therefore supplies a
`DirectTyDefEq` at the exact lower type shape requested by a constant
caller, avoiding any cross-level projection of recursively retained
codomain evidence. -/
def LR.DirectSelfTypeAt (Γ₀ : List SExpr)
    {ρ root X} (hX : LE_Interp.Witness ρ root X)
    (depth : Nat) : Prop :=
  ∀ {n : Nat} {mx : WShape n} {Δ : List SExpr} {u : SLevel},
    mx.T ≤ root →
    HasTypeStratifiedS Δ X (.sort u) true depth →
    mx.HasType .type →
    ∀ {{σ σ'}}, LR.SubstWF Γ₀ σ σ' Δ ρ →
      LR.DirectTyDefEq Γ₀ (X.subst σ) (X.subst σ') mx

/-- Consume a synchronized lower fixed-head endpoint at one common shape
level.

The ordered telescope may construct its term and type endpoints at different
`TShape` levels.  Both are lifted along equivalences to their maximum level
before invoking `SelfAdequateAt`; the registered-type witness is transported
only by root lowering.  No typing fact is projected from an upper term
observation to a lower one. -/
theorem LR.SelfAdequateAt.of_typedLowerWitness
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.SelfAdequateAt Γ₀ hX depth)
    {Δ : List SExpr} {B : SExpr} {core : Bool}
    {head : TShape}
    (hhead : head ≤ root)
    (hstrat : HasTypeStratifiedS Δ X B core depth)
    (endpoint : ∃ headElem headTy : TShape,
      headElem ≤ head ∧ headElem.HasType headTy ∧
        Nonempty (LE_Interp.Witness ρ headTy B)) :
    ∃ (n : Nat) (mx bx : WShape n),
      mx.T ≤ head ∧ mx.HasType bx ∧
        LR.Adequate Γ₀ Δ ρ X X B mx bx := by
  obtain ⟨headElem, headTy, helem, htyped, ⟨hB⟩⟩ := endpoint
  let n := max headElem.1 headTy.1
  have hElemLevel : headElem.1 ≤ n := Nat.le_max_left _ _
  have hTyLevel : headTy.1 ≤ n := Nat.le_max_right _ _
  let mx : WShape n := headElem.2.lift n
  let bx : WShape n := headTy.2.lift n
  have hmxElem : mx.T ≤ headElem := by
    exact (TShape.lift_eqv hElemLevel).1
  have hbxTy : bx.T ≤ headTy := by
    exact (TShape.lift_eqv hTyLevel).1
  have hmxbx : mx.HasType bx := by
    exact (TShape.HasType.def hElemLevel hTyLevel).1 htyped
  refine ⟨n, mx, bx, hmxElem.trans helem, hmxbx, ?_⟩
  exact H ((hmxElem.trans helem).trans hhead) hstrat hmxbx
    (hB.mono hbxTy)

/-- Select one synchronized lower term/type endpoint from a typed semantic
head and consume it with guarded self-adequacy.  Both shapes are lifted only
to their common maximum level, so no arbitrary higher refinement is
projected back into `LRD`. -/
theorem LRD.SelfAdequateAt.of_typedLowerWitness
    {hX : LE_Interp.Witness ρ root X}
    (H : LRD.SelfAdequateAt Γ₀ hX depth)
    {Δ : List SExpr} {B : SExpr} {core : Bool}
    {head : TShape}
    (hhead : head ≤ root)
    (hstrat : HasTypeStratifiedS Δ X B core depth)
    (endpoint : ∃ headElem headTy : TShape,
      headElem ≤ head ∧ headElem.HasType headTy ∧
        Nonempty (LE_Interp.Witness ρ headTy B)) :
    ∃ (n : Nat) (mx bx : WShape n),
      mx.T ≤ head ∧ mx.HasType bx ∧
        LRD.Adequate Γ₀ Δ ρ X X B mx bx := by
  obtain ⟨headElem, headTy, helem, htyped, ⟨hB⟩⟩ := endpoint
  let n := max headElem.1 headTy.1
  have hElemLevel : headElem.1 ≤ n := Nat.le_max_left _ _
  have hTyLevel : headTy.1 ≤ n := Nat.le_max_right _ _
  let mx : WShape n := headElem.2.lift n
  let bx : WShape n := headTy.2.lift n
  have hmxElem : mx.T ≤ headElem := by
    exact (TShape.lift_eqv hElemLevel).1
  have hbxTy : bx.T ≤ headTy := by
    exact (TShape.lift_eqv hTyLevel).1
  have hmxbx : mx.HasType bx := by
    exact (TShape.HasType.def hElemLevel hTyLevel).1 htyped
  refine ⟨n, mx, bx, hmxElem.trans helem, hmxbx, ?_⟩
  exact H ((hmxElem.trans helem).trans hhead) hstrat hmxbx
    (hB.mono hbxTy)

/-- Read the closed fixed head selected by guarded self-adequacy at one
literal lower endpoint.  Closedness removes the direct substitution without
changing the chosen term or type shapes. -/
theorem LRD.SelfAdequateAt.closedHeadSelf
    {hX : LE_Interp.Witness ρ root X}
    (H : LRD.SelfAdequateAt Γ₀ hX depth)
    {Δ : List SExpr} {σ σ' : Subst} {headType : SExpr} {core : Bool}
    {head : TShape}
    (hhead : head ≤ root)
    (hstrat : HasTypeStratifiedS Δ X headType core depth)
    (W : LR.DirectSubstWF Γ₀ σ σ' Δ ρ)
    (hXClosed : X.ClosedN) (hTypeClosed : headType.ClosedN)
    {n : Nat} {headElem headElemTy : WShape n}
    (helem : headElem.T ≤ head)
    (htyped : headElem.HasType headElemTy)
    (hTy : LE_Interp.Witness ρ headElemTy.T headType) :
    (LRD Γ₀).DefEq X X headType headElem headElemTy := by
  have hrel := ((H (helem.trans hhead) hstrat htyped hTy).1 W).1
  rw [hXClosed.subst_eq .zero, hXClosed.subst_eq .zero,
    hTypeClosed.subst_eq .zero] at hrel
  exact hrel

/--
info: 'Lean4Lean.SExpr.LRD.SelfAdequateAt.of_typedLowerWitness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.SelfAdequateAt.of_typedLowerWitness

/--
info: 'Lean4Lean.SExpr.LRD.SelfAdequateAt.closedHeadSelf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.SelfAdequateAt.closedHeadSelf

/-- Close a generated guarded RHS application directly from recursive
self-adequacy and the proof-relevant guarded telescope producer.

The producer supplies the registered-type witness at the exact head type
selected by its direct capture chain.  `closedHeadSelf` therefore consumes
its genuine `LE_Interp.Witness` premise; no witness is inferred from an
arbitrary `HasType` proof. -/
theorem LE_Interp.RHS.ShapeSpine.directApplyRuleWithProducerSelfAdequacy
    {Γ : List SExpr} {ρ : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {recLs : List SLevel}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
    {mx my captureType :
      (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {resultType : SExpr} {head root : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {depth : Nat}
    {hX : LE_Interp.Witness ρ root (SExpr.mkInst recLs rule.df.rhs)}
    (H : LE_Interp.RHS.ShapeSpine mcap head rule.capturePaths out.T)
    (producer : LR.DirectFixedHeadProducer Γ ρ mx my captureType H
      (headType := SExpr.mkInst recLs rule.df.type) (outTy := outTy))
    (houtNonbot : ¬out.T ≤ TShape.bot)
    (hne : rule.capturePaths ≠ [])
    (raw : SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst recLs rule.df.type) rule.capturePaths resultType)
    (resultRel : (LRD Γ).TyDefEq resultType resultType outTy)
    (convert : LRD.FixedHeadConvertStep Γ)
    (hself : LRD.SelfAdequateAt Γ hX depth)
    (hhead : head ≤ root)
    {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
    (hstrat : HasTypeStratifiedS Δ
      (SExpr.mkInst recLs rule.df.rhs)
      (SExpr.mkInst recLs rule.df.type) core depth)
    (W : LR.DirectSubstWF Γ σ σ' Δ ρ) :
    (LRD Γ).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my)
      resultType out outTy := by
  apply H.directApplyRuleWithProducerHeadSelf producer houtNonbot hne
      raw resultRel convert
  intro headLevel headElem headElemTy helem htyped hTy
  exact hself.closedHeadSelf hhead hstrat W
    rule.rhsClosed.mkInstS (rule.typeClosed recLs)
    helem htyped hTy

/--
info: 'Lean4Lean.SExpr.LE_Interp.RHS.ShapeSpine.directApplyRuleWithProducerSelfAdequacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.RHS.ShapeSpine.directApplyRuleWithProducerSelfAdequacy

/-- The ordered telescope is a complete producer for the synchronized
endpoint consumed by `SelfAdequateAt.of_typedLowerWitness`. -/
theorem LR.SelfAdequateAt.of_typedTelescope
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.SelfAdequateAt Γ₀ hX depth)
    {Δ : List SExpr} {B : SExpr} {core : Bool}
    {p : Pattern} {mcap : p.Path → TShape}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (hhead : head ≤ root)
    (hstrat : HasTypeStratifiedS Δ X B core depth)
    (telescope : LE_Interp.RHS.ShapeSpine.TypedTelescope
      mcap spine headTy outTy)
    (hTy : LE_Interp.Witness ρ headTy B) :
    ∃ (n : Nat) (mx bx : WShape n),
      mx.T ≤ head ∧ mx.HasType bx ∧
        LR.Adequate Γ₀ Δ ρ X X B mx bx :=
  H.of_typedLowerWitness hhead hstrat
    (telescope.lowerHead.withWitness hTy)

/-- Consume the full fixed-head telescope certificate at the self-adequacy
boundary.  The capture payload is retained for the subsequent application
fold, while this projection uses only its synchronized lower endpoint and
registered-type witness. -/
theorem LR.SelfAdequateAt.of_fixedHeadTelescope
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.SelfAdequateAt Γ₀ hX depth)
    {Δ : List SExpr} {B : SExpr} {core : Bool}
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out}
    (hhead : head ≤ root)
    (hstrat : HasTypeStratifiedS Δ X B core depth)
    (telescope : LR.FixedHeadTelescope
      (headTy := headTy) (outTy := outTy)
      Γ₀ mx my captureType spine)
    (hTy : LE_Interp.Witness ρ headTy B) :
    ∃ (n : Nat) (headElem headElemTy : WShape n),
      headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
        LR.Adequate Γ₀ Δ ρ X X B headElem headElemTy :=
  H.of_typedLowerWitness hhead hstrat
    (telescope.withWitness hTy)

/-- The `headSelf` callback of the fixed-head application fold, produced
without any global adequacy package at the rung's own depth.

This is the depth-refined replacement for `LR.AdequacyAtDepth.closedHeadSelf`.
The term half is the consumer's own `LR.SelfAdequateAt` at the *same* witness
and the *same* depth — the coherent algebra already holds it, so nothing is
manufactured; the type half is the isolated `LR.FixedHeadTypeValidStep`,
whose real demand sits at `depth - 1`.  Both endpoints are the literal ones
the packed telescope selected: no shape or index is re-chosen here. -/
theorem LR.SelfAdequateAt.closedHeadSelf
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.SelfAdequateAt Γ₀ hX depth)
    (typeValid : LR.FixedHeadTypeValidStep Γ₀ depth)
    {Δ : List SExpr} {σ σ' : Subst} {headType : SExpr} {core : Bool}
    {head : TShape}
    (hhead : head ≤ root)
    (hstrat : HasTypeStratifiedS Δ X headType core depth)
    (W : LR.SubstWF Γ₀ σ σ' Δ ρ)
    (hXClosed : X.ClosedN) (hTypeClosed : headType.ClosedN)
    {n : Nat} {headElem headElemTy : WShape n}
    (helem : headElem.T ≤ head)
    (htyped : headElem.HasType headElemTy)
    (hTy : LE_Interp.Witness ρ headElemTy.T headType) :
    (LR Γ₀).DefEq X X headType headElem headElemTy ∧
      (LR Γ₀).TyDefEq headType headType headElemTy := by
  have hrel := ((H (helem.trans hhead) hstrat htyped hTy).1 W).1
  rw [hXClosed.subst_eq .zero, hXClosed.subst_eq .zero,
    hTypeClosed.subst_eq .zero] at hrel
  exact ⟨hrel, typeValid W hstrat hTypeClosed htyped hTy⟩

/-- Finish the packed fixed-head application from the consumer's own
self-adequacy instead of a same-rung `LR.AdequacyAtDepth`.

Compare `LR.FixedHeadTelescope.toApplicationWithAdequacyAtDepth`, which
demands `LR.AdequacyAtDepth Γ₀ depth`.  That input is replaced here by two
strictly weaker ones that the coherent algebra can actually meet: the
self-adequacy result at this witness and depth, and the isolated type rung
`LR.FixedHeadTypeValidStep Γ₀ depth`.  Everything else is unchanged, so this
is a drop-in strengthening of the producer, not a new route. -/
theorem LR.FixedHeadTelescope.toApplicationWithSelfAdequacy
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    {headType resultType : SExpr}
    {hX : LE_Interp.Witness ρ root X} {depth : Nat}
    (H : LR.FixedHeadTelescope
      (headTy := headTy) (outTy := outTy.T)
      Γ₀ mx my captureType spine)
    (hTy : LE_Interp.Witness ρ headTy headType)
    (houtNonbot : ¬out.T ≤ TShape.bot)
    (raw : SExpr.PathSpineWF Γ₀ mx captureType
      headType paths resultType)
    (resultRel : (LR Γ₀).TyDefEq
      resultType resultType outTy)
    (convert : LR.FixedHeadConvertStep Γ₀)
    (hself : LR.SelfAdequateAt Γ₀ hX depth)
    (typeValid : LR.FixedHeadTypeValidStep Γ₀ depth)
    (hhead : head ≤ root)
    {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
    (hstrat : HasTypeStratifiedS Δ X headType core depth)
    (W : LR.SubstWF Γ₀ σ σ' Δ ρ)
    (hXClosed : X.ClosedN) (hTypeClosed : headType.ClosedN) :
    LR.FixedHeadApplication Γ₀ hX depth
      mcap mx my captureType paths headType resultType head out outTy := by
  apply H.toApplicationWith hTy houtNonbot raw resultRel convert
  intro headLevel headElem headElemTy helem htyped hheadTy
  exact hself.closedHeadSelf typeValid hhead hstrat W hXClosed hTypeClosed
    helem htyped hheadTy

/-- The same producer adapter for the monotone telescope. -/
theorem LR.FixedHeadTelescopeLE.toApplicationWithSelfAdequacy
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {spine : LE_Interp.RHS.ShapeSpine mcap head paths out.T}
    {headType resultType : SExpr}
    {hX : LE_Interp.Witness ρ root X} {depth : Nat}
    (H : LR.FixedHeadTelescopeLE
      (headTy := headTy) (outTy := outTy.T)
      Γ₀ mx my captureType spine)
    (hTy : LE_Interp.Witness ρ headTy headType)
    (houtNonbot : ¬out.T ≤ TShape.bot)
    (raw : SExpr.PathSpineWF Γ₀ mx captureType
      headType paths resultType)
    (resultRel : (LR Γ₀).TyDefEq
      resultType resultType outTy)
    (convert : LR.FixedHeadConvertStep Γ₀)
    (hself : LR.SelfAdequateAt Γ₀ hX depth)
    (typeValid : LR.FixedHeadTypeValidStep Γ₀ depth)
    (hhead : head ≤ root)
    {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
    (hstrat : HasTypeStratifiedS Δ X headType core depth)
    (W : LR.SubstWF Γ₀ σ σ' Δ ρ)
    (hXClosed : X.ClosedN) (hTypeClosed : headType.ClosedN) :
    LR.FixedHeadApplication Γ₀ hX depth
      mcap mx my captureType paths headType resultType head out outTy := by
  apply H.toApplicationWith hTy houtNonbot raw resultRel convert
  intro headLevel headElem headElemTy helem htyped hheadTy
  exact hself.closedHeadSelf typeValid hhead hstrat W hXClosed hTypeClosed
    helem htyped hheadTy

/-- Consume a completed fixed-head application package.

The exact fixed-head term relation is stored by the producer together with
the lower term/type endpoint and the exposed application chain.  Consumption
therefore performs no second adequacy call and cannot reselect a different
head witness or typing derivation. -/
theorem LR.FixedHeadApplication.apply
    {hX : LE_Interp.Witness rho root X}
    (H : LR.FixedHeadApplication Γ₀ hX depth
      mcap mx my captureType paths headType resultType head out outTy)
    : (LR Γ₀).DefEq
      (paths.foldl (fun f path => f.app (mx path)) X)
      (paths.foldl (fun f path => f.app (my path)) X)
      resultType out outTy := by
  obtain ⟨headLevel, headElem, headElemTy, helem, htyped,
    ⟨_hType⟩, hheadRel, chain⟩ := H
  exact chain.apply hheadRel

/-- Rewrite the generic fixed-head fold to the generated RHS syntax stored
by an iota descriptor. -/
theorem LR.FixedHeadApplication.applyRule
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
    {mx my captureType :
      (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {resultType : SExpr} {head : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {hX : LE_Interp.Witness rho root
      (SExpr.mkInst recLs rule.df.rhs)}
    (H : LR.FixedHeadApplication Γ₀ hX depth
      mcap mx my captureType rule.capturePaths
      (SExpr.mkInst recLs rule.df.type) resultType head out outTy)
    :
    (LR Γ₀).DefEq
      (r.1.applyS recLs mx) (r.1.applyS recLs my)
      resultType out outTy := by
  rw [← rule.rhsApply recLs mx, ← rule.rhsApply recLs my]
  simpa only [List.foldl_map] using H.apply

/-- Exact-root worker used to prove the downward-closed public contract. -/
private def LR.SelfAdequateExactAt (Γ₀ : List SExpr)
    {ρ root X} (hX : LE_Interp.Witness ρ root X)
    (depth : Nat) : Prop :=
  ∀ {n : Nat} {mx bx : WShape n} {Δ : List SExpr} {core : Bool}
      {B : SExpr},
    root = mx.T →
    HasTypeStratifiedS Δ X B core depth →
    mx.HasType bx →
    LE_Interp.Witness ρ bx.T B →
    LR.Adequate Γ₀ Δ ρ X X B mx bx

/-- The consumer result at one exact syntax depth. -/
def LR.CoherentRetainedAt (Γ₀ : List SExpr)
    {ρ root X} (hX : LE_Interp.Witness ρ root X)
    (depth : Nat) : Prop :=
  LR.SelfAdequateAt Γ₀ hX depth ∧
    LR.FixedHeadResultAt Γ₀ hX depth

/-- Add the downward-closed direct type rung to the existing coherent
consumer package.  The legacy halves remain literal fields so all current
iota and fixed-head consumers can project them unchanged while the direct
fundamental induction is developed additively. -/
def LR.DirectCoherentRetainedAt (Γ₀ : List SExpr)
    {ρ root X} (hX : LE_Interp.Witness ρ root X)
    (depth : Nat) : Prop :=
  LR.CoherentRetainedAt Γ₀ hX depth ∧
    LR.DirectSelfTypeAt Γ₀ hX depth

/-- Add full level-guarded term adequacy to the established coherent
consumer package.

The first component is retained literally: evaluator seed reconstruction and
all existing fixed-head consumers continue to use the same legacy package.
The second component is the stronger term-and-type action required by the
direct generated-RHS zipper. -/
def LRD.CoherentRetainedAt (Γ₀ : List SExpr)
    {ρ root X} (hX : LE_Interp.Witness ρ root X)
    (depth : Nat) : Prop :=
  LR.CoherentRetainedAt Γ₀ hX depth ∧
    LRD.SelfAdequateAt Γ₀ hX depth

/-- The all-depth direct coherent consumer attached to one exact evaluator
witness.  Its legacy half remains the seed used by the established evaluator
recursion; the guarded half is assembled by a separate strong induction over
syntax depth below. -/
def LRD.CoherentRetainedResult (Γ₀ : List SExpr)
    {ρ root X} (hX : LE_Interp.Witness ρ root X) : Prop :=
  ∀ depth, LRD.CoherentRetainedAt Γ₀ hX depth

/-- Inspectable recursive evidence for the full guarded coherent package.

The left injection is reserved for a genuine evaluator child and retains its
`LRD` result at every syntax depth.  A witness rebuilt after a strict syntax
decrease receives only the right injection at that exact depth.  This is the
guarded analogue of `LR.CoherentSeedAt`; keeping the two distinct prevents an
all-depth legacy result from being mistaken for all-depth guarded
self-adequacy. -/
abbrev LRD.CoherentSeedAt (Γ₀ : List SExpr) (depth : Nat)
    {ρ root X} (hX : LE_Interp.Witness ρ root X) : Prop :=
  LE_Interp.Witness.NatSeed
    (fun hX depth => LRD.CoherentRetainedAt Γ₀ hX depth) depth hX

/-- Inject the all-depth guarded result of a genuine evaluator child. -/
theorem LRD.CoherentSeedAt.all
    {hX : LE_Interp.Witness ρ root X}
    (H : LRD.CoherentRetainedResult Γ₀ hX) :
    LRD.CoherentSeedAt Γ₀ depth hX :=
  .inl H

/-- Inject a guarded result justified only at one strict syntax
predecessor. -/
theorem LRD.CoherentSeedAt.local
    {hX : LE_Interp.Witness ρ root X}
    (H : LRD.CoherentRetainedAt Γ₀ hX depth) :
    LRD.CoherentSeedAt Γ₀ depth hX :=
  .inr H

/-- Consume either guarded provenance branch at its stated depth. -/
theorem LRD.CoherentSeedAt.result
    {hX : LE_Interp.Witness ρ root X}
    (H : LRD.CoherentSeedAt Γ₀ depth hX) :
    LRD.CoherentRetainedAt Γ₀ hX depth :=
  H.elim (fun H => H depth) id

/-- The depth-polymorphic consumer attached to one exact evaluator witness.

This is not itself used as an undifferentiated tree predicate.  Semantic `R`
descent may legitimately restart the registered RHS at a larger syntax
depth.  The coherent step below instead distinguishes all-depth results
attached to genuine evaluator children from exact-depth results attached
only after a strict Nat decrease. -/
def LR.CoherentRetainedResult (Γ₀ : List SExpr)
    {ρ root X} (hX : LE_Interp.Witness ρ root X) : Prop :=
  ∀ depth, LR.CoherentRetainedAt Γ₀ hX depth

/-- Inspectable evidence attached to an actual evaluator edge.  Genuine
children carry the all-depth result; a tree rebuilt after a strict Nat
decrease carries only the exact-depth result. -/
abbrev LR.CoherentSeedAt (Γ₀ : List SExpr) (depth : Nat)
    {ρ root X} (hX : LE_Interp.Witness ρ root X) : Prop :=
  LE_Interp.Witness.NatSeed
    (fun hX depth => LR.CoherentRetainedAt Γ₀ hX depth) depth hX

/-- Conversion callback for the level-guarded fundamental induction.

Its source certificate is strictly shallower than the current syntax rung,
exactly as in `LR.SelfAdequateDefeqStepAt`; only the three recursive adequacy
premises and the conclusion are strengthened to `LRD`. -/
def LRD.SelfAdequateDefeqStepAt
    (Γ₀ : List SExpr) (outerDepth : Nat) : Prop :=
  ∀ {Γ : List SExpr} {A B e : SExpr} {u : SLevel} {depth : Nat}
      {ρ : Valuation} {n : Nat} {m b : WShape n},
    depth < outerDepth →
    HasTypeStratifiedS Γ A (.sort u) true depth →
    IsDefEqStrong Γ A B (.sort u) →
    LE_Interp ρ m.T e → LE_Interp ρ b.T B → m.HasType b →
    (∀ {n'} {ma sa : WShape n'},
      LE_Interp ρ ma.T A → LE_Interp ρ sa.T (.sort u) →
      ma.HasType sa → LRD.Adequate Γ₀ Γ ρ A A (.sort u) ma sa) →
    (∀ {n'} {mb sb : WShape n'},
      LE_Interp ρ mb.T B → LE_Interp ρ sb.T (.sort u) →
      mb.HasType sb → LRD.Adequate Γ₀ Γ ρ B B (.sort u) mb sb) →
    (∀ {n'} {me ae : WShape n'},
      LE_Interp ρ me.T e → LE_Interp ρ ae.T A →
      me.HasType ae → LRD.Adequate Γ₀ Γ ρ e e A me ae) →
    LRD.Adequate Γ₀ Γ ρ e e B m b

/-- Well-founded implementation of the guarded conversion callback.  The
heterogeneous type edge is obtained from the strict predecessor adequacy
rung; the term's self edge is the local recursive hypothesis.  No inversion
or path collapse is used. -/
theorem LRD.SelfAdequateDefeqStepAt.of_lowerAdequacy
    (hΓ₀ : Ctx.WF Γ₀) (outerDepth : Nat)
    (lowerAdequacy : ∀ d, d < outerDepth →
      LRD.ContextualAdequacyAtDepth d) :
    LRD.SelfAdequateDefeqStepAt Γ₀ outerDepth := by
  intro Γ A B e u depth ρ n m b hdepth hAty hEq hM hB hmem _ _ ihe
  apply LRD.adequateDefeq hEq hM hB hmem
  · intro n' ma sa hA hSort hma
    exact (lowerAdequacy depth hdepth hΓ₀)
      hEq hAty hA hSort hma
  · exact ihe

/--
info: 'Lean4Lean.SExpr.LRD.SelfAdequateDefeqStepAt.of_lowerAdequacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LRD.SelfAdequateDefeqStepAt.of_lowerAdequacy

/-- Constant callback for the level-guarded fundamental induction.

The semantic child tree is indexed by `LRD.CoherentSeedAt`: genuine evaluator
children retain all-depth guarded coherence, while strict restarts remain
local.  The established constant result is passed separately, just as it is
for the Pi and lambda constructors: direct substitutions cannot manufacture
adequacy quantified over every legacy `SubstWF`. -/
def LRD.SelfAdequateConstStep (Γ₀ : List SExpr) : Prop :=
  ∀ {c : Name} {ci : VConstant} {Γ : List SExpr}
      {ls : List SLevel} {u : SLevel} {depth : Nat}
      {ρ : Valuation} {n : Nat} {mx bx : WShape n},
    Params.env.constants c = some ci →
    ls.length = ci.uvars →
    HasTypeStratifiedS Γ (SExpr.mkInst ls ci.type)
      (.sort u) true depth →
    (∀ (d' : Nat), d' < depth + 1 →
      ∀ {ρ root X} (hX' : LE_Interp.Witness ρ root X),
        hX'.RDeepChildren (LRD.CoherentSeedAt Γ₀ d') →
        LRD.CoherentRetainedAt Γ₀ hX' d') →
    mx.HasType bx →
    LE_Interp.Witness ρ bx.T (SExpr.mkInst ls ci.type) →
    ∀ (hX : LE_Interp.Witness ρ mx.T (.const c ls)),
      hX.RDeepChildren (LRD.CoherentSeedAt Γ₀ (depth + 1)) →
      LR.Adequate Γ₀ Γ ρ (.const c ls) (.const c ls)
        (SExpr.mkInst ls ci.type) mx bx →
      LRD.Adequate Γ₀ Γ ρ (.const c ls) (.const c ls)
        (SExpr.mkInst ls ci.type) mx bx

/-- A recursive RHS witness together with exactly the typing evidence needed
to consume it as a fixed head.

Genuine evaluator children carry the all-depth result and need no chosen
typing certificate.  A rebuilt child remains local and must carry the
registered RHS typing at that same local depth.  Packaging the two branches
here prevents a later proof-irrelevant witness selection from pairing one
edge's result with another edge's depth certificate. -/
def LR.CoherentRhsSeedAt (Γ₀ Δ : List SExpr) (depth : Nat)
    {ρ root X} (hX : LE_Interp.Witness ρ root X) (B : SExpr) : Prop :=
  LR.CoherentRetainedResult Γ₀ hX ∨
    (LR.CoherentRetainedAt Γ₀ hX depth ∧
      HasTypeStratifiedS Δ X B true depth)

/-- Action-indexed evidence retained on the literal fixed RHS edge created
by focused reverse conversion.

The semantic preimage owns the exact applied-RHS and peeled-head
stratifications together with the selected head witness and shape spine.
`edge` identifies the concrete root lowering stored by the rebuilt constant,
while `realizes` prevents the certificate from being attached to a different
witness with the same public syntax and shape indices. -/
structure LR.FocusedRhsOriginAt (Γ₀ : List SExpr) (depth : Nat)
    {rho root X} (hX : LE_Interp.Witness rho root X) where
  recName : Name
  ctorName : Name
  major : Nat
  arity : Nat
  r : (RecursorIotaPattern recName major ctorName arity).RHS ×
    (RecursorIotaPattern recName major ctorName arity).Check
  rule : Pattern.IotaRule r
  Gamma : List SExpr
  e : SExpr
  ls : List SLevel
  capture : (RecursorIotaPattern recName major ctorName arity).Path → SExpr
  A : SExpr
  action : Pattern.Action Gamma r e ls capture A
  rhsRoot : TShape
  rhsWitness : LE_Interp.Witness rho rhsRoot
    (r.1.applyS ls capture)
  rhsDepth : Nat
  preimage : rule.FocusedActionPreimage action rhsWitness rhsDepth
  edge : preimage.headWitness.LowerEdge root X
  realizes : hX = edge.realize
  retained : LR.CoherentRetainedAt Γ₀ hX depth

/-- An action-indexed focused origin with its original proof-relevant edge
hidden, but its registered-head syntax retained as the index.

This is the conversion-path payload used when a later computational equality
must select a fresh endpoint witness.  The fresh edge receives its own local
retained result; this trace contributes only the earlier focused action and
can be replayed only at the same fixed-head syntax. -/
def LR.FocusedRhsTraceAt (Γ₀ : List SExpr) (depth : Nat)
    (X : SExpr) : Prop :=
  ∃ (rho : Valuation) (root : TShape),
    ∃ hX : LE_Interp.Witness rho root X,
      Nonempty (LR.FocusedRhsOriginAt Γ₀ depth hX)

/-- A conversion suffix carries the complete set of focused origins visible
in its source tree, rather than choosing one origin prematurely.

The predicate field records which registered-head syntaxes occur and
`replay` recovers the corresponding action-indexed certificate.  Keeping the
whole set is essential when one converted tree contains several generated
rules: a later fixed-head consumer, not the transport, is the first point
that knows which rule it needs. -/
structure LR.FocusedRhsTraceBundleAt
    (Γ₀ : List SExpr) (depth : Nat) where
  contains : SExpr → Prop
  replay : ∀ {X}, contains X → LR.FocusedRhsTraceAt Γ₀ depth X

/-- Inspectable seed used only inside retained semantic typing.

Ordinary transports retain the old Nat provenance.  A focused reverse iota
edge additionally carries its action-indexed typing origin.  Keeping this
wrapper outside `CoherentSeedAt` means the outer semantic/Nat recursion still
grants genuine children exactly the same hypotheses as before. -/
inductive LR.CoherentSemanticSeedAt (Γ₀ : List SExpr) (depth : Nat) :
    {rho : Valuation} → {root : TShape} → {X : SExpr} →
      LE_Interp.Witness rho root X → Prop where
  | ordinary {hX : LE_Interp.Witness rho root X} :
      LR.CoherentSeedAt Γ₀ depth hX →
      LR.CoherentSemanticSeedAt Γ₀ depth hX
  | focused {hX : LE_Interp.Witness rho root X} :
      Nonempty (LR.FocusedRhsOriginAt Γ₀ depth hX) →
      LR.CoherentSemanticSeedAt Γ₀ depth hX
  | carried {hX : LE_Interp.Witness rho root X} :
      LR.FocusedRhsTraceBundleAt Γ₀ depth →
      LR.CoherentRetainedAt Γ₀ hX depth →
      LR.CoherentSemanticSeedAt Γ₀ depth hX
  | replayed {hX : LE_Interp.Witness rho root X} :
      (bundle : LR.FocusedRhsTraceBundleAt Γ₀ depth) →
      bundle.contains X →
      LR.CoherentRetainedAt Γ₀ hX depth →
      LR.CoherentSemanticSeedAt Γ₀ depth hX

/-- Transportable recursive-edge provenance used inside retained semantic
typing.  The outer consumer algebra receives `CoherentSeedAt`, not this free
closure. -/
abbrev LR.CoherentProvenanceAt (Γ₀ : List SExpr) (depth : Nat)
    {ρ root X} (hX : LE_Interp.Witness ρ root X) : Prop :=
  LE_Interp.Witness.TransportClosure
    (LR.CoherentSemanticSeedAt Γ₀ depth) hX

/-- Inject the all-depth result of a genuine evaluator child. -/
theorem LR.CoherentSeedAt.all
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentRetainedResult Γ₀ hX) :
    LR.CoherentSeedAt Γ₀ depth hX :=
  .inl H

/-- Inject a result justified only at this exact smaller syntax depth. -/
theorem LR.CoherentSeedAt.local
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentRetainedAt Γ₀ hX depth) :
    LR.CoherentSeedAt Γ₀ depth hX :=
  .inr H

/-- Consume either form of inspectable recursive-edge evidence at its stated
depth. -/
theorem LR.CoherentSeedAt.result
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentSeedAt Γ₀ depth hX) :
    LR.CoherentRetainedAt Γ₀ hX depth :=
  H.elim (fun H => H depth) id

/-- Forget only the guarded component while preserving whether a seed is a
genuine all-depth child or a rebuilt local child. -/
theorem LRD.CoherentSeedAt.toLegacy
    {hX : LE_Interp.Witness ρ root X}
    (H : LRD.CoherentSeedAt Γ₀ depth hX) :
    LR.CoherentSeedAt Γ₀ depth hX := by
  cases H with
  | inl hall => exact .inl (fun d => (hall d).1)
  | inr hlocal => exact .inr hlocal.1

/-- Expose the native/local distinction without losing guarded coherence.
A genuine evaluator child may select the registered term's native typing
depth; a rebuilt child remains pinned to its supplied local rung. -/
theorem LRD.CoherentSeedAt.nativeOrLocal
    {hX : LE_Interp.Witness ρ root X}
    (H : LRD.CoherentSeedAt Γ₀ depth hX)
    (hstrong : IsDefEqStrong Δ X X B) :
    (∃ nativeDepth,
      LRD.CoherentRetainedAt Γ₀ hX nativeDepth ∧
        HasTypeStratifiedS Δ X B true nativeDepth) ∨
      LRD.CoherentRetainedAt Γ₀ hX depth := by
  cases H with
  | inl hall =>
    obtain ⟨nativeDepth, hstrat, _⟩ := hstrong.stratify
    exact .inl ⟨nativeDepth, hall nativeDepth, hstrat⟩
  | inr hlocal => exact .inr hlocal

/-- Expose the depth distinction carried by one coherent evaluator seed.

A genuine semantic child can be paired with the registered term's native
stratification depth because its retained result is depth-polymorphic.  A
rebuilt child remains explicitly local to the caller's rung.  In particular,
this eliminator never asks a local seed to type a syntactically deeper
registered RHS. -/
theorem LR.CoherentSeedAt.nativeOrLocal
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentSeedAt Γ₀ depth hX)
    (hstrong : IsDefEqStrong Δ X X B) :
    (∃ nativeDepth,
      LR.CoherentRetainedAt Γ₀ hX nativeDepth ∧
        HasTypeStratifiedS Δ X B true nativeDepth) ∨
      LR.CoherentRetainedAt Γ₀ hX depth := by
  cases H with
  | inl hall =>
    obtain ⟨nativeDepth, hstrat, _⟩ := hstrong.stratify
    exact .inl ⟨nativeDepth, hall nativeDepth, hstrat⟩
  | inr hlocal => exact .inr hlocal

/--
info: 'Lean4Lean.SExpr.LR.CoherentSeedAt.nativeOrLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.CoherentSeedAt.nativeOrLocal

/-- Inject the structurally recursive, all-depth result of a genuine
evaluator child into depth-local provenance. -/
theorem LR.CoherentProvenanceAt.all
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentRetainedResult Γ₀ hX) :
    LR.CoherentProvenanceAt Γ₀ depth hX :=
  .base (.ordinary (.inl H))

/-- Inject a result justified only at the current, strictly smaller syntax
depth.  This constructor deliberately does not manufacture an all-depth
recursive hypothesis. -/
theorem LR.CoherentProvenanceAt.local
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentRetainedAt Γ₀ hX depth) :
    LR.CoherentProvenanceAt Γ₀ depth hX :=
  .base (.ordinary (.inr H))

/-- Every transient semantic seed still supplies the retained consumer fact
at the current guarded depth.  Focused origins expose the same local result
without forgetting their action-indexed certificate. -/
theorem LR.CoherentSemanticSeedAt.result
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentSemanticSeedAt Γ₀ depth hX) :
    LR.CoherentRetainedAt Γ₀ hX depth := by
  cases H with
  | ordinary H => exact H.result
  | focused H => exact H.elim fun origin => origin.retained
  | carried _ H => exact H
  | replayed _ _ H => exact H

/-- A focused trace occurring inside one transported recursive-edge proof.
The constructors mirror exactly the syntax-preserving operations admitted by
`TransportClosure`. -/
private inductive LR.FocusedTraceInProvenanceAt
    (Γ₀ : List SExpr) (depth : Nat) (Y : SExpr) :
    {X : SExpr} → {ρ : Valuation} → {root : TShape} →
      {hX : LE_Interp.Witness ρ root X} →
      LR.CoherentProvenanceAt Γ₀ depth hX → Prop where
  | focused {hY : LE_Interp.Witness ρ root Y}
      (origin : Nonempty (LR.FocusedRhsOriginAt Γ₀ depth hY)) :
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y
        (.base (.focused origin) : LR.CoherentProvenanceAt Γ₀ depth hY)
  | replayed {hX : LE_Interp.Witness ρ root X}
      (bundle : LR.FocusedRhsTraceBundleAt Γ₀ depth)
      (current : bundle.contains X)
      (retained : LR.CoherentRetainedAt Γ₀ hX depth) :
      bundle.contains Y →
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y
        (.base (.replayed bundle current retained) :
          LR.CoherentProvenanceAt Γ₀ depth hX)
  | carried {hX : LE_Interp.Witness ρ root X}
      (bundle : LR.FocusedRhsTraceBundleAt Γ₀ depth)
      (retained : LR.CoherentRetainedAt Γ₀ hX depth) :
      bundle.contains Y →
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y
        (.base (.carried bundle retained) :
          LR.CoherentProvenanceAt Γ₀ depth hX)
  | mono {ρ : Valuation} {root m : TShape}
      {hX : LE_Interp.Witness ρ root X}
      {H : LR.CoherentProvenanceAt Γ₀ depth hX} (hle : m ≤ root) :
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y H →
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y
        (.mono (H := hX) hle H)
  | mono_l {ρ ρ' : Valuation} {root : TShape}
      {hX : LE_Interp.Witness ρ root X}
      {H : LR.CoherentProvenanceAt Γ₀ depth hX} (hρ : ρ.LE ρ') :
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y H →
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y
        (.mono_l (H := hX) hρ H)
  | join {ρ : Valuation} {root₁ root₂ : TShape}
      {hX₁ : LE_Interp.Witness ρ root₁ X}
      {hX₂ : LE_Interp.Witness ρ root₂ X}
      {H₁ : LR.CoherentProvenanceAt Γ₀ depth hX₁}
      {H₂ : LR.CoherentProvenanceAt Γ₀ depth hX₂}
      (hJoin : LE_Interp.Witness ρ (root₁.join root₂) X) :
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y H₁ →
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y
        (.join (H₁ := hX₁) (H₂ := hX₂) hJoin H₁ H₂)
  | join_right {ρ : Valuation} {root₁ root₂ : TShape}
      {hX₁ : LE_Interp.Witness ρ root₁ X}
      {hX₂ : LE_Interp.Witness ρ root₂ X}
      {H₁ : LR.CoherentProvenanceAt Γ₀ depth hX₁}
      {H₂ : LR.CoherentProvenanceAt Γ₀ depth hX₂}
      (hJoin : LE_Interp.Witness ρ (root₁.join root₂) X) :
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y H₂ →
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y
        (.join (H₁ := hX₁) (H₂ := hX₂) hJoin H₁ H₂)
  | closed {ρ ρ' : Valuation} {root : TShape}
      {hX : LE_Interp.Witness ρ root X}
      {H : LR.CoherentProvenanceAt Γ₀ depth hX}
      (cl : ClosedN X k) (hρ : ∀ i < k, ρ i = ρ' i) :
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y H →
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y
        (.closed (H := hX) cl hρ H)

/-- Recover the action-indexed payload from a transported occurrence. -/
private theorem LR.FocusedTraceInProvenanceAt.focusedTrace
    {hX : LE_Interp.Witness ρ root X}
    {H : LR.CoherentProvenanceAt Γ₀ depth hX}
    (occurs : LR.FocusedTraceInProvenanceAt Γ₀ depth Y H) :
    LR.FocusedRhsTraceAt Γ₀ depth Y := by
  induction occurs with
  | focused origin => exact ⟨_, _, _, origin⟩
  | replayed bundle _ _ member => exact bundle.replay member
  | carried bundle _ member => exact bundle.replay member
  | mono _ _ ih => exact ih
  | mono_l _ _ ih => exact ih
  | join _ _ ih => exact ih
  | join_right _ _ ih => exact ih
  | closed _ _ _ ih => exact ih

/-- A focused conversion trace occurring anywhere in one exact retained
tree.  The `Y` index ensures a later rebuild can replay it only at an
abstract edge for the same registered-head syntax. -/
private inductive LR.FocusedTraceInRDeepAt
    (Γ₀ : List SExpr) (depth : Nat) (Y : SExpr) :
    ∀ {ρ root X} {hX : LE_Interp.Witness ρ root X},
      hX.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) → Prop where
  | app_fun {cf ca} :
      LR.FocusedTraceInRDeepAt Γ₀ depth Y cf →
      LR.FocusedTraceInRDeepAt Γ₀ depth Y (.app cf ca)
  | app_arg {cf ca} :
      LR.FocusedTraceInRDeepAt Γ₀ depth Y ca →
      LR.FocusedTraceInRDeepAt Γ₀ depth Y (.app cf ca)
  | lam_dom {cDom cBody} :
      LR.FocusedTraceInRDeepAt Γ₀ depth Y cDom →
      LR.FocusedTraceInRDeepAt Γ₀ depth Y (.lam cDom cBody)
  | lam_body {cDom cBody} (x) (hx) :
      LR.FocusedTraceInRDeepAt Γ₀ depth Y (cBody x hx) →
      LR.FocusedTraceInRDeepAt Γ₀ depth Y (.lam cDom cBody)
  | forall_dom₁ {cDom₁ cDom₂ cBody} :
      LR.FocusedTraceInRDeepAt Γ₀ depth Y cDom₁ →
      LR.FocusedTraceInRDeepAt Γ₀ depth Y
        (.forallE cDom₁ cDom₂ cBody)
  | forall_dom₂ {cDom₁ cDom₂ cBody} :
      LR.FocusedTraceInRDeepAt Γ₀ depth Y cDom₂ →
      LR.FocusedTraceInRDeepAt Γ₀ depth Y
        (.forallE cDom₁ cDom₂ cBody)
  | forall_body {cDom₁ cDom₂ cBody} (x) (hx) :
      LR.FocusedTraceInRDeepAt Γ₀ depth Y (cBody x hx) →
      LR.FocusedTraceInRDeepAt Γ₀ depth Y
        (.forallE cDom₁ cDom₂ cBody)
  | const_type {cType pEdge cEdge} :
      LR.FocusedTraceInRDeepAt Γ₀ depth Y cType →
      LR.FocusedTraceInRDeepAt Γ₀ depth Y
        (.const cType pEdge cEdge)
  | const_edge {cType pEdge cEdge} (m) (e) (hr) :
      LR.FocusedTraceInProvenanceAt Γ₀ depth Y (pEdge m e hr) →
      LR.FocusedTraceInRDeepAt Γ₀ depth Y
        (.const cType pEdge cEdge)
  | const_deep {cType pEdge cEdge} (m) (e) (hr) :
      LR.FocusedTraceInRDeepAt Γ₀ depth Y (cEdge m e hr) →
      LR.FocusedTraceInRDeepAt Γ₀ depth Y
        (.const cType pEdge cEdge)

/-- Extract the action-indexed payload named by a tree occurrence. -/
private theorem LR.FocusedTraceInRDeepAt.focusedTrace
    {hX : LE_Interp.Witness ρ root X}
    {children : hX.RDeepChildren
      (LR.CoherentProvenanceAt Γ₀ depth)}
    (occurs : LR.FocusedTraceInRDeepAt Γ₀ depth Y children) :
    LR.FocusedRhsTraceAt Γ₀ depth Y := by
  induction occurs with
  | const_edge _ _ _ h => exact h.focusedTrace
  | app_fun _ ih => exact ih
  | app_arg _ ih => exact ih
  | lam_dom _ ih => exact ih
  | lam_body _ _ _ ih => exact ih
  | forall_dom₁ _ ih => exact ih
  | forall_dom₂ _ ih => exact ih
  | forall_body _ _ _ ih => exact ih
  | const_type _ ih => exact ih
  | const_deep _ _ _ _ ih => exact ih

/-- Package every focused occurrence in a retained tree without selecting a
particular registered rule. -/
private def LR.FocusedTraceInRDeepAt.bundle
    {hX : LE_Interp.Witness ρ root X}
    (children : hX.RDeepChildren
      (LR.CoherentProvenanceAt Γ₀ depth)) :
    LR.FocusedRhsTraceBundleAt Γ₀ depth := {
  contains := fun Y =>
    LR.FocusedTraceInRDeepAt Γ₀ depth Y children
  replay := fun occurs => occurs.focusedTrace }

/-- Rebuild the exact evaluator tree of a freshly selected witness at one
strictly smaller syntax depth.

Each abstract `R` child is traversed structurally before `seed` is invoked;
the resulting consumer fact is therefore local to `depth` and cannot be
promoted to the all-depth hypothesis reserved for genuine outer-recursion
children. -/
theorem LR.CoherentSeedAt.rebuild
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth)
    {hX : LE_Interp.Witness ρ root X} :
    hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) :=
  LE_Interp.Witness.RDeepChildren.of_step
    (P := LR.CoherentSeedAt Γ₀ depth)
    (fun hX children =>
      LR.CoherentSeedAt.local (seed hX children)) hX

/-- Rebuild a freshly selected witness after a strict syntax decrease, marking
every abstract evaluator edge as local guarded evidence.  Only the outer
semantic recursion may introduce the all-depth branch. -/
theorem LRD.CoherentSeedAt.rebuild
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LRD.CoherentSeedAt Γ₀ depth) →
        LRD.CoherentRetainedAt Γ₀ hX depth)
    {hX : LE_Interp.Witness ρ root X} :
    hX.RDeepChildren (LRD.CoherentSeedAt Γ₀ depth) :=
  LE_Interp.Witness.RDeepChildren.of_step
    (P := LRD.CoherentSeedAt Γ₀ depth)
    (fun hX children =>
      LRD.CoherentSeedAt.local (seed hX children)) hX

/-- Use a completed strictly-smaller Nat rung at a freshly selected exact
witness.

The witness is not handed directly to `lower`: its evaluator tree is first
rebuilt with depth-local seeds.  This is the reusable guarded restart for
ordinary syntax children, semantic conversion endpoints, and dependent
application witnesses. -/
theorem LR.CoherentRetainedAt.restart
    (lower : ∀ (d' : Nat), d' < outerDepth →
      ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
        hX.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
        LR.CoherentRetainedAt Γ₀ hX d')
    (hdepth : depth < outerDepth)
    {hX : LE_Interp.Witness ρ root X} :
    LR.CoherentRetainedAt Γ₀ hX depth := by
  let children : hX.RDeepChildren
      (LR.CoherentSeedAt Γ₀ depth) :=
    LR.CoherentSeedAt.rebuild
      (seed := fun hX children => lower depth hdepth hX children)
  exact lower depth hdepth hX children

/-- Guarded restart for the additive direct package.  Rebuilding still uses
the established coherent seed tree; each local seed projects the legacy
consumer half, while the final restart retains the direct type half too. -/
theorem LR.DirectCoherentRetainedAt.restart
    (lower : ∀ (d' : Nat), d' < outerDepth →
      ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
        hX.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
        LR.DirectCoherentRetainedAt Γ₀ hX d')
    (hdepth : depth < outerDepth)
    {hX : LE_Interp.Witness ρ root X} :
    LR.DirectCoherentRetainedAt Γ₀ hX depth := by
  let children : hX.RDeepChildren
      (LR.CoherentSeedAt Γ₀ depth) :=
    LR.CoherentSeedAt.rebuild
      (seed := fun hX children => (lower depth hdepth hX children).1)
  exact lower depth hdepth hX children

/-- Guarded restart for the full direct coherent package.  The rebuilt tree
uses only local `LRD` seeds; no strict restart is promoted to the all-depth
branch reserved for genuine semantic children. -/
theorem LRD.CoherentRetainedAt.restart
    (lower : ∀ (d' : Nat), d' < outerDepth →
      ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
        hX.RDeepChildren (LRD.CoherentSeedAt Γ₀ d') →
        LRD.CoherentRetainedAt Γ₀ hX d')
    (hdepth : depth < outerDepth)
    {hX : LE_Interp.Witness ρ root X} :
    LRD.CoherentRetainedAt Γ₀ hX depth := by
  let children : hX.RDeepChildren
      (LRD.CoherentSeedAt Γ₀ depth) :=
    LRD.CoherentSeedAt.rebuild
      (seed := fun hX children => lower depth hdepth hX children)
  exact lower depth hdepth hX children

/-- Assemble full level-guarded self-adequacy by induction on one exact
stratified typing certificate.

All non-constant constructors are discharged here.  Application, lambda and
Pi use the already proved `LRD` adequacy constructors; lambda and Pi also
consume the legacy adequacy produced at the same root, preserving the honest
quantifier distinction between `SubstWF` and `DirectSubstWF`.  Recursive
syntax calls use only strict-depth restarts.  Consequently the two remaining
inputs are localized exactly where they belong: conversion and constant
evaluation. -/
theorem LRD.selfAdequateAtStep
    (outerDepth : Nat)
    (defeqStep : LRD.SelfAdequateDefeqStepAt Γ₀ outerDepth)
    (constStep : LRD.SelfAdequateConstStep Γ₀)
    {ρ root X} (hX : LE_Interp.Witness ρ root X)
    (children : hX.RDeepChildren (LRD.CoherentSeedAt Γ₀ outerDepth))
    (legacy : LR.SelfAdequateAt Γ₀ hX outerDepth)
    (lower : ∀ (d' : Nat), d' < outerDepth → ∀ {ρ root X}
      (hX' : LE_Interp.Witness ρ root X),
      hX'.RDeepChildren (LRD.CoherentSeedAt Γ₀ d') →
      LRD.CoherentRetainedAt Γ₀ hX' d') :
    LRD.SelfAdequateAt Γ₀ hX outerDepth := by
  intro n mx bx Δ core B hroot hTyping htyped hB
  have restartDirect : ∀ (d' : Nat), d' < outerDepth →
      ∀ {ρ root X} (hX' : LE_Interp.Witness ρ root X),
        LRD.SelfAdequateAt Γ₀ hX' d' := by
    intro d' hdepth ρ root X hX'
    exact (LRD.CoherentRetainedAt.restart
      (lower := lower) hdepth (hX := hX')).2
  let hX' := hX.mono hroot
  let children' : hX'.RDeepChildren
      (LRD.CoherentSeedAt Γ₀ outerDepth) := children.mono hroot
  have legacyAdequate : LR.Adequate Γ₀ Δ ρ X X B mx bx :=
    legacy hroot hTyping htyped hB
  induction hTyping generalizing ρ n mx bx with
  | base htypedCore ih =>
    exact ih defeqStep hX children legacy lower hroot htyped hB
      restartDirect legacyAdequate
  | @sort' Δ l depth =>
    exact LRD.Adequate.sort hX'.toInterp htyped
  | @bvar Δ i A u depth hlookup hA ihA =>
    exact LRD.Adequate.bvar hlookup hX'.toInterp hB.toInterp htyped
  | @const c ci Γ ls u depth hreg hlen hTy _ =>
    exact constStep hreg hlen hTy lower htyped hB hX' children'
      legacyAdequate
  | @app Γ A u depth B v f x hAty hBty hfty hxty hRty
      _ _ _ _ _ =>
    have hdepth : depth < depth + 1 := Nat.lt_succ_self depth
    have ihf : ∀ {ρ : Valuation} {n' : Nat} {mf af : WShape n'},
        LE_Interp ρ mf.T f → LE_Interp ρ af.T (.forallE A B) →
        mf.HasType af →
        LRD.Adequate Γ₀ Γ ρ f f (.forallE A B) mf af := by
      intro ρ n' mf af hf hPi hmf
      exact (restartDirect depth hdepth hf.witness)
        .rfl hfty hmf hPi.witness
    have ihx : ∀ {ρ : Valuation} {n' : Nat} {ma aa : WShape n'},
        LE_Interp ρ ma.T x → LE_Interp ρ aa.T A → ma.HasType aa →
        LRD.Adequate Γ₀ Γ ρ x x A ma aa := by
      intro ρ n' ma aa hx hA hma
      exact (restartDirect depth hdepth hx.witness)
        .rfl hxty hma hA.witness
    have ihR : ∀ {ρ : Valuation} {n' : Nat} {mb av : WShape n'},
        LE_Interp ρ mb.T (B.inst x) → LE_Interp ρ av.T (.sort v) →
        mb.HasType av →
        LRD.Adequate Γ₀ Γ ρ (B.inst x) (B.inst x) (.sort v) mb av := by
      intro ρ n' mb av hResult hv hmb
      exact (restartDirect depth hdepth hResult.witness)
        .rfl hRty hmb hv.witness
    exact LRD.adequateApp hfty.strong hxty.strong hRty.strong
      hX'.toInterp hB.toInterp htyped ihf ihx ihR
  | @lam Γ A u depth B v body hAty hBty hbodyty hPity
      _ _ _ _ =>
    have hdepth : depth < depth + 1 := Nat.lt_succ_self depth
    have ihA : ∀ {ρ : Valuation} {n' : Nat} {ma aa : WShape n'},
        LE_Interp ρ ma.T A → LE_Interp ρ aa.T (.sort u) →
        ma.HasType aa →
        LRD.Adequate Γ₀ Γ ρ A A (.sort u) ma aa := by
      intro ρ n' ma aa hA hSort hma
      exact (restartDirect depth hdepth hA.witness)
        .rfl hAty hma hSort.witness
    have ihB : ∀ {ρ : Valuation} {n' : Nat} {mb ab : WShape n'},
        LE_Interp ρ mb.T B → LE_Interp ρ ab.T (.sort v) →
        mb.HasType ab →
        LRD.Adequate Γ₀ (A :: Γ) ρ B B (.sort v) mb ab := by
      intro ρ n' mb ab hBody hSort hmb
      exact (restartDirect depth hdepth hBody.witness)
        .rfl hBty hmb hSort.witness
    have ihBody : ∀ {ρ : Valuation} {n' : Nat} {mb ab : WShape n'},
        LE_Interp ρ mb.T body → LE_Interp ρ ab.T B →
        mb.HasType ab →
        LRD.Adequate Γ₀ (A :: Γ) ρ body body B mb ab := by
      intro ρ n' mb ab hBody hBTy hmb
      exact (restartDirect depth hdepth hBody.witness)
        .rfl hbodyty hmb hBTy.witness
    exact LRD.Adequate.lamSelf hAty.strong hBty.strong hbodyty.strong
      hX'.toInterp hB.toInterp htyped ihA ihB ihBody
      legacyAdequate
  | @forallE Γ A u depth body v hAty hbodyty _ _ =>
    have hdepth : depth < depth + 1 := Nat.lt_succ_self depth
    have ihA : ∀ {ρ : Valuation} {n' : Nat} {ma aa : WShape n'},
        LE_Interp ρ ma.T A → LE_Interp ρ aa.T (.sort u) →
        ma.HasType aa →
        LRD.Adequate Γ₀ Γ ρ A A (.sort u) ma aa := by
      intro ρ n' ma aa hA hSort hma
      exact (restartDirect depth hdepth hA.witness)
        .rfl hAty hma hSort.witness
    have ihBody : ∀ {ρ : Valuation} {n' : Nat} {mb ab : WShape n'},
        LE_Interp ρ mb.T body → LE_Interp ρ ab.T (.sort v) →
        mb.HasType ab →
        LRD.Adequate Γ₀ (A :: Γ) ρ body body (.sort v) mb ab := by
      intro ρ n' mb ab hBody hSort hmb
      exact (restartDirect depth hdepth hBody.witness)
        .rfl hbodyty hmb hSort.witness
    exact LRD.Adequate.forallESelf hAty.strong hbodyty.strong
      hX'.toInterp hB.toInterp htyped ihA ihBody
      legacyAdequate
  | @defeq Γ A B u depth e hEq hAty hBty heTy
      ihA ihB ihe =>
    have hdepth : depth < depth + 1 := Nat.lt_succ_self depth
    have ihA' : ∀ {ρ : Valuation} {n' : Nat} {ma sa : WShape n'},
        LE_Interp ρ ma.T A → LE_Interp ρ sa.T (.sort u) →
        ma.HasType sa → LRD.Adequate Γ₀ Γ ρ A A (.sort u) ma sa := by
      intro ρ n' ma sa hA hSort hma
      exact (restartDirect depth hdepth hA.witness)
        .rfl hAty hma hSort.witness
    have ihB' : ∀ {ρ : Valuation} {n' : Nat} {mb sb : WShape n'},
        LE_Interp ρ mb.T B → LE_Interp ρ sb.T (.sort u) →
        mb.HasType sb → LRD.Adequate Γ₀ Γ ρ B B (.sort u) mb sb := by
      intro ρ n' mb sb hB hSort hmb
      exact (restartDirect depth hdepth hB.witness)
        .rfl hBty hmb hSort.witness
    have ihe' : ∀ {ρ : Valuation} {n' : Nat} {me ae : WShape n'},
        LE_Interp ρ me.T e → LE_Interp ρ ae.T A →
        me.HasType ae → LRD.Adequate Γ₀ Γ ρ e e A me ae := by
      intro ρ n' me ae he hA hme
      exact (restartDirect depth hdepth he.witness)
        .rfl heTy hme hA.witness
    exact defeqStep hdepth hAty hEq hX'.toInterp hB.toInterp htyped
      ihA' ihB' ihe'

/--
info: 'Lean4Lean.SExpr.LRD.CoherentRetainedAt.restart' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.CoherentRetainedAt.restart

/--
info: 'Lean4Lean.SExpr.LRD.selfAdequateAtStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.selfAdequateAtStep

/-- The guarded restart together with the exact rebuilt evaluator tree used
to justify it. -/
theorem LR.CoherentRetainedAt.restartWithTree
    (lower : ∀ (d' : Nat), d' < outerDepth →
      ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
        hX.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
        LR.CoherentRetainedAt Γ₀ hX d')
    (hdepth : depth < outerDepth)
    (hX : LE_Interp.Witness ρ root X) :
    LR.CoherentRetainedAt Γ₀ hX depth ∧
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) := by
  let children : hX.RDeepChildren
      (LR.CoherentSeedAt Γ₀ depth) :=
    LR.CoherentSeedAt.rebuild
      (seed := fun hX children => lower depth hdepth hX children)
  exact ⟨lower depth hdepth hX children, children⟩

/-- THE DEPTH DISCHARGE.  The type rung follows from the *coherent* strict
predecessor family that `LR.CoherentFixedHeadStep` already carries — no
`LR.AdequacyAtDepth` at any rung, and nothing manufactured inside the
induction.

Two facts make this work, and both are specific to this obligation.

* The demand sits at `depth - 1` (`HasTypeStratifiedS.isType`), so it is a
  strict predecessor exactly when `0 < depth`; `LR.CoherentRetainedAt.restart`
  then supplies a completed rung at an **arbitrary** witness, rebuilding the
  evaluator tree itself (`LR.CoherentSeedAt.rebuild`).  The witness needed
  here — the registered type's own interpretation — is not a child of the
  fixed head's witness, so the `children` tree could not have supplied it;
  the guarded restart is what makes an unrelated witness admissible.
* The conclusion is **homogeneous** (`TyDefEq headType headType headElemTy`),
  and `LR.CoherentRetainedAt` carries exactly homogeneous self-adequacy.
  This is precisely why the same move does *not* discharge
  `LR.SelfAdequateDefeqStepAt`, whose conversion callback needs
  `LR.Adequate Γ₀ Γ ρ A B (.sort u) ma sa` with two *different* endpoints. -/
theorem LR.FixedHeadTypeValidStep.of_lowerCoherent
    {depth : Nat} (hdepth : 0 < depth)
    (lower : ∀ (d' : Nat), d' < depth → ∀ {ρ root X}
      (hX' : LE_Interp.Witness ρ root X),
      hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
      LR.CoherentRetainedAt Γ₀ hX' d') :
    LR.FixedHeadTypeValidStep Γ₀ depth := by
  intro Δ ρ σ σ' X headType core n headElem headElemTy W hstrat
    hTypeClosed htyped hTy
  obtain ⟨u, hTypeStrat⟩ := hstrat.isType
  have hTypeStrong : IsDefEqStrong Δ headType headType (.sort u) :=
    hTypeStrat.strong
  obtain ⟨n', typeElem, sortElem, le_n, le_type,
      hTypeInterp, hSortInterp, hTypeTyped⟩ :=
    (LE_Interp.sound hTypeStrong W.left.fits).2 hTy.toInterp |>.out
  have hselfTy : LR.SelfAdequateAt Γ₀ hTypeInterp.witness (depth - 1) :=
    (LR.CoherentRetainedAt.restart lower
      (Nat.sub_lt hdepth Nat.one_pos) (hX := hTypeInterp.witness)).1
  have hTypeAdequate :=
    (hselfTy .rfl hTypeStrat hTypeTyped hSortInterp.witness).2 W.left
  simp only [SExpr.subst] at hTypeAdequate
  rw [hTypeClosed.subst_eq .zero] at hTypeAdequate
  exact LR.toValTy le_n le_type htyped.isType
    hSortInterp hTypeTyped hTypeAdequate

/-- The depth-zero rung, where `of_lowerCoherent`'s strict decrease is
unavailable, is nevertheless free.

Every `HasTypeStratifiedS` constructor except `sort'` and `base` carries the
index `n + 1`, so a depth-`0` certificate forces the subject to be a sort and
its displayed type to be the successor sort.  That case needs no adequacy at
all: the fixed-head displayed type is then a sort, and its validity at the
observation is the `sort_iff` / `bot` split already used by the `sort'` case
of `LR.selfAdequateExactAtStep`. -/
theorem LR.FixedHeadTypeValidStep.zero : LR.FixedHeadTypeValidStep Γ₀ 0 := by
  intro Δ ρ σ σ' X headType core n headElem headElemTy W hstrat
    hTypeClosed htyped hTy
  obtain ⟨u, hTypeStrat⟩ := hstrat.isType
  have hTypeStrong : IsDefEqStrong Δ headType headType (.sort u) :=
    hTypeStrat.strong
  obtain ⟨n', typeElem, sortElem, le_n, le_type,
      hTypeInterp, hSortInterp, hTypeTyped⟩ :=
    (LE_Interp.sound hTypeStrong W.left.fits).2 hTy.toInterp |>.out
  refine LR.toValTy le_n le_type htyped.isType hSortInterp hTypeTyped ?_
  have hsort : ∃ l : SLevel, headType = .sort l.succ := by
    cases hstrat with
    | sort' => exact ⟨_, rfl⟩
    | base h => cases h with | sort' => exact ⟨_, rfl⟩
  obtain ⟨l, rfl⟩ := hsort
  cases hTypeTyped.unfold with
  | bot hm => exact (LR _).bot hm
  | sort => exact (LR _).sort_iff.2 ⟨_, .rfl, .rfl⟩
  | _ =>
    obtain h | h := WShape.le_sort.1 hTypeInterp.le_sort'
    · dsimp only at h
      rw [h]
      exact (LR _).bot hTypeTyped.isType
    · simp [WShape.ext_iff, WShape.forallE, WShape.sort, Shape.sort,
        WShape.lam', WShape.lam, WShape.bot, WShape.ctor, WShape.indTy,
        Shape.bot] at h <;>
        first
        | split at h <;> simp_all only [reduceCtorEq]
        | simp_all

/-- The whole family at one rung, from the coherent predecessor family alone.
This is what `LR.CoherentFixedHeadStep.of_convertStep` consumes, and it is why
`∀ depth, LR.FixedHeadTypeValidStep Γ₀ depth` is no longer an obligation. -/
theorem LR.FixedHeadTypeValidStep.of_coherentLower
    {depth : Nat}
    (lower : ∀ (d' : Nat), d' < depth → ∀ {ρ root X}
      (hX' : LE_Interp.Witness ρ root X),
      hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
      LR.CoherentRetainedAt Γ₀ hX' d') :
    LR.FixedHeadTypeValidStep Γ₀ depth := by
  rcases Nat.eq_zero_or_pos depth with rfl | hdepth
  · exact LR.FixedHeadTypeValidStep.zero
  · exact LR.FixedHeadTypeValidStep.of_lowerCoherent hdepth lower

/-- Rebuild a transportable semantic-typing tree from an inspectable local
seed constructor.  The transport closure is introduced only after the
underlying witness has obtained a canonical `CoherentSeedAt` tree. -/
theorem LR.CoherentProvenanceAt.rebuild
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth)
    {hX : LE_Interp.Witness ρ root X} :
    hX.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) :=
  LE_Interp.Witness.RDeepChildren.of_step
    (P := LR.CoherentProvenanceAt Γ₀ depth)
    (fun hX _children => LR.CoherentProvenanceAt.local <|
      seed hX (LR.CoherentSeedAt.rebuild seed)) hX

/-- Rebuild a freshly selected conversion endpoint while retaining every
focused action trace exposed by the source tree.

The endpoint witness and its retained result are still selected locally by
the guarded `seed`.  Each new recursive edge receives the whole source trace
bundle, so transport does not guess which registered rule a later fixed-head
consumer will request.  The bundle restores only proof-relevant origins; it
neither reuses a foreign witness nor promotes the local result to the
all-depth branch. -/
private theorem LR.CoherentProvenanceAt.rebuildTracingFocused
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth)
    {hSource : LE_Interp.Witness ρSource sourceRoot sourceX}
    (source : hSource.RDeepChildren
      (LR.CoherentProvenanceAt Γ₀ depth))
    {hX : LE_Interp.Witness ρ root X} :
    hX.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) := by
  classical
  let bundle : LR.FocusedRhsTraceBundleAt Γ₀ depth :=
    LR.FocusedTraceInRDeepAt.bundle source
  apply LE_Interp.Witness.RDeepChildren.of_step
    (P := LR.CoherentProvenanceAt Γ₀ depth)
  intro ρ' root' X' hX' _children
  let retained : LR.CoherentRetainedAt Γ₀ hX' depth :=
    seed hX' (LR.CoherentSeedAt.rebuild seed)
  by_cases current : bundle.contains X'
  · exact .base (.replayed bundle current retained)
  · exact .base (.carried bundle retained)

/-- Rebuild a converted endpoint while tagging exactly the lowerings of one
focused iota head witness with their action-indexed origin.

The structural traversal still computes every local retained result through
the guarded `seed`.  At an abstract evaluator edge it additionally checks
whether the reached proof-relevant witness is literally a realization of the
focused preimage's `LowerEdge`.  Only that witness receives `.focused`; all
other children receive the ordinary local injection. -/
theorem LR.CoherentProvenanceAt.rebuildFocused
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth)
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r}
    {Gamma : List SExpr} {e : SExpr} {ls : List SLevel}
    {capture : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {A : SExpr} {rho : Valuation} {rhsRoot : TShape}
    {action : Pattern.Action Gamma r e ls capture A}
    {rhsWitness : LE_Interp.Witness rho rhsRoot
      (r.1.applyS ls capture)} {rhsDepth : Nat}
    (preimage : rule.FocusedActionPreimage action rhsWitness rhsDepth)
    {root : TShape} {X : SExpr}
    (hX : LE_Interp.Witness rho root X) :
    hX.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) := by
  apply LE_Interp.Witness.RDeepChildren.of_step
    (P := LR.CoherentProvenanceAt Γ₀ depth)
  intro rho' root' X' hX' _children
  let retained : LR.CoherentRetainedAt Γ₀ hX' depth :=
    seed hX' (LR.CoherentSeedAt.rebuild seed)
  by_cases hρ : rho' = rho
  · subst rho'
    by_cases hEdge : ∃ edge : preimage.headWitness.LowerEdge root' X',
        hX' = edge.realize
    · obtain ⟨edge, realizes⟩ := hEdge
      exact .base (.focused ⟨{
        recName := rec
        ctorName := ctor
        major := major
        arity := arity
        r := r
        rule := rule
        Gamma := Gamma
        e := e
        ls := ls
        capture := capture
        A := A
        action := action
        rhsRoot := rhsRoot
        rhsWitness := rhsWitness
        rhsDepth := rhsDepth
        preimage := preimage
        edge := edge
        realizes := realizes
        retained := retained }⟩)
    · exact .base (.ordinary (.inr retained))
  · exact .base (.ordinary (.inr retained))

/-- Lowering the observed root preserves depth-indexed self-adequacy; the
selected evaluator tree and displayed type witness are unchanged. -/
theorem LR.SelfAdequateAt.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LR.SelfAdequateAt Γ₀ hX depth) :
    LR.SelfAdequateAt Γ₀ (hX.mono hle) depth := by
  intro n mx bx Δ core B hroot hTyping htyped hB
  exact H (hroot.trans hle) hTyping htyped hB

/-- A result constructed at a larger stratification depth also handles every
smaller depth: raise the caller's typing certificate before consuming it. -/
theorem LR.SelfAdequateAt.of_le
    (hdepth : depth ≤ outerDepth)
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.SelfAdequateAt Γ₀ hX outerDepth) :
    LR.SelfAdequateAt Γ₀ hX depth := by
  intro n mx bx Δ core B hroot hTyping htyped hB
  exact H hroot (hTyping.mono hdepth) htyped hB

/-- Root lowering preserves guarded self-adequacy. -/
theorem LRD.SelfAdequateAt.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LRD.SelfAdequateAt Γ₀ hX depth) :
    LRD.SelfAdequateAt Γ₀ (hX.mono hle) depth := by
  intro n mx bx Δ core B hroot hTyping htyped hB
  exact H (hroot.trans hle) hTyping htyped hB

/-- A guarded result constructed at a larger syntax depth consumes every
smaller typing certificate. -/
theorem LRD.SelfAdequateAt.of_le
    (hdepth : depth ≤ outerDepth)
    {hX : LE_Interp.Witness ρ root X}
    (H : LRD.SelfAdequateAt Γ₀ hX outerDepth) :
    LRD.SelfAdequateAt Γ₀ hX depth := by
  intro n mx bx Δ core B hroot hTyping htyped hB
  exact H hroot (hTyping.mono hdepth) htyped hB

/-- Root lowering preserves the direct type package. -/
theorem LR.DirectSelfTypeAt.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LR.DirectSelfTypeAt Γ₀ hX depth) :
    LR.DirectSelfTypeAt Γ₀ (hX.mono hle) depth := by
  intro n mx Δ u hroot hTyping htyped σ σ' W
  exact H (hroot.trans hle) hTyping htyped W

/-- A direct type package at a larger syntax depth consumes every smaller
typing certificate. -/
theorem LR.DirectSelfTypeAt.of_le
    (hdepth : depth ≤ outerDepth)
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.DirectSelfTypeAt Γ₀ hX outerDepth) :
    LR.DirectSelfTypeAt Γ₀ hX depth := by
  intro n mx Δ u hroot hTyping htyped σ σ' W
  exact H hroot (hTyping.mono hdepth) htyped W

/-- Fixed-head validity is contravariant in its explicit typing-depth index.
Only the stratification premise changes; the generated application result is
independent of which enlarged certificate discharged it. -/
theorem LR.FixedHeadResultAt.of_le
    (hdepth : depth ≤ outerDepth)
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.FixedHeadResultAt Γ₀ hX outerDepth) :
    LR.FixedHeadResultAt Γ₀ hX depth := by
  intro Δ σ σ' W n rec ctor major arity recLs mrec mctor r rule out head
    headTy mx my captureType A outTy hsyntax hhead hstrong hstrat hshape
    htel hTyReg hspineX hspineY hcap hout hA
  exact H W hsyntax hhead hstrong (hstrat.mono hdepth) hshape htel hTyReg
    hspineX hspineY hcap hout hA

/-- Lower the depth of both halves of the coherent retained package. -/
theorem LR.CoherentRetainedAt.of_le
    (hdepth : depth ≤ outerDepth)
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentRetainedAt Γ₀ hX outerDepth) :
    LR.CoherentRetainedAt Γ₀ hX depth :=
  ⟨LR.SelfAdequateAt.of_le (hX := hX) hdepth H.1,
    LR.FixedHeadResultAt.of_le (hX := hX) hdepth H.2⟩

/-- Lower a seed's usable depth without changing its provenance class.
Genuine evaluator children remain all-depth; rebuilt children remain local. -/
theorem LR.CoherentSeedAt.of_le
    (hdepth : depth ≤ outerDepth)
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentSeedAt Γ₀ outerDepth hX) :
    LR.CoherentSeedAt Γ₀ depth hX := by
  cases H with
  | inl H => exact .inl H
  | inr H => exact .inr (LR.CoherentRetainedAt.of_le hdepth H)

/-- Bottom observations are self-adequate at every syntax depth. -/
theorem LR.SelfAdequateAt.bot
    {nroot : Nat} {X : SExpr} (depth : Nat) :
    LR.SelfAdequateAt Γ₀
      (LE_Interp.Witness.bot (ρ := ρ) (n := nroot) (M := X)) depth := by
  intro n mx bx Δ core B hroot _hTyping htyped _hB
  have hmxBot : mx.T ≤ TShape.bot :=
    hroot.trans TShape.bot_eqv.1
  have hmx : mx = .bot := TShape.le_bot.1 hmxBot
  subst mx
  exact LR.Adequate.bot htyped.isType

/-- The coherent package is stable under root lowering, one of the primitive
operations recorded by `TransportClosure`. -/
theorem LR.CoherentRetainedResult.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LR.CoherentRetainedResult Γ₀ hX) :
    LR.CoherentRetainedResult Γ₀ (hX.mono hle) := by
  intro depth
  have hself : LR.SelfAdequateAt Γ₀ hX depth := (H depth).1
  have hfixed : LR.FixedHeadResultAt Γ₀ hX depth := (H depth).2
  exact ⟨LR.SelfAdequateAt.mono (hX := hX) hle hself,
    LR.FixedHeadResultAt.mono (hX := hX) hle hfixed⟩

/-- Root lowering preserves both halves of a coherent result at one depth. -/
theorem LR.CoherentRetainedAt.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LR.CoherentRetainedAt Γ₀ hX depth) :
    LR.CoherentRetainedAt Γ₀ (hX.mono hle) depth :=
  ⟨LR.SelfAdequateAt.mono (hX := hX) hle H.1,
    LR.FixedHeadResultAt.mono (hX := hX) hle H.2⟩

/-- Root lowering preserves both the established coherent package and its
guarded self-adequacy sidecar. -/
theorem LRD.CoherentRetainedAt.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LRD.CoherentRetainedAt Γ₀ hX depth) :
    LRD.CoherentRetainedAt Γ₀ (hX.mono hle) depth :=
  ⟨LR.CoherentRetainedAt.mono (hX := hX) hle H.1,
    LRD.SelfAdequateAt.mono (hX := hX) hle H.2⟩

/-- Lower both components of a guarded coherent package to a smaller syntax
depth. -/
theorem LRD.CoherentRetainedAt.of_le
    (hdepth : depth ≤ outerDepth)
    {hX : LE_Interp.Witness ρ root X}
    (H : LRD.CoherentRetainedAt Γ₀ hX outerDepth) :
    LRD.CoherentRetainedAt Γ₀ hX depth :=
  ⟨LR.CoherentRetainedAt.of_le (hX := hX) hdepth H.1,
    LRD.SelfAdequateAt.of_le (hX := hX) hdepth H.2⟩

/-- Root lowering preserves an all-depth guarded coherent result. -/
theorem LRD.CoherentRetainedResult.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LRD.CoherentRetainedResult Γ₀ hX) :
    LRD.CoherentRetainedResult Γ₀ (hX.mono hle) :=
  fun depth => LRD.CoherentRetainedAt.mono (hX := hX) hle (H depth)

/-- Root lowering preserves the direct seed's provenance class. -/
theorem LRD.CoherentSeedAt.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LRD.CoherentSeedAt Γ₀ depth hX) :
    LRD.CoherentSeedAt Γ₀ depth (hX.mono hle) := by
  cases H with
  | inl hall => exact .inl (LRD.CoherentRetainedResult.mono hle hall)
  | inr hlocal => exact .inr (LRD.CoherentRetainedAt.mono hle hlocal)

/-- Lowering the selected RHS observation preserves its coupled provenance
and local typing budget. -/
theorem LR.CoherentRhsSeedAt.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LR.CoherentRhsSeedAt Γ₀ Δ depth hX B) :
    LR.CoherentRhsSeedAt Γ₀ Δ depth (hX.mono hle) B := by
  cases H with
  | inl H => exact .inl (LR.CoherentRetainedResult.mono hle H)
  | inr H => exact .inr ⟨LR.CoherentRetainedAt.mono hle H.1, H.2⟩

/-- Couple an inspectable evaluator seed with the exact RHS typing
certificate available at this conversion depth.

The genuine-child branch keeps its all-depth result and does not depend on
the certificate.  The rebuilt branch records the certificate alongside the
local result, which is precisely the asymmetric contract consumed by the
coherent iota leaf. -/
theorem LR.CoherentRhsSeedAt.of_seed
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentSeedAt Γ₀ depth hX)
    (hstrat : HasTypeStratifiedS Δ X B true depth) :
    LR.CoherentRhsSeedAt Γ₀ Δ depth hX B := by
  cases H with
  | inl H => exact .inl H
  | inr H => exact .inr ⟨H, hstrat⟩

/-- A focused evaluator edge preserves the coupled RHS package by literal
root lowering of its generating witness. -/
theorem LR.CoherentRhsSeedAt.of_lowerEdge
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentRhsSeedAt Γ₀ Δ depth hX B)
    (edge : hX.LowerEdge m M) :
    LR.CoherentRhsSeedAt Γ₀ Δ depth edge.realize B := by
  obtain ⟨rfl, hle⟩ := edge
  exact LR.CoherentRhsSeedAt.mono (hX := hX) hle H

/-- Root lowering preserves whether an evaluator edge carries the genuine
all-depth result or only the result at the current guarded restart depth.

Keeping the injection unchanged is important: lowering an exact witness is
a structural transport and must not promote a local seed to the all-depth
side reserved for genuine outer-recursion children. -/
theorem LR.CoherentSeedAt.mono
    (hle : root ≤ root')
    {hX : LE_Interp.Witness ρ root' X}
    (H : LR.CoherentSeedAt Γ₀ depth hX) :
    LR.CoherentSeedAt Γ₀ depth (hX.mono hle) := by
  cases H with
  | inl H =>
    exact .inl (LR.CoherentRetainedResult.mono
      (hX := hX) hle H)
  | inr H =>
    exact .inr (LR.CoherentRetainedAt.mono (hX := hX) hle H)

/-- Coherent base case corresponding to `TransportClosure.bot`. -/
theorem LR.CoherentRetainedResult.bot
    {nroot : Nat} {X : SExpr} :
    LR.CoherentRetainedResult Γ₀
      (LE_Interp.Witness.bot (ρ := ρ) (n := nroot) (M := X)) := by
  intro depth
  have hfixed : LR.FixedHeadResult Γ₀
      (LE_Interp.Witness.bot (ρ := ρ) (n := nroot) (M := X)) :=
    LR.FixedHeadResult.bot
  exact ⟨LR.SelfAdequateAt.bot depth,
    LR.FixedHeadResult.at
      (hX := LE_Interp.Witness.bot (ρ := ρ) (n := nroot) (M := X))
      hfixed depth⟩

/-- The evaluator-coherent consumer algebra.

This is the sole producer contract for the repaired recursion: genuine
semantic children carry the full depth-polymorphic result, while witnesses
created later by root/valuation/closed transport or compatible join carry a
free `TransportClosure` proof instead of an unjustified consumer result. -/
def LR.CoherentRetainedStep (Γ₀ : List SExpr) : Prop :=
  ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
    hX.RDeepChildren
      (LE_Interp.Witness.TransportClosure
        (LR.CoherentRetainedResult Γ₀)) →
    LR.CoherentRetainedResult Γ₀ hX

/-- The executable evaluator-coherent algebra, with the Nat decrease exposed
at the point where syntax recursion may select another witness.

Unlike `CoherentRetainedStep`, a lower-depth restart is not global: the new
witness must carry a complete `CoherentSeedAt` tree.  Every local seed in
that tree is attached only after structural descent through the selected
witness and remains pinned to the smaller Nat index.  This is the
proof-relevant side condition that rules out the old “lower depth, restart
anywhere” cycle while still admitting witnesses selected by conversion. -/
def LR.CoherentRetainedNatStep (Γ₀ : List SExpr) : Prop :=
  ∀ (depth : Nat) {ρ root X}
      (hX : LE_Interp.Witness ρ root X),
    hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
    (∀ (d' : Nat), d' < depth →
      ∀ {ρ root X} (hX' : LE_Interp.Witness ρ root X),
        hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
        LR.CoherentRetainedAt Γ₀ hX' d') →
    LR.CoherentRetainedAt Γ₀ hX depth

/-- Self-adequacy half of the provenance-checked Nat algebra. -/
def LR.CoherentSelfStep (Γ₀ : List SExpr) : Prop :=
  ∀ (depth : Nat) {ρ root X}
      (hX : LE_Interp.Witness ρ root X),
    hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
    (∀ (d' : Nat), d' < depth →
      ∀ {ρ root X} (hX' : LE_Interp.Witness ρ root X),
        hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
        LR.CoherentRetainedAt Γ₀ hX' d') →
    LR.SelfAdequateAt Γ₀ hX depth

/-- Fixed-head half of the provenance-checked Nat algebra.  It receives the
self-adequacy result constructed at the same witness and depth, so the
ordered telescope never has to recover that fact from a transported child. -/
def LR.CoherentFixedHeadStep (Γ₀ : List SExpr) : Prop :=
  ∀ (depth : Nat) {ρ root X}
      (hX : LE_Interp.Witness ρ root X),
    LR.SelfAdequateAt Γ₀ hX depth →
    hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
    (∀ (d' : Nat), d' < depth →
      ∀ {ρ root X} (hX' : LE_Interp.Witness ρ root X),
        hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
        LR.CoherentRetainedAt Γ₀ hX' d') →
    LR.FixedHeadResultAt Γ₀ hX depth

/-- Assemble the two consumer-specific algebras without hiding either
well-founded input. -/
theorem LR.CoherentRetainedNatStep.of_steps
    (selfStep : LR.CoherentSelfStep Γ₀)
    (fixedStep : LR.CoherentFixedHeadStep Γ₀) :
    LR.CoherentRetainedNatStep Γ₀ := by
  intro depth ρ root X hX children lower
  have hself : LR.SelfAdequateAt Γ₀ hX depth :=
    selfStep depth hX children lower
  exact ⟨hself, fixedStep depth hX hself children lower⟩

/-- THE FIXED-HEAD HALF OF THE COHERENT NAT ALGEBRA.

Neither the seed tree nor the strict predecessor family is consumed.  Once the
N2 premise change hands the step its ordered capture telescope together with
the registered type's own witness at one index, the fixed-head half is a pure
fold: its only semantic inputs are the self-adequacy result supplied at the
same witness and the same depth by `LR.CoherentRetainedNatStep.of_steps`, and
the two named obligations below.  The redundant existential capture family is
never opened — the telescope already carries every capture at its own shapes,
which is exactly what the N2 decision was for.

Both closedness facts are free, and neither needs a new field on
`Pattern.IotaRule`.  The generated RHS is closed by `rhsClosed`; the
*registered type* is closed by `Params.henv.closed`, i.e. by the environment's
own ordering invariant.  The `typeClosed` field the previous port recorded as
missing is not needed after all.

The bottom observation is discharged before any of that, exactly as in
`LR.FixedHeadResult.bot`: a bottom result shape forces `out = .bot`. -/
theorem LR.CoherentFixedHeadStep.of_steps
    (convert : LR.FixedHeadConvertStep Γ₀)
    (typeValid : ∀ depth, LR.FixedHeadTypeValidStep Γ₀ depth) :
    LR.CoherentFixedHeadStep Γ₀ := by
  intro depth ρ root X hX hself _children _lower
  intro Δ σ σ' W n rec ctor major arity recLs mrec mctor r rule out head
    headTy mx my captureType A outTy hsyntax hhead _hstrong hstrat hshape
    htel hTyReg hspineX _hspineY _hcap hout hA
  subst hsyntax
  by_cases hbot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 hbot
    subst houtEq
    exact (LR Γ₀).bot hout.isType
  · exact LR.FixedHeadApplication.applyRule (hX := hX)
      (htel.toApplicationWithSelfAdequacy (hX := hX) hTyReg hbot hspineX hA
        convert hself (typeValid depth) hhead hstrat W
        rule.rhsClosed.mkInstS (rule.typeClosed recLs))

/-- THE FIXED-HEAD HALF, with the type rung discharged rather than assumed.

Identical to `of_steps` except that the `typeValid` family is no longer a
hypothesis: `LR.FixedHeadTypeValidStep.of_coherentLower` builds the instance
needed at this rung out of `lower`, the step's own strict predecessor family.
`of_steps` is kept unchanged as the reference statement (the treatment
`LR.FixedHeadTelescope.toApplicationWithAdequacyAtDepth` and
`LR.ConstDefnLocalStep` also received).

G4: `lower` arrives through the step interface — `LR.CoherentRetainedNatStep`
hands it over from `recRDeepNatProvenance` — and is consumed only through the
sanctioned guarded restart `LR.CoherentRetainedAt.restart`, exactly as
`LR.selfAdequateExactAtStep` already consumes it.  Nothing predecessor-shaped
is manufactured inside the induction, and no index a consumer fixed is
re-chosen. -/
theorem LR.CoherentFixedHeadStep.of_convertStep
    (convert : LR.FixedHeadConvertStep Γ₀) :
    LR.CoherentFixedHeadStep Γ₀ := by
  intro depth ρ root X hX hself _children lower
  intro Δ σ σ' W n rec ctor major arity recLs mrec mctor r rule out head
    headTy mx my captureType A outTy hsyntax hhead _hstrong hstrat hshape
    htel hTyReg hspineX _hspineY _hcap hout hA
  subst hsyntax
  by_cases hbot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 hbot
    subst houtEq
    exact (LR Γ₀).bot hout.isType
  · exact LR.FixedHeadApplication.applyRule (hX := hX)
      (htel.toApplicationWithSelfAdequacy (hX := hX) hTyReg hbot hspineX hA
        convert hself (LR.FixedHeadTypeValidStep.of_coherentLower lower)
        hhead hstrat W
        rule.rhsClosed.mkInstS (rule.typeClosed recLs))

/-- Close the semantic fixed point from one provenance-sensitive algebra.
No typing-depth index is fixed before following an evaluator `R` edge. -/
theorem LR.coherentRetainedResult_of_step
    (step : LR.CoherentRetainedStep Γ₀)
    {ρ root X} (hX : LE_Interp.Witness ρ root X) :
    LR.CoherentRetainedResult Γ₀ hX :=
  hX.recRDeepTransport step

/-- Close the coherent result from the provenance-checked Nat algebra.
Semantic `R` descent supplies every depth; arbitrary witness changes are
available only at a strict Nat decrease and with their transport certificate
still attached. -/
theorem LR.coherentRetainedResult_of_natStep
    (step : LR.CoherentRetainedNatStep Γ₀)
    {ρ root X} (hX : LE_Interp.Witness ρ root X) :
    LR.CoherentRetainedResult Γ₀ hX := by
  exact hX.recRDeepNatProvenance
    (Q := fun hX depth => LR.CoherentRetainedAt Γ₀ hX depth)
    step

/-- Guarded semantic-first/Nat-second algebra.  Actual evaluator edges carry
the all-depth `LRD` result; only arbitrary-witness restarts at a strict syntax
decrease may carry a local result. -/
def LRD.CoherentRetainedNatStep (Γ₀ : List SExpr) : Prop :=
  ∀ (depth : Nat) {ρ root X}
      (hX : LE_Interp.Witness ρ root X),
    hX.RDeepChildren (LRD.CoherentSeedAt Γ₀ depth) →
    (∀ (d' : Nat), d' < depth →
      ∀ {ρ root X} (hX' : LE_Interp.Witness ρ root X),
        hX'.RDeepChildren (LRD.CoherentSeedAt Γ₀ d') →
        LRD.CoherentRetainedAt Γ₀ hX' d') →
    LRD.CoherentRetainedAt Γ₀ hX depth

/-- Assemble one exact guarded rung from the completed legacy coherent
algebra and the two genuinely new direct callbacks.

The guarded package now follows the same semantic-first/Nat-second recursion
as the legacy package.  Consequently actual evaluator children receive the
all-depth branch of `LRD.CoherentSeedAt`; strong Nat descent is still the only
way to restart an arbitrary witness, and such a restart remains local. -/
theorem LRD.coherentRetainedAt_of_steps
    (legacyStep : LR.CoherentRetainedNatStep Γ₀)
    (defeqStep : ∀ depth, LRD.SelfAdequateDefeqStepAt Γ₀ depth)
    (constStep : LRD.SelfAdequateConstStep Γ₀)
    (depth : Nat) {ρ root X}
    (hX : LE_Interp.Witness ρ root X) :
    LRD.CoherentRetainedAt Γ₀ hX depth := by
  let step : LRD.CoherentRetainedNatStep Γ₀ := by
    intro depth ρ root X hY children lower
    have legacyResult : LR.CoherentRetainedResult Γ₀ hY :=
      LR.coherentRetainedResult_of_natStep legacyStep hY
    have hlegacy : LR.CoherentRetainedAt Γ₀ hY depth :=
      legacyResult depth
    exact ⟨hlegacy,
      LRD.selfAdequateAtStep depth (defeqStep depth) constStep
        hY children hlegacy.1 lower⟩
  exact hX.recRDeepNatProvenance
    (Q := fun hX depth => LRD.CoherentRetainedAt Γ₀ hX depth)
    step depth

/-- Close the all-depth guarded result without changing the established
evaluator seed recursion. -/
theorem LRD.coherentRetainedResult_of_steps
    (legacyStep : LR.CoherentRetainedNatStep Γ₀)
    (defeqStep : ∀ depth, LRD.SelfAdequateDefeqStepAt Γ₀ depth)
    (constStep : LRD.SelfAdequateConstStep Γ₀)
    {ρ root X} (hX : LE_Interp.Witness ρ root X) :
    LRD.CoherentRetainedResult Γ₀ hX :=
  fun depth => LRD.coherentRetainedAt_of_steps
    legacyStep defeqStep constStep depth hX

/--
info: 'Lean4Lean.SExpr.LRD.coherentRetainedAt_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.coherentRetainedAt_of_steps

/--
info: 'Lean4Lean.SExpr.LRD.coherentRetainedResult_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.coherentRetainedResult_of_steps

/-- Forget the coherent construction after selecting its fixed-head half at
every stratification depth. -/
theorem LR.CoherentRetainedResult.fixedHead
    {hX : LE_Interp.Witness ρ root X}
    (H : LR.CoherentRetainedResult Γ₀ hX) :
    LR.FixedHeadResult Γ₀ hX := by
  apply LR.FixedHeadResult.of_forall_at
  exact fun depth => (H depth).2

/-- The exact iota leaf follows from the provenance-checked Nat algebra.

This is the formal statement of the residual gap at the abstract-evaluator
leaf: once `CoherentRetainedNatStep` is instantiated, every closed-valuation
witness carries the full coherent result, whose fixed-head half discharges
the generated RHS obligation of one native exact link through
`iotaDefEq_of_ctorExactAt_closedFixedHead`.

`producer` carries the caller's own result typing `out.HasType outTyP`; see
`iotaDefEq_of_ctorExactAt_fixedHead` for why the premise is required. -/
theorem LRS.iotaDefEq_of_ctorExactAt_natStep
    {n : Nat}
    {R : TShape → SExpr → Prop} {ρ : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs : List SExpr} {recLs : List SLevel}
    {majorX majorY recHeadType A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    {hwf : IsStruct ctor → WShape.ListNonZero ctorShapes.reverse}
    (step : LR.CoherentRetainedNatStep Γ₀)
    (producer : ∀ (rule : Pattern.IotaRule r) {head : TShape}
      (mx my captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      {outTyP : WShape (n + 1)}
      (houtP : out.HasType outTyP)
      (hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T),
      LR.FixedHeadProducer Γ₀ Valuation.nil rule mx my captureType hshape
        (recLs := recLs) (outTy := outTyP))
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T r.1)
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (leaf : LRS.CtorExact Γ₀ (LR Γ₀) majorX majorY
      (.ctor ctor ctorShapes.reverse hwf))
    (hleaf : LR.PatternLeafSpine Γ₀ (LR Γ₀) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ctor ctorShapes.reverse hwf) :: recShapes) A out outTy)
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hout : out.HasType outTy)
    (hA : (LR Γ₀).TyDefEq A A outTy) :
    (LR Γ₀).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy :=
  LRS.iotaDefEq_of_ctorExactAt_closedFixedHead hΓ hpat hmf hma hrhs hR
    (fun hX =>
      (LR.coherentRetainedResult_of_natStep step hX).fixedHead)
    producer leaf hleaf hrecHead hout hA

/-- Close one exact constructor iota leaf from provenance-sensitive
fixed-head seeds at a single stratification depth.

Unlike `iotaDefEq_of_ctorExactAt_fixedHead`, this theorem does not erase a
local guarded restart into an all-depth result.  A genuine semantic child
chooses the registered RHS's native stratification depth from its all-depth
result.  Only a local child needs the RHS typing raised to the exact `depth`
carried by its right injection.

`producer` carries the caller's own result typing `out.HasType outTyP`; see
`iotaDefEq_of_ctorExactAt_fixedHead` for why the premise is required. -/
theorem LRS.iotaDefEq_of_ctorExactAt_coherent
    {n : Nat}
    {R : TShape → SExpr → Prop} {ρ : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs : List SExpr} {recLs : List SLevel}
    {majorX majorY recHeadType A : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {out outTy : WShape (n + 1)}
    {hwf : IsStruct ctor → WShape.ListNonZero ctorShapes.reverse}
    {Δ : List SExpr} {σ σ' : Subst} {depth : Nat}
    (W : LR.SubstWF Γ₀ σ σ' Δ ρ)
    (hΓ : Ctx.WF Γ₀)
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor)
    (hrhs : LE_Interp.RHS recLs (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T r.1)
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hP : ∀ (rule : Pattern.IotaRule r) {m}
      (hr : R m (SExpr.mkInst recLs rule.df.rhs)),
      LR.CoherentRhsSeedAt Γ₀ Δ depth (hR hr)
        (SExpr.mkInst recLs rule.df.type))
    (producer : ∀ (rule : Pattern.IotaRule r) {head : TShape}
      (mx my captureType :
        (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      {outTyP : WShape (n + 1)}
      (houtP : out.HasType outTyP)
      (hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T),
      LR.FixedHeadProducer Γ₀ ρ rule mx my captureType hshape
        (recLs := recLs) (outTy := outTyP))
    (leaf : LRS.CtorExact Γ₀ (LR Γ₀) majorX majorY
      (.ctor ctor ctorShapes.reverse hwf))
    (hleaf : LR.PatternLeafSpine Γ₀ (LR Γ₀) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ctor ctorShapes.reverse hwf) :: recShapes) A out outTy)
    (hrecHead : Γ₀ ⊢ .const rec recLs : recHeadType)
    (hout : out.HasType outTy)
    (hA : (LR Γ₀).TyDefEq A A outTy) :
    (LR Γ₀).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const rec recLs)).app majorY)
      A out outTy := by
  apply LRS.iotaDefEq_of_ctorExactAt hΓ hpat hmf hma hrhs leaf hleaf
    hrecHead hout hA
  intro rule
  apply LRS.IotaRHSDefEq.of_nonbotWitnessResult
    (P := fun {ρ m M} (h : LE_Interp.Witness ρ m M) =>
      M = SExpr.mkInst recLs rule.df.rhs →
        LR.CoherentRhsSeedAt Γ₀ Δ depth h
          (SExpr.mkInst recLs rule.df.type)) hR
  · intro m M hr hM
    subst M
    exact hP rule hr
  · intro m m' M hle hM H hMrhs
    exact LR.CoherentRhsSeedAt.mono (hX := hM) hle (H hMrhs)
  · intro head mx my captureType A outTy hhead hseed _hstrong hshape
      _htyped hspineX hspineY hcap hout hA
    have hseed := hseed rfl
    have hstrong : IsDefEqStrong Δ
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) :=
      rule.rhsStrong recLs
    refine producer rule mx my captureType hout hshape (outTyP := outTy) ?_
    intro headTy htel hTyReg
    cases hseed with
    | inl hall =>
      obtain ⟨rhsDepth, hstrat, _⟩ := hstrong.stratify
      exact (hall rhsDepth).2 W rfl .rfl hstrong hstrat hshape htel hTyReg
        hspineX hspineY hcap hout hA
    | inr hlocal =>
      exact hlocal.1.2 W rfl .rfl hstrong hlocal.2 hshape
        htel hTyReg hspineX hspineY hcap hout hA

/-- Proof-relevant semantic transport for the one non-syntax-directed case
of stratified typing.  The output witness stays at the same shape and retains
the recursive-result tree selected before conversion. -/
def LE_Interp.Witness.DefeqRDeepTransport
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop)
    (Γ₀ : List SExpr) : Prop :=
  ∀ {Γ : List SExpr} {A B : SExpr} {u : SLevel}
      {ρ : Valuation} {a sortShape : TShape},
    IsDefEqStrong Γ A B (.sort u) →
    LE_Interp.Witness.FitsRDeep P Γ₀ Γ ρ →
    Valuation.Fits Γ₀ Γ ρ →
    ∀ (hA : LE_Interp.Witness ρ a A),
      LE_Interp.Witness ρ sortShape (.sort u) →
      a.HasType sortShape →
      hA.RDeepChildren P →
      ∃ hB : LE_Interp.Witness ρ a B, hB.RDeepChildren P

/-- Proof-relevant conversion transport with the exact endpoint
stratifications retained.

The unstratified `DefeqRDeepTransport` above remains a useful generic
isolation boundary, but it is too weak for a focused constant evaluator: a
reverse action must attach its newly created `R` edge to the particular RHS
typing derivation that justified the conversion.  This contract keeps both
endpoint derivations and their common depth in scope at that construction
point. -/
def LE_Interp.Witness.StratifiedDefeqRDeepTransport
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop)
    (Γ₀ : List SExpr) : Prop :=
  ∀ {Γ : List SExpr} {A B : SExpr} {u : SLevel} {depth : Nat}
      {ρ : Valuation} {a sortShape : TShape},
    IsDefEqStrong Γ A B (.sort u) →
    HasTypeStratifiedS Γ A (.sort u) true depth →
    HasTypeStratifiedS Γ B (.sort u) true depth →
    LE_Interp.Witness.FitsRDeep P Γ₀ Γ ρ →
    Valuation.Fits Γ₀ Γ ρ →
    ∀ (hA : LE_Interp.Witness ρ a A),
      LE_Interp.Witness ρ sortShape (.sort u) →
      a.HasType sortShape →
      hA.RDeepChildren P →
      ∃ hB : LE_Interp.Witness ρ a B, hB.RDeepChildren P

/-- Every proof-independent conversion transport is a derivation-aware one
that simply ignores the additional endpoint certificates.  The converse is
intentionally unavailable. -/
theorem LE_Interp.Witness.DefeqRDeepTransport.stratified
    (H : LE_Interp.Witness.DefeqRDeepTransport P Γ₀) :
    LE_Interp.Witness.StratifiedDefeqRDeepTransport P Γ₀ := by
  intro Γ A B u depth ρ a sortShape hEq _hA _hB W Wfits
    hA hSort htyped children
  exact H hEq W Wfits hA hSort htyped children

/-- Conversion transport when no consumer data is retained at evaluator
edges. -/
theorem LE_Interp.Witness.defeqRDeepTransport_true (Gamma0 : List SExpr) :
    LE_Interp.Witness.DefeqRDeepTransport (fun _ => True) Gamma0 := by
  intro Gamma A B u rho a sortShape hEq _W Wfits
    hA _hSort _htyped _children
  have hBpublic : LE_Interp rho a B :=
    (LE_Interp.sound hEq Wfits).1.1 hA.toInterp
  let hB : LE_Interp.Witness rho a B := hBpublic.witness
  exact ⟨hB, LE_Interp.Witness.RDeepChildren.trivial hB⟩

/-- Proof-relevant reverse transport for one concrete generated iota
action at an already-typed semantic observation.

The exact RHS witness is peeled before the redex is rebuilt.  Consequently
the new constant node stores only root lowerings of the literal registered
head witness.  Recursive provenance is attached afterward through the
caller's depth-local seed constructor, so this theorem neither assumes nor
manufactures a same-depth result. -/
theorem LR.focusedIotaReverseRDeepAt
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth)
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r)
    {Gamma : List SExpr} {e : SExpr} {ls : List SLevel}
    {capture : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {A : SExpr} {rho : Valuation} {root : TShape}
    (action : Pattern.Action Gamma r e ls capture A)
    (hLeft : StrongSound Gamma e A)
    (Wfits : Valuation.Fits Γ₀ Gamma rho)
    (hRhs : LE_Interp.Witness rho root (r.1.applyS ls capture))
    (hRhsStratified : HasTypeStratifiedS Gamma
      (r.1.applyS ls capture) A true rhsDepth) :
    ∃ hLeft' : LE_Interp.Witness rho root e,
      hLeft'.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) := by
  by_cases hbot : root ≤ TShape.bot
  · rw [TShape.le_bot'.1 hbot]
    exact ⟨.bot, .bot⟩
  · let typed :=
      ((LE_Interp.sound hRhsStratified.strong Wfits).2
        hRhs.toInterp).outView
    have htypedNonbot : ¬typed.termShape.T ≤ TShape.bot := by
      intro hupper
      exact hbot (typed.root_le.trans hupper)
    let hRhs' : LE_Interp.Witness rho typed.termShape.T
        (r.1.applyS ls capture) := typed.termInterp.witness
    let view := Classical.choice <|
      rule.focusedActionPreimage action hLeft Wfits hRhs'
        hRhsStratified htypedNonbot
    let hLeftUpper := view.witness Wfits hLeft
      typed.typed.T typed.typeInterp.witness
    exact ⟨hLeftUpper.mono typed.root_le,
      (LR.CoherentProvenanceAt.rebuildFocused seed view hLeftUpper).mono
        typed.root_le⟩

/-- Reverse one proof-carrying local action while preserving the focused
evaluator edge of generated iota rules.

`Params.pat_simple` makes the only operational distinction needed here.
Definition patterns have no captured application spine, so the ordinary
guarded endpoint rebuild remains sufficient.  An iota pattern instead uses
`focusedIotaReverseRDeepAt`, retaining the literal fixed RHS head selected by
the source witness. -/
theorem LR.focusedExtraReverseRDeepAt
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth)
    {p : Pattern} {r : p.RHS × p.Check}
    {Γ : List SExpr} {e : SExpr} {ls : List SLevel}
    {capture : p.Path → SExpr} {A : SExpr}
    {ρ : Valuation} {root : TShape}
    (action : Pattern.Action Γ r e ls capture A)
    (hLeft : IsDefEqStrong Γ e e A)
    (hRight : IsDefEqStrong Γ (r.1.applyS ls capture)
      (r.1.applyS ls capture) A)
    (Wfits : Valuation.Fits Γ₀ Γ ρ)
    (hRhs : LE_Interp.Witness ρ root (r.1.applyS ls capture))
    (hRhsStratified : HasTypeStratifiedS Γ
      (r.1.applyS ls capture) A true rhsDepth) :
    ∃ hLeft' : LE_Interp.Witness ρ root e,
      hLeft'.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) := by
  obtain ⟨sp, hp⟩ := Params.pat_simple action.pat
  cases sp with
  | defn c =>
    have hLeftPublic : LE_Interp ρ root e :=
      (LE_Interp.sound (.extra action hLeft hRight) Wfits).1.2
        hRhs.toInterp
    let hLeft' : LE_Interp.Witness ρ root e := hLeftPublic.witness
    exact ⟨hLeft', LR.CoherentProvenanceAt.rebuild seed⟩
  | iota rec major ctor arity =>
    subst p
    exact LR.focusedIotaReverseRDeepAt seed
      (Params.Semantic.iotaRule action.pat) action
      (LE_Interp.strongSound hLeft).left Wfits hRhs
      hRhsStratified

/-- Guarded transport used for equality constructors that do not expose a
more precise structural action.

Both endpoint witnesses are selected at the caller's already-smaller local
depth.  Their trees are rebuilt from the endpoint's own evaluator structure,
while focused action traces present in the source tree are replayed only at
recursive edges with the same syntax.  This is intentionally a bidirectional
package so `symm` and `trans` can be interpreted structurally without losing
a nested iota action. -/
private theorem LR.coherentDefeqRDeepFallbackPairAt
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth)
    (hEq : IsDefEqStrong Γ A B T)
    (Wfits : Valuation.Fits Γ₀ Γ ρ) :
    (∀ (hA : LE_Interp.Witness ρ root A),
      hA.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) →
      ∃ hB : LE_Interp.Witness ρ root B,
        hB.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth)) ∧
    (∀ (hB : LE_Interp.Witness ρ root B),
      hB.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) →
      ∃ hA : LE_Interp.Witness ρ root A,
        hA.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth)) := by
  by_cases hsyntax : A = B
  · subst B
    exact ⟨fun hA children => ⟨hA, children⟩,
      fun hA children => ⟨hA, children⟩⟩
  · constructor
    · intro hA children
      have hBpublic : LE_Interp ρ root B :=
        (LE_Interp.sound hEq Wfits).1.1 hA.toInterp
      let hB : LE_Interp.Witness ρ root B := hBpublic.witness
      exact ⟨hB,
        LR.CoherentProvenanceAt.rebuildTracingFocused seed children⟩
    · intro hB children
      have hApublic : LE_Interp ρ root A :=
        (LE_Interp.sound hEq Wfits).1.2 hB.toInterp
      let hA : LE_Interp.Witness ρ root A := hApublic.witness
      exact ⟨hA,
        LR.CoherentProvenanceAt.rebuildTracingFocused seed children⟩

/-- Bidirectional, derivation-aware transport for displayed-type equality.

Symmetry swaps the two continuations and transitivity composes them.  This
ensures an iota action remains visible even when it is nested below either
constructor.  Syntax-directed application and binder constructors transport
their exact subtrees.  Remaining constructors use the guarded local rebuild,
which replays focused traces at matching recursive-edge syntax; the reverse
branch of `extra` additionally dispatches generated iota patterns to the
focused evaluator. -/
private theorem LR.coherentDefeqRDeepPairAt
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth)
    (hEq : IsDefEqStrong Γ A B T)
    (hAStratified : HasTypeStratifiedS Γ A T true leftDepth)
    (hBStratified : HasTypeStratifiedS Γ B T true rightDepth)
    (Wfits : Valuation.Fits Γ₀ Γ ρ) :
    (∀ (hA : LE_Interp.Witness ρ root A),
      hA.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) →
      ∃ hB : LE_Interp.Witness ρ root B,
        hB.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth)) ∧
    (∀ (hB : LE_Interp.Witness ρ root B),
      hB.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) →
      ∃ hA : LE_Interp.Witness ρ root A,
        hA.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth)) := by
  let rec go {Γ A B T} (hEq : IsDefEqStrong Γ A B T)
      {leftDepth rightDepth : Nat}
      (hAStratified : HasTypeStratifiedS Γ A T true leftDepth)
      (hBStratified : HasTypeStratifiedS Γ B T true rightDepth)
      {ρ root}
      (Wfits : Valuation.Fits Γ₀ Γ ρ) :
      (∀ (hA : LE_Interp.Witness ρ root A),
        hA.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) →
        ∃ hB : LE_Interp.Witness ρ root B,
          hB.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth)) ∧
      (∀ (hB : LE_Interp.Witness ρ root B),
        hB.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth) →
        ∃ hA : LE_Interp.Witness ρ root A,
          hA.RDeepChildren (LR.CoherentProvenanceAt Γ₀ depth)) :=
    match hEq with
    | .symm h =>
      let ih := go h hBStratified hAStratified Wfits
      ⟨ih.2, ih.1⟩
    | .trans h₁ h₂ =>
      let hMid := Classical.choose (h₁.stratify)
      let hMidStratified := (Classical.choose_spec (h₁.stratify)).2
      let ih₁ := go h₁ hAStratified hMidStratified Wfits
      let ih₂ := go h₂ hMidStratified hBStratified Wfits
      ⟨fun hA children => by
          obtain ⟨hMid, midChildren⟩ := ih₁.1 hA children
          exact ih₂.1 hMid midChildren,
        fun hB children => by
          obtain ⟨hMid, midChildren⟩ := ih₂.2 hB children
          exact ih₁.2 hMid midChildren⟩
    | .appDF _ _ hf ha _ => by
      obtain ⟨_, hfLeft, hfRight⟩ := hf.stratify
      obtain ⟨_, haLeft, haRight⟩ := ha.stratify
      constructor
      · intro hApp children
        cases hApp with
        | bot => exact ⟨.bot, .bot⟩
        | app hFun hArg hle =>
          cases children with
          | app cFun cArg =>
            obtain ⟨hFun', cFun'⟩ :=
              (go hf hfLeft hfRight Wfits).1 hFun cFun
            obtain ⟨hArg', cArg'⟩ :=
              (go ha haLeft haRight Wfits).1 hArg cArg
            exact ⟨.app hFun' hArg' hle, .app cFun' cArg'⟩
      · intro hApp children
        cases hApp with
        | bot => exact ⟨.bot, .bot⟩
        | app hFun hArg hle =>
          cases children with
          | app cFun cArg =>
            obtain ⟨hFun', cFun'⟩ :=
              (go hf hfLeft hfRight Wfits).2 hFun cFun
            obtain ⟨hArg', cArg'⟩ :=
              (go ha haLeft haRight Wfits).2 hArg cArg
            exact ⟨.app hFun' hArg' hle, .app cFun' cArg'⟩
    | @IsDefEqStrong.lamDF _ _ Dom Dom' _ _ _ _ _
        hDom _ _ hBody hBody' => by
      obtain ⟨_, hDomLeft, hDomRight⟩ := hDom.stratify
      obtain ⟨_, hBodyLeft, hBodyRight⟩ := hBody.stratify
      obtain ⟨_, hBodyLeft', hBodyRight'⟩ := hBody'.stratify
      have fitTypeLeft : ∀ {a}, LE_Interp ρ a Dom →
          ∃ a', a ≤ a' ∧ LE_Interp ρ a' Dom ∧ a'.HasType .type := by
        intro a hA
        exact InterpTyped.hsort
          (fun hA' => (LE_Interp.sound hDom Wfits).2 hA') hA
      have fitTypeRight : ∀ {a}, LE_Interp ρ a Dom' →
          ∃ a', a ≤ a' ∧ LE_Interp ρ a' Dom' ∧ a'.HasType .type := by
        intro a hA
        exact InterpTyped.hsort
          (fun hA' => (LE_Interp.sound hDom.symm Wfits).2 hA') hA
      constructor
      · intro hLam children
        cases hLam with
        | bot => exact ⟨.bot, .bot⟩
        | lam hDom₁ hshape hbody hle =>
          cases children with
          | lam cDom₁ cbody =>
            obtain ⟨hDom₁', cDom₁'⟩ :=
              (go hDom hDomLeft hDomRight Wfits).1 hDom₁ cDom₁
            let transported := fun x (hx : x.HasType _) =>
              (go hBody hBodyLeft hBodyRight
                (Wfits.cons fitTypeLeft hDom₁.toInterp hx.T)).1
                (hbody x hx) (cbody x hx)
            let hbody' := fun x hx => Classical.choose (transported x hx)
            have cbody' : ∀ x hx,
                (hbody' x hx).RDeepChildren
                  (LR.CoherentProvenanceAt Γ₀ depth) :=
              fun x hx => Classical.choose_spec (transported x hx)
            exact ⟨.lam hDom₁' hshape hbody' hle,
              .lam cDom₁' cbody'⟩
      · intro hLam children
        cases hLam with
        | bot => exact ⟨.bot, .bot⟩
        | lam hDom₁ hshape hbody hle =>
          cases children with
          | lam cDom₁ cbody =>
            obtain ⟨hDom₁', cDom₁'⟩ :=
              (go hDom hDomLeft hDomRight Wfits).2 hDom₁ cDom₁
            let transported := fun x (hx : x.HasType _) =>
              (go hBody' hBodyLeft' hBodyRight'
                (Wfits.cons fitTypeRight hDom₁.toInterp hx.T)).2
                (hbody x hx) (cbody x hx)
            let hbody' := fun x hx => Classical.choose (transported x hx)
            have cbody' : ∀ x hx,
                (hbody' x hx).RDeepChildren
                  (LR.CoherentProvenanceAt Γ₀ depth) :=
              fun x hx => Classical.choose_spec (transported x hx)
            exact ⟨.lam hDom₁' hshape hbody' hle,
              .lam cDom₁' cbody'⟩
    | @IsDefEqStrong.forallEDF _ _ Dom Dom' _ _ _ _
        hDom hBody hBody' => by
      obtain ⟨_, hDomLeft, hDomRight⟩ := hDom.stratify
      obtain ⟨_, hBodyLeft, hBodyRight⟩ := hBody.stratify
      obtain ⟨_, hBodyLeft', hBodyRight'⟩ := hBody'.stratify
      have fitTypeLeft : ∀ {a}, LE_Interp ρ a Dom →
          ∃ a', a ≤ a' ∧ LE_Interp ρ a' Dom ∧ a'.HasType .type := by
        intro a hA
        exact InterpTyped.hsort
          (fun hA' => (LE_Interp.sound hDom Wfits).2 hA') hA
      have fitTypeRight : ∀ {a}, LE_Interp ρ a Dom' →
          ∃ a', a ≤ a' ∧ LE_Interp ρ a' Dom' ∧ a'.HasType .type := by
        intro a hA
        exact InterpTyped.hsort
          (fun hA' => (LE_Interp.sound hDom.symm Wfits).2 hA') hA
      constructor
      · intro hPi children
        cases hPi with
        | bot => exact ⟨.bot, .bot⟩
        | forallE hDom₁ hDom₂ hshape hbody hle =>
          cases children with
          | forallE cDom₁ cDom₂ cbody =>
            obtain ⟨hDom₁', cDom₁'⟩ :=
              (go hDom hDomLeft hDomRight Wfits).1 hDom₁ cDom₁
            obtain ⟨hDom₂', cDom₂'⟩ :=
              (go hDom hDomLeft hDomRight Wfits).1 hDom₂ cDom₂
            let transported := fun x (hx : x.HasType _) =>
              (go hBody hBodyLeft hBodyRight
                (Wfits.cons fitTypeLeft hDom₂.toInterp hx.T)).1
                (hbody x hx) (cbody x hx)
            let hbody' := fun x hx => Classical.choose (transported x hx)
            have cbody' : ∀ x hx,
                (hbody' x hx).RDeepChildren
                  (LR.CoherentProvenanceAt Γ₀ depth) :=
              fun x hx => Classical.choose_spec (transported x hx)
            exact ⟨.forallE hDom₁' hDom₂' hshape hbody' hle,
              .forallE cDom₁' cDom₂' cbody'⟩
      · intro hPi children
        cases hPi with
        | bot => exact ⟨.bot, .bot⟩
        | forallE hDom₁ hDom₂ hshape hbody hle =>
          cases children with
          | forallE cDom₁ cDom₂ cbody =>
            obtain ⟨hDom₁', cDom₁'⟩ :=
              (go hDom hDomLeft hDomRight Wfits).2 hDom₁ cDom₁
            obtain ⟨hDom₂', cDom₂'⟩ :=
              (go hDom hDomLeft hDomRight Wfits).2 hDom₂ cDom₂
            let transported := fun x (hx : x.HasType _) =>
              (go hBody' hBodyLeft' hBodyRight'
                (Wfits.cons fitTypeRight hDom₂.toInterp hx.T)).2
                (hbody x hx) (cbody x hx)
            let hbody' := fun x hx => Classical.choose (transported x hx)
            have cbody' : ∀ x hx,
                (hbody' x hx).RDeepChildren
                  (LR.CoherentProvenanceAt Γ₀ depth) :=
              fun x hx => Classical.choose_spec (transported x hx)
            exact ⟨.forallE hDom₁' hDom₂' hshape hbody' hle,
              .forallE cDom₁' cDom₂' cbody'⟩
    | .defeqDF _ h => by
      obtain ⟨_, hLeft, hRight⟩ := h.stratify
      exact go h hLeft hRight Wfits
    | h@(.beta _ _ _ _) => by
      constructor
      · intro hRedex children
        cases hRedex with
        | bot => exact ⟨.bot, .bot⟩
        | @app _ _ f _ _ _ _ hLam hArg hroot =>
          cases children with
          | app cLam cArg =>
            cases f using WShape.casesOn' with
            | @lam g hg =>
              obtain ⟨hInst, cInst⟩ := cLam.lam_inst
                LE_Interp.Witness.TransportClosure.laws.mono_l
                LE_Interp.Witness.TransportClosure.laws.closed cArg
              exact ⟨hInst.mono hroot, cInst.mono hroot⟩
            | _ =>
              have hrootBot : root ≤ TShape.bot :=
                hroot.trans TShape.bot_le'
              rw [TShape.le_bot'.1 hrootBot]
              exact ⟨.bot, .bot⟩
      · exact (LR.coherentDefeqRDeepFallbackPairAt
          (root := root) seed h Wfits).2
    | .proofIrrel hProp hLeft hRight => by
      have collapses
          {term : SExpr}
          (hTerm : IsDefEqStrong Γ term term T)
          (hTermWitness : LE_Interp.Witness ρ root term) :
          root ≤ TShape.bot := by
        obtain ⟨termUpper, typeUpper, hroot, _hTermUpper,
            hTypeUpper, htyped⟩ :=
          (LE_Interp.sound hTerm Wfits).2 hTermWitness.toInterp
        obtain ⟨typeUpper', sortUpper, htype,
            _hTypeUpper', hSortUpper, htypeTyped⟩ :=
          (LE_Interp.sound hProp Wfits).2 hTypeUpper
        have htypeProp : typeUpper'.HasType (.sort false) :=
          TShape.HasType.mono_r (by simpa using hSortUpper.le_sort)
            .sort htypeTyped
        exact hroot.trans <|
          htypeProp.proofIrrel (htypeProp.mono_r htype htyped)
      constructor
      · intro hTerm _children
        rw [TShape.le_bot'.1 (collapses hLeft hTerm)]
        exact ⟨.bot, .bot⟩
      · intro hTerm _children
        rw [TShape.le_bot'.1 (collapses hRight hTerm)]
        exact ⟨.bot, .bot⟩
    | .extra action hLeft hRight =>
      let fallback := LR.coherentDefeqRDeepFallbackPairAt seed
        (.extra action hLeft hRight) Wfits
      ⟨fallback.1, fun hRhs _children =>
        LR.focusedExtraReverseRDeepAt seed action hLeft hRight
          Wfits hRhs hBStratified⟩
    | h => LR.coherentDefeqRDeepFallbackPairAt seed h Wfits
  exact go hEq hAStratified hBStratified Wfits

/-- Exact conversion transport justified by a depth-local seed constructor.

The strong equality is traversed through `symm` and `trans`, so a reverse
generated-iota action is handled by the focused evaluator even when nested
under those constructors.  Other branches select an endpoint by semantic
soundness and rebuild its tree only with the caller's local seed.  Thus a
reverse iota edge remains pinned to its literal RHS head, while every fresh
tree is still guarded by the already-complete smaller-depth callback. -/
theorem LR.coherentDefeqRDeepTransportAt
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth) :
    LE_Interp.Witness.StratifiedDefeqRDeepTransport
      (LR.CoherentProvenanceAt Γ₀ depth) Γ₀ := by
  intro Γ A B u endpointDepth ρ a sortShape hEq hAStratified
    hBStratified _W Wfits
    hA _hSort _htyped children
  exact (LR.coherentDefeqRDeepPairAt seed hEq hAStratified
    hBStratified Wfits).1 hA children

/-- Retained semantic typing from syntax recursion plus exact conversion
transport.

Binder validity uses ordinary semantic typing of the stratified domain; it
does not restart the retained consumer on an unrelated witness.  Thus the
only provenance-sensitive input is `convert`, and no Nat-first callback is
needed. -/
theorem LE_Interp.Witness.typedRDeep_of_stratifiedWith
    (laws : LE_Interp.Witness.RDeepChildren.Laws P)
    (convert : LE_Interp.Witness.StratifiedDefeqRDeepTransport P Γ₀)
    (H : HasTypeStratifiedS Γ M A core depth)
    (W : LE_Interp.Witness.FitsRDeep P Γ₀ Γ ρ)
    (Wfits : Valuation.Fits Γ₀ Γ ρ)
    (hM : LE_Interp.Witness ρ m M)
    (childrenP : hM.RDeepChildren P) :
    LE_Interp.Witness.TypedRDeep P ρ m M A := by
  induction H generalizing ρ m with
  | base _ ih => exact ih W Wfits hM childrenP
  | @sort' Γ l depth =>
    let tm := TShape.sort (decide (l ≠ .zero))
    let ty := TShape.type
    let hterm : LE_Interp.Witness ρ tm (.sort l) := .sort .rfl
    let htype : LE_Interp.Witness ρ ty (.sort l.succ) :=
      .sort (by simpa [ty, TShape.type] using
        (TShape.LE.rfl : TShape.sort true ≤ TShape.sort true))
    exact ⟨tm, ty, hterm, htype, hM.toInterp.le_sort,
      .sort, .sort, .sort⟩
  | @bvar Γ i A u depth hlookup hA ihA =>
    have hle := LE_Interp.bvar_iff.1 hM.toInterp
    exact (W.lookup laws hlookup).mono hle
  | @const c ci Γ ls u depth hreg hlen hTy ihTy =>
    cases hM with
    | bot => exact .bot TShape.bot_eqv.1
    | @const _ _ ci' _ m' _ a' _ R hreg' hlen' hle hty hA hC hR =>
      cases hreg.symm.trans hreg'
      cases childrenP with
      | const cA pR cR =>
        let hconst : LE_Interp.Witness ρ m' (.const c ls) :=
          .const hreg hlen .rfl hty hA hC hR
        exact ⟨m', a', hconst, hA, hle, hty,
          .const cA pR cR, cA⟩
  | @app Γ A u depth B v f a hA hCod hf ha hResult
      ihA ihCod ihf iha ihResult =>
    exact LE_Interp.Witness.TypedRDeep.app
      (F := f) (A := A) (B := B) (X := a)
      laws.mono_l laws.closed
      (H1 := fun hF cF => ihf W Wfits hF cF)
      (H2 := fun hB cB => (ihResult W Wfits hB cB).toType)
      childrenP
  | @lam Γ A u depth B v body hA hB hbody hPi
      ihA ihB ihbody ihPi =>
    have fitType : ∀ {a}, LE_Interp ρ a A →
        ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type := by
      intro a ha
      exact InterpTyped.hsort
        (fun hAsem => (LE_Interp.sound hA.strong Wfits).2 hAsem) ha
    exact LE_Interp.Witness.TypedRDeep.lam laws
      (H2 := fun {a x} hDom cDom hx {e} hBody cBody =>
        ihbody
          (W.push (ihA W Wfits hDom cDom).toType hx)
          (Wfits.cons fitType hDom.toInterp hx) hBody cBody)
      childrenP
  | @forallE Γ A u depth body v hA hbody ihA ihbody =>
    have fitType : ∀ {a}, LE_Interp ρ a A →
        ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type := by
      intro a ha
      exact InterpTyped.hsort
        (fun hAsem => (LE_Interp.sound hA.strong Wfits).2 hAsem) ha
    exact LE_Interp.Witness.TypedRDeep.forallE laws
      (H1 := fun hDom cDom => ihA W Wfits hDom cDom)
      (H2 := fun {a x} hDom cDom hx {e} hBody cBody =>
        ihbody
          (W.push (ihA W Wfits hDom cDom).toType hx)
          (Wfits.cons fitType hDom.toInterp hx) hBody cBody)
      childrenP
  | @defeq Γ A B u depth e hEq hA hB he ihA ihB ihe =>
    obtain ⟨tm, a, he', hA', hle, htyped, ce, cA⟩ :=
      ihe W Wfits hM childrenP
    obtain ⟨a', sortShape, hA'', hSort, ha, haTyped, cA', _cSort⟩ :=
      ihA W Wfits hA' cA
    obtain ⟨hB', cB⟩ :=
      convert hEq hA hB W Wfits hA'' hSort haTyped cA'
    exact ⟨tm, a, he', hB'.mono ha, hle, htyped, ce, cB.mono ha⟩

/-- Compatibility entry point for consumers whose conversion invariant does
not depend on the endpoint derivations. -/
theorem LE_Interp.Witness.typedRDeep_of_stratified
    (laws : LE_Interp.Witness.RDeepChildren.Laws P)
    (convert : LE_Interp.Witness.DefeqRDeepTransport P Γ₀)
    (H : HasTypeStratifiedS Γ M A core depth)
    (W : LE_Interp.Witness.FitsRDeep P Γ₀ Γ ρ)
    (Wfits : Valuation.Fits Γ₀ Γ ρ)
    (hM : LE_Interp.Witness ρ m M)
    (childrenP : hM.RDeepChildren P) :
    LE_Interp.Witness.TypedRDeep P ρ m M A :=
  LE_Interp.Witness.typedRDeep_of_stratifiedWith laws
    convert.stratified H W Wfits hM childrenP

/-- Retained semantic typing at a local provenance depth.

The only non-syntax-directed branch is discharged by rebuilding the
converted endpoint tree with `seed`.  This specialization is the admissible
replacement for assuming a global, arbitrary-predicate
`DefeqRDeepTransport`. -/
theorem LE_Interp.Witness.typedRDeep_of_stratifiedLocal
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth)
    (H : HasTypeStratifiedS Γ M A core depth)
    (W : LE_Interp.Witness.FitsRDeep
      (LR.CoherentProvenanceAt Γ₀ depth) Γ₀ Γ ρ)
    (Wfits : Valuation.Fits Γ₀ Γ ρ)
    (hM : LE_Interp.Witness ρ m M)
    (children : hM.RDeepChildren
      (LR.CoherentProvenanceAt Γ₀ depth)) :
    LE_Interp.Witness.TypedRDeep
      (LR.CoherentProvenanceAt Γ₀ depth) ρ m M A := by
  exact LE_Interp.Witness.typedRDeep_of_stratifiedWith
    LE_Interp.Witness.TransportClosure.laws
    (LR.coherentDefeqRDeepTransportAt seed)
    H W Wfits hM children

/-- Rebuild proof-relevant valuation bindings in the transportable coherent
provenance used by retained semantic typing.  Every binding witness is chosen
from the existing public `Fits` proof and receives a tree rebuilt by the same
depth-local seed as the term being typed. -/
theorem Valuation.Fits.toCoherentProvenanceFitsRDeep
    (W : Valuation.Fits Γ₀ Γ ρ)
    (seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth) :
    LE_Interp.Witness.FitsRDeep
      (LR.CoherentProvenanceAt Γ₀ depth) Γ₀ Γ ρ :=
  W.toFitsRDeep (fun _ => LR.CoherentProvenanceAt.rebuild seed)

/-- Retained semantic typing of an exact witness at a genuinely smaller
syntax rung.

The strict predecessor supplies the local coherent seed for arbitrary
witnesses.  That one seed rebuilds both the witness's provenance tree and
all valuation-binding trees, after which `typedRDeep_of_stratifiedLocal`
returns the registered term/type witnesses without any proof-irrelevant
reselection at the consumer boundary. -/
theorem LE_Interp.Witness.typedRDeep_of_stratifiedRestart
    (lower : ∀ (d' : Nat), d' < outerDepth →
      ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
        hX.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
        LRD.CoherentRetainedAt Γ₀ hX d')
    (hdepth : depth < outerDepth)
    (H : HasTypeStratifiedS Γ M A core depth)
    (W : Valuation.Fits Γ₀ Γ ρ)
    (hM : LE_Interp.Witness ρ m M) :
    LE_Interp.Witness.TypedRDeep
      (LR.CoherentProvenanceAt Γ₀ depth) ρ m M A := by
  let seed : ∀ {ρ root X} (hX : LE_Interp.Witness ρ root X),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
        LR.CoherentRetainedAt Γ₀ hX depth := fun hX children =>
    (lower depth hdepth hX children).1
  exact LE_Interp.Witness.typedRDeep_of_stratifiedLocal seed H
    (W.toCoherentProvenanceFitsRDeep seed) W hM
    (LR.CoherentProvenanceAt.rebuild seed)

/--
info: 'Lean4Lean.SExpr.Valuation.Fits.toCoherentProvenanceFitsRDeep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Valuation.Fits.toCoherentProvenanceFitsRDeep

/--
info: 'Lean4Lean.SExpr.LE_Interp.Witness.typedRDeep_of_stratifiedRestart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.Witness.typedRDeep_of_stratifiedRestart

/-- Package the direct retained-typing theorem at one exact stratification
depth. -/
theorem LE_Interp.Witness.soundRDeepAt_of_defeqTransport
    (laws : LE_Interp.Witness.RDeepChildren.Laws P)
    (convert : LE_Interp.Witness.DefeqRDeepTransport P Γ₀)
    {hM : LE_Interp.Witness ρ m M}
    (childrenP : hM.RDeepChildren P) (depth : Nat) :
    LE_Interp.Witness.SoundRDeepAt P Γ₀ hM depth := by
  intro Γ A core H W Wfits
  exact LE_Interp.Witness.typedRDeep_of_stratified
    laws convert H W Wfits hM childrenP

/-- Every exact witness has retained semantic typing when evaluator edges
carry only `True`. -/
theorem LE_Interp.Witness.soundRDeepAt_true
    (hM : LE_Interp.Witness rho m M) (depth : Nat) :
    LE_Interp.Witness.SoundRDeepAt (fun _ => True) Gamma0 hM depth :=
  LE_Interp.Witness.soundRDeepAt_of_defeqTransport
    LE_Interp.Witness.RDeepChildren.Laws.true
    (LE_Interp.Witness.defeqRDeepTransport_true Gamma0)
    (LE_Interp.Witness.RDeepChildren.trivial hM) depth

/-- Type one exact proof-relevant witness at its strong derivation's native
stratification depth while retaining only trivial recursive-edge data.

This is the appropriate registered-type observation for a fixed-head
producer: it stays paired with the selected term witness, but it neither
requires a caller-fixed depth nor promotes a local coherent seed. -/
theorem LE_Interp.Witness.typedRDeepTrue_of_strong
    (hM : LE_Interp.Witness ρ m M)
    (H : IsDefEqStrong Γ M M A)
    (W : Valuation.Fits Γ₀ Γ ρ) :
    LE_Interp.Witness.TypedRDeep (fun _ => True) ρ m M A := by
  obtain ⟨depth, hstrat, _⟩ := H.stratify
  exact hM.soundRDeepAt_true depth hstrat W.toFitsRDeepTrue W

/--
info: 'Lean4Lean.SExpr.LE_Interp.Witness.typedRDeepTrue_of_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.Witness.typedRDeepTrue_of_strong

/-- Select one non-bottom fixed head together with both the recursive result
carried by its exact abstract edge and semantic typing of that same witness.

The typing observation is constructed at the registered term's native
stratification depth, so this package does not require a depth restart or a
strict predecessor certificate from its caller. -/
noncomputable def LE_Interp.RHS.fixedLowerWitnessTypedResult
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hP : ∀ {m M} (hr : R m M), P (hR hr))
    (hmono : ∀ {m m' M} (hle : m ≤ m')
      (H : LE_Interp.Witness ρ m' M), P H → P (H.mono hle))
    (H : LE_Interp.RHS ls m2 (LE_Interp.Lower R) m (.fixed e cl))
    (hnonbot : ¬m ≤ TShape.bot)
    (hstrong : IsDefEqStrong Γ (SExpr.mkInst ls e)
      (SExpr.mkInst ls e) A)
    (W : Valuation.Fits Γ₀ Γ ρ) :
    {h : LE_Interp.Witness ρ m (SExpr.mkInst ls e) //
      P h ∧ LE_Interp.Witness.TypedRDeep
        (fun _ => True) ρ m (SExpr.mkInst ls e) A} :=
  let result := H.fixedLowerWitnessResult hR hP hmono hnonbot
  ⟨result.1, result.2,
    result.1.typedRDeepTrue_of_strong hstrong W⟩

/--
info: 'Lean4Lean.SExpr.LE_Interp.RHS.fixedLowerWitnessTypedResult' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.RHS.fixedLowerWitnessTypedResult

/-- Select a fixed lower head together with its exact coherent seed branch,
native/local typing distinction, and proof-relevant semantic type witness.

Root lowering preserves the original provenance tag through
`CoherentSeedAt.mono`; the result therefore never upgrades a rebuilt local
edge to the genuine all-depth branch. -/
noncomputable def LE_Interp.RHS.fixedLowerWitnessCoherentResult
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hseed : ∀ {m M} (hr : R m M),
      LR.CoherentSeedAt Γ₀ depth (hR hr))
    (H : LE_Interp.RHS ls m2 (LE_Interp.Lower R) m (.fixed e cl))
    (hnonbot : ¬m ≤ TShape.bot)
    (hstrong : IsDefEqStrong Δ (SExpr.mkInst ls e)
      (SExpr.mkInst ls e) A)
    (W : Valuation.Fits Γ₁ Δ ρ) :
    {h : LE_Interp.Witness ρ m (SExpr.mkInst ls e) //
      ((∃ nativeDepth,
          LR.CoherentRetainedAt Γ₀ h nativeDepth ∧
            HasTypeStratifiedS Δ (SExpr.mkInst ls e) A true nativeDepth) ∨
        LR.CoherentRetainedAt Γ₀ h depth) ∧
      LE_Interp.Witness.TypedRDeep
        (fun _ => True) ρ m (SExpr.mkInst ls e) A} :=
  let result := H.fixedLowerWitnessTypedResult hR hseed
    (fun hle hM H => LR.CoherentSeedAt.mono (hX := hM) hle H)
    hnonbot hstrong W
  ⟨result.1, result.2.1.nativeOrLocal hstrong, result.2.2⟩

/--
info: 'Lean4Lean.SExpr.LE_Interp.RHS.fixedLowerWitnessCoherentResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LE_Interp.RHS.fixedLowerWitnessCoherentResult

/-- Typed recursive-result-preserving form of `of_nonbotWitnessResult`.

The callback receives semantic typing of the exact fixed-head witness selected
with its recursive result.  The observation is recovered from the registered
strong typing at its native stratification depth, independently of the
caller's guarded coherence rung. -/
theorem LRD.IotaRHSDefEq.of_nonbotWitnessResultTyped
    {R : TShape → SExpr → Prop} {ρ : Valuation}
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hP : ∀ {m M} (hr : R m M), P (hR hr))
    (hmono : ∀ {m m' M} (hle : m ≤ m')
      (hM : LE_Interp.Witness ρ m' M), P hM → P (hM.mono hle))
    (W : Valuation.Fits Γ₀ Γ ρ)
    (H : ∀ {head : TShape}
        {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {captureType :
          (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {A : SExpr} {outTy : WShape (n + 1)}
        (hhead : LE_Interp.Witness ρ head
          (SExpr.mkInst recLs rule.df.rhs)),
      P hhead →
      LE_Interp.Witness.TypedRDeep (fun _ => True) ρ head
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) →
      LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T →
      (∃ headElem headTy : TShape,
        headElem ≤ head ∧ headElem.HasType headTy) →
      SExpr.PathSpineWF Γ mx captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      SExpr.PathSpineWF Γ my captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LR.DirectCaptureDefEqAligned
            (n := n + 1) (LRD Γ) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
            (mctor p) (mx path) (my path) (captureType path)) →
      out.HasType outTy →
      (LRD Γ).TyDefEq A A outTy →
      (LRD Γ).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy) :
    LRD.IotaRHSDefEq (Γ := Γ) (LE_Interp.Lower R) recLs
      mrec mctor r rule out := by
  apply LRD.IotaRHSDefEq.of_nonbotWitnessResult hR hP hmono
  intro head mx my captureType A outTy hhead hresult hstrong hshape
    htyped hspineX hspineY hcap hout hA
  exact H hhead hresult
    (hhead.typedRDeepTrue_of_strong hstrong W) hshape htyped
    hspineX hspineY hcap hout hA

/--
info: 'Lean4Lean.SExpr.LRD.IotaRHSDefEq.of_nonbotWitnessResultTyped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LRD.IotaRHSDefEq.of_nonbotWitnessResultTyped

/-- Coherent recursive-result-preserving form of the guarded fixed-RHS
consumer.

The callback receives the exact selected witness together with its genuine
native-depth or rebuilt local branch and proof-relevant semantic typing.  The
registered RHS is strongly typed directly in the valuation's source context;
no relation-context certificate is transported or paired with a reselected
witness. -/
theorem LRD.IotaRHSDefEq.of_nonbotWitnessResultCoherent
    {R : TShape → SExpr → Prop} {ρ : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    {depth : Nat} {Δ Γ₁ : List SExpr}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hseed : ∀ {m M} (hr : R m M),
      LR.CoherentSeedAt Γ₀ depth (hR hr))
    (W : Valuation.Fits Γ₁ Δ ρ)
    (H : ∀ {head : TShape}
        {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {captureType :
          (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {A : SExpr} {outTy : WShape (n + 1)}
        (hhead : LE_Interp.Witness ρ head
          (SExpr.mkInst recLs rule.df.rhs)),
      ((∃ nativeDepth,
          LR.CoherentRetainedAt Γ₀ hhead nativeDepth ∧
            HasTypeStratifiedS Δ
              (SExpr.mkInst recLs rule.df.rhs)
              (SExpr.mkInst recLs rule.df.type) true nativeDepth) ∨
        LR.CoherentRetainedAt Γ₀ hhead depth) →
      LE_Interp.Witness.TypedRDeep (fun _ => True) ρ head
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) →
      LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T →
      (∃ headElem headTy : TShape,
        headElem ≤ head ∧ headElem.HasType headTy) →
      SExpr.PathSpineWF Γ mx captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      SExpr.PathSpineWF Γ my captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LR.DirectCaptureDefEqAligned
            (n := n + 1) (LRD Γ) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
            (mctor p) (mx path) (my path) (captureType path)) →
      out.HasType outTy →
      (LRD Γ).TyDefEq A A outTy →
      (LRD Γ).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy) :
    LRD.IotaRHSDefEq (Γ := Γ) (LE_Interp.Lower R) recLs
      mrec mctor r rule out := by
  apply LRD.IotaRHSDefEq.of_nonbotWitnessResult hR hseed
    (fun hle hM H => LR.CoherentSeedAt.mono (hX := hM) hle H)
  intro head mx my captureType A outTy hhead hresult _hstrong hshape
    htyped hspineX hspineY hcap hout hA
  have hstrongΔ : IsDefEqStrong Δ
      (SExpr.mkInst recLs rule.df.rhs)
      (SExpr.mkInst recLs rule.df.rhs)
      (SExpr.mkInst recLs rule.df.type) :=
    rule.rhsStrong recLs
  exact H hhead (hresult.nativeOrLocal hstrongΔ)
    (hhead.typedRDeepTrue_of_strong hstrongΔ W) hshape htyped
    hspineX hspineY hcap hout hA

/--
info: 'Lean4Lean.SExpr.LRD.IotaRHSDefEq.of_nonbotWitnessResultCoherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LRD.IotaRHSDefEq.of_nonbotWitnessResultCoherent

/-- Guarded-coherent recursive-result form of the fixed-RHS consumer.

Unlike `of_nonbotWitnessResultCoherent`, genuine evaluator children expose
their all-depth `LRD` result.  A rebuilt child is still local, so the callback
must handle the two provenance branches separately and may not promote the
second one. -/
theorem LRD.IotaRHSDefEq.of_nonbotWitnessResultDirectCoherent
    {R : TShape → SExpr → Prop} {ρ : Valuation}
    {rec ctor : Name} {major arity : Nat}
    {recLs : List SLevel}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r} {out : WShape (n + 1)}
    {depth : Nat} {Δ Γ₁ : List SExpr}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hseed : ∀ {m M} (hr : R m M),
      LRD.CoherentSeedAt Γ₀ depth (hR hr))
    (W : Valuation.Fits Γ₁ Δ ρ)
    (H : ∀ {head : TShape}
        {mx my : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {captureType :
          (RecursorIotaPattern rec major ctor arity).Path → SExpr}
        {A : SExpr} {outTy : WShape (n + 1)}
        (hhead : LE_Interp.Witness ρ head
          (SExpr.mkInst recLs rule.df.rhs)),
      ((∃ nativeDepth,
          LRD.CoherentRetainedAt Γ₀ hhead nativeDepth ∧
            HasTypeStratifiedS Δ
              (SExpr.mkInst recLs rule.df.rhs)
              (SExpr.mkInst recLs rule.df.type) true nativeDepth) ∨
        LRD.CoherentRetainedAt Γ₀ hhead depth) →
      LE_Interp.Witness.TypedRDeep (fun _ => True) ρ head
        (SExpr.mkInst recLs rule.df.rhs)
        (SExpr.mkInst recLs rule.df.type) →
      LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor)
        head rule.capturePaths out.T →
      (∃ headElem headTy : TShape,
        headElem ≤ head ∧ headElem.HasType headTy) →
      SExpr.PathSpineWF Γ mx captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      SExpr.PathSpineWF Γ my captureType
        (SExpr.mkInst recLs rule.df.type) rule.capturePaths A →
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LR.DirectCaptureDefEqAligned
            (n := n + 1) (LRD Γ) (mrec p)
            (mx path) (my path) (captureType path)
        | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
            (mctor p) (mx path) (my path) (captureType path)) →
      out.HasType outTy →
      (LRD Γ).TyDefEq A A outTy →
      (LRD Γ).DefEq
        (r.1.applyS recLs mx) (r.1.applyS recLs my) A out outTy) :
    LRD.IotaRHSDefEq (Γ := Γ) (LE_Interp.Lower R) recLs
      mrec mctor r rule out := by
  apply LRD.IotaRHSDefEq.of_nonbotWitnessResult hR hseed
    (fun hle hM H => LRD.CoherentSeedAt.mono (hX := hM) hle H)
  intro head mx my captureType A outTy hhead hresult _hstrong hshape
    htyped hspineX hspineY hcap hout hA
  have hstrongΔ : IsDefEqStrong Δ
      (SExpr.mkInst recLs rule.df.rhs)
      (SExpr.mkInst recLs rule.df.rhs)
      (SExpr.mkInst recLs rule.df.type) :=
    rule.rhsStrong recLs
  exact H hhead (hresult.nativeOrLocal hstrongΔ)
    (hhead.typedRDeepTrue_of_strong hstrongΔ W) hshape htyped
    hspineX hspineY hcap hout hA

/--
info: 'Lean4Lean.SExpr.LRD.IotaRHSDefEq.of_nonbotWitnessResultDirectCoherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LRD.IotaRHSDefEq.of_nonbotWitnessResultDirectCoherent

/-- The direct constant producer left by the syntax-directed self-adequacy
algebra.

The recursive edge tree deliberately retains `CoherentSeedAt`: a constant
case may select a registered RHS while it still needs to distinguish a
genuine all-depth evaluator child from a depth-local rebuilt child.  A
strictly smaller restart likewise requires the exact rebuilt tree before it
may return a local coherent result. -/
def LR.SelfAdequateConstStep (Γ₀ : List SExpr) : Prop :=
  ∀ {c : Name} {ci : VConstant} {Γ : List SExpr}
      {ls : List SLevel} {u : SLevel} {depth : Nat}
      {ρ : Valuation} {n : Nat} {mx bx : WShape n},
    Params.env.constants c = some ci →
    ls.length = ci.uvars →
    HasTypeStratifiedS Γ (SExpr.mkInst ls ci.type)
      (.sort u) true depth →
    (∀ (d' : Nat), d' < depth + 1 →
      ∀ {ρ root X} (hX' : LE_Interp.Witness ρ root X),
        hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
        LR.CoherentRetainedAt Γ₀ hX' d') →
    mx.HasType bx →
    LE_Interp.Witness ρ bx.T (SExpr.mkInst ls ci.type) →
    ∀ (hX : LE_Interp.Witness ρ mx.T (.const c ls)),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ (depth + 1)) →
      LR.Adequate Γ₀ Γ ρ (.const c ls) (.const c ls)
        (SExpr.mkInst ls ci.type) mx bx

/-- Direct constant-step contract.  It differs from
`SelfAdequateConstStep` only in the guarded predecessor package: every
strictly smaller restart also carries `DirectSelfTypeAt`.  The produced term
adequacy remains the established relation, so the direct route can be wired
into the current coherent algebra without changing its consumers. -/
def LR.SelfAdequateConstStepDirect (Γ₀ : List SExpr) : Prop :=
  ∀ {c : Name} {ci : VConstant} {Γ : List SExpr}
      {ls : List SLevel} {u : SLevel} {depth : Nat}
      {ρ : Valuation} {n : Nat} {mx bx : WShape n},
    Params.env.constants c = some ci →
    ls.length = ci.uvars →
    HasTypeStratifiedS Γ (SExpr.mkInst ls ci.type)
      (.sort u) true depth →
    (∀ (d' : Nat), d' < depth + 1 →
      ∀ {ρ root X} (hX' : LE_Interp.Witness ρ root X),
        hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
        LR.DirectCoherentRetainedAt Γ₀ hX' d') →
    mx.HasType bx →
    LE_Interp.Witness ρ bx.T (SExpr.mkInst ls ci.type) →
    ∀ (hX : LE_Interp.Witness ρ mx.T (.const c ls)),
      hX.RDeepChildren (LR.CoherentSeedAt Γ₀ (depth + 1)) →
      LR.Adequate Γ₀ Γ ρ (.const c ls) (.const c ls)
        (SExpr.mkInst ls ci.type) mx bx

/-- The conversion case of depth-indexed self-adequacy.

The source type certificate is strictly shallower than `outerDepth`.  The
current compatibility construction discharges this callback from completed
stratified inversion; the depth fixpoint instead discharges it directly from
heterogeneous adequacy at that smaller certificate depth. -/
def LR.SelfAdequateDefeqStepAt
    (Γ₀ : List SExpr) (outerDepth : Nat) : Prop :=
  ∀ {Γ : List SExpr} {A B e : SExpr} {u : SLevel} {depth : Nat}
      {ρ : Valuation} {n : Nat} {m b : WShape n},
    depth < outerDepth →
    HasTypeStratifiedS Γ A (.sort u) true depth →
    IsDefEqStrong Γ A B (.sort u) →
    LE_Interp ρ m.T e → LE_Interp ρ b.T B → m.HasType b →
    (∀ {n'} {ma sa : WShape n'},
      LE_Interp ρ ma.T A → LE_Interp ρ sa.T (.sort u) →
      ma.HasType sa → LR.Adequate Γ₀ Γ ρ A A (.sort u) ma sa) →
    (∀ {n'} {mb sb : WShape n'},
      LE_Interp ρ mb.T B → LE_Interp ρ sb.T (.sort u) →
      mb.HasType sb → LR.Adequate Γ₀ Γ ρ B B (.sort u) mb sb) →
    (∀ {n'} {me ae : WShape n'},
      LE_Interp ρ me.T e → LE_Interp ρ ae.T A →
      me.HasType ae → LR.Adequate Γ₀ Γ ρ e e A me ae) →
    LR.Adequate Γ₀ Γ ρ e e B m b

/-- Compatibility implementation of the conversion callback from the
already-complete inversion package. -/
theorem LR.SelfAdequateDefeqStepAt.of_stratifiedInversion
    (inv : JointStratifiedInversion) (hΓ₀ : Ctx.WF Γ₀)
    (outerDepth : Nat) :
    LR.SelfAdequateDefeqStepAt Γ₀ outerDepth := by
  intro Γ A B e u depth ρ n m b _ _ hEq hM hB hmem ihA ihB ihe
  exact LR.adequateDefeqSelf_of_stratifiedInversion inv hΓ₀ hEq
    hM hB hmem ihA ihB ihe

/-- Well-founded implementation of the conversion callback from strictly
smaller depth-bounded adequacy.  This is the handoff used by the new depth
fixpoint; no inversion or path collapse is involved. -/
theorem LR.SelfAdequateDefeqStepAt.of_lowerAdequacy
    (hΓ₀ : Ctx.WF Γ₀) (outerDepth : Nat)
    (lowerAdequacy : ∀ d, d < outerDepth →
      LR.ContextualAdequacyAtDepth d) :
    LR.SelfAdequateDefeqStepAt Γ₀ outerDepth := by
  intro Γ A B e u depth ρ n m b hdepth hAty hEq hM hB hmem _ _ ihe
  apply LR.adequateDefeq hEq hM hB hmem
  · intro n' ma sa hA hSort hma
    exact (lowerAdequacy depth hdepth hΓ₀)
      hEq hAty hA hSort hma
  · exact ihe

/-- Every non-constant stratified typing constructor preserves retained
self-adequacy. The constant constructor is deliberately exposed as the
separate producer contract above. -/
private theorem LR.selfAdequateExactAtStep
    (outerDepth : Nat)
    (defeqStep : LR.SelfAdequateDefeqStepAt Γ₀ outerDepth)
    (hΓ₀ : Ctx.WF Γ₀)
    (constStep : LR.SelfAdequateConstStep Γ₀)
    {ρ root X} (hX : LE_Interp.Witness ρ root X)
    (children : hX.RDeepChildren (LR.CoherentSeedAt Γ₀ outerDepth))
    (lower : ∀ (d' : Nat), d' < outerDepth → ∀ {ρ root X}
      (hX' : LE_Interp.Witness ρ root X),
      hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
      LR.CoherentRetainedAt Γ₀ hX' d') :
    LR.SelfAdequateExactAt Γ₀ hX outerDepth := by
  intro n mx bx Δ core B hroot hTyping htyped hB
  subst root
  have restartSelf : ∀ (d' : Nat), d' < outerDepth →
      ∀ {ρ root X} (hX' : LE_Interp.Witness ρ root X),
        LR.SelfAdequateAt Γ₀ hX' d' := by
    intro d' hdepth ρ root X hX'
    exact (LR.CoherentRetainedAt.restart
      (lower := lower) hdepth (hX := hX')).1
  induction hTyping generalizing ρ n mx bx with
  | base htypedCore ih =>
    exact ih defeqStep lower htyped hB hX children restartSelf
  | @sort' Δ l depth =>
    suffices (LR Γ₀).DefEq (.sort l) (.sort l) (.sort l.succ) mx bx from
      ⟨fun _ _ _ => ⟨this, this⟩, fun _ _ => this⟩
    cases htyped.unfold with
    | bot hm => exact (LR _).bot hm
    | sort => exact (LR _).sort_iff.2 ⟨_, .rfl, .rfl⟩
    | _ =>
      obtain h | h := WShape.le_sort.1 hX.toInterp.le_sort'
      · dsimp only at h
        rw [h]
        exact (LR _).bot htyped.isType
      · simp [WShape.ext_iff, WShape.forallE, WShape.sort, Shape.sort,
          WShape.lam', WShape.lam, WShape.bot, WShape.ctor, WShape.indTy,
          Shape.bot] at h <;>
          first
          | split at h <;> simp_all only [reduceCtorEq]
          | simp_all
  | @bvar Δ i A u depth hlookup hA ihA =>
    refine .refl fun _ _ W => ?_
    have hle := LE_Interp.bvar_iff.1 hX.toInterp
    clear hX children ihA hA
    induction W generalizing i A with
    | id =>
      cases show mx = .bot from TShape.le_bot.1 (hle.trans TShape.bot_le)
      exact (LR _).bot htyped.isType
    | cons W' _ _ _ _ h0 ih =>
      cases hlookup with
      | zero =>
        exact lift_subst ▸ (h0.2 bx hB.toInterp).2 (.bvar hle) htyped
      | succ h' => exact lift_subst ▸ ih h' hB.unweak hle
  | @const c ci Γ ls u depth hreg hlen hTy _ =>
    exact constStep hreg hlen hTy lower htyped hB hX children
  | @app Γ A u depth B v f x hAty hBty hfty hxty hRty
      _ _ _ _ _ =>
    have hdepth : depth < depth + 1 := Nat.lt_succ_self depth
    have ihf : ∀ {ρ : Valuation} {n' : Nat} {mf af : WShape n'},
        LE_Interp ρ mf.T f → LE_Interp ρ af.T (.forallE A B) →
        mf.HasType af →
        LR.Adequate Γ₀ Γ ρ f f (.forallE A B) mf af := by
      intro ρ n' mf af hf hPi hmf
      let whf := hf.witness
      let whPi := hPi.witness
      exact (restartSelf depth hdepth whf) .rfl hfty hmf whPi
    have ihx : ∀ {ρ : Valuation} {n' : Nat} {ma aa : WShape n'},
        LE_Interp ρ ma.T x → LE_Interp ρ aa.T A →
        ma.HasType aa → LR.Adequate Γ₀ Γ ρ x x A ma aa := by
      intro ρ n' ma aa hx hA hma
      let whx := hx.witness
      let whA := hA.witness
      exact (restartSelf depth hdepth whx) .rfl hxty hma whA
    have ihR : ∀ {ρ : Valuation} {n' : Nat} {mb av : WShape n'},
        LE_Interp ρ mb.T (B.inst x) → LE_Interp ρ av.T (.sort v) →
        mb.HasType av →
        LR.Adequate Γ₀ Γ ρ (B.inst x) (B.inst x) (.sort v) mb av := by
      intro ρ n' mb av hResult hv hmb
      let whResult := hResult.witness
      let whv := hv.witness
      exact (restartSelf depth hdepth whResult) .rfl hRty hmb whv
    exact LR.adequateApp hfty.strong hxty.strong hRty.strong
      hX.toInterp hB.toInterp htyped ihf ihx ihR
  | @lam Γ A u depth B v body hAty hBty hbodyty hPity
      _ _ _ _ =>
    let HA := hAty.strong
    let HB := hBty.strong
    let HBody := hbodyty.strong
    have hdepth : depth < depth + 1 := Nat.lt_succ_self depth
    have ihA : ∀ {ρ : Valuation} {n' : Nat} {ma aa : WShape n'},
        LE_Interp ρ ma.T A → LE_Interp ρ aa.T (.sort u) →
        ma.HasType aa → LR.Adequate Γ₀ Γ ρ A A (.sort u) ma aa := by
      intro ρ n' ma aa hA hSort hma
      exact (restartSelf depth hdepth hA.witness)
        .rfl hAty hma hSort.witness
    have ihB : ∀ {ρ : Valuation} {n' : Nat} {mb ab : WShape n'},
        LE_Interp ρ mb.T B → LE_Interp ρ ab.T (.sort v) →
        mb.HasType ab →
        LR.Adequate Γ₀ (A :: Γ) ρ B B (.sort v) mb ab := by
      intro ρ n' mb ab hB hSort hmb
      exact (restartSelf depth hdepth hB.witness)
        .rfl hBty hmb hSort.witness
    have ihBody : ∀ {ρ : Valuation} {n' : Nat} {mb ab : WShape n'},
        LE_Interp ρ mb.T body → LE_Interp ρ ab.T B →
        mb.HasType ab →
        LR.Adequate Γ₀ (A :: Γ) ρ body body B mb ab := by
      intro ρ n' mb ab hbody hB hmb
      exact (restartSelf depth hdepth hbody.witness)
        .rfl hbodyty hmb hB.witness
    have hTerm := hX.toInterp
    have hPi := hB.toInterp
    suffices ∀ {X Y X' Y' σ σ'},
        LE_Interp ρ mx.T (.lam X Y) → LR.SubstWF Γ₀ σ σ' Γ ρ →
        (∀ {k np} {p : WShape np} {mb ab : WShape k},
          (ρ.push p.T).Fits Γ₀ (A :: Γ) →
          LE_Interp (ρ.push p.T) mb.T Y →
          LE_Interp (ρ.push p.T) ab.T B → mb.HasType ab →
          LR.Adequate Γ₀ (A :: Γ) (ρ.push p.T) Y Y' B mb ab) →
        (LR Γ₀).DefEq (.subst (.lam X Y) σ)
          (.subst (.lam X' Y') σ') (.subst (.forallE A B) σ) mx bx by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩,
        fun σ W => this hTerm W fun _ => ihBody⟩
      · exact this hTerm W
          fun _ hMb hBb hmb => (ihBody hMb hBb hmb).left
      · refine this ?_ W fun W hMb' hBb hmb => ?_
        · exact (LE_Interp.sound
            (.lamDF HA HB HB HBody HBody) W.fits).1.1 hTerm
        · exact (ihBody
            ((LE_Interp.sound HBody W).1.2 hMb') hBb hmb).symm.left
    intro X Y X' Y' σ σ' hTerm' W IH
    suffices ∀ n' b (fshape : WShapeFun _), n = n' + 1 →
        bx ≍ (.forallE b fshape : WShape (n' + 1)) →
        (LR Γ₀).DefEq (.subst (.lam X Y) σ)
          (.subst (.lam X' Y') σ') (.subst (.forallE A B) σ) mx bx by
      cases htyped.unfold with
      | bot hm =>
        cases hm.unfold with
        | bot | sort => cases n <;> trivial
        | indTy => trivial
        | forallE => exact this _ _ _ rfl .rfl
      | sort =>
        cases n <;> let .lam _ _ _ h := hTerm' <;>
          cases TShape.sort_not_le_lam' h
      | forallE =>
        let .lam _ _ _ h := hTerm'
        cases TShape.forallE_not_le_lam' h
      | lam => exact this _ _ _ rfl .rfl
      | ctor =>
        let .lam _ _ _ h := hTerm'
        cases TShape.ctor_not_le_lam' h
      | indTy =>
        let .lam _ _ _ h := hTerm'
        cases TShape.indTy_not_le_lam' h
    rintro k a₁ a₂ rfl ⟨⟩
    have ⟨_, aty, _⟩ := WShape.HasType.forallE_l.1 htyped.isType
    have hTypA : Γ₀ ⊢ A.subst σ : .sort u :=
      (HA.subst W.left.toSubstEq).hasType.1
    have hTypB : A.subst σ :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      HB.subst (W.left.toSubstEq.lift HA.defeq.hasType.1)
    have hA1 := hPi.forallE_inv.1
    have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
    have cons := LR.Adequate.cons ihA HA
    obtain ⟨g, hg, htm⟩ := WShape.HasType.forallE_inv htyped
    unfold WShape.lam' at hg
    split at hg <;> [skip; (subst hg; exact (LR _).bot htyped.isType)]
    rename_i hlam
    subst hg
    simp only [LR, LRS, LRS.DefEq.lam_forallE]
    have aty := WShape.HasTypePi.iff.1 aty
    refine ⟨A.subst σ, B.subst σ.lift, u, v, .rfl,
      hTypA, ?_, hTypB, ?_, ?_⟩
    · exact (LR Γ₀).left_ty <|
        LR.toValTy le_n le_a aty.1.isType hSort hmem'
          ((ihA hA' hSort hmem').2 W.left)
    · simp only [LRS.PiDefEq]
      have edge : ∀ {{x x' p}}, p.HasType a₁ →
          Γ₀ ⊢ x ≡ x' : A.subst σ →
          (LR Γ₀).DefEq x x' (A.subst σ) p a₁ →
          LRS.PiInstDefEq (LR Γ₀) (B.subst σ.lift)
            (B.subst σ.lift) x x' (a₂.app p) := by
        intro x x' p hp ha hv
        have W' := cons hp hA1 ha hv W.left
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HB W'.fits).2
            (hPi.forallE_inv'.2 p) |>.out
        have hsem : (LR Γ₀).TyDefEq
            ((B.subst σ.lift).inst x) ((B.subst σ.lift).inst x')
            (a₂.app p) := by
          simpa [inst_lift_cons] using
            LR.toValTy le le' (aty.2 _ hp).toType iv hmb
              ((ihB iB iv hmb).1 W').1
        have hraw : Γ₀ ⊢
            (B.subst σ.lift).inst x ≡
              (B.subst σ.lift).inst x' : .sort v := by
          simpa only [inst_lift_cons, SExpr.subst] using
            (HB.substCongr W'.toSubstEq).1
        exact ⟨hsem, hsem, ⟨v, hraw⟩, ⟨v, hraw⟩⟩
      exact ⟨edge, fun _ _ hp ha hv => (edge hp ha hv).leftTy⟩
    have beta {X Y t : SExpr} {σ} :
        Γ₀ ⊢ .app (.lam (X.subst σ) (Y.subst σ.lift)) t ⤳*
          Y.subst (σ.cons t) :=
      inst_lift_cons (x := t) ▸ .tail .rfl .beta
    refine ⟨fun x x' p hp ha hv => ?_, fun x p hp ha hv => ?_⟩
    all_goals
      rw [inst_lift_cons]
      have hBb_sd := hPi.forallE_inv'.2 p
      replace IH W := IH W (hTerm'.lam_inv' p) hBb_sd
        ((WShape.HasTypeLam.iff.1 htm).2.2 p hp)
    · have W' := cons hp hA1 ha hv W.left
      constructor
      · exact ((LR Γ₀).whr beta beta).2 <| ((IH W'.fits).1 W').1
      · have vtAA' := LR.toValTy le_n le_a aty.1.isType hSort hmem'
          ((ihA hA' hSort hmem').1 W).1
        have ha' : Γ₀ ⊢ x ≡ x' : A.subst σ' :=
          ((HA.substCongr W.toSubstEq).1).defeqDF ha
        have hv' := (LR Γ₀).conv vtAA' hv
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HB W'.fits).2 hBb_sd |>.out
        have W2 := cons hp hA1 ha.hasType.1 ((LR Γ₀).left hv) W
        have vtBB := LR.toValTy le le' (aty.2 _ hp).toType iv hmb
          ((ihB iB iv hmb).1 W2).1
        refine ((LR Γ₀).whr beta beta).2 <|
          (LR Γ₀).conv ((LR Γ₀).symm_ty vtBB) ?_
        exact ((IH W'.fits).1
          (cons hp hA1 ha' hv' W.symm.left)).2
    · have W' := cons hp hA1 ha hv W
      exact ((LR Γ₀).whr beta beta).2 <|
        (LR _).trans ((IH W'.fits).2 W'.left) ((IH W'.fits).1 W').2
  | @forallE Γ A u depth body v hAty hbodyty _ _ =>
    have hdepth : depth < depth + 1 := Nat.lt_succ_self depth
    have ihA : ∀ {ρ : Valuation} {n' : Nat} {ma aa : WShape n'},
        LE_Interp ρ ma.T A → LE_Interp ρ aa.T (.sort u) →
        ma.HasType aa → LR.Adequate Γ₀ Γ ρ A A (.sort u) ma aa := by
      intro ρ n' ma aa hA hSort hma
      exact (restartSelf depth hdepth hA.witness)
        .rfl hAty hma hSort.witness
    have ihBody : ∀ {ρ : Valuation} {n' : Nat} {mb ab : WShape n'},
        LE_Interp ρ mb.T body → LE_Interp ρ ab.T (.sort v) →
        mb.HasType ab →
        LR.Adequate Γ₀ (A :: Γ) ρ body body (.sort v) mb ab := by
      intro ρ n' mb ab hbody hSort hmb
      exact (restartSelf depth hdepth hbody.witness)
        .rfl hbodyty hmb hSort.witness
    exact LR.adequateForallESelf hAty.strong hbodyty.strong
      hX.toInterp hB.toInterp htyped ihA ihBody
  | @defeq Γ A B u depth e hEq hAty hBty heTy
      ihA ihB ihe =>
    have hdepth : depth < depth + 1 := Nat.lt_succ_self depth
    have ihA' : ∀ {ρ : Valuation} {n' : Nat} {ma sa : WShape n'},
        LE_Interp ρ ma.T A → LE_Interp ρ sa.T (.sort u) →
        ma.HasType sa → LR.Adequate Γ₀ Γ ρ A A (.sort u) ma sa := by
      intro ρ n' ma sa hA hSort hma
      exact (restartSelf depth hdepth hA.witness)
        .rfl hAty hma hSort.witness
    have ihB' : ∀ {ρ : Valuation} {n' : Nat} {mb sb : WShape n'},
        LE_Interp ρ mb.T B → LE_Interp ρ sb.T (.sort u) →
        mb.HasType sb → LR.Adequate Γ₀ Γ ρ B B (.sort u) mb sb := by
      intro ρ n' mb sb hB hSort hmb
      exact (restartSelf depth hdepth hB.witness)
        .rfl hBty hmb hSort.witness
    have ihe' : ∀ {ρ : Valuation} {n' : Nat} {me ae : WShape n'},
        LE_Interp ρ me.T e → LE_Interp ρ ae.T A →
        me.HasType ae → LR.Adequate Γ₀ Γ ρ e e A me ae := by
      intro ρ n' me ae he hA hme
      exact (restartSelf depth hdepth he.witness)
        .rfl heTy hme hA.witness
    exact defeqStep hdepth hAty hEq hX.toInterp hB.toInterp htyped
      ihA' ihB' ihe'

/-- The exact-root syntax-directed worker is stable under lowering because
`Witness.mono` and `RDeepChildren.mono` retain the selected evaluator tree. -/
theorem LR.selfAdequateAtStep
    (depth : Nat)
    (defeqStep : LR.SelfAdequateDefeqStepAt Γ₀ depth)
    (hΓ₀ : Ctx.WF Γ₀)
    (constStep : LR.SelfAdequateConstStep Γ₀)
    {ρ root X} (hX : LE_Interp.Witness ρ root X)
    (children : hX.RDeepChildren (LR.CoherentSeedAt Γ₀ depth))
    (lower : ∀ (d' : Nat), d' < depth → ∀ {ρ root X}
      (hX' : LE_Interp.Witness ρ root X),
      hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
      LR.CoherentRetainedAt Γ₀ hX' d') :
    LR.SelfAdequateAt Γ₀ hX depth := by
  intro n mx bx Δ core B hroot hTyping htyped hB
  exact LR.selfAdequateExactAtStep depth defeqStep hΓ₀ constStep
    (hX.mono hroot) (children.mono hroot) lower
    rfl hTyping htyped hB

/-- Reuse the syntax-directed self-adequacy algebra without forgetting the
provenance-sensitive edge classification.

Both the constant producer and every strictly-smaller restart receive the
exact `CoherentSeedAt` tree.  In particular, this adapter does not map a
local seed to the old proof-independent retained package. -/
theorem LR.coherentSelfStep_of_steps
    (defeqStep : ∀ depth, LR.SelfAdequateDefeqStepAt Γ₀ depth)
    (hΓ₀ : Ctx.WF Γ₀)
    (constStep : LR.SelfAdequateConstStep Γ₀) :
    LR.CoherentSelfStep Γ₀ := by
  intro depth ρ root X hX children lower
  intro n mx bx Δ core B hroot hTyping htyped hB
  exact LR.selfAdequateAtStep (hX := hX)
    depth (defeqStep depth) hΓ₀ constStep
    children lower
    hroot hTyping htyped hB

/-- Compatibility construction of the coherent self algebra from completed
stratified inversion.  The recursion plumbing itself is independent of this
choice; a depth-bounded caller may supply a different `defeqStep`. -/
theorem LR.CoherentSelfStep.of_stratifiedInversion
    (inv : JointStratifiedInversion) (hΓ₀ : Ctx.WF Γ₀)
    (constStep : LR.SelfAdequateConstStep Γ₀) :
    LR.CoherentSelfStep Γ₀ :=
  LR.coherentSelfStep_of_steps
    (fun depth =>
      LR.SelfAdequateDefeqStepAt.of_stratifiedInversion inv hΓ₀ depth)
    hΓ₀ constStep

/-- A zero-arity semantic definition rule is also a concrete one-step head
reduction.  Keeping this consequence next to adequacy makes the recursive
constant case consume the local, proof-carrying contraction rather than
reconstructing a registered equation from global membership. -/
theorem Params.Semantic.defn_whRed
    {c : Name} {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (hpat : Params.Pat (.const c) r)
    {ci : VConstant} {ls : List SLevel} {Γ : List SExpr}
    (hci : Params.env.constants c = some ci) (hlen : ls.length = ci.uvars) :
    ∃ (value : VExpr) (closed : value.Closed),
      r = (.fixed value closed, .true) ∧
      IsDefEqStrong Γ (.const c ls) (SExpr.mkInst ls value)
        (SExpr.mkInst ls ci.type) ∧
      WHRed Γ (.const c ls) (SExpr.mkInst ls value) := by
  obtain ⟨value, closed, hr, hdef⟩ := Params.Semantic.defn hpat
  subst r
  have hstrong : IsDefEqStrong Γ (.const c ls) (SExpr.mkInst ls value)
      (SExpr.mkInst ls ci.type) := hdef (Γ := Γ) hci hlen
  obtain ⟨m2, hmatch⟩ : ∃ m2,
      (Pattern.const c).MatchesS (.const c ls) ls m2 :=
    ⟨_, .const (c := c) (ls := ls)⟩
  let action : Pattern.Action Γ (.fixed value closed, .true)
      (.const c ls) ls m2 (SExpr.mkInst ls ci.type) := {
    pat := hpat
    matched := hmatch
    dfs := []
    defeqs := rfl
    checked := by simp
    sound := hstrong.defeq }
  exact ⟨value, closed, rfl, hstrong, .extra action⟩

/-- The recursive iota-leaf obligation of the constant self-adequacy
producer, stated against the constant witness's own retained evaluator
data.

Everything the eventual discharge may consume is received explicitly: the
per-`R`-edge inspectable seeds and exact child trees of the constant
witness (never a reselected interpretation), the caller's substitution
certificate pinning the ambient valuation, and the strictly smaller
coherent restart family.  The seeds are deliberately NOT restated at
`Valuation.nil`: a per-edge retained result quantifies over `SubstWF` at
the seed's own valuation and is not transportable across `closedAt`,
while the prepared consumer `iotaDefEq_of_ctorExactAt_coherent` threads
exactly this ambient-`W` interface through `CoherentRhsSeedAt.mono` with
no valuation change (see the premortem's 2026-08-15 interface-decision
section).  The global `iotaWitnessStep` obligation never appears.

Status (2026-08-15 rung audit, revised by the same day's structural
repair): the major-side decomposition is still open, but its residual has
been narrowed.  Splitting the joint match and normalizing the major
through `LRS.CtorDefEq.toChain` is available, and every per-link consumer
is inversion-free.  Folding the normalized chain no longer needs
`LR.MajorChainFoldStep`: `LRS.CtorDefEq.foldRaw_of_majorChainAnchorStep`
reaches the same conclusion from `LR.MajorChainAnchorStep`, whose interior
half is a per-leaf retyping carried by the native `LRS.CtorExact`
certificate rather than raw type uniqueness at arbitrary terms, and whose
remaining raw input is subject reduction at the two root views only.  A
second, mechanical layer also remains: the framed leaf is native at its
own level, so the rectangle must be run there and transported back through
`LogRel.LiftEquiv.rect`.  See the premortem's 2026-08-15 chain-wall
entries. -/
def LR.CoherentIotaLeafStep (Γ₀ : List SExpr) : Prop :=
  ∀ (depth : Nat) {Δ : List SExpr} {σ σ' : Subst}
      {ρ : Valuation} {c : Name} {ls : List SLevel}
      {R : TShape → SExpr → Prop}
      (hR : ∀ m M, R m M → LE_Interp.Witness ρ m M),
    Ctx.WF Γ₀ →
    LR.SubstWF Γ₀ σ σ' Δ ρ →
    (∀ m M (hr : R m M), LR.CoherentSeedAt Γ₀ depth (hR m M hr)) →
    (∀ m M (hr : R m M),
      (hR m M hr).RDeepChildren (LR.CoherentSeedAt Γ₀ depth)) →
    (∀ (d' : Nat), d' < depth →
      ∀ {ρ' : Valuation} {root : TShape} {X : SExpr}
        (hX' : LE_Interp.Witness ρ' root X),
        hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
        LR.CoherentRetainedAt Γ₀ hX' d') →
    ∀ (level : Nat),
      LR.IotaLeafDefEqAt Γ₀ level c ls (LE_Interp.Lower R)

/-- Guarded counterpart of `LR.CoherentIotaLeafStep`.

Genuine semantic evaluator edges retain all-depth guarded coherence through
`LRD.CoherentSeedAt`; rebuilt strict predecessors remain explicitly local.
The ambient substitution, paired leaf spine, and result relation retain their
guarded forms. -/
def LRD.CoherentIotaLeafStep (Γ₀ : List SExpr) : Prop :=
  ∀ (depth : Nat) {Δ : List SExpr} {σ σ' : Subst}
      {ρ : Valuation} {c : Name} {ls : List SLevel}
      {R : TShape → SExpr → Prop}
      (hR : ∀ m M, R m M → LE_Interp.Witness ρ m M),
    Ctx.WF Γ₀ →
    LR.DirectSubstWF Γ₀ σ σ' Δ ρ →
    (∀ m M (hr : R m M), LRD.CoherentSeedAt Γ₀ depth (hR m M hr)) →
    (∀ m M (hr : R m M),
      (hR m M hr).RDeepChildren (LRD.CoherentSeedAt Γ₀ depth)) →
    (∀ (d' : Nat), d' < depth →
      ∀ {ρ' : Valuation} {root : TShape} {X : SExpr}
        (hX' : LE_Interp.Witness ρ' root X),
        hX'.RDeepChildren (LRD.CoherentSeedAt Γ₀ d') →
        LRD.CoherentRetainedAt Γ₀ hX' d') →
    ∀ (level : Nat),
      LRD.IotaLeafDefEqAt Γ₀ level c ls (LE_Interp.Lower R)

/-- A guarded iota-leaf callback indexed by the registered constant type's
actual stratification certificate.

Unlike `LRD.CoherentIotaLeafStep`, this interface exposes the registration,
universe-arity, and typing evidence that created the enclosing constant
witness.  Its evaluator seeds live at the corresponding strict successor,
so a leaf implementation can justify strict recursive restarts from the
registered type instead of from an unrelated numeric budget. -/
def LRD.CoherentTypedIotaLeafStep (Γ₀ : List SExpr) : Prop :=
  ∀ (typeDepth : Nat) {Δ : List SExpr} {σ σ' : Subst}
      {ρ : Valuation} {c : Name} {ci : VConstant}
      {ls : List SLevel} {u : SLevel}
      {R : TShape → SExpr → Prop},
    Params.env.constants c = some ci →
    ls.length = ci.uvars →
    HasTypeStratifiedS Δ (SExpr.mkInst ls ci.type)
      (.sort u) true typeDepth →
    (hR : ∀ m M, R m M → LE_Interp.Witness ρ m M) →
    Ctx.WF Γ₀ →
    LR.DirectSubstWF Γ₀ σ σ' Δ ρ →
    (∀ m M (hr : R m M),
      LRD.CoherentSeedAt Γ₀ (typeDepth + 1) (hR m M hr)) →
    (∀ m M (hr : R m M),
      (hR m M hr).RDeepChildren
        (LRD.CoherentSeedAt Γ₀ (typeDepth + 1))) →
    (∀ (d' : Nat), d' < typeDepth + 1 →
      ∀ {ρ' : Valuation} {root : TShape} {X : SExpr}
        (hX' : LE_Interp.Witness ρ' root X),
        hX'.RDeepChildren (LRD.CoherentSeedAt Γ₀ d') →
        LRD.CoherentRetainedAt Γ₀ hX' d') →
    ∀ (level : Nat),
      LRD.RegisteredIotaLeafDefEqAt Γ₀ ρ
        (SExpr.mkInst ls ci.type) level c ls (LE_Interp.Lower R)

/-- The original numeric-budget leaf callback remains a source for the typed
interface: instantiate it at the registered type's strict successor. -/
theorem LRD.CoherentIotaLeafStep.toTyped
    (H : LRD.CoherentIotaLeafStep Γ₀) :
    LRD.CoherentTypedIotaLeafStep Γ₀ := by
  intro typeDepth Δ σ σ' ρ c ci ls u R _hreg _hlen _hTy
    hR hΓ W pR cR lower level
  exact LRD.IotaLeafDefEqAt.toRegistered
    (ρ := ρ) (headType := SExpr.mkInst ls ci.type)
    (H (typeDepth + 1) hR hΓ W pR cR lower level)

/-- Build the full guarded constant callback when zero-argument registered
patterns are impossible.

This is the exact generic interface needed by the iota-only Nat fixture.
The registered type is restarted at the strict syntax predecessor and its
guarded Pi observation feeds `LRD.constDefEqRootLam`; reached nonempty leaves
are delegated to `LRD.CoherentIotaLeafStep`.  Constructor and inductive-head
observations add no guarded side condition, and the caller's separately
supplied legacy result provides their additive first projection. -/
theorem LRD.SelfAdequateConstStep.of_noConstPat_typed
    (hΓ₀ : Ctx.WF Γ₀)
    (leafStep : LRD.CoherentTypedIotaLeafStep Γ₀)
    (noConstPat : ∀ {c : Name}
      {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      Params.Pat (.const c) r → False) :
    LRD.SelfAdequateConstStep Γ₀ := by
  intro c ci Γ ls u depth ρ n mx bx hreg hlen hTy lower htyped hB hX
    children legacyAdequate
  cases children with
  | bot => exact LRD.Adequate.bot htyped.isType
  | const cA pR cR =>
    rename_i a₀ ci' R m' hm'ty n₀ hR hle hreg' hlen' hA'w hC
    cases hreg.symm.trans hreg'
    have restartDirect : ∀ {ρ' : Valuation} {root : TShape} {X : SExpr}
        (hX' : LE_Interp.Witness ρ' root X),
        LRD.SelfAdequateAt Γ₀ hX' depth := fun hX' =>
      (LRD.CoherentRetainedAt.restart (lower := lower)
        (Nat.lt_succ_self depth) (hX := hX')).2
    suffices h : ∀ {σ σ'}, LR.DirectSubstWF Γ₀ σ σ' Γ ρ →
        (LRD Γ₀).DefEq (.const c ls) (.const c ls)
          ((SExpr.mkInst ls ci.type).subst σ) mx bx from
      ⟨fun _ _ W => ⟨h W, h W⟩, fun _ W => h W⟩
    intro σ σ' W
    have hlegacy : (LR Γ₀).DefEq (.const c ls) (.const c ls)
        ((SExpr.mkInst ls ci.type).subst σ) mx bx := by
      simpa only [SExpr.subst] using
        (legacyAdequate.2 W.left.toSubstWF)
    rw [(Params.henv.closedC hreg).mkInstS.subst_eq .zero]
    rw [(Params.henv.closedC hreg).mkInstS.subst_eq .zero] at hlegacy
    have hC' : LE_Interp.Const c ls (LE_Interp.Lower R) [] mx.T :=
      hC.mono hle fun le hr => ⟨_, le, hr⟩
    cases hC' with
    | bot => exact LRD.DefEq.bot htyped.isType
    | lam hrec hlam =>
      rename_i fsem
      cases htyped.unfold with
      | bot hm => exact LRD.DefEq.bot hm
      | sort => exact (TShape.sort_not_le_lam' hlam).elim
      | forallE => exact (TShape.forallE_not_le_lam' hlam).elim
      | @lam k f a₁ a₂ htm =>
        obtain ⟨n', mTy, sTy, le_n, le_a, hTy', hSort, hmTy⟩ :=
          (LE_Interp.sound hTy.strong W.left.fits).2 hB.toInterp |>.out
        have htyAdequate := (restartDirect hTy'.witness)
          .rfl hTy hmTy hSort.witness
        have htyRelation : (LRD Γ₀).DefEq
            (mkInst ls ci.type) (mkInst ls ci.type) (.sort u) mTy sTy := by
          simpa only [SExpr.subst,
            (Params.henv.closedC hreg).mkInstS.subst_eq .zero] using
            (htyAdequate.2 W.left)
        have htyDirect : (LRD Γ₀).TyDefEq
            (mkInst ls ci.type) (mkInst ls ci.type) (.forallE a₁ a₂) :=
          LRD.toValTy le_n le_a htyped.isType hSort hmTy htyRelation
        have hregistered : LE_Interp.Witness ρ
            (WShape.forallE a₁ a₂).T (mkInst ls ci.type) :=
          hTy'.witness.mono le_a
        unfold WShape.lam'
        split <;> rename_i hf
        · have evalPat : ∀ j,
              LRD.RegisteredPatternLeafDefEqAt Γ₀ ρ
                (mkInst ls ci.type) j c ls
                (LE_Interp.Lower R) := fun j =>
            LRD.RegisteredPatternLeafDefEqAt.of_iota
              (leafStep depth hreg hlen hTy hR hΓ₀ W pR cR lower j)
          exact LRD.constDefEqRootLam (hf := hf) htm hlam hrec
            (fun le hr => hr.mono le) evalPat (.const hreg hlen)
            (by simpa [WShape.lam', hf] using hlegacy) htyDirect
            hregistered
        · exact LRD.DefEq.bot htyped.isType
      | ctor => exact (TShape.ctor_not_le_lam' hlam).elim
      | indTy => exact (TShape.indTy_not_le_lam' hlam).elim
    | ctor hcl hctor =>
      cases htyped.unfold with
      | bot hm => exact LRD.DefEq.bot hm
      | sort => exact (TShape.sort_not_le_ctor' hctor).elim
      | forallE => exact (TShape.forallE_not_le_ctor' hctor).elim
      | lam htm =>
        unfold WShape.lam' at hctor ⊢
        split at hctor <;> rename_i hnz
        · exact (TShape.lam_not_le_ctor' hctor).elim
        · simpa [hnz] using LRD.DefEq.bot htyped.isType
      | ctor => exact LRD.DefEq.of_legacy_indTy hlegacy
      | indTy => exact (TShape.indTy_not_le_ctor' hctor).elim
    | indTy hcl hind =>
      cases htyped.unfold with
      | bot hm => exact LRD.DefEq.bot hm
      | sort => exact (TShape.sort_not_le_indTy hind).elim
      | forallE => exact (TShape.forallE_not_le_indTy hind).elim
      | lam htm =>
        unfold WShape.lam' at hind ⊢
        split at hind <;> rename_i hnz
        · exact (TShape.lam_not_le_indTy hind).elim
        · simpa [hnz] using LRD.DefEq.bot htyped.isType
      | ctor => exact (TShape.ctor_not_le_indTy hind).elim
      | indTy => exact LRD.DefEq.of_legacy_indTy_type hlegacy
    | pat hpat hmatch hrhs =>
      have hp := hmatch.nil_inv
      subst hp
      exact (noConstPat hpat).elim

/-- Compatibility wrapper for callers that already discharge every numeric
leaf budget.  New fixture-specific proofs should prefer
`of_noConstPat_typed`, which exposes the enclosing registered-type evidence. -/
theorem LRD.SelfAdequateConstStep.of_noConstPat
    (hΓ₀ : Ctx.WF Γ₀)
    (leafStep : LRD.CoherentIotaLeafStep Γ₀)
    (noConstPat : ∀ {c : Name}
      {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      Params.Pat (.const c) r → False) :
    LRD.SelfAdequateConstStep Γ₀ :=
  LRD.SelfAdequateConstStep.of_noConstPat_typed
    hΓ₀ leafStep.toTyped noConstPat

/--
info: 'Lean4Lean.SExpr.LRD.SelfAdequateConstStep.of_noConstPat_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LRD.SelfAdequateConstStep.of_noConstPat_typed

/--
info: 'Lean4Lean.SExpr.LRD.SelfAdequateConstStep.of_noConstPat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRD.SelfAdequateConstStep.of_noConstPat

/-- The definitional-unfold obligation of the constant producer at a local
(guarded-restart) evaluator seed.

The stratified `const` rule certifies only the constant's type, so the
registered value's certificate depth is unrelated to a local seed's
budget: a genuine semantic child covers every depth through its all-depth
result, but a rebuilt child is pinned to one index.  This hypothesis
names that residual budget question — a local coherent result on a
registered definitional value extends to the value's own certificate
depths — instead of widening `CoherentSeedAt` mid-construction. -/
def LR.ConstDefnLocalStep (Γ₀ : List SExpr) : Prop :=
  ∀ {c : Name} {ci : VConstant} {value : VExpr} {closed : value.Closed},
    Params.Pat (.const c) (.fixed value closed, .true) →
    Params.env.constants c = some ci →
    ∀ {ls : List SLevel}, ls.length = ci.uvars →
    ∀ (depth : Nat) {ρ : Valuation} {root : TShape}
      (hV : LE_Interp.Witness ρ root (SExpr.mkInst ls value)),
      LR.CoherentRetainedAt Γ₀ hV depth →
      hV.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
      ∀ (depth' : Nat), LR.SelfAdequateAt Γ₀ hV depth'

/-- The strictly deeper half of `ConstDefnLocalStep`, which is all of its
residual content.

`LR.SelfAdequateAt` mentions its depth index only in the stratified
certificate it consumes, and `HasTypeStratifiedS.mono` raises a certificate
to any larger index.  So a local seed at index `depth` already discharges
every `depth' ≤ depth` without any further hypothesis
(`ConstDefnLocalStep.of_deepStep` below), and the whole question is the
strictly deeper case.

That is exactly where the definitional-unfold budget lives.  The stratified
`const` rule certifies only `SExpr.mkInst ls ci.type` (SExpr:2383-2387), so
nothing in a constant's own derivation bounds the stratified depth of its
registered value — a definitional value is routinely deeper than its
declared type.  Closedness of the value does not help: it constrains
substitution, not stratification depth.  A discharge must therefore couple
the budget to the seed at its creation point, in the manner
`CoherentRhsSeedAt` already models one level up. -/
def LR.ConstDefnDeepStep (Γ₀ : List SExpr) : Prop :=
  ∀ {c : Name} {ci : VConstant} {value : VExpr} {closed : value.Closed},
    Params.Pat (.const c) (.fixed value closed, .true) →
    Params.env.constants c = some ci →
    ∀ {ls : List SLevel}, ls.length = ci.uvars →
    ∀ (depth : Nat) {ρ : Valuation} {root : TShape}
      (hV : LE_Interp.Witness ρ root (SExpr.mkInst ls value)),
      LR.CoherentRetainedAt Γ₀ hV depth →
      hV.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
      ∀ (depth' : Nat), depth < depth' → LR.SelfAdequateAt Γ₀ hV depth'

/-- Only strictly deeper certificates are residual.  A certificate at or
below the local seed's own index is raised to that index by
`HasTypeStratifiedS.mono` and consumed by the local result directly, so this
reduction spends no adequacy content whatsoever — it is pure depth
arithmetic. -/
theorem LR.ConstDefnLocalStep.of_deepStep
    (deep : LR.ConstDefnDeepStep Γ₀) : LR.ConstDefnLocalStep Γ₀ := by
  intro c ci value closed hpat hreg ls hlen depth ρ root hV hlocal children
    depth'
  rcases Nat.lt_or_ge depth depth' with hlt | hle
  · exact deep hpat hreg hlen depth hV hlocal children depth' hlt
  · intro n mx bx Δ core B hroot hstrat hmem hB
    exact hlocal.1 hroot (hstrat.mono hle) hmem hB

/-! ### Retention and demand narrowing for the definitional-unfold budget

The two Props above commit two erasures at their single call site
(`LR.SelfAdequateConstStep.of_steps`).  In the *supply* direction they drop
the strictly smaller coherent restart family `lower` and `Ctx.WF Γ₀`, both
of which are in scope where they are consumed: the producer knew more than
it handed over.  In the *demand* direction their conclusion quantifies over
every `Δ`, `B` and `core` of `LR.SelfAdequateAt`, while the call site
consumes exactly one instance, pinned to `B := SExpr.mkInst ls ci.type` and
`core := true` by the registered definitional equation
`Params.Semantic.defn_whRed`.

Unlike the depth index, the *type* index is fixed by the declaration rather
than chosen downstream, so it can be narrowed leaf-locally — the same move
the chain-wall repair made (narrow the subject, keep the position).  The
declarations below carry out both narrowings; the originals are kept
unchanged as reference statements, and the faithfulness lemmas record that
the new forms are weakenings, so whatever discharges the old obligations
discharges these.

This does NOT discharge the residual: it narrows it.  What remains still
needs the δ-rank well-founded component (separate design pass). -/

/-- Retentive form of `LR.ConstDefnLocalStep`: the restart family `lower`
and `Ctx.WF Γ₀` are retained instead of erased. -/
def LR.ConstDefnLocalStepR (Γ₀ : List SExpr) : Prop :=
  ∀ {c : Name} {ci : VConstant} {value : VExpr} {closed : value.Closed},
    Params.Pat (.const c) (.fixed value closed, .true) →
    Params.env.constants c = some ci →
    ∀ {ls : List SLevel}, ls.length = ci.uvars →
    ∀ (depth : Nat) {ρ : Valuation} {root : TShape}
      (hV : LE_Interp.Witness ρ root (SExpr.mkInst ls value)),
      LR.CoherentRetainedAt Γ₀ hV depth →
      hV.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
      (∀ (d' : Nat), d' < depth →
        ∀ {ρ' : Valuation} {root' : TShape} {X : SExpr}
          (hX : LE_Interp.Witness ρ' root' X),
          hX.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
          LR.CoherentRetainedAt Γ₀ hX d') →
      Ctx.WF Γ₀ →
      ∀ (depth' : Nat), LR.SelfAdequateAt Γ₀ hV depth'

/-- Retentive form of `LR.ConstDefnDeepStep`. -/
def LR.ConstDefnDeepStepR (Γ₀ : List SExpr) : Prop :=
  ∀ {c : Name} {ci : VConstant} {value : VExpr} {closed : value.Closed},
    Params.Pat (.const c) (.fixed value closed, .true) →
    Params.env.constants c = some ci →
    ∀ {ls : List SLevel}, ls.length = ci.uvars →
    ∀ (depth : Nat) {ρ : Valuation} {root : TShape}
      (hV : LE_Interp.Witness ρ root (SExpr.mkInst ls value)),
      LR.CoherentRetainedAt Γ₀ hV depth →
      hV.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
      (∀ (d' : Nat), d' < depth →
        ∀ {ρ' : Valuation} {root' : TShape} {X : SExpr}
          (hX : LE_Interp.Witness ρ' root' X),
          hX.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
          LR.CoherentRetainedAt Γ₀ hX d') →
      Ctx.WF Γ₀ →
      ∀ (depth' : Nat), depth < depth' → LR.SelfAdequateAt Γ₀ hV depth'

/-- Only strictly deeper certificates are residual — the
`LR.ConstDefnLocalStep.of_deepStep` argument, threaded through the retained
restart family unchanged. -/
theorem LR.ConstDefnDeepStepR.toLocal {Γ₀ : List SExpr}
    (deep : LR.ConstDefnDeepStepR Γ₀) : LR.ConstDefnLocalStepR Γ₀ := by
  intro c ci value closed hpat hreg ls hlen depth ρ root hV hlocal children
    lower hΓ₀ depth'
  rcases Nat.lt_or_ge depth depth' with hlt | hle
  · exact deep hpat hreg hlen depth hV hlocal children lower hΓ₀ depth' hlt
  · intro n mx bx Δ core B hroot hstrat hmem hB
    exact hlocal.1 hroot (hstrat.mono hle) hmem hB

/-- Faithfulness: the retentive Props are *weakenings*, not restatements. -/
theorem LR.ConstDefnDeepStepR.of_constDefnDeepStep {Γ₀ : List SExpr}
    (H : LR.ConstDefnDeepStep Γ₀) : LR.ConstDefnDeepStepR Γ₀ := by
  intro c ci value closed hpat hreg ls hlen depth ρ root hV hlocal children
    _lower _hΓ₀ depth' hlt
  exact H hpat hreg hlen depth hV hlocal children depth' hlt

/-- Faithfulness for the local form. -/
theorem LR.ConstDefnLocalStepR.of_constDefnLocalStep {Γ₀ : List SExpr}
    (H : LR.ConstDefnLocalStep Γ₀) : LR.ConstDefnLocalStepR Γ₀ := by
  intro c ci value closed hpat hreg ls hlen depth ρ root hV hlocal children
    _lower _hΓ₀ depth'
  exact H hpat hreg hlen depth hV hlocal children depth'

/-- The δ-unfold obligation as the single instance the call site consumes.

Strictly weaker than `LR.ConstDefnDeepStepR`: the certificate depth `nV` is
now bound where the certificate is supplied rather than universally ahead of
it, and the observed type is pinned to the registered `SExpr.mkInst ls
ci.type` at `core := true`. -/
def LR.ConstDefnDeepInstStep (Γ₀ : List SExpr) : Prop :=
  ∀ {c : Name} {ci : VConstant} {value : VExpr} {closed : value.Closed},
    Params.Pat (.const c) (.fixed value closed, .true) →
    Params.env.constants c = some ci →
    ∀ {ls : List SLevel}, ls.length = ci.uvars →
    ∀ (depth : Nat) {ρ : Valuation} {root : TShape}
      (hV : LE_Interp.Witness ρ root (SExpr.mkInst ls value)),
      LR.CoherentRetainedAt Γ₀ hV depth →
      hV.RDeepChildren (LR.CoherentSeedAt Γ₀ depth) →
      (∀ (d' : Nat), d' < depth →
        ∀ {ρ' : Valuation} {root' : TShape} {X : SExpr}
          (hX : LE_Interp.Witness ρ' root' X),
          hX.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
          LR.CoherentRetainedAt Γ₀ hX d') →
      Ctx.WF Γ₀ →
      ∀ {Γ : List SExpr} {n : Nat} {mx bx : WShape n} {nV : Nat},
        mx.T ≤ root →
        HasTypeStratifiedS Γ (SExpr.mkInst ls value)
          (SExpr.mkInst ls ci.type) true nV →
        mx.HasType bx →
        LE_Interp.Witness ρ bx.T (SExpr.mkInst ls ci.type) →
        LR.Adequate Γ₀ Γ ρ (SExpr.mkInst ls value) (SExpr.mkInst ls value)
          (SExpr.mkInst ls ci.type) mx bx

/-! #### The δ-rank producer

The environment supplies only the ranked certificate for a registered
definition.  Recursion remains an explicit premise: it is outermost in the
δ-rank and independent of the existing depth/witness recursion.  This
separation prevents a cyclic `VEnv.WF` block from silently becoming a
termination proof.
-/

/-- `SelfAdequateAt` restricted to typing derivations below one δ-rank. -/
def LR.SelfAdequateAtR [Params.DeltaRank] (Γ₀ : List SExpr)
    {rho : Valuation} {root : TShape} {X : SExpr}
    (_hX : LE_Interp.Witness rho root X) (depth rankBound : Nat) : Prop :=
  ∀ {n : Nat} {mx bx : WShape n} {Delta : List SExpr}
      {core : Bool} {B : SExpr},
    mx.T ≤ root →
    HasTypeStratifiedR Params.DeltaRank.rank Delta X B core depth rankBound →
    mx.HasType bx →
    LE_Interp.Witness rho bx.T B →
    LR.Adequate Γ₀ Delta rho X X B mx bx

/-- Adequacy at every rank recovers the unranked statement. -/
theorem LR.selfAdequateAt_of_allRanks [Params.DeltaRank]
    {hX : LE_Interp.Witness rho root X} {depth : Nat}
    (H : ∀ rankBound, LR.SelfAdequateAtR Γ₀ hX depth rankBound) :
    LR.SelfAdequateAt Γ₀ hX depth := by
  intro n mx bx Delta core B hroot hstrat hmem hB
  obtain ⟨rankBound, hranked⟩ :=
    HasTypeStratifiedR.exists_rank Params.DeltaRank.rank hstrat
  exact H rankBound hroot hranked hmem hB

/-- Unranked self-adequacy can always serve a fixed rank. -/
theorem LR.SelfAdequateAt.toRank [Params.DeltaRank]
    {hX : LE_Interp.Witness rho root X} {depth rankBound : Nat}
    (H : LR.SelfAdequateAt Γ₀ hX depth) :
    LR.SelfAdequateAtR Γ₀ hX depth rankBound :=
  fun hroot hstrat hmem hB => H hroot hstrat.toS hmem hB

/-- The induction hypotheses supplied by an outer strong recursion on the
δ-rank. -/
def LR.DeltaRankRestart [Params.DeltaRank] (Γ₀ : List SExpr)
    (rankBound : Nat) : Prop :=
  ∀ rank' : Nat, rank' < rankBound →
    ∀ {rho : Valuation} {root : TShape} {X : SExpr}
      (hX : LE_Interp.Witness rho root X) (depth : Nat),
      LR.SelfAdequateAtR Γ₀ hX depth rank'

theorem LR.DeltaRankRestart.of_le [Params.DeltaRank]
    {rankBound rankBound' : Nat} (hle : rankBound' ≤ rankBound)
    (H : LR.DeltaRankRestart Γ₀ rankBound) :
    LR.DeltaRankRestart Γ₀ rankBound' :=
  fun rank' hlt => H rank' (Nat.lt_of_lt_of_le hlt hle)

/-- The sole staged δ obligation: every rank receives its strict
predecessors. -/
def LR.DeltaRankStage [Params.DeltaRank] (Γ₀ : List SExpr) : Prop :=
  ∀ rankBound, LR.DeltaRankRestart Γ₀ rankBound

/-- The narrowed definitional-unfold obligation follows directly from the
environment certificate and the restart at the unfolded constant's rank. -/
theorem LR.ConstDefnDeepInstStep.of_deltaRank [Params.DeltaRank]
    (restart : ∀ c : Name,
      LR.DeltaRankRestart Γ₀ (Params.DeltaRank.rank c)) :
    LR.ConstDefnDeepInstStep Γ₀ := by
  intro c ci value closed hpat hreg ls hlen depth rho root hV hlocal children
    lower hGamma Gamma n mx bx nV hroot hstrat htyped hB
  obtain ⟨nV', rankV, hlt, hcert⟩ :=
    Params.DeltaRank.defnCert (Γ := Gamma) hpat hreg hlen
  exact restart c rankV hlt hV nV' hroot hcert htyped hB

/-- The stronger retentive interface is exactly what a complete outer rank
stage supplies; it adds no further semantic premise. -/
theorem LR.ConstDefnDeepStepR.of_deltaRankStage [Params.DeltaRank]
    (stage : LR.DeltaRankStage Γ₀) : LR.ConstDefnDeepStepR Γ₀ := by
  intro c ci value closed hpat hreg ls hlen depth rho root hV hlocal children
    lower hGamma depth' hlt
  refine LR.selfAdequateAt_of_allRanks (hX := hV) fun rankBound => ?_
  exact stage (rankBound + 1) rankBound (Nat.lt_succ_self rankBound) hV depth'

/-- info: 'Lean4Lean.SExpr.LR.ConstDefnDeepInstStep.of_deltaRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LR.ConstDefnDeepInstStep.of_deltaRank

/-- info: 'Lean4Lean.SExpr.LR.ConstDefnDeepStepR.of_deltaRankStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LR.ConstDefnDeepStepR.of_deltaRankStage

/-- Faithfulness: the narrowed form is implied by the retentive form, hence
(through `LR.ConstDefnDeepStepR.of_constDefnDeepStep`) by the current
`LR.ConstDefnDeepStep`. -/
theorem LR.ConstDefnDeepInstStep.of_deepStepR {Γ₀ : List SExpr}
    (H : LR.ConstDefnDeepStepR Γ₀) : LR.ConstDefnDeepInstStep Γ₀ := by
  intro c ci value closed hpat hreg ls hlen depth ρ root hV hlocal children
    lower hΓ₀ Γ n mx bx nV hroot hstrat htyped hB
  rcases Nat.lt_or_ge depth nV with hlt | hle
  · exact H hpat hreg hlen depth hV hlocal children lower hΓ₀ nV hlt
      hroot hstrat htyped hB
  · exact hlocal.1 hroot (hstrat.mono hle) htyped hB

/-- Produce the constant case of retained self-adequacy from the witness's
own `children`/`lower` data.

This is the derivation-induction-free remake of the constant case: the
constant's type restarts through `lower` at the strictly smaller
certificate depth carried by the stratified `const` rule; the constructor
and inductive-type heads are discharged from that same restart; the
definitional unfold consumes the seed retained on the witness's own `R`
edge (`ConstDefnLocalStep` covers only the local-seed branch); and every
reached iota leaf consumes `CoherentIotaLeafStep` at the witness's own
seeds under the ambient substitution certificate.  Neither the global
`iotaWitnessStep` obligation nor any same-depth adequacy is consumed. -/
theorem LR.SelfAdequateConstStep.of_steps
    (piInv : LRS.PiPathInv)
    (hΓ₀ : Ctx.WF Γ₀)
    (leafStep : LR.CoherentIotaLeafStep Γ₀)
    (defnStep : LR.ConstDefnDeepInstStep Γ₀) :
    LR.SelfAdequateConstStep Γ₀ := by
  intro c ci Γ ls u depth ρ n mx bx hreg hlen hTy lower htyped hB hX children
  cases children with
  | bot => exact LR.Adequate.bot htyped.isType
  | const cA pR cR =>
    rename_i a₀ ci' R m' hm'ty n₀ hR hle hreg' hlen' hA'w hC
    cases hreg.symm.trans hreg'
    have restartSelf : ∀ {ρ' : Valuation} {root : TShape} {X : SExpr}
        (hX' : LE_Interp.Witness ρ' root X),
        LR.SelfAdequateAt Γ₀ hX' depth := fun hX' =>
      (LR.CoherentRetainedAt.restart (lower := lower)
        (Nat.lt_succ_self depth) (hX := hX')).1
    suffices h : ∀ {σ σ'}, LR.SubstWF Γ₀ σ σ' Γ ρ →
        (LR Γ₀).DefEq (.const c ls) (.const c ls)
          ((SExpr.mkInst ls ci.type).subst σ) mx bx from
      ⟨fun _ _ W => ⟨h W, h W⟩, fun _ W => h W⟩
    intro σ σ' W
    rw [(Params.henv.closedC hreg).mkInstS.subst_eq .zero]
    have hC' : LE_Interp.Const c ls (LE_Interp.Lower R) [] mx.T :=
      hC.mono hle fun le hr => ⟨_, le, hr⟩
    cases hC' with
    | bot => exact (LR Γ₀).bot htyped.isType
    | lam hrec hlam =>
      rename_i fsem
      cases htyped.unfold with
      | bot hm => exact (LR Γ₀).bot hm
      | sort => exact (TShape.sort_not_le_lam' hlam).elim
      | forallE => exact (TShape.forallE_not_le_lam' hlam).elim
      | @lam k f a₁ a₂ htm =>
        obtain ⟨n', mTy, sTy, le_n, le_a, hTy', hSort, hmTy⟩ :=
          (LE_Interp.sound hTy.strong W.left.fits).2 hB.toInterp |>.out
        have hty' := (restartSelf hTy'.witness .rfl hTy hmTy
          hSort.witness).2 W.left
        rw [(Params.henv.closedC hreg).mkInstS.subst_eq .zero] at hty'
        have hty : (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type)
            (.forallE a₁ a₂) :=
          toValTy le_n le_a htyped.isType hSort hmTy hty'
        rw [LR_succ] at hty ⊢
        unfold WShape.lam'
        split <;> rename_i hf
        · obtain ⟨A₁, A₂, _, _, u₁, u₂, hred, _, hA₁, hA₂, hvalA₁, hpi⟩ := hty
          refine (LRS.DefEq.lam_forallE (M := .const c ls) (N := .const c ls)
            (A := mkInst ls ci.type) (f := f) (hf := hf) (a₁ := a₁) (a₂ := a₂)
            (LR Γ₀)).2
            ⟨A₁, A₂, u₁, u₂, hred, hA₁.leftType,
              (LR Γ₀).left_ty hvalA₁, hA₂.leftType, LRS.PiDefEq.left hpi, ?_⟩
          have eval : ∀ {K : Nat}, K = k → ∀
              {x y : SExpr} {p : WShape K} {x₀ y₀ : WShape n₀},
              p.HasType (a₁.lift K) →
              Γ₀ ⊢ x ≡ y : A₁ →
              (LR Γ₀).DefEq x y A₁ p (a₁.lift K) →
              (x₀, y₀) ∈ fsem → x₀.T ≤ p.T →
              ((f.lift K).app p).T ≤ y₀.T →
              (LR Γ₀).DefEq ((const c ls).app x) ((const c ls).app y)
                (A₂.inst x) ((f.lift K).app p) ((a₂.lift K).app p) := by
            intro K hK
            subst K
            intro x y p x₀ y₀ hp hxy hv hmem₀ hx₀ hy₀
            have hn : k ≤ k := Nat.le_refl k
            have hPiK : LRS.PiDefEq (LR Γ₀) A₁ A₂ A₂
                (a₁.lift k) (a₂.lift k) :=
              (LRS.PiDefEq.lift hn htm.1).2 (LRS.PiDefEq.left hpi)
            have hAK : (LR Γ₀).TyDefEq (A₂.inst x) (A₂.inst x)
                ((a₂.lift k).app p) :=
              hPiK.2 hp hxy.hasType.1 ((LR Γ₀).left hv)
            have hout : ((f.lift k).app p).HasType ((a₂.lift k).app p) :=
              (WShape.HasTypeLam.iff.1 ((WShape.HasTypeLam.lift hn).2 htm)).2.2 p hp
            have hType₀ : Γ₀ ⊢ mkInst ls ci.type : .sort u := by
              simpa only [(Params.henv.closedC hreg).mkInstS.subst_eq .zero,
                SExpr.subst] using
                (hTy.strong.subst W.left.toSubstEq).hasType.1
            have hTypePi : Γ₀ ⊢
                mkInst ls ci.type ≡ .forallE A₁ A₂ : .sort u :=
              hred.defeq_of_piPathInv piInv hΓ₀ hType₀
            have hConstPi : Γ₀ ⊢ .const c ls : .forallE A₁ A₂ :=
              hTypePi.defeqDF (.const hreg hlen)
            have hAppTerm : Γ₀ ⊢
                SExpr.app (SExpr.const c ls) x ≡
                  SExpr.app (SExpr.const c ls) y : A₂.inst x :=
              .appDF hConstPi hxy
            have hAppType : Γ₀ ⊢ A₂.inst x : .sort u₂ :=
              (IsDefEq.beta hA₂.leftType hxy.hasType.1).hasType.2
            have hAppSpineX : SExpr.SpineWF Γ₀ (mkInst ls ci.type)
                [x] (A₂.inst x) := by
              simpa only [List.nil_append] using
                (SExpr.SpineWF.nil (Γ := Γ₀) (A := mkInst ls ci.type)).snoc
                  hTypePi hxy.hasType.1
            obtain ⟨_, hAppCodomain⟩ := (hPiK.1 hp hxy hv).leftDefEq
            have hAppSpineY : SExpr.SpineWF Γ₀ (mkInst ls ci.type)
                [y] (A₂.inst x) := by
              have hspine :=
                (SExpr.SpineWF.nil (Γ := Γ₀) (A := mkInst ls ci.type)).snoc
                  hTypePi hxy.hasType.2
              exact SExpr.SpineWF.ret hspine hAppCodomain.symm
            have hA₁K : (LR Γ₀).TyDefEq A₁ A₁ (a₁.lift k) :=
              (LR.TyDefEq.lift hn
                (WShape.HasTypePi.iff.1 htm.1).1.isType).2
                ((LR Γ₀).left_ty hvalA₁)
            let hAppPair : SExpr.SpineWF.LastPair Γ₀
                (mkInst ls ci.type) [] [] x y (A₂.inst x) := {
                prefixType := mkInst ls ci.type
                domain := A₁
                codomain := A₂
                piSort := u
                resultSortX := u₂
                resultSortY := _
                prefixX := .nil
                prefixY := .nil
                pi := hTypePi
                major := hxy
                resultX := hAppType
                resultY := hAppCodomain.symm }
            have hAppAligned : LRS.CtorSpineDefEq (LR Γ₀)
                (mkInst ls ci.type) [x] [y] [p] (A₂.inst x) :=
              .cons .nil hTypePi hp hA₁K hxy hv hAppCodomain.symm
            have hAppLeaf : LR.PatternLeafSpine Γ₀ (LR Γ₀)
                (mkInst ls ci.type) [x] [y] [p] (A₂.inst x)
                ((f.lift k).app p) ((a₂.lift k).app p) := {
              majorX := x
              recXs := []
              majorY := y
              recYs := []
              majorShape := p
              recShapes := []
              majorTypeShape := a₁.lift k
              resultShape := f.lift k
              resultTypeShape := a₂.lift k
              args_eq := rfl
              args'_eq := rfl
              rargs_eq := rfl
              out_eq := rfl
              outTy_eq := rfl
              pair := hAppPair
              majorHasType := hp
              resultType := (WShape.HasTypePi.lift hn).2 htm.1
              majorType := hA₁K
              majorRel := hv
              aligned := hAppAligned
              pi := hPiK }
            have evalPat : LR.PatternLeafDefEqAt Γ₀ k c ls
                (LE_Interp.Lower R) :=
              LR.PatternLeafDefEqAt.of_iota
                (leafStep (depth + 1) hR hΓ₀ W pR cR lower k)
            simpa only [List.foldr_cons, List.foldr_nil] using
              LR.constDefEq piInv hΓ₀ (fun le hr => hr.mono le)
                (hrec x₀ y₀ hmem₀) evalPat
                (.cons hx₀ .nil) hAppLeaf
                hAppTerm ⟨u₂, hAppType⟩ (.const hreg hlen) hAppSpineX hAppSpineY
                hout hAK hy₀
          exact LR.constLamDefEq (hf := hf) (nArgs := 0) htm hlam
            (fun {_ _ _ _ _} hp hxy hv hmem₀ hx₀ hy₀ =>
              LogRel.DefEqRect.diagonal
                (eval (Nat.max_eq_left (Nat.zero_le k))
                  hp hxy hv hmem₀ hx₀ hy₀))
        · exact (LR Γ₀).bot htyped.isType
      | ctor => exact (TShape.ctor_not_le_lam' hlam).elim
      | indTy => exact (TShape.indTy_not_le_lam' hlam).elim
    | ctor hcl hctor =>
      cases htyped.unfold with
      | bot hm => exact (LR Γ₀).bot hm
      | sort => exact (TShape.sort_not_le_ctor' hctor).elim
      | forallE => exact (TShape.forallE_not_le_ctor' hctor).elim
      | lam htm =>
        unfold WShape.lam' at hctor ⊢
        split at hctor <;> rename_i hnz
        · exact (TShape.lam_not_le_ctor' hctor).elim
        · simpa [hnz] using (LR Γ₀).bot htyped.isType
      | @ctor k c' l' h' =>
        obtain ⟨hc, hl⟩ := TShape.ctor_le_ctor'_nil (by simpa using hcl) hctor
        subst c'
        subst l'
        obtain ⟨n', mTy, sTy, le_n, le_a, hTy', hSort, hmTy⟩ :=
          (LE_Interp.sound hTy.strong W.left.fits).2 hB.toInterp |>.out
        have hty' := (restartSelf hTy'.witness .rfl hTy hmTy
          hSort.witness).2 W.left
        rw [(Params.henv.closedC hreg).mkInstS.subst_eq .zero] at hty'
        have htyB : (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type)
            .indTy :=
          toValTy le_n le_a htyped.isType hSort hmTy hty'
        have hhead : LRS.IndTyHead Γ₀ (mkInst ls ci.type) := by
          rw [LR_succ] at htyB
          have h : LRS.IndTyHead Γ₀ (mkInst ls ci.type) ∧
              LRS.IndTyHead Γ₀ (mkInst ls ci.type) := htyB
          exact h.1
        rw [LR_succ]
        change LRS.IndDefEq Γ₀ (LR Γ₀) (const c ls) (const c ls) (mkInst ls ci.type)
          (WShape.ctor c [] h')
        exact ⟨hhead, LRS.CtorDefEq.exact
          (IH := LR Γ₀) (c := c) (rargs := [])
          (M := const c ls) (N := const c ls)
          (ls := ls) (ls' := ls) (args := []) (args' := [])
          (by simpa using hcl) rfl rfl rfl .rfl .rfl
          (.const hreg hlen) (.const hreg hlen)
          (.nil (Γ := Γ₀) (A := mkInst ls ci.type))
          (.nil (Γ := Γ₀) (A := mkInst ls ci.type)) .nil
          (LRS.CtorSpineDefEq.nil
            (IH := LR Γ₀) (Head := mkInst ls ci.type))
          (LRS.CtorSpineDefEq.nil
            (IH := LR Γ₀) (Head := mkInst ls ci.type))⟩
      | indTy => exact (TShape.indTy_not_le_ctor' hctor).elim
    | indTy hcl hind =>
      cases htyped.unfold with
      | bot hm => exact (LR Γ₀).bot hm
      | sort => exact (TShape.sort_not_le_indTy hind).elim
      | forallE => exact (TShape.forallE_not_le_indTy hind).elim
      | lam htm =>
        unfold WShape.lam' at hind ⊢
        split at hind <;> rename_i hnz
        · exact (TShape.lam_not_le_indTy hind).elim
        · simpa [hnz] using (LR Γ₀).bot htyped.isType
      | ctor => exact (TShape.ctor_not_le_indTy hind).elim
      | indTy =>
        rw [LR_succ]
        change LRS.IndTyHead Γ₀ (const c ls) ∧ LRS.IndTyHead Γ₀ (const c ls)
        have hhead : LRS.IndTyHead Γ₀ (const c ls) :=
          ⟨c, ls, [], by simpa using hcl, .rfl⟩
        exact ⟨hhead, hhead⟩
    | pat hpat hmatch hrhs =>
      have hp := hmatch.nil_inv
      subst hp
      obtain ⟨value, closed, hr, hdefΓ, _⟩ :=
        Params.Semantic.defn_whRed (Γ := Γ) hpat hreg hlen
      subst hr
      obtain ⟨value', closed', hr', hdef₀, hred₀⟩ :=
        Params.Semantic.defn_whRed (Γ := Γ₀) hpat hreg hlen
      cases hr'
      cases hrhs with
      | bot => exact (LR Γ₀).bot htyped.isType
      | const hvalue =>
        obtain ⟨m₁, hle₁, hr₁⟩ := hvalue
        obtain ⟨nV, -, hstratV⟩ := hdefΓ.stratify
        have adV : LR.Adequate Γ₀ Γ ρ (SExpr.mkInst ls value)
            (SExpr.mkInst ls value) (SExpr.mkInst ls ci.type) mx bx := by
          cases pR m₁ _ hr₁ with
          | inl hall => exact (hall nV).1 hle₁ hstratV htyped hB
          | inr hlocal =>
            exact defnStep hpat hreg hlen (depth + 1)
              (hR m₁ _ hr₁) hlocal (cR m₁ _ hr₁) lower hΓ₀
              hle₁ hstratV htyped hB
        have hredS : Γ₀ ⊢ .const c ls ⤳* SExpr.mkInst ls value :=
          .tail .rfl hred₀
        refine ((LR Γ₀).whr hredS hredS).2 ?_
        have hv := (adV.1 W).1
        simpa only [closed.mkInstS.subst_eq .zero,
          (Params.henv.closedC hreg).mkInstS.subst_eq .zero] using hv

/-- Build the constant step from the direct guarded predecessor package.
The lambda branch is the only changed branch: it asks the recursive type
rung for the registered type at the caller's exact Pi shape and delegates to
`constDefEqDirectRootLam`.  Constructor, inductive-head, and definitional
unfold branches project the established coherent predecessor unchanged. -/
theorem LR.SelfAdequateConstStepDirect.of_steps
    (hΓ₀ : Ctx.WF Γ₀)
    (leafStep : LR.CoherentIotaLeafStep Γ₀)
    (defnStep : LR.ConstDefnDeepInstStep Γ₀) :
    LR.SelfAdequateConstStepDirect Γ₀ := by
  intro c ci Γ ls u depth ρ n mx bx hreg hlen hTy lower htyped hB hX children
  cases children with
  | bot => exact LR.Adequate.bot htyped.isType
  | const cA pR cR =>
    rename_i a₀ ci' R m' hm'ty n₀ hR hle hreg' hlen' hA'w hC
    cases hreg.symm.trans hreg'
    have lowerLegacy : ∀ (d' : Nat), d' < depth + 1 →
        ∀ {ρ root X} (hX' : LE_Interp.Witness ρ root X),
          hX'.RDeepChildren (LR.CoherentSeedAt Γ₀ d') →
          LR.CoherentRetainedAt Γ₀ hX' d' :=
      fun d' hd {ρ root X} hX' children =>
        (lower d' hd hX' children).1
    have restartSelf : ∀ {ρ' : Valuation} {root : TShape} {X : SExpr}
        (hX' : LE_Interp.Witness ρ' root X),
        LR.SelfAdequateAt Γ₀ hX' depth := fun hX' =>
      (LR.CoherentRetainedAt.restart (lower := lowerLegacy)
        (Nat.lt_succ_self depth) (hX := hX')).1
    have restartDirect : ∀ {ρ' : Valuation} {root : TShape} {X : SExpr}
        (hX' : LE_Interp.Witness ρ' root X),
        LR.DirectCoherentRetainedAt Γ₀ hX' depth := fun hX' =>
      LR.DirectCoherentRetainedAt.restart (lower := lower)
        (Nat.lt_succ_self depth) (hX := hX')
    suffices h : ∀ {σ σ'}, LR.SubstWF Γ₀ σ σ' Γ ρ →
        (LR Γ₀).DefEq (.const c ls) (.const c ls)
          ((SExpr.mkInst ls ci.type).subst σ) mx bx from
      ⟨fun _ _ W => ⟨h W, h W⟩, fun _ W => h W⟩
    intro σ σ' W
    rw [(Params.henv.closedC hreg).mkInstS.subst_eq .zero]
    have hC' : LE_Interp.Const c ls (LE_Interp.Lower R) [] mx.T :=
      hC.mono hle fun le hr => ⟨_, le, hr⟩
    cases hC' with
    | bot => exact (LR Γ₀).bot htyped.isType
    | lam hrec hlam =>
      rename_i fsem
      cases htyped.unfold with
      | bot hm => exact (LR Γ₀).bot hm
      | sort => exact (TShape.sort_not_le_lam' hlam).elim
      | forallE => exact (TShape.forallE_not_le_lam' hlam).elim
      | @lam k f a₁ a₂ htm =>
        obtain ⟨n', mTy, sTy, le_n, le_a, hTy', hSort, hmTy⟩ :=
          (LE_Interp.sound hTy.strong W.left.fits).2 hB.toInterp |>.out
        have htyDirect := (restartDirect hTy'.witness).2
          le_a hTy htyped.isType W.left
        rw [(Params.henv.closedC hreg).mkInstS.subst_eq .zero] at htyDirect
        unfold WShape.lam'
        split <;> rename_i hf
        · have evalPat : ∀ j, LR.PatternLeafDefEqAt Γ₀ j c ls
              (LE_Interp.Lower R) := fun j =>
            LR.PatternLeafDefEqAt.of_iota
              (leafStep (depth + 1) hR hΓ₀ W pR cR lowerLegacy j)
          exact LR.constDefEqDirectRootLam (hf := hf) htm hlam hrec
            (fun le hr => hr.mono le) evalPat (.const hreg hlen) htyDirect
        · exact (LR Γ₀).bot htyped.isType
      | ctor => exact (TShape.ctor_not_le_lam' hlam).elim
      | indTy => exact (TShape.indTy_not_le_lam' hlam).elim
    | ctor hcl hctor =>
      cases htyped.unfold with
      | bot hm => exact (LR Γ₀).bot hm
      | sort => exact (TShape.sort_not_le_ctor' hctor).elim
      | forallE => exact (TShape.forallE_not_le_ctor' hctor).elim
      | lam htm =>
        unfold WShape.lam' at hctor ⊢
        split at hctor <;> rename_i hnz
        · exact (TShape.lam_not_le_ctor' hctor).elim
        · simpa [hnz] using (LR Γ₀).bot htyped.isType
      | @ctor k c' l' h' =>
        obtain ⟨hc, hl⟩ := TShape.ctor_le_ctor'_nil (by simpa using hcl) hctor
        subst c'
        subst l'
        obtain ⟨n', mTy, sTy, le_n, le_a, hTy', hSort, hmTy⟩ :=
          (LE_Interp.sound hTy.strong W.left.fits).2 hB.toInterp |>.out
        have hty' := (restartSelf hTy'.witness .rfl hTy hmTy
          hSort.witness).2 W.left
        rw [(Params.henv.closedC hreg).mkInstS.subst_eq .zero] at hty'
        have htyB : (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type)
            .indTy :=
          toValTy le_n le_a htyped.isType hSort hmTy hty'
        have hhead : LRS.IndTyHead Γ₀ (mkInst ls ci.type) := by
          rw [LR_succ] at htyB
          have h : LRS.IndTyHead Γ₀ (mkInst ls ci.type) ∧
              LRS.IndTyHead Γ₀ (mkInst ls ci.type) := htyB
          exact h.1
        rw [LR_succ]
        change LRS.IndDefEq Γ₀ (LR Γ₀) (const c ls) (const c ls) (mkInst ls ci.type)
          (WShape.ctor c [] h')
        exact ⟨hhead, LRS.CtorDefEq.exact
          (IH := LR Γ₀) (c := c) (rargs := [])
          (M := const c ls) (N := const c ls)
          (ls := ls) (ls' := ls) (args := []) (args' := [])
          (by simpa using hcl) rfl rfl rfl .rfl .rfl
          (.const hreg hlen) (.const hreg hlen)
          (.nil (Γ := Γ₀) (A := mkInst ls ci.type))
          (.nil (Γ := Γ₀) (A := mkInst ls ci.type)) .nil
          (LRS.CtorSpineDefEq.nil
            (IH := LR Γ₀) (Head := mkInst ls ci.type))
          (LRS.CtorSpineDefEq.nil
            (IH := LR Γ₀) (Head := mkInst ls ci.type))⟩
      | indTy => exact (TShape.indTy_not_le_ctor' hctor).elim
    | indTy hcl hind =>
      cases htyped.unfold with
      | bot hm => exact (LR Γ₀).bot hm
      | sort => exact (TShape.sort_not_le_indTy hind).elim
      | forallE => exact (TShape.forallE_not_le_indTy hind).elim
      | lam htm =>
        unfold WShape.lam' at hind ⊢
        split at hind <;> rename_i hnz
        · exact (TShape.lam_not_le_indTy hind).elim
        · simpa [hnz] using (LR Γ₀).bot htyped.isType
      | ctor => exact (TShape.ctor_not_le_indTy hind).elim
      | indTy =>
        rw [LR_succ]
        change LRS.IndTyHead Γ₀ (const c ls) ∧ LRS.IndTyHead Γ₀ (const c ls)
        have hhead : LRS.IndTyHead Γ₀ (const c ls) :=
          ⟨c, ls, [], by simpa using hcl, .rfl⟩
        exact ⟨hhead, hhead⟩
    | pat hpat hmatch hrhs =>
      have hp := hmatch.nil_inv
      subst hp
      obtain ⟨value, closed, hr, hdefΓ, _⟩ :=
        Params.Semantic.defn_whRed (Γ := Γ) hpat hreg hlen
      subst hr
      obtain ⟨value', closed', hr', hdef₀, hred₀⟩ :=
        Params.Semantic.defn_whRed (Γ := Γ₀) hpat hreg hlen
      cases hr'
      cases hrhs with
      | bot => exact (LR Γ₀).bot htyped.isType
      | const hvalue =>
        obtain ⟨m₁, hle₁, hr₁⟩ := hvalue
        obtain ⟨nV, -, hstratV⟩ := hdefΓ.stratify
        have adV : LR.Adequate Γ₀ Γ ρ (SExpr.mkInst ls value)
            (SExpr.mkInst ls value) (SExpr.mkInst ls ci.type) mx bx := by
          cases pR m₁ _ hr₁ with
          | inl hall => exact (hall nV).1 hle₁ hstratV htyped hB
          | inr hlocal =>
            exact defnStep hpat hreg hlen (depth + 1)
              (hR m₁ _ hr₁) hlocal (cR m₁ _ hr₁) lowerLegacy hΓ₀
              hle₁ hstratV htyped hB
        have hredS : Γ₀ ⊢ .const c ls ⤳* SExpr.mkInst ls value :=
          .tail .rfl hred₀
        refine ((LR Γ₀).whr hredS hredS).2 ?_
        have hv := (adV.1 W).1
        simpa only [closed.mkInstS.subst_eq .zero,
          (Params.henv.closedC hreg).mkInstS.subst_eq .zero] using hv

/--
info: 'Lean4Lean.SExpr.LR.SelfAdequateConstStepDirect.of_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LR.SelfAdequateConstStepDirect.of_steps

/-- The complete constant self-adequacy producer, modulo the independently
staged rank recursion and coherent iota leaf. -/
theorem LR.SelfAdequateConstStep.of_deltaRank [Params.DeltaRank]
    (piInv : LRS.PiPathInv)
    (hGamma : Ctx.WF Γ₀) (leafStep : LR.CoherentIotaLeafStep Γ₀)
    (restart : ∀ c : Name,
      LR.DeltaRankRestart Γ₀ (Params.DeltaRank.rank c)) :
    LR.SelfAdequateConstStep Γ₀ :=
  LR.SelfAdequateConstStep.of_steps piInv hGamma leafStep
    (LR.ConstDefnDeepInstStep.of_deltaRank restart)

/-- Assemble the self-adequacy half of the coherent Nat algebra from its
two remaining leaf-shaped obligations and the conversion callback. -/
theorem LR.CoherentSelfStep.of_leafSteps
    (piInv : LRS.PiPathInv)
    (hΓ₀ : Ctx.WF Γ₀)
    (defeqStep : ∀ depth, LR.SelfAdequateDefeqStepAt Γ₀ depth)
    (leafStep : LR.CoherentIotaLeafStep Γ₀)
    (defnStep : LR.ConstDefnDeepInstStep Γ₀) :
    LR.CoherentSelfStep Γ₀ :=
  LR.coherentSelfStep_of_steps defeqStep hΓ₀
    (LR.SelfAdequateConstStep.of_steps piInv hΓ₀ leafStep defnStep)

/-- The same assembly against the strictly smaller definitional-unfold
obligation.  Together with `MajorChainFoldStep` this is the current minimal
hypothesis inventory of the coherent self-adequacy half. -/
theorem LR.CoherentSelfStep.of_leafStepsDeep
    (piInv : LRS.PiPathInv)
    (hΓ₀ : Ctx.WF Γ₀)
    (defeqStep : ∀ depth, LR.SelfAdequateDefeqStepAt Γ₀ depth)
    (leafStep : LR.CoherentIotaLeafStep Γ₀)
    (deepStep : LR.ConstDefnDeepStepR Γ₀) :
    LR.CoherentSelfStep Γ₀ :=
  LR.CoherentSelfStep.of_leafSteps piInv hΓ₀ defeqStep leafStep
    (LR.ConstDefnDeepInstStep.of_deepStepR deepStep)

/-- Derivation induction once the recursive constructor-major leaf has been
supplied explicitly.  This is the non-circular adequacy core used by the
level-indexed joint construction. -/
theorem LR.adequacy_of_iotaWitnessStep
    (piInv : LRS.PiPathInv)
    (iotaStep : LR.IotaWitnessStep Γ₀)
    (hΓ₀ : Ctx.WF Γ₀)
    (H : IsDefEqStrong Γ M N A)
    (hM : LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A) (hmem : m.HasType a) :
    Adequate (n := n) Γ₀ Γ ρ M N A m a := by
  induction H generalizing ρ n m a with
  | @bvar Γ i A _ h h2 ih =>
    refine .refl fun _ _ W => ?_; clear h2 ih
    have hle := LE_Interp.bvar_iff.1 hM; clear hM
    induction W generalizing i A with
    | id =>
      cases show m = .bot from TShape.le_bot.1 (hle.trans TShape.bot_le)
      exact (LR _).bot hmem.isType
    | cons W' _ _ _ _ h0 ih =>
      cases h with
      | zero => exact lift_subst ▸ (h0.2 a hA).2 (.bvar hle) hmem
      | succ h' => exact lift_subst ▸ ih h' (LE_Interp.weak_iff.1 hA) hle
  | symm H ih => exact .fits fun W => (ih ((LE_Interp.sound H W).1.2 hM) hA hmem).symm
  | trans H1 H2 ih1 ih2 =>
    exact .fits fun W => (ih1 hM hA hmem).trans (ih2 ((LE_Interp.sound H1 W).1.1 hM) hA hmem)
  | @sort _ l =>
    suffices (LR Γ₀).DefEq (.sort l) (.sort l) (.sort l.succ) m a from
      ⟨fun _ _ _ => ⟨this, this⟩, fun _ _ => this⟩
    cases hmem.unfold with
    | bot hm => exact (LR _).bot hm
    | sort => exact (LR _).sort_iff.2 ⟨_, .rfl, .rfl⟩
    | _ =>
      obtain h | h := WShape.le_sort.1 hM.le_sort'
      · dsimp only at h; rw [h]; exact (LR _).bot hmem.isType
      · simp [WShape.ext_iff, WShape.forallE, WShape.sort, Shape.sort,
          WShape.lam', WShape.lam, WShape.bot, WShape.ctor, WShape.indTy,
          Shape.bot] at h <;> first | split at h <;> simp_all only [reduceCtorEq] | simp_all
  | @const c ci Γ ls u h1 h2 hTy F hF hDef ihTy ihF ihDef =>
    -- Constant evaluation is derivation-sensitive: retain one constructor
    -- tree so every reached `R` leaf uses its matching recursive callback.
    cases hM.witness with
    | bot => exact .bot hmem.isType
    | @const _ _ ci' _ m' _ a' _ R hreg _ hle hm'ty hA' hConst hR =>
      cases h1.symm.trans hreg
      suffices ∀ {σ σ'}, LR.SubstWF Γ₀ σ σ' Γ ρ →
          (LR Γ₀).DefEq (const c ls) (const c ls) ((mkInst ls ci.type).subst σ) m a
        from ⟨fun _ _ W => ⟨this W, this W⟩, fun _ W => this W⟩
      intro σ σ' W
      rw [(Params.henv.closedC h1).mkInstS.subst_eq .zero]
      have hC : LE_Interp.Const c ls (LE_Interp.Lower R) [] m.T :=
        hConst.mono hle (fun le hr => ⟨_, le, hr⟩)
      cases hC with
      | bot => exact (LR Γ₀).bot hmem.isType
      | lam hrec hlam =>
        rename_i nsem hlen_sem fsem
        cases hmem.unfold with
        | bot hm => exact (LR Γ₀).bot hm
        | sort => exact (TShape.sort_not_le_lam' hlam).elim
        | forallE => exact (TShape.forallE_not_le_lam' hlam).elim
        | @lam k f a₁ a₂ htm =>
          obtain ⟨n', mTy, sTy, le_n, le_a, hTy', hSort, hmTy⟩ :=
            (LE_Interp.sound hTy W.left.fits).2 hA |>.out
          have hty' := (ihTy hTy' hSort hmTy).2 W.left
          rw [(Params.henv.closedC h1).mkInstS.subst_eq .zero] at hty'
          have hty : (LR Γ₀).TyDefEq (mkInst ls ci.type) (mkInst ls ci.type)
              (.forallE a₁ a₂) :=
            toValTy le_n le_a hmem.isType hSort hmTy hty'
          rw [LR_succ] at hty ⊢
          unfold WShape.lam'
          split <;> rename_i hf
          · obtain ⟨A₁, A₂, _, _, u₁, u₂, hred, _, hA₁, hA₂, hvalA₁, hpi⟩ := hty
            refine (LRS.DefEq.lam_forallE (M := .const c ls) (N := .const c ls)
              (A := mkInst ls ci.type) (f := f) (hf := hf) (a₁ := a₁) (a₂ := a₂)
              (LR Γ₀)).2
              ⟨A₁, A₂, u₁, u₂, hred, hA₁.leftType,
                (LR Γ₀).left_ty hvalA₁, hA₂.leftType, LRS.PiDefEq.left hpi, ?_⟩
            -- `hrec` is the semantic action of this constant.  Its child at
            -- each related argument is the well-founded predecessor needed
            -- to establish this `LamDefEq`; no type-shape work remains here.
            have eval : ∀ {K : Nat}, K = k → ∀
                {x y : SExpr} {p : WShape K} {x₀ y₀ : WShape nsem},
                p.HasType (a₁.lift K) →
                Γ₀ ⊢ x ≡ y : A₁ →
                (LR Γ₀).DefEq x y A₁ p (a₁.lift K) →
                (x₀, y₀) ∈ fsem → x₀.T ≤ p.T →
                ((f.lift K).app p).T ≤ y₀.T →
                (LR Γ₀).DefEq ((const c ls).app x) ((const c ls).app y)
                  (A₂.inst x) ((f.lift K).app p) ((a₂.lift K).app p) := by
              intro K hK
              subst K
              intro x y p x₀ y₀ hp hxy hv hmem₀ hx₀ hy₀
              have hn : k ≤ k := Nat.le_refl k
              have hPiK : LRS.PiDefEq (LR Γ₀) A₁ A₂ A₂
                  (a₁.lift k) (a₂.lift k) :=
                (LRS.PiDefEq.lift hn htm.1).2 (LRS.PiDefEq.left hpi)
              have hAK : (LR Γ₀).TyDefEq (A₂.inst x) (A₂.inst x)
                  ((a₂.lift k).app p) :=
                hPiK.2 hp hxy.hasType.1 ((LR Γ₀).left hv)
              have hout : ((f.lift k).app p).HasType ((a₂.lift k).app p) :=
                (WShape.HasTypeLam.iff.1 ((WShape.HasTypeLam.lift hn).2 htm)).2.2 p hp
              have hType₀ : Γ₀ ⊢ mkInst ls ci.type : .sort u := by
                simpa only [(Params.henv.closedC h1).mkInstS.subst_eq .zero,
                  SExpr.subst] using
                  (hTy.subst W.left.toSubstEq).hasType.1
              have hTypePi : Γ₀ ⊢
                  mkInst ls ci.type ≡ .forallE A₁ A₂ : .sort u :=
                hred.defeq_of_piPathInv piInv hΓ₀ hType₀
              have hConstPi : Γ₀ ⊢ .const c ls : .forallE A₁ A₂ :=
                hTypePi.defeqDF (.const h1 h2)
              have hAppTerm : Γ₀ ⊢
                  SExpr.app (SExpr.const c ls) x ≡
                    SExpr.app (SExpr.const c ls) y : A₂.inst x :=
                .appDF hConstPi hxy
              have hAppType : Γ₀ ⊢ A₂.inst x : .sort u₂ :=
                (IsDefEq.beta hA₂.leftType hxy.hasType.1).hasType.2
              have hAppSpineX : SExpr.SpineWF Γ₀ (mkInst ls ci.type)
                  [x] (A₂.inst x) := by
                simpa only [List.nil_append] using
                  (SExpr.SpineWF.nil (Γ := Γ₀) (A := mkInst ls ci.type)).snoc
                    hTypePi hxy.hasType.1
              obtain ⟨_, hAppCodomain⟩ := (hPiK.1 hp hxy hv).leftDefEq
              have hAppSpineY : SExpr.SpineWF Γ₀ (mkInst ls ci.type)
                  [y] (A₂.inst x) := by
                have hspine :=
                  (SExpr.SpineWF.nil (Γ := Γ₀) (A := mkInst ls ci.type)).snoc
                    hTypePi hxy.hasType.2
                exact SExpr.SpineWF.ret hspine hAppCodomain.symm
              have hA₁K : (LR Γ₀).TyDefEq A₁ A₁ (a₁.lift k) :=
                (LR.TyDefEq.lift hn
                  (WShape.HasTypePi.iff.1 htm.1).1.isType).2
                  ((LR Γ₀).left_ty hvalA₁)
              let hAppPair : SExpr.SpineWF.LastPair Γ₀
                  (mkInst ls ci.type) [] [] x y (A₂.inst x) := {
                  prefixType := mkInst ls ci.type
                  domain := A₁
                  codomain := A₂
                  piSort := u
                  resultSortX := u₂
                  resultSortY := _
                  prefixX := .nil
                  prefixY := .nil
                  pi := hTypePi
                  major := hxy
                  resultX := hAppType
                  resultY := hAppCodomain.symm }
              have hAppAligned : LRS.CtorSpineDefEq (LR Γ₀)
                  (mkInst ls ci.type) [x] [y] [p] (A₂.inst x) :=
                .cons .nil hTypePi hp hA₁K hxy hv hAppCodomain.symm
              have hAppLeaf : LR.PatternLeafSpine Γ₀ (LR Γ₀)
                  (mkInst ls ci.type) [x] [y] [p] (A₂.inst x)
                  ((f.lift k).app p) ((a₂.lift k).app p) := {
                majorX := x
                recXs := []
                majorY := y
                recYs := []
                majorShape := p
                recShapes := []
                majorTypeShape := a₁.lift k
                resultShape := f.lift k
                resultTypeShape := a₂.lift k
                args_eq := rfl
                args'_eq := rfl
                rargs_eq := rfl
                out_eq := rfl
                outTy_eq := rfl
                pair := hAppPair
                majorHasType := hp
                resultType := (WShape.HasTypePi.lift hn).2 htm.1
                majorType := hA₁K
                majorRel := hv
                aligned := hAppAligned
                pi := hPiK }
              have hRI : ∀ {m M}, R m M →
                  LE_Interp.Witness ρ m M :=
                fun hr => hR _ _ hr
              have evalPat : LR.PatternLeafDefEqAt Γ₀ k c ls
                  (LE_Interp.Lower R) :=
                LR.PatternLeafDefEqAt.of_iota (iotaStep hΓ₀ hRI)
              simpa only [List.foldr_cons, List.foldr_nil] using
                LR.constDefEq piInv hΓ₀ (fun le hr => hr.mono le)
                  (hrec x₀ y₀ hmem₀) evalPat
                  (.cons hx₀ .nil) hAppLeaf
                  hAppTerm ⟨u₂, hAppType⟩ (.const h1 h2) hAppSpineX hAppSpineY
                  hout hAK hy₀
            exact LR.constLamDefEq (hf := hf) (nArgs := 0) htm hlam
              (fun {_ _ _ _ _} hp hxy hv hmem₀ hx₀ hy₀ =>
                LogRel.DefEqRect.diagonal
                  (eval (Nat.max_eq_left (Nat.zero_le k))
                    hp hxy hv hmem₀ hx₀ hy₀))
          · exact (LR Γ₀).bot hmem.isType
        | ctor => exact (TShape.ctor_not_le_lam' hlam).elim
        | indTy => exact (TShape.indTy_not_le_lam' hlam).elim
      | ctor hcl hctor =>
        cases hmem.unfold with
        | bot hm => exact (LR Γ₀).bot hm
        | sort => exact (TShape.sort_not_le_ctor' hctor).elim
        | forallE => exact (TShape.forallE_not_le_ctor' hctor).elim
        | lam htm =>
          unfold WShape.lam' at hctor ⊢
          split at hctor <;> rename_i hn
          · exact (TShape.lam_not_le_ctor' hctor).elim
          · simpa [hn] using (LR Γ₀).bot hmem.isType
        | @ctor n c' l' h' =>
          obtain ⟨hc, hl⟩ := TShape.ctor_le_ctor'_nil (by simpa using hcl) hctor
          subst c'
          subst l'
          let cl : CtorBundle.IsCtor c := ⟨.ctor 0, by simpa using hcl, rfl⟩
          let Fc := F cl
          have hsort : LE_Interp ρ (WShape.type : WShape (n+1)).T (.sort Fc.u) := by
            exact .sort (decide_eq_true Fc.hu0 ▸ TShape.sort_eqv.1)
          have hty := (ihF cl hA hsort WShape.HasType.indTy).2 W.left
          have hhead : LRS.IndTyHead Γ₀ (mkInst ls ci.type) := by
            rw [(Params.henv.closedC h1).mkInstS.subst_eq .zero] at hty
            simpa only [LR_succ, LRS.DefEq.sort_a, LRS.TyDefEq.indTy_m] using hty.1
          rw [LR_succ]
          change LRS.IndDefEq Γ₀ (LR Γ₀) (const c ls) (const c ls) (mkInst ls ci.type)
            (WShape.ctor c [] h')
          exact ⟨hhead, LRS.CtorDefEq.exact
            (IH := LR Γ₀) (c := c) (rargs := [])
            (M := const c ls) (N := const c ls)
            (ls := ls) (ls' := ls) (args := []) (args' := [])
            (by simpa using hcl) rfl rfl rfl .rfl .rfl
            (.const h1 h2) (.const h1 h2)
            (.nil (Γ := Γ₀) (A := mkInst ls ci.type))
            (.nil (Γ := Γ₀) (A := mkInst ls ci.type)) .nil
            (LRS.CtorSpineDefEq.nil
              (IH := LR Γ₀) (Head := mkInst ls ci.type))
            (LRS.CtorSpineDefEq.nil
              (IH := LR Γ₀) (Head := mkInst ls ci.type))⟩
        | indTy => exact (TShape.indTy_not_le_ctor' hctor).elim
      | indTy hcl hind =>
        cases hmem.unfold with
        | bot hm => exact (LR Γ₀).bot hm
        | sort => exact (TShape.sort_not_le_indTy hind).elim
        | forallE => exact (TShape.forallE_not_le_indTy hind).elim
        | lam htm =>
          unfold WShape.lam' at hind ⊢
          split at hind <;> rename_i hn
          · exact (TShape.lam_not_le_indTy hind).elim
          · simpa [hn] using (LR Γ₀).bot hmem.isType
        | ctor => exact (TShape.ctor_not_le_indTy hind).elim
        | indTy =>
          rw [LR_succ]
          change LRS.IndTyHead Γ₀ (const c ls) ∧ LRS.IndTyHead Γ₀ (const c ls)
          have hhead : LRS.IndTyHead Γ₀ (const c ls) :=
            ⟨c, ls, [], by simpa using hcl, .rfl⟩
          exact ⟨hhead, hhead⟩
      | @pat p r _ _ _ hpat hmatch hrhs =>
        have hp : p = .const c := hmatch.nil_inv
        subst p
        obtain ⟨value, closed, hr, hdef, hred⟩ :=
          Params.Semantic.defn_whRed (Γ := Γ₀) hpat h1 h2
        subst r
        cases hrhs with
        | bot => exact (LR Γ₀).bot hmem.isType
        | const hvalue =>
          have hvalue' : LE_Interp ρ m.T (SExpr.mkInst ls value) :=
            hvalue.realize (fun hr => (hR _ _ hr).toInterp)
          simpa only [SExpr.subst, (Params.henv.closedC h1).mkInstS.subst_eq .zero] using
            ((ihDef hpat hvalue' hA hmem).1 W).2
  | @appDF Γ A u B v F F' X X' _ _ Hf Ha HBa _ _ ihf iha ihBa =>
    cases hM with | bot => exact .bot hmem.isType | @app _ nf_app f _ _ _ x hif hia le_m
    suffices ∀ {F F' X X' σ σ'}, SubstWF Γ₀ σ σ' Γ ρ →
        IsDefEqStrong Γ F F' (A.forallE B) →
        IsDefEqStrong Γ X X' A →
        IsDefEqStrong Γ (B.inst X) (B.inst X') (.sort v) →
        LE_Interp ρ f.T F → LE_Interp ρ x.T X → LE_Interp ρ a.T (B.inst X) →
        (∀ {n'} {mf af : WShape n'}, LE_Interp ρ mf.T F → LE_Interp ρ af.T (.forallE A B) →
          mf.HasType af → Adequate Γ₀ Γ ρ F F' (.forallE A B) mf af) →
        (∀ {n'} {ma aa : WShape n'}, LE_Interp ρ ma.T X → LE_Interp ρ aa.T A →
          ma.HasType aa → Adequate Γ₀ Γ ρ X X' A ma aa) →
        (∀ {n'} {mb av : WShape n'}, LE_Interp ρ mb.T (B.inst X) → LE_Interp ρ av.T (.sort v) →
          mb.HasType av → Adequate Γ₀ Γ ρ (B.inst X) (B.inst X') (.sort v) mb av) →
        (LR Γ₀).DefEq (.subst (.app F X) σ) (.subst (.app F' X') σ')
          (.subst (B.inst X) σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => this W Hf Ha HBa hif hia hA ihf iha ihBa⟩
      · refine this W (Hf.trans Hf.symm) (Ha.trans Ha.symm) (HBa.trans HBa.symm)
          hif hia hA ?_ ?_ ?_
        · exact fun hf hPi hmf => (ihf hf hPi hmf).left
        · exact fun ha hA hma => (iha ha hA hma).left
        · exact fun hB hv hmb => (ihBa hB hv hmb).left
      · refine (LR _).conv ((LR _).symm_ty ?_) <| this W
          (Hf.symm.trans Hf) (Ha.symm.trans Ha) (HBa.symm.trans HBa)
          ((LE_Interp.sound Hf W.fits).1.1 hif) ((LE_Interp.sound Ha W.fits).1.1 hia)
          ((LE_Interp.sound HBa W.fits).1.1 hA)
          (fun hf hPi hmf => ?_) (fun ha hA hma => ?_) (fun hB hv hmb => ?_)
        · have ⟨_, _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HBa W.fits).2 hA |>.out
          exact toValTy le le' hmem.isType iv hmb ((ihBa iB iv hmb).2 W.left)
        · exact (ihf ((LE_Interp.sound Hf W.left.fits).1.2 hf) hPi hmf).symm.left
        · exact (iha ((LE_Interp.sound Ha W.left.fits).1.2 ha) hA hma).symm.left
        · exact (ihBa ((LE_Interp.sound HBa W.left.fits).1.2 hB) hv hmb).symm.left
    intro F F' X X' σ σ' W hF hX hBa hif hia hA ihf iha ihBa
    have ⟨_, mf, _, le_nf, le_mf, hf', hPi, hmf⟩ := (LE_Interp.sound hF W.left.fits).2 hif |>.out
    have Af := ihf hf' hPi hmf
    by_cases hm0 : mf = .bot
    · simp only [hm0] at le_mf hmf
      refine (?_ : m = .bot) ▸ (LR _).bot hmem.isType
      cases show f = .bot from TShape.le_bot.1 (le_mf.trans TShape.bot_le')
      exact TShape.le_bot.1 ((WShape.bot_app ▸ le_m).trans TShape.bot_eqv.1)
    cases hPi with | bot => cases hm0 hmf.bot_r | forallE haA hbA hd hiB le
    cases hmf.unfold with | bot => cases hm0 rfl | lam hg => ?_ | _ =>
      refine have le₂ := Nat.succ_le_succ (Nat.le_max_right ..)
        have := (TShape.LE.def (Nat.le_succ_of_le (Nat.le_max_left ..)) le₂).1 le; ?_
      simp only [WShape.lift_sort, WShape.LE.def, WShape.lift_val le₂] at this; cases this
    rename_i n₁ b₁' b₂' f' n₂ b₁ b₂ f
    simp at le_nf
    let k := max n (max n₁ n₂); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
    have le_nf_k : nf_app ≤ k := Nat.le_trans le_nf hk.2.2
    have hA' := hA.lift hk.1
    have ⟨_, le_x', hx'_a₁, hgx2⟩ := WShape.HasDom.iff.1 hg.2.1 (x.lift _)
    have hia' := (hia.lift le_nf).mono le_x'.T
    have hax' := LE_Interp.forallE' haA hbA hd hiB |>.mono le |>.forallE_inv.2 hia'
    have hJ := TShape.Join.mk (hA.compat hax')
    have ⟨hJ1, hJ2⟩ := (hJ _).1 .rfl
    have hk' := Nat.max_le.2 ⟨hk.1, hk.2.2⟩
    have hJ1' := (TShape.LE.def hk.1 hk').1 hJ1
    have hJ2' := (TShape.LE.def hk.2.2 hk').1 hJ2
    have hgx' := (WShape.HasTypeLam.iff.1 hg).2.2 _ hx'_a₁
    have hJ_t := TShape.HasType.sort_r.2 hmem.isType
      |>.join' hJ <| TShape.HasType.sort_r.2 hgx'.isType
    have hmem_k := (WShape.HasType.lift hk.1).2 hmem
    rw [subst_inst]
    have hJ_t' := TShape.HasType.sort_r.1 <|
      hJ_t.mono_l (TShape.lift_eqv hk').2 (TShape.lift_eqv hk').1
    refine (LR.DefEq.lift hk.1 hmem).1 <| (LR Γ₀).mono_r_2 hJ1' hmem_k hJ_t' ?_
    have hgx'' := (WShape.HasType.lift hk.2.2).2 hgx'
    refine (LR Γ₀).mono_l ?_ (.mono_r hJ1' hJ_t' hmem_k) (.mono_r hJ2' hJ_t' hgx'') ?_
    · exact (TShape.LE.def hk.1 hk.2.2).1 <| le_m.trans <|
        (TShape.app_mono le_mf (TShape.lift_eqv le_nf).2).trans (WShape.lam'_app ▸ hgx2.T)
    refine (LR Γ₀).mono_r_1 hJ2' hgx'' (.mono_r hJ2' hJ_t' hgx'') ?_ ?_
    · have ⟨_, _, _, le_j, le_j', hBj, hSj, hmj⟩ :=
        (LE_Interp.sound hBa W.left.fits).2 (hA.join hJ hax') |>.out
      exact (LR Γ₀).left_ty <| (TyDefEq.lift hk' (TShape.HasType.sort_r.1 hJ_t)).2 <|
        subst_inst ▸ toValTy le_j le_j' (TShape.HasType.sort_r.1 hJ_t) hSj hmj
          ((ihBa hBj hSj hmj).2 W.left)
    · have hAf := (LR _).trans (Af.2 W.left) (Af.1 W).2
      dsimp only [LR, LRS] at hAf
      unfold WShape.lam' at hAf; split at hAf
      · rw [LRS.DefEq.lam_forallE] at hAf
        obtain ⟨_, _, _, _, red, _, _, _, _, valPi⟩ := hAf
        cases WHNF.forallE.whRedS red
        have le' := (TShape.LE.def (Nat.succ_le_succ hk.2.2) (Nat.succ_le_succ hk.2.1)).1 le
        simp only [WShape.T, WShape.lift_forallE hk.2.2, WShape.lift_forallE hk.2.1,
          WShape.forallE_le_forallE] at le'
        have Aa := iha hia' (haA.mono ((TShape.LE.def hk.2.2 hk.2.1).2 le'.1)) hx'_a₁
        have := (LR _).trans (Aa.2 W.left) (Aa.1 W).2
        exact (DefEq.lift hk.2.2 hgx').2 <| (LR _).trans
          (valPi.2 hx'_a₁ (hX.subst W.toSubstEq).hasType.1 <| (LR _).left this)
          (valPi.1 hx'_a₁ (hX.subst W.toSubstEq) this).2
      · refine (hm0 ?_).elim; unfold WShape.lam'; simp_all
  | @lamDF Γ A A' u B v body body' HA HB HB' HBody HBody'
      ihA ihB _ ihBody _ =>
    suffices ∀ {X Y X' Y' σ σ'},
        LE_Interp ρ m.T (.lam X Y) → SubstWF Γ₀ σ σ' Γ ρ →
        (∀ {k np} {p : WShape np} {mb ab : WShape k},
          (ρ.push p.T).Fits Γ₀ (A :: Γ) →
          LE_Interp (ρ.push p.T) mb.T Y → LE_Interp (ρ.push p.T) ab.T B → mb.HasType ab →
          Adequate Γ₀ (A :: Γ) (ρ.push p.T) Y Y' B mb ab) →
        (LR Γ₀).DefEq (.subst (.lam X Y) σ) (.subst (.lam X' Y') σ')
          (.subst (.forallE A B) σ) m a by
      refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => this hM W fun _ => ihBody⟩
      · exact this hM W fun _ hMb hBb hmb => (ihBody hMb hBb hmb).left
      · refine this ?_ W fun W hMb' hBb hmb => ?_
        · exact (LE_Interp.sound (.lamDF HA HB HB' HBody HBody') W.fits).1.1 hM
        · exact (ihBody ((LE_Interp.sound HBody W).1.2 hMb') hBb hmb).symm.left
    intro X Y X' Y' σ σ' hTerm W IH
    suffices ∀ n' b (f : WShapeFun _), n = n' + 1 → a ≍ (.forallE b f : WShape (n'+1)) →
        (LR Γ₀).DefEq (.subst (.lam X Y) σ) (.subst (.lam X' Y') σ')
          (.subst (.forallE A B) σ) m a by
      cases hmem.unfold with
      | bot hm =>
        cases hm.unfold with
        | bot | sort => cases n <;> trivial | indTy => trivial
        | forallE => exact this _ _ _ rfl .rfl
      | sort => cases n <;> let .lam _ _ _ h := hTerm <;> cases TShape.sort_not_le_lam' h
      | forallE => let .lam _ _ _ h := hTerm <;> cases TShape.forallE_not_le_lam' h
      | lam => exact this _ _ _ rfl .rfl
      | ctor => let .lam _ _ _ h := hTerm; cases TShape.ctor_not_le_lam' h
      | indTy => let .lam _ _ _ h := hTerm; cases TShape.indTy_not_le_lam' h
    rintro k a₁ a₂ rfl ⟨⟩
    have ⟨_, aty, _⟩ := WShape.HasType.forallE_l.1 hmem.isType
    have hTypA : Γ₀ ⊢ A.subst σ : .sort u :=
      (HA.subst W.left.toSubstEq).hasType.1
    have hTypB : A.subst σ :: Γ₀ ⊢ B.subst σ.lift : .sort v :=
      HB.subst (W.left.toSubstEq.lift HA.defeq.hasType.1)
    have hA1 := hA.forallE_inv.1
    have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
      (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
    have cons := Adequate.cons ihA HA
    obtain ⟨g, hg, htm⟩ := WShape.HasType.forallE_inv hmem
    unfold WShape.lam' at hg; split at hg <;> [skip; (subst hg; exact (LR _).bot hmem.isType)]
    rename_i hlam; subst hg
    simp only [LR, LRS, LRS.DefEq.lam_forallE]
    have aty := WShape.HasTypePi.iff.1 aty
    refine ⟨A.subst σ, B.subst σ.lift, u, v, .rfl, hTypA, ?_, hTypB, ?_, ?_⟩
    · exact (LR Γ₀).left_ty <| toValTy le_n le_a aty.1.isType hSort hmem'
        ((ihA hA' hSort hmem').2 W.left)
    · simp only [LRS.PiDefEq]
      have edge : ∀ {{x x' p}}, p.HasType a₁ →
          Γ₀ ⊢ x ≡ x' : A.subst σ →
          (LR Γ₀).DefEq x x' (A.subst σ) p a₁ →
          LRS.PiInstDefEq (LR Γ₀) (B.subst σ.lift)
            (B.subst σ.lift) x x' (a₂.app p) := by
        intro x x' p hp ha hv
        have W' := cons hp hA1 ha hv W.left
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HB W'.fits).2 (hA.forallE_inv'.2 p) |>.out
        have hsem : (LR Γ₀).TyDefEq
            ((B.subst σ.lift).inst x) ((B.subst σ.lift).inst x') (a₂.app p) := by
          simpa [inst_lift_cons] using
            toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W').1
        have hraw : Γ₀ ⊢
            (B.subst σ.lift).inst x ≡ (B.subst σ.lift).inst x' : .sort v := by
          simpa only [inst_lift_cons, SExpr.subst] using
            (HB.substCongr W'.toSubstEq).1
        exact ⟨hsem, hsem, ⟨v, hraw⟩, ⟨v, hraw⟩⟩
      exact ⟨edge, fun _ _ hp ha hv => (edge hp ha hv).leftTy⟩
    have beta {X Y t : SExpr} {σ} : Γ₀ ⊢ .app (.lam (X.subst σ) (Y.subst σ.lift)) t ⤳*
        Y.subst (σ.cons t) := inst_lift_cons (x := t) ▸ .tail .rfl .beta
    refine ⟨fun x x' p hp ha hv => ?_, fun x p hp ha hv => ?_⟩
    all_goals
      rw [inst_lift_cons]
      have hBb_sd := hA.forallE_inv'.2 p
      replace IH W := IH W (hTerm.lam_inv' p) hBb_sd ((WShape.HasTypeLam.iff.1 htm).2.2 p hp)
    · have W' := cons hp hA1 ha hv W.left
      constructor
      · exact ((LR Γ₀).whr beta beta).2 <| ((IH W'.fits).1 W').1
      · have vtAA' := toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        have ha' : Γ₀ ⊢ x ≡ x' : A.subst σ' :=
          ((HA.substCongr W.toSubstEq).1).defeqDF ha
        have hv' := (LR Γ₀).conv vtAA' hv
        have ⟨n', _, _, le, le', iB, iv, hmb⟩ := (LE_Interp.sound HB W'.fits).2 hBb_sd |>.out
        have W2 := cons hp hA1 ha.hasType.1 ((LR Γ₀).left hv) W
        have vtBB := toValTy le le' (aty.2 _ hp).toType iv hmb ((ihB iB iv hmb).1 W2).1
        refine ((LR Γ₀).whr beta beta).2 <| (LR Γ₀).conv ((LR Γ₀).symm_ty vtBB) ?_
        exact ((IH W'.fits).1 (cons hp hA1 ha' hv' W.symm.left)).2
    · have W' := cons hp hA1 ha hv W
      exact ((LR Γ₀).whr beta beta).2 <|
        (LR _).trans ((IH W'.fits).2 W'.left) ((IH W'.fits).1 W').2
  | @forallEDF Γ A A' u body body' v HA HBody _ ihA ihBody =>
    cases hmem.unfold with
    | bot hm =>
      cases hm.unfold with
      | forallE => let .sort h := hA; cases (TShape.LE.lift_r (by simp [TShape.sort])).1 h
      | _ => exact .bot hmem.isType
    | sort => cases n <;> have .forallE _ _ _ _ h := hM <;> cases TShape.sort_not_le_forallE h
    | @lam _ f₀ =>
      revert hM; unfold WShape.lam'; split <;> [skip; exact fun _ => .bot hmem.isType]
      intro | .forallE _ _ _ _ h => cases TShape.lam_not_le_forallE h
    | ctor => have .forallE _ _ _ _ h := hM; cases TShape.ctor_not_le_forallE h
    | indTy => have .forallE _ _ _ _ h := hM; cases TShape.indTy_not_le_forallE h
    | @forallE k a₂ a₁ r aty
    have aty := WShape.HasTypePi.iff.1 aty
    have hA1 := hM.forallE_inv.1
    have cons := Adequate.cons ihA HA
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;> (
      have ⟨_, a', _, le_n, le_a, hA', hSort, hmem'⟩ :=
        (LE_Interp.sound HA W.left.fits).2 hA1 |>.out
      have HAAσ := HA.subst W.left.toSubstEq
      have S' := W.toSubstEq.lift HA.defeq.hasType.1)
    · have HAσ := (HA.substCongr W.toSubstEq).1
      have HA'σ := (HA.substCongr W.toSubstEq).2
      constructor
      · refine ⟨A.subst σ, body.subst σ.lift, A.subst σ', body.subst σ'.lift, u, v,
          .rfl, .rfl, .single HAσ, .single (HBody.substCongr S').1, ?_, ?_⟩
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).1
        simp only [LRS.PiDefEq]
        constructor
        · intro x x' p hp ha hv
          have hB := hM.forallE_inv'.2 p
          have WL := cons hp hA1 ha hv W.left
          have ⟨_, _, _, leL, leL', iBL, ivL, hmbL⟩ :=
            (LE_Interp.sound HBody WL.fits).2 hB |>.out
          have semL : (LR Γ₀).TyDefEq
              ((body.subst σ.lift).inst x) ((body.subst σ.lift).inst x')
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy leL leL' (aty.2 _ hp).toType ivL hmbL
                ((ihBody iBL ivL hmbL).1 WL).1
          have valA := toValTy le_n le_a aty.1.isType hSort hmem'
            ((ihA hA' hSort hmem').1 W).1
          have WR := cons hp hA1 (HAσ.defeqDF ha) ((LR Γ₀).conv valA hv)
            W.symm.left
          have ⟨_, _, _, leR, leR', iBR, ivR, hmbR⟩ :=
            (LE_Interp.sound HBody WR.fits).2 hB |>.out
          have semR : (LR Γ₀).TyDefEq
              ((body.subst σ'.lift).inst x) ((body.subst σ'.lift).inst x')
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy leR leR' (aty.2 _ hp).toType ivR hmbR
                ((ihBody iBR ivR hmbR).1 WR).1
          have rawL : Γ₀ ⊢
              (body.subst σ.lift).inst x ≡ (body.subst σ.lift).inst x' : .sort v := by
            simpa only [inst_lift_cons, SExpr.subst] using
              (HBody.substCongr WL.toSubstEq).1
          have rawR : Γ₀ ⊢
              (body.subst σ'.lift).inst x ≡ (body.subst σ'.lift).inst x' : .sort v := by
            simpa only [inst_lift_cons, SExpr.subst] using
              (HBody.substCongr WR.toSubstEq).1
          exact ⟨semL, semR, ⟨v, rawL⟩, ⟨v, rawR⟩⟩
        · intro x p hp ha hv
          have hB := hM.forallE_inv'.2 p
          have WX := cons hp hA1 ha.hasType.1 ((LR Γ₀).left hv) W
          have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.sound HBody WX.fits).2 hB |>.out
          have hout : (LR Γ₀).TyDefEq
              ((body.subst σ.lift).inst x) ((body.subst σ'.lift).inst x)
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 WX).1
          exact cast (by congr 1) hout
      · refine ⟨A'.subst σ, body'.subst σ.lift, A'.subst σ', body'.subst σ'.lift, u, v,
          .rfl, .rfl, .single HA'σ,
          .single (HAAσ.defeqDF_l (HBody.substCongr S').2), ?_, ?_⟩
        · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').1 W).2
        simp only [LRS.PiDefEq]
        have valA' := toValTy le_n le_a aty.1.isType hSort hmem'
          ((ihA hA' hSort hmem').2 W.left)
        constructor
        · intro x x' p hp ha hv
          have ha₀ := HAAσ.symm.defeqDF ha
          have hv₀ := (LR Γ₀).conv ((LR Γ₀).symm_ty valA') hv
          have hB := hM.forallE_inv'.2 p
          have WL := cons hp hA1 ha₀ hv₀ W.left
          have ⟨_, _, _, leL, leL', iBL, ivL, hmbL⟩ :=
            (LE_Interp.sound HBody WL.fits).2 hB |>.out
          have semL : (LR Γ₀).TyDefEq
              ((body'.subst σ.lift).inst x) ((body'.subst σ.lift).inst x')
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy leL leL' (aty.2 _ hp).toType ivL hmbL
                ((ihBody iBL ivL hmbL).1 WL).2
          have valA := toValTy le_n le_a aty.1.isType hSort hmem'
            ((ihA hA' hSort hmem').1 W).1
          have WR := cons hp hA1 (HAσ.defeqDF ha₀) ((LR Γ₀).conv valA hv₀)
            W.symm.left
          have ⟨_, _, _, leR, leR', iBR, ivR, hmbR⟩ :=
            (LE_Interp.sound HBody WR.fits).2 hB |>.out
          have semR : (LR Γ₀).TyDefEq
              ((body'.subst σ'.lift).inst x) ((body'.subst σ'.lift).inst x')
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy leR leR' (aty.2 _ hp).toType ivR hmbR
                ((ihBody iBR ivR hmbR).1 WR).2
          have rawL : Γ₀ ⊢
              (body'.subst σ.lift).inst x ≡ (body'.subst σ.lift).inst x' : .sort v := by
            simpa only [inst_lift_cons, SExpr.subst] using
              (HBody.substCongr WL.toSubstEq).2
          have rawR : Γ₀ ⊢
              (body'.subst σ'.lift).inst x ≡ (body'.subst σ'.lift).inst x' : .sort v := by
            simpa only [inst_lift_cons, SExpr.subst] using
              (HBody.substCongr WR.toSubstEq).2
          exact ⟨semL, semR, ⟨v, rawL⟩, ⟨v, rawR⟩⟩
        · intro x p hp ha hv
          have ha₀ := HAAσ.symm.defeqDF ha
          have hv₀ := (LR Γ₀).conv ((LR Γ₀).symm_ty valA') hv
          have hB := hM.forallE_inv'.2 p
          have WX := cons hp hA1 ha₀ ((LR Γ₀).left hv₀) W
          have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
            (LE_Interp.sound HBody WX.fits).2 hB |>.out
          have hout : (LR Γ₀).TyDefEq
              ((body'.subst σ.lift).inst x) ((body'.subst σ'.lift).inst x)
              (a₂.app p) := by
            simpa [inst_lift_cons] using
              toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).1 WX).2
          exact cast (by congr 1) hout
    · refine ⟨A.subst σ, body.subst σ.lift, A'.subst σ, body'.subst σ.lift, u, v,
        .rfl, .rfl, .single HAAσ, .single (HBody.subst S'), ?_, ?_⟩
      · exact toValTy le_n le_a aty.1.isType hSort hmem' ((ihA hA' hSort hmem').2 W)
      simp only [LRS.PiDefEq]
      constructor
      · intro x x' p hp ha hv
        have hB := hM.forallE_inv'.2 p
        have W' := cons hp hA1 ha hv W
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HBody W'.fits).2 hB |>.out
        have sem := (ihBody iB iv hmb).1 W'
        have semL : (LR Γ₀).TyDefEq
            ((body.subst σ.lift).inst x) ((body.subst σ.lift).inst x')
            (a₂.app p) := by
          simpa [inst_lift_cons] using
            toValTy le le' (aty.2 _ hp).toType iv hmb sem.1
        have semR : (LR Γ₀).TyDefEq
            ((body'.subst σ.lift).inst x) ((body'.subst σ.lift).inst x')
            (a₂.app p) := by
          simpa [inst_lift_cons] using
            toValTy le le' (aty.2 _ hp).toType iv hmb sem.2
        have hraw := HBody.substCongr W'.toSubstEq
        have rawL : Γ₀ ⊢
            (body.subst σ.lift).inst x ≡ (body.subst σ.lift).inst x' : .sort v := by
          simpa only [inst_lift_cons, SExpr.subst] using hraw.1
        have rawR : Γ₀ ⊢
            (body'.subst σ.lift).inst x ≡ (body'.subst σ.lift).inst x' : .sort v := by
          simpa only [inst_lift_cons, SExpr.subst] using hraw.2
        exact ⟨semL, semR, ⟨v, rawL⟩, ⟨v, rawR⟩⟩
      · intro x p hp ha hv
        have hB := hM.forallE_inv'.2 p
        have W' := cons hp hA1 ha hv W
        have ⟨_, _, _, le, le', iB, iv, hmb⟩ :=
          (LE_Interp.sound HBody W'.fits).2 hB |>.out
        have hout : (LR Γ₀).TyDefEq
            ((body.subst σ.lift).inst x) ((body'.subst σ.lift).inst x)
            (a₂.app p) := by
          simpa [inst_lift_cons] using
            toValTy le le' (aty.2 _ hp).toType iv hmb ((ihBody iB iv hmb).2 W')
        exact cast (by congr 1) hout
  | @defeqDF Γ A' B' u' _ _ Hty He ihTy ihE =>
    have tyConv {σ} (W : SubstWF Γ₀ σ σ Γ ρ) :=
      have hA' := (LE_Interp.sound Hty W.fits).1.2 hA
      have ⟨_, a', _, le_n, le_a, hA'', hSort, hmem'⟩ :=
        (LE_Interp.sound Hty W.fits).2 hA' |>.out
      toValTy le_n le_a hmem.isType hSort hmem' ((ihTy hA'' hSort hmem').2 W)
    refine ⟨fun σ σ' W => ?_, fun σ W => ?_⟩ <;>
      have hA' := (LE_Interp.sound Hty W.left.fits).1.2 hA
    · exact ⟨(LR Γ₀).conv (tyConv W.left) ((ihE hM hA' hmem).1 W).1,
             (LR Γ₀).conv (tyConv W.left) ((ihE hM hA' hmem).1 W).2⟩
    · exact (LR Γ₀).conv (tyConv W) ((ihE hM hA' hmem).2 W)
  | beta He Ha Happ Hinst _ihe _iha ihapp ihinst =>
    refine ⟨fun _ _ W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihapp hM hA hmem).1 W).1
    · exact ((ihinst ((LE_Interp.sound (.beta He Ha Happ Hinst) W.fits).1.1 hM)
        hA hmem).1 W).2
    · exact ((LR _).whr .rfl (subst_inst ▸ .tail .rfl .beta)).1 ((ihapp hM hA hmem).2 W)
  | @eta _ e0 A0 B0 He Hlam ihe ihlam =>
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihlam hM hA hmem).1 W).1
    · exact ((ihe ((LE_Interp.sound (.eta He Hlam) W.fits).1.1 hM) hA hmem).1 W).2
    have hM' := (LE_Interp.sound (.eta He Hlam) W.fits).1.1 hM
    cases hmem.unfold with
    | bot hm => exact (LR _).bot hm
    | sort => cases n <;> let .lam _ _ _ h := hM <;> cases TShape.sort_not_le_lam' h
    | forallE => let .lam _ _ _ h := hM; cases TShape.forallE_not_le_lam' h
    | ctor => let .lam _ _ _ h := hM; cases TShape.ctor_not_le_lam' h
    | indTy => let .lam _ _ _ h := hM; cases TShape.indTy_not_le_lam' h
    | lam htm
    revert hM hM' hmem; unfold WShape.lam'
    split <;> intro hM hM' hmem <;> [skip; exact (LR _).bot hmem.isType]
    have ⟨A₁, A₂, u, v, whr_t, htA₁, vtyA₁, htA₂, edge, vpi_M⟩ := (ihlam hM hA hmem).2 W
    have ⟨_, _, _, _, whr_N, _, _, _, _, vpi_N⟩ := (ihe hM' hA hmem).2 W
    cases whr_t.determ .forallE whr_N .forallE
    refine ⟨A₁, A₂, u, v, whr_t, htA₁, vtyA₁, htA₂, edge, ?_, fun a p hp ha hv => ?_⟩
    · exact fun a b p hp ha hv => ⟨(vpi_M.1 hp ha hv).1, (vpi_N.1 hp ha hv).2⟩
    refine ((LR _).whr ?_ .rfl).2 (vpi_N.2 hp ha hv)
    rw [(?_ : (e0.subst σ).app a = _)]; · exact .tail .rfl .beta
    rw [inst_lift_cons, subst, lift_subst_cons]; rfl
  | proofIrrel Hp =>
    refine .fits fun W => ?_
    have ⟨_, _, s, le_n, le_a, _, hSort, hmem'⟩ := (LE_Interp.sound Hp W).2 hA |>.out
    have hS := WShape.HasType.mono_r hSort.le_sort' .sort hmem'; simp at hS
    have ha' := hS.mono_r ((TShape.LE.lift_l le_n).1 le_a) ((WShape.HasType.lift le_n).2 hmem)
    cases (WShape.lift_eq_bot le_n).1 (hS.proofIrrel ha')
    exact .bot hmem.isType
  | @defn c ci Γ ls u r hreg hlen hTy F hF action hRhs
      ihTy ihF ihRhs =>
    let Hdef : IsDefEqStrong Γ (.const c ls)
        (r.1.applyS ls Empty.elim) (SExpr.mkInst ls ci.type) :=
      .defn hreg hlen hTy F hF action hRhs
    have hlocal : WHRed Γ (.const c ls) (r.1.applyS ls Empty.elim) :=
      .extra action
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · have hRhsInterp := (LE_Interp.sound Hdef W.fits).1.1 hM
      have hAdeq := ihRhs hRhsInterp hA hmem
      have hredL := hlocal.subst W.left.toSubstEq.left
      have hredR := hlocal.subst W.symm.left.toSubstEq.left
      exact ((LR Γ₀).whr (.tail .rfl hredL) (.tail .rfl hredR)).2
        (hAdeq.1 W).1
    · have hRhsInterp := (LE_Interp.sound Hdef W.fits).1.1 hM
      exact (ihRhs hRhsInterp hA hmem).1 W |>.2
    · have hRhsInterp := (LE_Interp.sound Hdef W.fits).1.1 hM
      have hAdeq := ihRhs hRhsInterp hA hmem
      have hred := hlocal.subst W.toSubstEq.left
      exact ((LR Γ₀).whr (.tail .rfl hred) .rfl).2 (hAdeq.2 W)
  | extra action Hl Hr ihl ihr =>
    refine ⟨fun σ σ' W => ⟨?_, ?_⟩, fun σ W => ?_⟩
    · exact ((ihl hM hA hmem).1 W).1
    · exact ((ihr ((LE_Interp.sound
        (.extra action Hl Hr) W.fits).1.1 hM)
        hA hmem).1 W).2
    · have hself := (ihl hM hA hmem).2 W
      have hlocal := SExpr.WHRed.extra action
      have hred := hlocal.subst W.toSubstEq.left
      exact ((LR _).whr .rfl (.tail .rfl hred)).1 hself

/-- The depth bootstrap.  Every contextual adequacy rung follows by strong
Nat induction on stratified typing depth once each rung's joint leaf is
supplied as an `IotaWitnessStepAtDepth` hypothesis.  The induction adds
nothing of its own at a rung: it hands the strict predecessor family to
the leaf obligation unchanged and runs the derivation induction
`adequacy_of_iotaWitnessStep` with the resulting leaf.  In particular no
predecessor inversion or uniqueness package is assembled here; turning
the supplied family into such packages is the leaf producer's decision
(`JointStratifiedPathInversionAt.of_predecessorAdequacy`,
`SelfAdequateDefeqStepAt.of_lowerAdequacy`).

The stratification certificate of the rung being produced is deliberately
not offered to the leaf: the derivation induction is depth-blind, so a
root certificate cannot bound the leaf instances reached through `trans`
or evaluator descent.  Whatever depth bound a leaf producer needs must
come from its own registered-rule certificates. -/
theorem LR.contextualAdequacyAtDepth_of_iotaSteps
    (piInv : LRS.PiPathInv)
    (steps : ∀ d, LR.ContextualIotaWitnessStepAtDepth d) :
    ∀ d, LR.ContextualAdequacyAtDepth d := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro Γ₀ hΓ₀
    intro n Γ ρ M N A B core m a H _hstrat hM hA hmem
    exact LR.adequacy_of_iotaWitnessStep piInv (steps d ih) hΓ₀ H hM hA hmem

/-- Contextual adequacy at every shape level from the complete depth
tower: a strong equality stratifies its left endpoint at some finite
depth (`IsDefEqStrong.stratify`), and the heterogeneous rung at that
depth subsumes the level-indexed statement.  This is the only assembly
the level-indexed packages still require; the level tower survives as a
facade over the depth fixpoint. -/
theorem LR.contextualAdequacyAt_of_adequacyAtDepth
    (tower : ∀ d, LR.ContextualAdequacyAtDepth d) (n : Nat) :
    LR.ContextualAdequacyAt n := by
  intro Γ₀ hΓ₀
  intro Γ ρ M N A m a H hM hA hmem
  obtain ⟨d, hstrat, _⟩ := H.stratify
  exact tower d hΓ₀ H hstrat hM hA hmem

/-- End-to-end conditional form of the depth bootstrap: the complete
depth-indexed leaf family yields every level-indexed contextual adequacy
package. -/
theorem LR.contextualAdequacyAt_of_iotaSteps
    (piInv : LRS.PiPathInv)
    (steps : ∀ d, LR.ContextualIotaWitnessStepAtDepth d) (n : Nat) :
    LR.ContextualAdequacyAt n :=
  LR.contextualAdequacyAt_of_adequacyAtDepth
    (LR.contextualAdequacyAtDepth_of_iotaSteps piInv steps) n

/-! #### The conditional wrap of the joint iota leaf (L4L-16C′w)

The block below wraps the sorried `LR.iotaWitnessStep` as the conditional
`LR.iotaWitnessStep_of_piPathInv`.  The wrap executes the seam map's chain
fold exactly: `hmajorCtor.2` is folded through
`LRS.CtorDefEq.foldRaw_of_majorChainAnchorStep`, conditional on
`LRS.PiPathInv` via `LR.MajorChainAnchorStep.of_piPathInv`, with the
fold's `Q` the root-level `LogRel.DefEqRect` in the major pair; `trans` is
`DefEqRect.trans`, and `anchor` is `DefEqRect.whr` backward along
`WHRedS.major` (both rec prefixes are major premises, certified from the
match arities).  `Q` additionally threads the root-major bridge
`IsDefEq Γ₀ majorX X domain` — available at `anchor` from the root
callbacks and at `trans` by composition — so the per-link handler receives
each chain vertex's raw connection to the original major.

The algebra's `exact` field is the one seam-map step that is NOT closed
here; it is isolated as the named premise `LR.MajorLinkRect` below.  The
recorded deviation reason: firing `LRS.iotaDefEqRect_of_ctorExactAt`
natively at the leaf's level requires the root spine package (the
rec-prefix relations, the last-Pi edge, and the result-type interpretation)
rebased to the leaf vertex's relation `J`, and the return rectangle
transported back to the root observation.  Both transports cross the
frame's `lift`/`unlift` steps only at observations that are exact lift
images (`LogRel.LiftEquiv` constrains the higher relation nowhere else),
while the package's observations — and, in the return direction, the native
leaf's own field observations — are not lift images in general; the frame's
`mono` steps additionally lose the `HasType` coherence at `lam`/`forallE`
field shapes (`WShape.HasTypeLam.mono_l` needs both order directions).
Level counting makes this an obstruction rather than a missing lemma: a
frame that dips below the root level admits no level-`k` observation
dominating a deeper root result observation, so no transported rectangle
can end at the root pair.  The link handler therefore genuinely needs the
semantic normalization content of L4L-16N (the registered RHS's fixed-head
result and the leaf-field adequacy that `piInv` alone does not yet
provide), and `LR.MajorLinkRect` names exactly that residual; it is
discharged at 16N-N5 and nowhere before. -/

/-- The type observation of an ordinary-constructor shape is forced to
`WShape.indTy` (the `ctor'`-typing row of the shape table, extracted from
the body of `LR.DefEq.ctor'_inv` so the wrap can pin the major type shape
before the chain fold). -/
theorem WShape.hasType_ctor'_indTy
    {n : Nat} {c : Name} {fields : List (WShape n)} {a : WShape (n + 1)}
    (hcl : Params.classify c = some (.ctor fields.length))
    (ht : (WShape.ctor' c fields).HasType a) : a = WShape.indTy := by
  have hwf : IsStruct c → WShape.ListNonZero fields := by
    simp [IsStruct, hcl]
  rw [WShape.ctor', dif_pos hwf] at ht
  apply WShape.ext
  change Shape.hasType (n := n + 1)
    (ShapeS.ctor c (fields.map fun x : WShape n => x.1)) a.1 at ht
  cases ha : a.1 <;> simp [ha, Shape.hasType, WShape.indTy] at ht ⊢

/-- Reflect a constructor observation through an exact lift: if a lifted
shape displays as a `.ctor` form, the shape already was that `.ctor` form
one level down, with exactly lifted fields. -/
theorem WShape.lift_ctor_inv {n m' : Nat} (le : n ≤ m')
    {s : WShape (n + 1)} {c : Name} {l : List (WShape m')} {h}
    (heq : s.lift (m' + 1) = WShape.ctor c l h) :
    ∃ l₀ h₀, s = WShape.ctor c l₀ h₀ ∧ l = l₀.map (.lift m') := by
  cases s using WShape.casesOn' with
  | bot =>
    rw [WShape.lift_bot] at heq
    simp [WShape.ext_iff, WShape.bot, WShape.ctor, Shape.bot] at heq
  | sort r =>
    rw [WShape.lift_sort] at heq
    simp [WShape.ext_iff, WShape.sort, WShape.ctor, Shape.sort] at heq
  | forallE a f =>
    rw [WShape.lift_forallE le] at heq
    simp [WShape.ext_iff, WShape.forallE, WShape.ctor] at heq
  | lam f hf =>
    rw [WShape.lift_lam le] at heq
    simp [WShape.ext_iff, WShape.lam, WShape.ctor] at heq
  | ctor c₀ l₀ h₀ =>
    rw [WShape.lift_ctor le] at heq
    obtain ⟨rfl, hl⟩ := WShape.ctor.inj.1 heq
    exact ⟨l₀, h₀, rfl, hl.symm⟩
  | indTy =>
    rw [WShape.lift_indTy] at heq
    simp [WShape.ext_iff, WShape.indTy, WShape.ctor] at heq

/-- A constructor frame preserves each root field as a lower observation of
the corresponding native field.  The comparison is stated between total
shapes because `lift` and `unlift` frames may change the relation level.

This is the fieldwise invariant hidden by `CtorFrame.shape_ctor`: native
evidence can safely be consumed above the registered observation, whereas an
arbitrary native field cannot in general be projected back to the exact root
field. -/
theorem LRS.CtorFrame.shape_ctor_fields {Γ : List SExpr}
    {n k : Nat} {IH : LogRel Γ n} {J : LogRel Γ k}
    {m : WShape (n + 1)} {p : WShape (k + 1)}
    (F : LRS.CtorFrame Γ IH m J p) :
    ∀ {c : Name} {l : List (WShape n)} {h},
      m = WShape.ctor c l h →
      ∃ l' h', p = WShape.ctor c l' h' ∧
        l.Forall₂ (fun root native => root.T ≤ native.T) l' := by
  induction F with
  | refl =>
    intro c l h hm
    exact ⟨l, h, hm,
      List.Forall₂.rfl fun _ _ => TShape.LE.rfl⟩
  | mono hle F' ih =>
    intro c l h hm
    subst hm
    obtain ⟨l₂, h₂, rfl, hroot⟩ := WShape.ctor_le.1 hle
    obtain ⟨l', h', rfl, hnative⟩ := ih rfl
    exact ⟨l', h', rfl,
      List.Forall₂.trans
        (fun _ _ _ h₁ h₂ => (WShape.LE.T h₁).trans h₂)
        hroot hnative⟩
  | lift le E F' ih =>
    intro c l h hm
    obtain ⟨l₀, h₀, rfl, rfl⟩ := WShape.lift_ctor_inv le hm
    obtain ⟨l', h', rfl, hnative⟩ := ih rfl
    refine ⟨l', h', rfl, ?_⟩
    rw [List.forall₂_map_left_iff]
    exact Lean4Lean.List.Forall₂.imp (h := hnative) fun root native hroot =>
      (TShape.lift_eqv le).1.trans hroot
  | unlift le E F' ih =>
    intro c l h hm
    subst hm
    obtain ⟨l', h', rfl, hnative⟩ := ih (WShape.lift_ctor le)
    refine ⟨l', h', rfl, ?_⟩
    rw [List.forall₂_map_left_iff] at hnative
    exact Lean4Lean.List.Forall₂.imp (h := hnative) fun root native hroot =>
      (TShape.lift_eqv le).2.trans hroot

/-- A constructor frame preserves the constructor observation's head and
field count: every shape a `CtorFrame` connects to a `.ctor`-rooted
observation is itself a `.ctor` form with the same head and arity.  This is
the first move of any discharge of `LR.MajorLinkRect`: it aligns the
native leaf's constructor spine with the pattern arity matched at the
root. -/
theorem LRS.CtorFrame.shape_ctor {Γ : List SExpr}
    {n k : Nat} {IH : LogRel Γ n} {J : LogRel Γ k}
    {m : WShape (n + 1)} {p : WShape (k + 1)}
    (F : LRS.CtorFrame Γ IH m J p) :
    ∀ {c : Name} {l : List (WShape n)} {h},
      m = WShape.ctor c l h →
      ∃ l' h', p = WShape.ctor c l' h' ∧ l'.length = l.length := by
  induction F with
  | refl =>
    intro c l h hm
    exact ⟨l, h, hm, rfl⟩
  | mono hle F' ih =>
    intro c l h hm
    subst hm
    obtain ⟨l₂, h₂, rfl, hforall⟩ := WShape.ctor_le.1 hle
    obtain ⟨l', h', rfl, hlen⟩ := ih rfl
    exact ⟨l', h', rfl,
      hlen.trans (Lean4Lean.List.Forall₂.length_eq hforall).symm⟩
  | lift le E F' ih =>
    intro c l h hm
    obtain ⟨l₀, h₀, rfl, rfl⟩ := WShape.lift_ctor_inv le hm
    obtain ⟨l', h', rfl, hlen⟩ := ih rfl
    exact ⟨l', h', rfl, by simpa using hlen⟩
  | unlift le E F' ih =>
    intro c l h hm
    subst hm
    obtain ⟨l', h', rfl, hlen⟩ := ih (WShape.lift_ctor le)
    exact ⟨l', h', rfl, by simpa using hlen⟩

/-- Peel the newest field of a related constructor spine through any
`ret` retypings: recover the remaining spine, the field step's own Pi edge
and payload, and a `TypeDefEqPath` from the instantiated codomain to the
displayed result type.  This is the vertex-spine rebuild step of the
eventual `LR.MajorLinkRect` discharge: the path-valued result type is what
lets the rebuilt spine at the chain vertices avoid identifying the two
independently derived sorts (the chain-wall discipline). -/
theorem LRS.CtorSpineDefEq.cons_inv
    {Γ : List SExpr} {n : Nat} {IH : LogRel Γ n} {Head : SExpr}
    {x y : SExpr} {xs ys : List SExpr} {q : WShape n} {ps : List (WShape n)}
    {A : SExpr}
    (H : LRS.CtorSpineDefEq IH Head (x :: xs) (y :: ys) (q :: ps) A) :
    ∃ (A₀ D C : SExpr) (u v w : SLevel) (a : WShape n),
      LRS.CtorSpineDefEq IH Head xs ys ps A₀ ∧
      IsDefEq Γ A₀ (.forallE D C) (.sort u) ∧
      q.HasType a ∧
      IH.TyDefEq D D a ∧
      IsDefEq Γ x y D ∧
      IH.DefEq x y D q a ∧
      IsDefEq Γ (C.inst y) (C.inst x) (.sort v) ∧
      TypeDefEqPath Γ (C.inst x) A w := by
  generalize hxxs : x :: xs = xxs at H
  generalize hyys : y :: ys = yys at H
  generalize hqps : q :: ps = qps at H
  induction H with
  | nil => cases hxxs
  | cons hrest hPi hp hty hxy hv hresult =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hxxs
    obtain ⟨rfl, rfl⟩ := List.cons.inj hyys
    obtain ⟨rfl, rfl⟩ := List.cons.inj hqps
    exact ⟨_, _, _, _, _, _, _, hrest, hPi, hp, hty, hxy, hv, hresult,
      .single hresult.hasType.2⟩
  | ret hrest hresult ih =>
    obtain ⟨A₀, D, C, u', v, w, a, hspine, hPi, hp, hty, hxy, hv, hres,
      hpath⟩ := ih hxxs hyys hqps
    exact ⟨A₀, D, C, u', v, w, a, hspine, hPi, hp, hty, hxy, hv, hres,
      hpath.trans (.single hresult)⟩

/-- **The isolated per-link residual of the conditional iota-leaf wrap.**

One framed native constructor link of the major chain yields the
root-level synchronized iota rectangle: given the root iota context (the
pattern, the two matches, the registered-RHS interpretation at the root
result observation, the rec-prefix relations, the last-Pi package with the
major type shape pinned at `.indTy`, and the result observations), every
`CtorFrame`-framed `CtorExact` leaf between chain vertices `X, Y` — with
the vertices' raw equality and the root-major bridge `mX ≡ X` — produces
the `LogRel.DefEqRect` of the four recursor applications at the root
observation pair.

This is exactly the `exact` field of the chain-fold algebra in
`LR.iotaWitnessStep_of_piPathInv` below; the other algebra fields and the
whole surrounding derivation are closed there.  Its discharge is 16N-N5's:
the handler must fire `LRS.iotaDefEqRect_of_ctorExactAt` at the link and
return through `LRS.RecAppSync.rect`/`LRS.CtorFrame.rect_via_recAppFrame`,
which requires the semantic normalization inputs (the registered fixed
head's `LR.FixedHeadResult` and leaf-field adequacy) that
`LRS.PiPathInv` alone does not supply — see the section comment above for
the machine-level obstruction record.

Vacuity discipline: the observation-lattice-bottom test is
`LR.MajorLinkRect.rect_at_bot` (the demanded rectangle is satisfiable
outright at a bottom result-type observation), and
`LR.MajorLinkRect.of_noIota` records the environment-conditional vacuous
inhabitant (any `Params` instance registering no recursor iota patterns).
Both are stated below, before this premise's sole consumer. -/
def LR.MajorLinkRect (Γ₀ : List SExpr) : Prop :=
  ∀ {nCtor : Nat} {rec ctor : Name} {major arity : Nat}
    {rI : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {ls : List SLevel} {ρ : Valuation} {R : TShape → SExpr → Prop}
    {recShapes : List (WShape (nCtor + 1))}
    {ctorShapes : List (WShape nCtor)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs : List SExpr} {CHead A : SExpr} {mX mY : SExpr}
    {resultShape resultTypeShape : WShapeFun (nCtor + 1)},
    Ctx.WF Γ₀ →
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    Params.Pat (RecursorIotaPattern rec major ctor arity) rI →
    LE_Interp.Matches (n := nCtor + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec →
    LE_Interp.Matches (n := nCtor)
      (Pattern.varN (.const ctor) arity) ctor ctorShapes mctor →
    LE_Interp.RHS ls (Sum.elim mrec mctor) (LE_Interp.Lower R)
      (resultShape.app (WShape.ctor' ctor ctorShapes.reverse)).T rI.1 →
    LRS.CtorArgsDefEq (LR Γ₀) recXs recYs recShapes →
    IsDefEq Γ₀ (.const rec ls) (.const rec ls) CHead →
    (∃ u, IsDefEq Γ₀ A A (.sort u)) →
    ∀ hpair : SExpr.SpineWF.LastPair Γ₀ CHead recXs recYs mX mY A,
    WShape.HasTypePi resultTypeShape
      (WShape.indTy (n := nCtor)) true →
    (LR Γ₀).TyDefEq hpair.domain hpair.domain
      (WShape.indTy (n := nCtor + 1)) →
    LRS.PiDefEq (LR Γ₀) hpair.domain hpair.codomain hpair.codomain
      (WShape.indTy (n := nCtor)) resultTypeShape →
    (resultShape.app (WShape.ctor' ctor ctorShapes.reverse)).HasType
      (resultTypeShape.app (WShape.ctor' ctor ctorShapes.reverse)) →
    (LR Γ₀).TyDefEq A A
      (resultTypeShape.app (WShape.ctor' ctor ctorShapes.reverse)) →
    ∀ {k : Nat} {J : LogRel Γ₀ k} {p : WShape (k + 1)} {X Y : SExpr},
      LRS.CtorFrame Γ₀ (LR Γ₀)
        (WShape.ctor' ctor ctorShapes.reverse) J p →
      LRS.CtorExact Γ₀ J X Y p →
      IsDefEq Γ₀ X Y hpair.domain →
      IsDefEq Γ₀ mX X hpair.domain →
      LogRel.DefEqRect (LR Γ₀)
        ((recXs.foldr (fun a f => f.app a) (SExpr.const rec ls)).app X)
        ((recXs.foldr (fun a f => f.app a) (SExpr.const rec ls)).app Y)
        ((recYs.foldr (fun a f => f.app a) (SExpr.const rec ls)).app X)
        ((recYs.foldr (fun a f => f.app a) (SExpr.const rec ls)).app Y)
        A (resultShape.app (WShape.ctor' ctor ctorShapes.reverse))
        (resultTypeShape.app (WShape.ctor' ctor ctorShapes.reverse))

/-- Vacuity-discipline check for `LR.MajorLinkRect` (the premortem's
"instantiate at `TShape.bot`" test): at a bottom result-type observation
the demanded rectangle is satisfiable outright, so the premise does not
collapse at the observation-lattice bottom. -/
theorem LR.MajorLinkRect.rect_at_bot
    {Γ₀ : List SExpr} {n : Nat} {M₁ M₂ N₁ N₂ A : SExpr}
    {out : WShape (n + 1)} :
    LogRel.DefEqRect (LR Γ₀) M₁ M₂ N₁ N₂ A out .bot :=
  ⟨trivial, trivial, trivial⟩

/-- Environment-conditional vacuity record for `LR.MajorLinkRect`: in any
`Params` instance registering no recursor iota patterns (e.g. a
definitions-only instance), the premise holds outright. -/
theorem LR.MajorLinkRect.of_noIota
    (hno : ∀ {rec ctor : Name} {major arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check},
      ¬ Params.Pat (RecursorIotaPattern rec major ctor arity) r) :
    LR.MajorLinkRect Γ₀ := by
  intro _nCtor _rec _ctor _major _arity _rI _ls _ρ _R _recShapes _ctorShapes
    _mrec _mctor _recXs _recYs _CHead _A _mX _mY _resultShape _resultTypeShape
    _hΓ₀ _hR hpat
  exact absurd hpat hno

/-- **The conditional wrap of the joint iota leaf** (L4L-16C′w, E1).

Everything of the sorried `LR.iotaWitnessStep` except the per-link
rectangle is closed here from `LRS.PiPathInv`: the match is split, the
major type shape is pinned to `.indTy` (`WShape.hasType_ctor'_indTy`), the
major pair's constructor observation is normalized through
`LR.DefEq.ctor'_inv`, and the resulting free closure is folded by
`LRS.CtorDefEq.foldRaw_of_majorChainAnchorStep` with the anchor step
supplied by `LR.MajorChainAnchorStep.of_piPathInv piInv` — the wrap's only
use of the leaf Prop, exactly as the 2026-08-15 re-cut prescribed.  The
fold's `Q` is the root-level rectangle in the major pair with the
root-major bridge threaded through; `trans` and `anchor` are discharged by
`LogRel.DefEqRect.trans` and `LogRel.DefEqRect.whr` along `WHRedS.major`
(the rec prefixes are major premises by `Pattern.varN_const_matchesS` at
the match arities).  The rectangle's diagonal at the original majors is
the leaf conclusion.

`piInv` is a hypothesis, full stop: nothing here fires
`LRS.PiPathInv.of_adequacy` or `.of_jointStratifiedPathInversion`, and the
`linkRect` premise is the named residual discharged at 16N-N5. -/
theorem LR.iotaWitnessStep_of_piPathInv
    (piInv : LRS.PiPathInv) (linkRect : LR.MajorLinkRect Γ₀) :
    LR.IotaWitnessStep Γ₀ := by
  intro hΓ₀ ρ c ls R hR
  intro nI rargsI rec major ctor arity rI mcapI
    xsI ysI CHeadI AI outI outTyI hpatI hmatchI hrhsI hleafI
    htermI hAIType hheadI hspineXI hspineYI houtI hAI
  cases hmatchI with
  | @app fPat nCtor head recShapes mrec aPat ctorHead
      ctorShapes mctor hmfI hmaI =>
    rcases hleafI with
      ⟨majorX, recXs, majorY, recYs, majorShape, recShapesI,
        majorTypeShape, resultShape, resultTypeShape,
        hxs, hys, hrargs, houtEq, houtTyEq, hlastPair,
        hpMajor, hresultType, htyMajor, hvMajor, halignedI, hPiI⟩
    subst xsI
    subst ysI
    simp only [List.cons.injEq] at hrargs
    rcases hrargs with ⟨hmajorShape, hrecShapes⟩
    subst majorShape
    subst recShapesI
    subst outI
    subst outTyI
    have hctorHead : ctor = ctorHead := hmaI.varN_const_head
    subst ctorHead
    have hctorClass : Params.classify ctor =
        some (.ctor ctorShapes.reverse.length) := by
      simpa using hmaI.head_wf_eq (Params.pat_wf hpatI).2
    have hmajorCtor := LR.DefEq.ctor'_inv hctorClass hpMajor hvMajor
    have hrecargsI : LRS.CtorArgsDefEq (LR Γ₀)
        recXs recYs recShapes :=
      halignedI.args.tail
    have hmts : majorTypeShape = WShape.indTy :=
      WShape.hasType_ctor'_indTy hctorClass hpMajor
    subst majorTypeShape
    have hrecHead : rec = c := hmfI.varN_const_head
    subst c
    have hrecShapesLen : recShapes.length = major :=
      hmfI.varN_length
    obtain ⟨hXlen, hYlen⟩ := hrecargsI.lengths
    have hmajorPremX : IsMajorPremise
        (recXs.foldr (fun a f => f.app a) (.const rec ls)) := by
      have hlen : recXs.length = major := hXlen.trans hrecShapesLen
      obtain ⟨m2, hm2⟩ := hlen ▸ Pattern.varN_const_matchesS rec ls recXs
      exact ⟨_, ⟨rI, hpatI⟩, _, _, .refl, ls, m2, hm2⟩
    have hmajorPremY : IsMajorPremise
        (recYs.foldr (fun a f => f.app a) (.const rec ls)) := by
      have hlen : recYs.length = major := hYlen.trans hrecShapesLen
      obtain ⟨m2, hm2⟩ := hlen ▸ Pattern.varN_const_matchesS rec ls recYs
      exact ⟨_, ⟨rI, hpatI⟩, _, _, .refl, ls, m2, hm2⟩
    have step := LR.MajorChainAnchorStep.of_piPathInv piInv hΓ₀
    have hfold := LRS.CtorDefEq.foldRaw_of_majorChainAnchorStep
      (D := hlastPair.domain)
      (Q := fun X Y =>
        IsDefEq Γ₀ majorX X hlastPair.domain →
          LogRel.DefEqRect (LR Γ₀)
            ((recXs.foldr (fun a f => f.app a) (SExpr.const rec ls)).app X)
            ((recXs.foldr (fun a f => f.app a) (SExpr.const rec ls)).app Y)
            ((recYs.foldr (fun a f => f.app a) (SExpr.const rec ls)).app X)
            ((recYs.foldr (fun a f => f.app a) (SExpr.const rec ls)).app Y)
            AI (resultShape.app (WShape.ctor' ctor ctorShapes.reverse))
            (resultTypeShape.app (WShape.ctor' ctor ctorShapes.reverse)) ∧
          IsDefEq Γ₀ majorX Y hlastPair.domain)
      step
      { exact := fun {k J p X Y} F E hXY hbr =>
          ⟨linkRect hΓ₀ hR hpatI hmfI hmaI hrhsI hrecargsI hheadI hAIType
            hlastPair hresultType htyMajor hPiI houtI hAI F E hXY hbr,
           hbr.trans hXY⟩
        trans := fun h₁ h₂ => by
          intro hbr
          obtain ⟨r₁, hY⟩ := h₁ hbr
          obtain ⟨r₂, hZ⟩ := h₂ hY
          exact ⟨r₁.trans r₂, hZ⟩
        anchor := fun {M N X Y} VM VN hMX hNY hQ => by
          intro hbr
          obtain ⟨rXY, hY⟩ := hQ (hbr.trans hMX)
          cases VM with
          | intro _ hredM =>
            cases VN with
            | intro _ hredN =>
              exact ⟨(LogRel.DefEqRect.whr
                (WHRedS.major hmajorPremX hredM)
                (WHRedS.major hmajorPremX hredN)
                (WHRedS.major hmajorPremY hredM)
                (WHRedS.major hmajorPremY hredN)).2 rXY,
                hY.trans hNY.symm⟩ }
      hmajorCtor.2
      hlastPair.major.hasType.1
      hlastPair.major.hasType.2
    exact (hfold hlastPair.major.hasType.1).1.cross

/-- Main adequacy theorem, now a thin consumer of the conditional joint
leaf: the two leaf inputs `piInv` and `linkRect` are hypotheses, and
`LR.iotaWitnessStep_of_piPathInv` closes everything else. -/
theorem LR.adequacy (H : IsDefEqStrong Γ M N A)
    (hΓ₀ : Ctx.WF Γ₀)
    (piInv : LRS.PiPathInv) (linkRect : LR.MajorLinkRect Γ₀)
    (hM : LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A)
    (hmem : m.HasType a) :
    Adequate (n := n) Γ₀ Γ ρ M N A m a :=
  LR.adequacy_of_iotaWitnessStep piInv
    (LR.iotaWitnessStep_of_piPathInv piInv linkRect) hΓ₀ H hM hA hmem

/-- The polymorphic theorem supplies each individual level package.  Keeping
this adapter separate is what lets the joint proof replace it with the
strictly earlier package during well-founded recursion. -/
theorem LR.adequacyAt (Γ₀ : List SExpr) (hΓ₀ : Ctx.WF Γ₀)
    (piInv : LRS.PiPathInv) (linkRect : LR.MajorLinkRect Γ₀) (n : Nat) :
    LR.AdequacyAt Γ₀ n :=
  fun H hM hA hmem => LR.adequacy H hΓ₀ piInv linkRect hM hA hmem

/-- Pi-head inversion from adequacy at one positive shape level.  Domain and
codomain conversions are retained as paths because the weak judgment does
not yet identify the universe assigned to an intermediate type. -/
theorem forallE_whRed_l_of_adequacy
    {n : Nat} (adequacy : LR.AdequacyAt Γ (n + 1))
    (d : IsDefEqStrong Γ A₀ (SExpr.forallE B₁ F₁) (.sort s)) :
    ∃ B₀ F₀, Γ ⊢ A₀ ⤳* .forallE B₀ F₀ ∧ ∃ u v,
      TypeDefEqPath Γ B₀ B₁ u ∧ TypeDefEqPath (B₀ :: Γ) F₀ F₁ v := by
  have hPi : LE_Interp .nil
      (WShape.T (n := n + 1) (.forallE (.bot : WShape n) WShapeFun.bot))
      (.forallE B₁ F₁) := by
    refine .forallE' .bot .bot (.bot <| .bot' .sort) fun _ h => ?_
    cases h.bot_r; exact WShapeFun.bot_app.symm ▸ .bot
  have hmem : WShape.HasType (n := n + 1)
      (.forallE (.bot : WShape n) WShapeFun.bot) (.sort (s ≠ .zero)) := by
    refine WShape.HasType.forallE_l.2 ⟨_, ?_, rfl⟩
    refine WShape.HasTypePi.iff.2 ⟨.bot (.bot' .sort), fun x hx => ?_⟩
    cases WShape.HasType.bot_r hx; exact WShapeFun.bot_app.symm ▸ .bot .sort
  have := (adequacy d ((LE_Interp.sound d .nil).1.2 hPi)
    (.sort TShape.sort_eqv.1) hmem).2 .id
  have ⟨_, _, _, _, _, _, redA₀, redPi, convB, convF, _⟩ := subst_id ▸ subst_id ▸ subst_id ▸ this
  cases WHNF.forallE.whRedS redPi; exact ⟨_, _, redA₀, _, _, convB, convF⟩

theorem forallE_whRed_l
    (hΓ : Ctx.WF Γ)
    (piInv : LRS.PiPathInv) (linkRect : LR.MajorLinkRect Γ)
    (d : IsDefEqStrong Γ A₀ (SExpr.forallE B₁ F₁) (.sort s)) :
    ∃ B₀ F₀, Γ ⊢ A₀ ⤳* .forallE B₀ F₀ ∧ ∃ u v,
      TypeDefEqPath Γ B₀ B₁ u ∧ TypeDefEqPath (B₀ :: Γ) F₀ F₁ v :=
  forallE_whRed_l_of_adequacy (n := 0) (LR.adequacyAt Γ hΓ piInv linkRect 1) d

/-- Collapse path-valued Pi-head inversion using contextual raw type
uniqueness.  The domain path supplies the typing needed to establish that
the extended binder context is well formed before the codomain path is
collapsed. -/
theorem forallE_whRed_l_of_adequacy_collapsed
    {n : Nat} (adequacy : LR.AdequacyAt Γ (n + 1))
    (uniq : LogRel.ContextualRawTypeUniq) (hΓ : Ctx.WF Γ)
    (d : IsDefEqStrong Γ A₀ (SExpr.forallE B₁ F₁) (.sort s)) :
    ∃ B₀ F₀, Γ ⊢ A₀ ⤳* .forallE B₀ F₀ ∧ ∃ u v,
      Γ ⊢ B₀ ≡ B₁ : .sort u ∧ B₀ :: Γ ⊢ F₀ ≡ F₁ : .sort v := by
  obtain ⟨B₀, F₀, hred, u, v, hB, hF⟩ :=
    forallE_whRed_l_of_adequacy adequacy d
  have hB' := hB.collapse (uniq hΓ)
  have hBΓ : Ctx.WF (B₀ :: Γ) := ⟨hΓ, ⟨u, hB.leftType⟩⟩
  exact ⟨B₀, F₀, hred, u, v, hB', hF.collapse (uniq hBΓ)⟩

/-- Pi–Pi injectivity: if two Pi types are definitionally equal,
their domains and codomains are each definitionally equal. -/
theorem forallE_inv_of_adequacy
    {n : Nat} (adequacy : LR.AdequacyAt Γ (n + 1))
    (H : IsDefEqStrong Γ (SExpr.forallE A₀ B₀) (SExpr.forallE A₁ B₁) (.sort s)) :
    ∃ u v, TypeDefEqPath Γ A₀ A₁ u ∧
      TypeDefEqPath (A₀ :: Γ) B₀ B₁ v := by
  have ⟨_, _, red, H⟩ := forallE_whRed_l_of_adequacy adequacy H
  cases WHNF.forallE.whRedS red; exact H

theorem forallE_inv
    (hΓ : Ctx.WF Γ)
    (piInv : LRS.PiPathInv) (linkRect : LR.MajorLinkRect Γ)
    (H : IsDefEqStrong Γ (SExpr.forallE A₀ B₀) (SExpr.forallE A₁ B₁) (.sort s)) :
    ∃ u v, TypeDefEqPath Γ A₀ A₁ u ∧
      TypeDefEqPath (A₀ :: Γ) B₀ B₁ v :=
  forallE_inv_of_adequacy (n := 0) (LR.adequacyAt Γ hΓ piInv linkRect 1) H

/-- Ordinary Pi injectivity recovered from the path-valued adequacy result
at the precise contextual-uniqueness boundary. -/
theorem forallE_inv_of_adequacy_collapsed
    {n : Nat} (adequacy : LR.AdequacyAt Γ (n + 1))
    (uniq : LogRel.ContextualRawTypeUniq) (hΓ : Ctx.WF Γ)
    (H : IsDefEqStrong Γ (SExpr.forallE A₀ B₀)
      (SExpr.forallE A₁ B₁) (.sort s)) :
    ∃ u v, Γ ⊢ A₀ ≡ A₁ : .sort u ∧
      A₀ :: Γ ⊢ B₀ ≡ B₁ : .sort v := by
  obtain ⟨_, _, hred, hInv⟩ :=
    forallE_whRed_l_of_adequacy_collapsed adequacy uniq hΓ H
  cases WHNF.forallE.whRedS hred
  exact hInv

theorem sort_forallE_inv_of_adequacy
    {n : Nat} (adequacy : LR.AdequacyAt Γ (n + 1)) :
    ¬IsDefEqStrong Γ (.sort u) (SExpr.forallE A₁ B₁) (.sort s) :=
  fun H => have ⟨_, _, H⟩ := forallE_whRed_l_of_adequacy adequacy H
    nomatch WHNF.sort.whRedS H.1

theorem sort_forallE_inv (hΓ : Ctx.WF Γ)
    (piInv : LRS.PiPathInv) (linkRect : LR.MajorLinkRect Γ) :
    ¬IsDefEqStrong Γ (.sort u) (SExpr.forallE A₁ B₁) (.sort s) :=
  sort_forallE_inv_of_adequacy (n := 0) (LR.adequacyAt Γ hΓ piInv linkRect 1)

/-- Sort injectivity: if two sorts are definitionally equal, their levels are equal. -/
theorem sort_inv_of_adequacy
    {k : Nat} (adequacy : LR.AdequacyAt Γ (k + 1))
    (d : IsDefEqStrong Γ (SExpr.sort u) (SExpr.sort v) V) : u = v := by
  have hM : LE_Interp .nil
      (WShape.T (n := k + 1) (.sort (decide (u ≠ .zero)))) (.sort u) :=
    .sort TShape.sort_eqv.1
  have ⟨n, mU, mV, h1, h2, h3, hA, h5⟩ := (LE_Interp.sound d .nil).2 hM |>.out
  have h2' := WShape.lift_sort ▸ (TShape.LE.lift_l h1).1 h2; dsimp only at h2'
  cases WShape.sort_le.1 h2'
  cases show mV = (.sort true : WShape (k + 1)).lift n by
    let _+1 := n
    simp only [WShape.HasType, WShape.sort] at h5
    ext1; generalize mV.val = mv at h5
    let .sort := Shape.HasType.unfold_iff.1 h5; rfl
  have h1' : k + 1 ≤ n := h1
  have := (adequacy d hM (hA.unlift h1') .sort).2 .id
  have ⟨w, h1, h2⟩ := (LR _).sort_iff.1 (subst_id ▸ subst_id ▸ subst_id ▸ this)
  cases WHNF.sort.whRedS h1; cases WHNF.sort.whRedS h2; rfl

/-- Package the stratified inversion interface from positive-level adequacy
once contextual raw type uniqueness is available.

The raw uniqueness argument is used only to collapse the path-valued Pi
observation and to align the universe indices on the shallower stratified
domain/codomain typings.  This remains a useful successor-stage adapter; the
level-zero bootstrap is instead solved non-circularly by
`JointStratifiedInversion.of_adequacy` above. -/
theorem JointStratifiedInversion.of_adequacy_and_typeUniq
    (adequacy : LR.ContextualAdequacyAt 1)
    (uniq : LogRel.ContextualRawTypeUniq) :
    JointStratifiedInversion where
  sortInv hΓ h := sort_inv_of_adequacy (k := 0) (adequacy hΓ) h
  forallEInv := by
    intro Γ A B A' B' V V' s n n' hΓ h hL hR
    obtain ⟨uL, vL, hAL, hBL⟩ := hL.forallE_inv
    obtain ⟨uR, vR, hAR, hBR⟩ := hR.forallE_inv
    obtain ⟨u, v, hAA, hBB⟩ :=
      forallE_inv_of_adequacy_collapsed (n := 0)
        (adequacy hΓ) uniq hΓ h
    have levelEq {Δ : List SExpr} (hΔ : Ctx.WF Δ)
        {X : SExpr} {l₁ l₂ : SLevel}
        (hx₁ : IsDefEq Δ X X (.sort l₁))
        (hx₂ : IsDefEq Δ X X (.sort l₂)) : l₁ = l₂ := by
      obtain ⟨_, hs⟩ := uniq hΔ hx₁ hx₂
      exact sort_inv_of_adequacy (k := 0) (adequacy hΔ) (hs.strong hΔ)
    have huL : uL = u := levelEq hΓ hAL.hasType hAA.hasType.1
    cases huL
    have hΓA : Ctx.WF (A :: _) := ⟨hΓ, ⟨_, hAA.hasType.1⟩⟩
    have hvL : vL = v := levelEq hΓA hBL.hasType hBB.hasType.1
    cases hvL
    have hΓA' : Ctx.WF (A' :: _) := ⟨hΓ, ⟨_, hAA.hasType.2⟩⟩
    have hBB' : IsDefEq (A' :: _) B' B' (.sort vL) :=
      hAA.defeqDF_l hBB.hasType.2
    have hvR : vR = vL := levelEq hΓA' hBR.hasType hBB'
    cases hvR
    exact ⟨⟨uL, hAA, hAL⟩, vL, hBB, hBL, hBR⟩

theorem sort_inv (hΓ : Ctx.WF Γ)
    (piInv : LRS.PiPathInv) (linkRect : LR.MajorLinkRect Γ)
    (d : IsDefEqStrong Γ (SExpr.sort u) (SExpr.sort v) V) : u = v :=
  sort_inv_of_adequacy (k := 0) (LR.adequacyAt Γ hΓ piInv linkRect 1) d

/-- Experimental end-to-end sort injectivity for `VExpr`, assuming the rewrite-rule
infrastructure packaged by `SExpr.Params`. -/
theorem _root_.Lean4Lean.VEnv.IsDefEqU.sort_invS
    [Params.Semantic]
    (piInv : LRS.PiPathInv) (linkRect : ∀ Γ, LR.MajorLinkRect Γ)
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (h : Params.env.IsDefEqU Params.univs Γ (.sort u) (.sort v)) : u ≈ v := by
  obtain ⟨A, h⟩ := h
  have hΓwf := (VEnv.CtxStrong.strong Params.henv hΓ).levelWF
  have hu : u.WF Params.univs := (h.levelWF hΓwf).1
  have hv : v.WF Params.univs := (h.levelWF hΓwf).2.1
  have huv := SExpr.sort_inv (Ctx.WF.mkS hΓ) piInv (linkRect _)
    ((h.strong Params.henv hΓ).mkS)
  apply VLevel.equiv_def'.2
  rw [← SLevel.mk_val hu, ← SLevel.mk_val hv, huv]
