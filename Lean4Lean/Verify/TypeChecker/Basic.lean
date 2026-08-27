/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Typing.ConditionallyTyped
import Lean4Lean.TypeChecker
import Lean4Lean.Theory.ProjectionView
import Lean4Lean.Theory.RestoredBlockProjection

namespace Except

def WF (x : Except ε α) (Q : α → Prop) : Prop := ∀ a, x = .ok a → Q a

theorem WF.bind {x : Except ε α} {f : α → Except ε β} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → (f a).WF R) : (x >>= f).WF R := by
  intro b
  simp [(· >>= ·), Except.bind]
  split; · simp
  exact h2 _ (h1 _ rfl) _

theorem WF.pure {Q} (H : Q a) :
    (pure a : Except ε α).WF Q := by rintro _ ⟨⟩; exact H

theorem WF.map {x : Except ε α} {f : α → β} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → R (f a)) : (f <$> x).WF R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ h => .pure (h2 _ h)

theorem WF.mono {x : Except ε α} {Q R}
    (h1 : x.WF Q) (h2 : ∀ a, Q a → R a) : x.WF R := by
  simpa using h1.bind fun _ h => .pure (h2 _ h)

theorem WF.throw {Q} : (throw e : Except ε α).WF Q := nofun

theorem WF.le {Q R} {x : Except ε α}
    (h1 : x.WF Q) (H : ∀ a, Q a → R a) :
    x.WF R := fun _ e => H _ (h1 _ e)

theorem WF.pureBind  {f : β → Except ε α} {Q}
    {x : β} (H : WF (f x) Q) : ((Pure.pure x : Except ε β) >>= f).WF Q := H

end Except

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace EquivManager

variable {env : VEnv} {Us : List Name} {Δ : VLCtx}
variable (env Us Δ) in
inductive IsDefEqE : Expr → Expr → Prop
  | rfl : IsDefEqE e e
  | trans : IsDefEqE e₁ e₂ → IsDefEqE e₂ e₃ → IsDefEqE e₁ e₃
  | defeq : TrExprS env Us Δ e₁ e' → TrExpr env Us Δ e₂ e' → IsDefEqE e₁ e₂
  | app : IsDefEqE f₁ f₂ → IsDefEqE a₁ a₂ → IsDefEqE (.app f₁ a₁) (.app f₂ a₂)
  | lam : IsDefEqE d₁ d₂ → IsDefEqE b₁ b₂ → IsDefEqE (.lam _ d₁ b₁ _) (.lam _ d₂ b₂ _)
  | forallE : IsDefEqE d₁ d₂ → IsDefEqE b₁ b₂ → IsDefEqE (.forallE _ d₁ b₁ _) (.forallE _ d₂ b₂ _)
  | letE : IsDefEqE t₁ t₂ → IsDefEqE v₁ v₂ → IsDefEqE b₁ b₂ →
    IsDefEqE (.letE _ t₁ v₁ b₁ _) (.letE _ t₂ v₂ b₂ _)
  | mdata : IsDefEqE e₁ e₂ → IsDefEqE (.mdata _ e₁) (.mdata _ e₂)
  | proj : IsDefEqE e₁ e₂ → IsDefEqE (.proj _ i e₁) (.proj _ i e₂)

theorem IsDefEqE.symm (H1 : IsDefEqE env Us Δ e₁ e₂) : IsDefEqE env Us Δ e₂ e₁ := by
  induction H1 with
  | rfl => exact .rfl
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1
  | defeq h1 h2 => let ⟨_, h2, h3⟩ := h2; exact .defeq h2 ⟨_, h1, h3.symm⟩
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

variable! (henv : env.WF) (W : VLCtx.FVLift' Δ Δ' 0 n 0) (hΔ : VLCtx.WF env Us.length Δ') in
theorem IsDefEqE.weak' (H1 : IsDefEqE env Us Δ e₁ e₂) : IsDefEqE env Us Δ' e₁ e₂ := by
  induction H1 with
  | rfl => exact .rfl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | defeq h1 h2 => exact .defeq (h1.weakFV' henv W hΔ) (h2.weakFV' henv W hΔ)
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

variable (env Us Δ) in
structure WF (m : EquivManager) where
  wf {i} : i < m.uf.size ↔ ∃ e : Expr, m.toNodeMap[e]? = some i
  defeq {e₁ e₂ : Expr} {i₁ i₂} :
    m.toNodeMap[e₁]? = some i₁ → m.toNodeMap[e₂]? = some i₂ → m.uf.Equiv i₁ i₂ →
    IsDefEqE env Us Δ e₁ e₂

theorem WF.empty : WF env Us Δ {} where
  wf := by simp
  defeq := by simp

variable! (henv : env.WF) (W : VLCtx.FVLift' Δ Δ' 0 n 0) (hΔ : VLCtx.WF env Us.length Δ') in
theorem WF.weak' (wf : WF env Us Δ m) : WF env Us Δ' m where
  wf := wf.wf
  defeq h1 h2 h3 := wf.defeq h1 h2 h3 |>.weak' henv W hΔ

end EquivManager

/-- Newly inserted loose variables occur only at and above the insertion
point. -/
theorem Expr.hasLooseBVar'_liftLooseBVars_below
    {expression : Expr} {start amount index : Nat}
    (below : index < amount) :
    (expression.liftLooseBVars' start amount).hasLooseBVar'
      (start + index) = false := by
  induction expression generalizing start index with
  | bvar i =>
      simp [Expr.liftLooseBVars', Expr.hasLooseBVar']
      split <;> omega
  | fvar fv => simp [Expr.liftLooseBVars', Expr.hasLooseBVar']
  | mvar m => simp [Expr.liftLooseBVars', Expr.hasLooseBVar']
  | sort u => simp [Expr.liftLooseBVars', Expr.hasLooseBVar']
  | const n us => simp [Expr.liftLooseBVars', Expr.hasLooseBVar']
  | lit l => simp [Expr.liftLooseBVars', Expr.hasLooseBVar']
  | mdata data body ih =>
      simpa [Expr.liftLooseBVars', Expr.hasLooseBVar'] using ih below
  | proj n i body ih =>
      simpa [Expr.liftLooseBVars', Expr.hasLooseBVar'] using ih below
  | app fn arg ihFn ihArg =>
      simp [Expr.liftLooseBVars', Expr.hasLooseBVar', ihFn below, ihArg below]
  | lam n type body bi ihType ihBody =>
      simp only [Expr.liftLooseBVars', Expr.hasLooseBVar']
      rw [ihType below]
      simp only [Bool.false_or]
      rw [show start + index + 1 = (start + 1) + index by omega]
      exact ihBody (start := start + 1) (index := index) below
  | forallE n type body bi ihType ihBody =>
      simp only [Expr.liftLooseBVars', Expr.hasLooseBVar']
      rw [ihType below]
      simp only [Bool.false_or]
      rw [show start + index + 1 = (start + 1) + index by omega]
      exact ihBody (start := start + 1) (index := index) below
  | letE n type value body nd ihType ihValue ihBody =>
      simp only [Expr.liftLooseBVars', Expr.hasLooseBVar']
      rw [ihType below, ihValue below]
      simp only [Bool.false_or]
      rw [show start + index + 1 = (start + 1) + index by omega]
      exact ihBody (start := start + 1) (index := index) below

/-- Substitution strictly above a loose-variable slot preserves whether that
slot occurs. -/
theorem Expr.hasLooseBVar'_instantiate1_below
    {expression argument : Expr} {depth index : Nat}
    (below : index < depth) :
    (expression.instantiate1' argument depth).hasLooseBVar' index =
      expression.hasLooseBVar' index := by
  induction expression generalizing depth index with
  | bvar i =>
      simp [Expr.instantiate1', Expr.hasLooseBVar']
      split <;> rename_i hlt
      · rfl
      · split <;> rename_i heq
        · subst i
          have hne : depth ≠ index := by omega
          simpa [hne] using
            (Expr.hasLooseBVar'_liftLooseBVars_below
              (expression := argument) (start := 0) below)
        · simp [Expr.hasLooseBVar']
          omega
  | fvar fv => simp [Expr.instantiate1', Expr.hasLooseBVar']
  | mvar m => simp [Expr.instantiate1', Expr.hasLooseBVar']
  | sort u => simp [Expr.instantiate1', Expr.hasLooseBVar']
  | const n us => simp [Expr.instantiate1', Expr.hasLooseBVar']
  | lit l => simp [Expr.instantiate1', Expr.hasLooseBVar']
  | mdata data body ih =>
      simpa [Expr.instantiate1', Expr.hasLooseBVar'] using ih below
  | proj n i body ih =>
      simpa [Expr.instantiate1', Expr.hasLooseBVar'] using ih below
  | app fn arg ihFn ihArg =>
      simp [Expr.instantiate1', Expr.hasLooseBVar', ihFn below, ihArg below]
  | lam n type body bi ihType ihBody =>
      simp [Expr.instantiate1', Expr.hasLooseBVar', ihType below,
        ihBody (Nat.succ_lt_succ below)]
  | forallE n type body bi ihType ihBody =>
      simp [Expr.instantiate1', Expr.hasLooseBVar', ihType below,
        ihBody (Nat.succ_lt_succ below)]
  | letE n type value body nd ihType ihValue ihBody =>
      simp [Expr.instantiate1', Expr.hasLooseBVar', ihType below,
        ihValue below, ihBody (Nat.succ_lt_succ below)]

theorem Expr.hasLooseBVar'_instantiateLevelParamsCoreCpp'
    (expression : Expr) (reduce : Bool) (substitution : Name → Level)
    (depth : Nat) :
    (expression.instantiateLevelParamsCoreCpp' reduce substitution).hasLooseBVar'
      depth = expression.hasLooseBVar' depth := by
  induction expression generalizing depth with
  | bvar | fvar | mvar | sort | const | lit =>
      simp [Expr.instantiateLevelParamsCoreCpp', Expr.hasLooseBVar']
  | app function argument functionIH argumentIH =>
      simp [Expr.instantiateLevelParamsCoreCpp', Expr.hasLooseBVar',
        functionIH, argumentIH]
  | lam name domain body binderInfo domainIH bodyIH =>
      simp [Expr.instantiateLevelParamsCoreCpp', Expr.hasLooseBVar',
        domainIH, bodyIH]
  | forallE name domain body binderInfo domainIH bodyIH =>
      simp [Expr.instantiateLevelParamsCoreCpp', Expr.hasLooseBVar',
        domainIH, bodyIH]
  | letE name type value body nondep typeIH valueIH bodyIH =>
      simp [Expr.instantiateLevelParamsCoreCpp', Expr.hasLooseBVar',
        typeIH, valueIH, bodyIH]
  | proj structName index expression expressionIH =>
      simp [Expr.instantiateLevelParamsCoreCpp', Expr.hasLooseBVar', expressionIH]
  | mdata data expression expressionIH =>
      simp [Expr.instantiateLevelParamsCoreCpp', Expr.hasLooseBVar', expressionIH]

theorem Expr.hasLooseBVar'_instantiateLevelParamsCpp
    (expression : Expr) (parameters : List Name) (levels : List Level)
    (depth : Nat) :
    (expression.instantiateLevelParamsCpp parameters levels).hasLooseBVar' depth =
      expression.hasLooseBVar' depth := by
  rw [Expr.instantiateLevelParamsCpp_eq]
  exact Expr.hasLooseBVar'_instantiateLevelParamsCoreCpp'
    expression _ _ depth

/-- A syntactic skip below a substitution point survives that substitution. -/
theorem VExpr.Skips.instN_high
    {expression argument : VExpr} {amount start depth : Nat}
    (self : expression.Skips amount start) (high : start + amount ≤ depth) :
    (expression.inst argument depth).Skips amount start := by
  obtain ⟨base, rfl⟩ := VExpr.skips_iff_exists.1 self
  obtain ⟨offset, rfl⟩ := Nat.le_iff_exists_add'.1 high
  apply VExpr.skips_iff_exists.2
  refine ⟨base.inst argument (start + offset), ?_⟩
  rw [show offset + (start + amount) = amount + (start + offset) by omega]
  exact (VExpr.liftN_instN_lo amount base argument (start + offset) start
    (Nat.le_add_right start offset)).symm

/-- A syntactic skip below a lift point survives that lift. -/
theorem VExpr.Skips.liftN_high
    {expression : VExpr} {skipAmount skipStart liftAmount liftStart : Nat}
    (self : expression.Skips skipAmount skipStart)
    (high : skipStart + skipAmount ≤ liftStart) :
    (expression.liftN liftAmount liftStart).Skips skipAmount skipStart := by
  rw [VExpr.skips_iff] at self ⊢
  induction expression generalizing skipStart liftStart with
  | bvar index =>
      simp only [VExpr.Skips', VExpr.liftN]
      simp only [VExpr.Skips'] at self
      unfold liftVar
      split <;> omega
  | sort level => trivial
  | const name levels => trivial
  | app function argument functionIH argumentIH =>
      simp only [VExpr.Skips', VExpr.liftN] at self ⊢
      exact ⟨functionIH self.1 high, argumentIH self.2 high⟩
  | lam domain body domainIH bodyIH =>
      simp only [VExpr.Skips', VExpr.liftN] at self ⊢
      exact ⟨domainIH self.1 high, bodyIH self.2 (by omega)⟩
  | forallE domain body domainIH bodyIH =>
      simp only [VExpr.Skips', VExpr.liftN] at self ⊢
      exact ⟨domainIH self.1 high, bodyIH self.2 (by omega)⟩

theorem VExpr.Skips.instL
    {expression : VExpr} {amount start : Nat} {levels : List VLevel}
    (self : expression.Skips amount start) :
    (expression.instL levels).Skips amount start := by
  obtain ⟨base, rfl⟩ := VExpr.skips_iff_exists.1 self
  rw [VExpr.instL_liftN]
  exact .liftN

/-- Nested restoration preserves a syntactic skip whenever its replacement
values are closed. -/
theorem VExpr.Skips.restoreExpr
    {entries : List VInductDecl.RestoreEntry}
    {recMap : List (Name × Name)} {expression : VExpr}
    {amount start : Nat}
    (closed : VInductDecl.RestoreEntriesClosed entries)
    (self : expression.Skips amount start) :
    (VInductDecl.restoreExpr entries recMap expression).Skips amount start := by
  obtain ⟨base, rfl⟩ := VExpr.skips_iff_exists.1 self
  rw [← VInductDecl.restoreExpr_liftN entries closed]
  exact .liftN

/-- Producer-owned syntactic dependency alignment between a host Pi prefix
and its exact Theory translation.  Projection inference only needs this
one-way fact: when a host body omits its newly bound variable, the registered
Theory body literally skips the corresponding slot. -/
inductive ProjectionSpineSupport : Nat → Expr → VExpr → Prop where
  | nil (source : Expr) (target : VExpr) :
      ProjectionSpineSupport 0 source target
  | cons
      (skip : body.hasLooseBVar' 0 = false → targetBody.Skips 1 0)
      (tail : ProjectionSpineSupport count body targetBody) :
      ProjectionSpineSupport (count + 1)
        (.forallE name domain body binderInfo)
        (.forallE targetDomain targetBody)

/-- Restore the Theory side of a host/Theory Pi-prefix dependency witness.
Restoration is structural on binders and closed replacement values preserve
the only nontrivial datum carried by the witness: skipped de Bruijn slots. -/
theorem ProjectionSpineSupport.restoreExpr
    {entries : List VInductDecl.RestoreEntry}
    {recMap : List (Name × Name)}
    (closed : VInductDecl.RestoreEntriesClosed entries)
    (self : ProjectionSpineSupport count source target) :
    ProjectionSpineSupport count source
      (VInductDecl.restoreExpr entries recMap target) := by
  induction self with
  | nil => exact .nil _ _
  | @cons count body targetBody name domain binderInfo targetDomain
      skip tail ih =>
    simp only [VInductDecl.restoreExpr]
    exact .cons (fun sourceClosed => (skip sourceClosed).restoreExpr closed) ih

/-- The exact flattened constructor dependency witness retained by nested
staging transports to the literal restored source constructor. -/
theorem VInductDecl.NestedBlockCertificate.restoreProjectionSpineSupport
    {source : VInductDecl} {before after : VEnv}
    (certificate : source.NestedBlockCertificate before after)
    (targetsWF : VInductDecl.NestedTargetsWF before
      certificate.nested.elim.targets)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : VInductDecl.NestedStructureSelection certificate.nested
      familyIndex sourceFamily sourceConstructor)
    (support : ProjectionSpineSupport count hostType
      selection.flatConstructor.type) :
    ProjectionSpineSupport count hostType sourceConstructor.type := by
  have restored := support.restoreExpr
    (recMap := certificate.nested.recMap)
    (certificate.declEntriesClosed targetsWF)
  rw [certificate.restoreSelectedConstructorType selection] at restored
  exact restored

/-- Instantiate a source Pi body without typing the argument when the source
omits that binder and the producer certificate says the target does too.
Inverse weakening supplies the strict translation in the smaller context;
the literal target skip then lowers its definitional equality. -/
theorem TrExprS.instantiate1_skipped
    {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {targetDomain : VExpr} {body : Expr} {targetBody : VExpr}
    (henv : env.WF) (hΔ : Δ.WF env Us.length)
    (targetDomainType : env.IsType Us.length Δ.toCtx targetDomain)
    (translation : TrExprS env Us ((none, .vlam targetDomain) :: Δ)
      body targetBody)
    (sourceClosed : Closed body 0)
    (targetSkip : targetBody.Skips 1 0)
    (sourceArgument : Expr) (targetArgument : VExpr) :
    TrExpr env Us Δ (body.instantiate1' sourceArgument)
      (targetBody.inst targetArgument) := by
  have extendedWF : VLCtx.WF env Us.length
      ((none, .vlam targetDomain) :: Δ) := by
    exact ⟨hΔ, nofun, targetDomainType⟩
  let lift : VLCtx.BVLift Δ ((none, .vlam targetDomain) :: Δ)
      1 0 1 0 := .skip (.vlam targetDomain) .refl
  obtain ⟨baseBody, baseTranslation⟩ :=
    translation.weakBV_inv henv lift (.refl henv extendedWF) sourceClosed
  have weakened := baseTranslation.weakBV henv.ordered lift
  rw [Expr.liftLooseBVars_eq_self sourceClosed.looseBVarRange_le] at weakened
  have targetDef := weakened.uniq henv (.refl henv extendedWF) translation
  obtain ⟨targetBase, targetEq⟩ := VExpr.skips_iff_exists.1 targetSkip
  rw [targetEq] at targetDef ⊢
  have targetDefSmall :=
    (VEnv.IsDefEqU.weakN_iff henv extendedWF.toCtx lift.toCtx).1 targetDef
  rw [Expr.instantiate1_eq_self sourceClosed.looseBVarRange_zero,
    VExpr.inst_liftN]
  exact ⟨baseBody, baseTranslation, targetDefSmall⟩

/-- Definitional-target form of `TrExprS.instantiate1_skipped`.  This is the
form needed after WHNF, where the strict translation is only known equal to
the producer-owned projection cursor. -/
theorem TrExpr.instantiate1_skipped
    {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {targetDomain : VExpr} {body : Expr} {targetBody : VExpr}
    (henv : env.WF) (hΔ : Δ.WF env Us.length)
    (targetDomainType : env.IsType Us.length Δ.toCtx targetDomain)
    (translation : TrExpr env Us ((none, .vlam targetDomain) :: Δ)
      body targetBody)
    (sourceClosed : Closed body 0)
    (targetSkip : targetBody.Skips 1 0)
    (sourceArgument : Expr) (targetArgument : VExpr) :
    TrExpr env Us Δ (body.instantiate1' sourceArgument)
      (targetBody.inst targetArgument) := by
  have extendedWF : VLCtx.WF env Us.length
      ((none, .vlam targetDomain) :: Δ) := by
    exact ⟨hΔ, nofun, targetDomainType⟩
  let lift : VLCtx.BVLift Δ ((none, .vlam targetDomain) :: Δ)
      1 0 1 0 := .skip (.vlam targetDomain) .refl
  obtain ⟨strictBody, strictTranslation, strictDef⟩ := translation
  obtain ⟨baseBody, baseTranslation⟩ :=
    strictTranslation.weakBV_inv henv lift (.refl henv extendedWF) sourceClosed
  have weakened := baseTranslation.weakBV henv.ordered lift
  rw [Expr.liftLooseBVars_eq_self sourceClosed.looseBVarRange_le] at weakened
  have baseDefStrict :=
    weakened.uniq henv (.refl henv extendedWF) strictTranslation
  have baseDefTarget := baseDefStrict.trans henv extendedWF.toCtx strictDef
  obtain ⟨targetBase, targetEq⟩ := VExpr.skips_iff_exists.1 targetSkip
  rw [targetEq] at baseDefTarget ⊢
  have targetDefSmall :=
    (VEnv.IsDefEqU.weakN_iff henv extendedWF.toCtx lift.toCtx).1 baseDefTarget
  rw [Expr.instantiate1_eq_self sourceClosed.looseBVarRange_zero,
    VExpr.inst_liftN]
  exact ⟨baseBody, baseTranslation, targetDefSmall⟩

theorem ProjectionSpineSupport.liftN
    (self : ProjectionSpineSupport count source target) :
    ProjectionSpineSupport count source (target.liftN amount depth) := by
  induction self generalizing depth with
  | nil => exact .nil _ _
  | @cons count body targetBody name domain binderInfo targetDomain
      skip tail ih =>
    simp only [VExpr.liftN]
    exact .cons
      (fun closed => (skip closed).liftN_high (by omega))
      (ih (depth := depth + 1))

/-- Retain only the source prefix demanded by a projection lookup. -/
theorem ProjectionSpineSupport.prefix
    (self : ProjectionSpineSupport count source target)
    (bound : requested ≤ count) :
    ProjectionSpineSupport requested source target := by
  induction requested generalizing count source target with
  | zero => exact .nil _ _
  | succ requested ih =>
      cases self with
      | nil => omega
      | @cons count body targetBody name domain binderInfo targetDomain
          skip tail =>
        exact .cons skip (ih tail (by omega))

/-- Replace the terminal of a skipped Pi telescope by another expression that
skips the corresponding outer range. -/
theorem VExpr.Skips.forallN_retarget
    (self : (VExpr.forallN fields terminal).Skips amount start)
    (terminalSkip : terminal'.Skips amount (start + fields.length)) :
    (VExpr.forallN fields terminal').Skips amount start := by
  induction fields generalizing start with
  | nil => simpa only [VExpr.forallN, List.length_nil, Nat.add_zero] using
      terminalSkip
  | cons field fields ih =>
      have parts := VExpr.skips_iff.mp self
      simp only [VExpr.forallN, VExpr.Skips'] at parts
      have terminalSkip' : terminal'.Skips amount
          (start + 1 + fields.length) := by
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using terminalSkip
      have tail := ih (VExpr.skips_iff.mpr parts.2) terminalSkip'
      apply VExpr.skips_iff.mpr
      simp only [VExpr.forallN, VExpr.Skips']
      exact ⟨parts.1, VExpr.skips_iff.mp tail⟩

/-- A support witness that covers an entire Pi telescope is independent of
its terminal result.  Runtime projection cursors use the producer's semantic
telescope with a closed sort terminal. -/
theorem ProjectionSpineSupport.retargetForallN
    (self : ProjectionSpineSupport fields.length source
      (VExpr.forallN fields terminal)) :
    ProjectionSpineSupport fields.length source
      (VExpr.forallN fields (.sort .zero)) := by
  induction fields generalizing source with
  | nil => exact .nil _ _
  | cons field fields ih =>
      simp only [List.length_cons, VExpr.forallN] at self ⊢
      cases self with
      | @cons _ body targetBody name domain binderInfo targetDomain skip tail =>
          exact .cons
            (fun closed => (skip closed).forallN_retarget (by
              rw [VExpr.skips_iff]
              trivial))
            (ih tail)

theorem ProjectionSpineSupport.instN
    (self : ProjectionSpineSupport count source target) :
    ProjectionSpineSupport count
      (source.instantiate1' sourceArgument depth)
      (target.inst targetArgument depth) := by
  induction self generalizing depth with
  | nil => exact .nil _ _
  | @cons count body targetBody name domain binderInfo targetDomain
      skip tail ih =>
    simp only [Expr.instantiate1', VExpr.inst]
    refine .cons ?_ (ih (depth := depth + 1))
    intro closed
    have originalClosed : body.hasLooseBVar' 0 = false := by
      rw [Expr.hasLooseBVar'_instantiate1_below
        (expression := body) (argument := sourceArgument)
        (depth := depth + 1) (index := 0) (by omega)] at closed
      exact closed
    exact (skip originalClosed).instN_high (by omega)

theorem ProjectionSpineSupport.instL
    (self : ProjectionSpineSupport count source target) :
    ProjectionSpineSupport count
      (source.instantiateLevelParamsCpp parameters sourceLevels)
      (target.instL targetLevels) := by
  induction self with
  | nil => exact .nil _ _
  | @cons count body targetBody name domain binderInfo targetDomain
      skip tail ih =>
    simp only [Expr.instantiateLevelParamsCpp_eq,
      Expr.instantiateLevelParamsCoreCpp', VExpr.instL] at ih ⊢
    exact .cons
      (fun closed => (skip (by
        rw [← Expr.hasLooseBVar'_instantiateLevelParamsCoreCpp'
          (expression := body)]
        exact closed)).instL)
      ih

/-- Turn support for a body in which one binder has been replaced by a fresh
local back into support for the anonymous-binder source. -/
theorem ProjectionSpineSupport.of_instantiateFVar
    (self : ProjectionSpineSupport count
      (source.instantiate1' (.fvar fresh) depth) target) :
    ProjectionSpineSupport count source target := by
  induction count generalizing source target depth with
  | zero => exact .nil _ _
  | succ count ih =>
      cases source with
      | bvar index =>
          simp only [Expr.instantiate1'] at self
          split at self
          · cases self
          · split at self <;> cases self
      | fvar | mvar | sort | const | app | lam | letE | lit | mdata |
          proj =>
          simp only [Expr.instantiate1'] at self
          cases self
      | forallE name domain body binderInfo =>
        simp only [Expr.instantiate1'] at self
        cases self with
        | @cons _ _ targetBody _ _ _ targetDomain skip tail =>
          exact .cons
            (fun closed => skip (by
              rw [Expr.hasLooseBVar'_instantiate1_below
                (expression := body) (argument := .fvar fresh)
                (depth := depth + 1) (index := 0) (by omega)]
              exact closed))
            (ih (depth := depth + 1) tail)

/-- Replacing the terminal result of a skipped constructor telescope by a
closed sort preserves the same strengthening fact. -/
theorem VExpr.Skips.forallN_ctorFields_sort
    {expression : VExpr} {amount start : Nat}
    (self : expression.Skips amount start) :
    (VExpr.forallN (VInductDecl.ctorFields expression)
      (.sort .zero)).Skips amount start := by
  rw [VExpr.skips_iff] at self ⊢
  induction expression generalizing start with
  | bvar | sort | const | app | lam =>
      simp_all [VInductDecl.ctorFields, VExpr.forallN, VExpr.Skips']
  | forallE domain body domainIH bodyIH =>
      simp only [VInductDecl.ctorFields, VExpr.forallN, VExpr.Skips'] at self ⊢
      exact ⟨self.1, bodyIH self.2⟩

/-- A complete source-aligned support witness is insensitive to the
constructor result.  Projection runtime prefixes use the same complete Pi
telescope with a closed sort terminal. -/
theorem ProjectionSpineSupport.forallN_ctorFields_sort
    (self : ProjectionSpineSupport count source target)
    (full : count = (VInductDecl.ctorFields target).length) :
    ProjectionSpineSupport count source
      (VExpr.forallN (VInductDecl.ctorFields target) (.sort .zero)) := by
  induction self with
  | nil => exact .nil _ _
  | @cons count body targetBody name domain binderInfo targetDomain
      skip tail ih =>
    simp only [VInductDecl.ctorFields, List.length_cons,
      Nat.add_left_inj] at full
    simp only [VInductDecl.ctorFields, VExpr.forallN]
    exact .cons
      (fun closed => (skip closed).forallN_ctorFields_sort)
      (ih full)

/-- Instantiate a block constructor support witness while exposing the exact
parameter/field split retained by the selected normalized constructor. -/
theorem ProjectionSpineSupport.blockSemanticInstL
    {selected : VBlockStructureView} {source : Expr}
    {parameters : List Name} {sourceLevels : List Level}
    {targetLevels : List VLevel}
    (support : ProjectionSpineSupport
      (selected.nparams + selected.fields.length)
      source selected.constructor.raw.type) :
    ProjectionSpineSupport
      (selected.nparams + selected.fields.length)
      (source.instantiateLevelParamsCpp parameters sourceLevels)
      (VExpr.forallN
        (selected.constructorParams.map (VExpr.instL targetLevels))
        (VExpr.forallN
          (selected.fields.map (VExpr.instL targetLevels))
          ((selected.constructor.rawResult selected.nparams).instL
            targetLevels))) := by
  have instantiated := support.instL
    (parameters := parameters) (sourceLevels := sourceLevels)
    (targetLevels := targetLevels)
  rw [selected.constructor.rawType_eq] at instantiated
  simpa [VBlockStructureView.constructorParams,
    VBlockStructureView.fields,
    VInductDecl.NormalizedCtor.declaredBinders,
    VExpr.instL_forallN, VExpr.forallN_append,
    List.map_append] using instantiated

/-- Replace a block constructor's terminal result by a closed sort before
universe instantiation.  This is the common source for the major-local and
canonical-constructor runtime cursors. -/
theorem ProjectionSpineSupport.blockRuntimeInstL
    {selected : VBlockStructureView} {source : Expr}
    {parameters : List Name} {sourceLevels : List Level}
    {targetLevels : List VLevel}
    (support : ProjectionSpineSupport
      (selected.nparams + selected.fields.length)
      source selected.constructor.raw.type) :
    ProjectionSpineSupport
      (selected.nparams + selected.fields.length)
      (source.instantiateLevelParamsCpp parameters sourceLevels)
      (VExpr.forallN
        (selected.constructorParams.map (VExpr.instL targetLevels) ++
          selected.fields.map (VExpr.instL targetLevels))
        (.sort .zero)) := by
  have sorted := support.forallN_ctorFields_sort
    (VProjectionView.constructorSpine_length (.block selected))
  have instantiated := sorted.instL
    (parameters := parameters) (sourceLevels := sourceLevels)
    (targetLevels := targetLevels)
  simp only [VExpr.instL_forallN, VExpr.instL] at instantiated
  have fieldsEq : VInductDecl.ctorFields selected.constructor.raw.type =
      selected.constructorParams ++ selected.fields := by
    simpa [VProjectionView.constructor, VProjectionView.constructorParams,
      VProjectionView.fields, VProjectionView.nparams,
      VProjectionView.source, VBlockStructureView.constructorParams,
      VBlockStructureView.fields] using
        VProjectionView.constructorFields_eq (.block selected)
  rw [fieldsEq, List.map_append] at instantiated
  simpa [VBlockStructureView.constructorParams,
    VBlockStructureView.fields,
    VInductDecl.NormalizedCtor.declaredBinders,
    VExpr.instL_forallN, VExpr.forallN_append,
    List.map_append, VLevel.inst] using instantiated

/-- Projection dependency support split at the exact parameter/field
boundary.  Parameter binders retain only common Pi shape: projection
inference consumes their actual arguments through the ordinary typed spine.
The field suffix retains `ProjectionSpineSupport`, because runtime-generated
projector arguments may be omitted precisely when the remaining host body is
independent of that field. -/
inductive ProjectionFieldSpineSupport : Nat → Nat → Expr → VExpr → Prop where
  | fields (support : ProjectionSpineSupport fieldCount source target) :
      ProjectionFieldSpineSupport 0 fieldCount source target
  | param
      (tail : ProjectionFieldSpineSupport parameterCount fieldCount
        body targetBody) :
      ProjectionFieldSpineSupport (parameterCount + 1) fieldCount
        (.forallE name domain body binderInfo)
        (.forallE targetDomain targetBody)

/-- A positive retained parameter count exposes a host Pi at the source. -/
theorem ProjectionFieldSpineSupport.source_isForall
    (self : ProjectionFieldSpineSupport parameterCount fieldCount
      source target)
    (positive : parameterCount ≠ 0) : source.isForall = true := by
  cases self with
  | fields => exact (positive rfl).elim
  | param => rfl

/-- A traditional full-spine witness in particular supplies the split
parameter/field contract. -/
theorem ProjectionSpineSupport.toFieldSpineSupport
    (self : ProjectionSpineSupport (parameterCount + fieldCount)
      source target) :
    ProjectionFieldSpineSupport parameterCount fieldCount source target := by
  induction parameterCount generalizing source target with
  | zero =>
      simpa only [Nat.zero_add] using
        (ProjectionFieldSpineSupport.fields self)
  | succ parameterCount ih =>
      have self' : ProjectionSpineSupport
          (parameterCount + fieldCount + 1) source target := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using self
      cases self' with
      | @cons _ body targetBody name domain binderInfo targetDomain
          skip tail =>
        exact .param (ih tail)

/-- Simultaneous source/target instantiation preserves the split boundary. -/
theorem ProjectionFieldSpineSupport.instN
    (self : ProjectionFieldSpineSupport parameterCount fieldCount
      source target) :
    ProjectionFieldSpineSupport parameterCount fieldCount
      (source.instantiate1' sourceArgument depth)
      (target.inst targetArgument depth) := by
  induction self generalizing depth with
  | fields support => exact .fields support.instN
  | @param parameterCount fieldCount body targetBody name domain
      binderInfo targetDomain tail ih =>
    simp only [Expr.instantiate1', VExpr.inst]
    exact .param (ih (depth := depth + 1))

/-- Universe instantiation preserves the exact parameter/field boundary. -/
theorem ProjectionFieldSpineSupport.instL
    (self : ProjectionFieldSpineSupport parameterCount fieldCount
      source target) :
    ProjectionFieldSpineSupport parameterCount fieldCount
      (source.instantiateLevelParamsCpp parameters sourceLevels)
      (target.instL targetLevels) := by
  induction self with
  | fields support => exact .fields support.instL
  | @param parameterCount fieldCount body targetBody name domain
      binderInfo targetDomain tail ih =>
    simp only [Expr.instantiateLevelParamsCpp_eq,
      Expr.instantiateLevelParamsCoreCpp', VExpr.instL] at ih ⊢
    exact .param ih

/-- Consuming one typed parameter exposes the same split contract on the
instantiated tails. -/
theorem ProjectionFieldSpineSupport.consume
    (self : ProjectionFieldSpineSupport (parameterCount + 1) fieldCount
      (.forallE name domain body binderInfo)
      (.forallE targetDomain targetBody)) :
    ProjectionFieldSpineSupport parameterCount fieldCount
      (body.instantiate1' sourceArgument)
      (targetBody.inst targetArgument) := by
  cases self with
  | param tail =>
      simpa only [Expr.instantiate1_eq] using
        (tail.instN (sourceArgument := sourceArgument)
          (targetArgument := targetArgument) (depth := 0))

/-- Source-only transport for a dependency spine.  The two telescopes have
the same Pi shape; at each binder the new source may be less dependent only
when the old source was already independent.  This is precisely the
reflection direction required to reuse a producer-owned target skip. -/
inductive ProjectionSpineSourceTransport : Nat → Expr → Expr → Prop where
  | nil (source restored : Expr) :
      ProjectionSpineSourceTransport 0 source restored
  | cons
      (reflect : restoredBody.hasLooseBVar' 0 = false →
        sourceBody.hasLooseBVar' 0 = false)
      (tail : ProjectionSpineSourceTransport count sourceBody restoredBody) :
      ProjectionSpineSourceTransport (count + 1)
        (.forallE sourceName sourceDomain sourceBody sourceBinderInfo)
        (.forallE restoredName restoredDomain restoredBody restoredBinderInfo)

/-- Simultaneously abstracting one FVar preserves source dependency
transport.  At every transported binder the abstraction depth is positive in
its body, so the binder's own loose variable remains index zero. -/
theorem ProjectionSpineSourceTransport.abstract1
    (self : ProjectionSpineSourceTransport count source restored)
    (id : FVarId) (depth : Nat := 0) :
    ProjectionSpineSourceTransport count
      (source.abstract1 id depth) (restored.abstract1 id depth) := by
  induction self generalizing depth with
  | nil => exact .nil _ _
  | @cons count sourceBody restoredBody sourceName sourceDomain
      sourceBinderInfo restoredName restoredDomain restoredBinderInfo
      reflect tail ih =>
      simp only [Expr.abstract1]
      refine ProjectionSpineSourceTransport.cons ?_ ?_
      · intro closed
        have restoredIndex :
            (restoredBody.abstract1 id (depth + 1)).hasLooseBVar' 0 =
              restoredBody.hasLooseBVar' 0 := by
          simpa using Expr.abstract1_hasLooseBVar id restoredBody
            (depth + 1) 0
        have sourceIndex :
            (sourceBody.abstract1 id (depth + 1)).hasLooseBVar' 0 =
              sourceBody.hasLooseBVar' 0 := by
          simpa using Expr.abstract1_hasLooseBVar id sourceBody
            (depth + 1) 0
        rw [restoredIndex] at closed
        rw [sourceIndex]
        exact reflect closed
      · exact ih (depth + 1)

/-- Reuse an exact target dependency spine after a source-only telescope
transport. -/
theorem ProjectionSpineSupport.transportSource
    (self : ProjectionSpineSupport count source target)
    (transport : ProjectionSpineSourceTransport count source restored) :
    ProjectionSpineSupport count restored target := by
  induction self generalizing restored with
  | nil => exact .nil _ _
  | @cons count sourceBody targetBody sourceName sourceDomain
      sourceBinderInfo targetDomain skip tail ih =>
    cases transport with
    | cons reflect transportTail =>
      exact .cons (fun closed => skip (reflect closed)) (ih transportTail)

/-- Source transport split at the constructor parameter/field boundary.
Parameter binders require only common Pi shape.  The field suffix carries the
dependency-reflection relation consumed by sparse projection inference. -/
inductive ProjectionFieldSourceTransport : Nat → Nat → Expr → Expr → Prop where
  | fields
      (transport : ProjectionSpineSourceTransport fieldCount source restored) :
      ProjectionFieldSourceTransport 0 fieldCount source restored
  | param
      (tail : ProjectionFieldSourceTransport parameterCount fieldCount
        sourceBody restoredBody) :
      ProjectionFieldSourceTransport (parameterCount + 1) fieldCount
        (.forallE sourceName sourceDomain sourceBody sourceBinderInfo)
        (.forallE restoredName restoredDomain restoredBody restoredBinderInfo)

/-- Simultaneous FVar abstraction preserves the parameter/field split. -/
theorem ProjectionFieldSourceTransport.abstract1
    (self : ProjectionFieldSourceTransport parameterCount fieldCount
      source restored)
    (id : FVarId) (depth : Nat := 0) :
    ProjectionFieldSourceTransport parameterCount fieldCount
      (source.abstract1 id depth) (restored.abstract1 id depth) := by
  induction self generalizing depth with
  | fields transport => exact .fields (transport.abstract1 id depth)
  | param tail ih =>
      simp only [Expr.abstract1]
      exact .param (ih (depth + 1))

/-- Transport a split projection witness to a new host source without
changing its exact Theory target. -/
theorem ProjectionFieldSpineSupport.transportSource
    (self : ProjectionFieldSpineSupport parameterCount fieldCount
      source target)
    (transport : ProjectionFieldSourceTransport parameterCount fieldCount
      source restored) :
    ProjectionFieldSpineSupport parameterCount fieldCount restored target := by
  induction self generalizing restored with
  | fields support =>
      cases transport with
      | fields sourceTransport =>
          exact .fields (support.transportSource sourceTransport)
  | @param parameterCount fieldCount sourceBody targetBody sourceName
      sourceDomain sourceBinderInfo targetDomain tail ih =>
      cases transport with
      | param transportTail =>
          exact .param (ih transportTail)

/-- Persistent all-projector typing for projection backends whose complete
program family is admissible. -/
structure ProjectionDensePrograms (view : VProjectionView)
    (venv : VEnv) : Prop where
  programsWF : view.ProgramsWF venv
  programsWF_mono : ∀ {venv' : VEnv}, venv ≤ venv' →
    view.ProgramsWF venv'

theorem ProjectionDensePrograms.mono
    {view : VProjectionView} {venv venv' : VEnv}
    (self : ProjectionDensePrograms view venv) (hle : venv ≤ venv') :
    ProjectionDensePrograms view venv' where
  programsWF := self.programsWF_mono hle
  programsWF_mono hle' := self.programsWF_mono (hle.trans hle')

/-- Honest projection-program support.  Singleton and fully admissible block
views retain the traditional dense contract.  A recursive block-backed host
family may instead construct only the source-ordered programs actually
demanded by projection inference; its checked layout supplies that runtime
construction. -/
inductive ProjectionProgramSupport (info : InductiveVal)
    (constructorInfo : ConstructorVal)
    (view : VProjectionView) (venv : VEnv) : Prop where
  | dense (programs : ProjectionDensePrograms view venv)
  | runtimeBlock (selected : VBlockStructureView)
      (view_eq : view = .block selected)
      (spineSupport : ProjectionSpineSupport
        (selected.nparams + selected.fields.length)
        constructorInfo.type
        selected.constructor.raw.type)

theorem ProjectionProgramSupport.mono
    {info : InductiveVal} {view : VProjectionView} {venv venv' : VEnv}
    {constructorInfo : ConstructorVal}
    (self : ProjectionProgramSupport info constructorInfo view venv)
    (hle : venv ≤ venv') :
    ProjectionProgramSupport info constructorInfo view venv' := by
  cases self with
  | dense programs => exact .dense (programs.mono hle)
  | runtimeBlock selected view_eq spineSupport =>
      exact .runtimeBlock selected view_eq spineSupport

/-- Exact alignment between one host structure record and the registered
Theory artifact used to interpret primitive projections.  The positional
metadata is retained explicitly because ordinary constant translation checks
types but does not identify the kernel's parameter/constructor roles. -/
structure ProjectionArtifact (env : Environment) (name : Name)
    (info : InductiveVal) (venv : VEnv) where
  view : VProjectionView
  name_eq : view.name = name
  viewWF : view.LayoutWF venv
  constructorInfo : ConstructorVal
  constructor_find : env.find? view.constructorName =
    some (.ctorInfo constructorInfo)
  recursorInfo : RecursorVal
  recursor_find : env.find? view.recursorName =
    some (.recInfo recursorInfo)
  recursor_levelParams_length : recursorInfo.levelParams.length = view.recUvars
  constructor_numParams_eq : constructorInfo.numParams = view.nparams
  constructor_numFields_eq : constructorInfo.numFields = view.fields.length
  levelParams_length : info.levelParams.length = view.uvars
  numParams_eq : info.numParams = view.nparams
  numIndices_eq : info.numIndices = 0
  ctors_eq : info.ctors = [view.constructorName]
  programs : ProjectionProgramSupport info constructorInfo view venv

/-- Exact host/Theory metadata alignment for a restored nested structure,
before choosing an operational projector backend.  This is deliberately a
separate handoff from `ProjectionArtifact`: the restored source constructor
is registered at the public endpoint, while its projector implementation is
owned by the paired flattened block and must be transported rather than
re-presented as an ordinary block view. -/
structure RestoredProjectionArtifactLayout (env : Environment) (name : Name)
    (info : InductiveVal) (venv : VEnv) where
  view : VRestoredBlockStructureView
  name_eq : view.name = name
  viewWF : view.FamilyLayoutWF venv
  constructorInfo : ConstructorVal
  constructor_find : env.find? view.constructorName =
    some (.ctorInfo constructorInfo)
  recursorInfo : RecursorVal
  recursor_find : env.find? view.recursorName =
    some (.recInfo recursorInfo)
  recursor_levelParams_length :
    recursorInfo.levelParams.length = view.nested.generation.recUvars
  constructor_numParams_eq : constructorInfo.numParams = view.nparams
  constructor_numFields_eq : constructorInfo.numFields = view.fields.length
  levelParams_length : info.levelParams.length = view.uvars
  numParams_eq : info.numParams = view.nparams
  numIndices_eq : info.numIndices = 0
  ctors_eq : info.ctors = [view.constructorName]

/-- Persistent typing for the complete restored operational projector
inventory.  As for ordinary dense programs, monotonicity is retained as an
explicit producer fact because `OperationalProgramsWF` quantifies over
contexts and spines in the target environment and is not covariant by a
simple weakening argument. -/
structure RestoredProjectionDensePrograms
    (view : VRestoredBlockStructureView) (venv : VEnv) : Prop where
  programsWF : view.OperationalProgramsWF venv
  programsWF_mono : ∀ {venv' : VEnv}, venv ≤ venv' →
    view.OperationalProgramsWF venv'

theorem RestoredProjectionDensePrograms.mono
    {view : VRestoredBlockStructureView} {venv venv' : VEnv}
    (self : RestoredProjectionDensePrograms view venv)
    (hle : venv ≤ venv') :
    RestoredProjectionDensePrograms view venv' where
  programsWF := self.programsWF_mono hle
  programsWF_mono hle' := self.programsWF_mono (hle.trans hle')

/-- Honest operational support for a restored nested projector backend.
The dense case owns typing for every restored program.  The runtime case
retains the exact parameter/field split: parameters are consumed by their
typed spine, while only field binders carry the syntactic dependency witness
needed by sparse runtime projection.  The view's
`ConstructorParameterLayoutWF` remains a separate artifact field: it is
needed to type those restored prefixes and cannot be inferred from this pure
dependency witness. -/
inductive RestoredProjectionProgramSupport (info : InductiveVal)
    (constructorInfo : ConstructorVal)
    (view : VRestoredBlockStructureView) (venv : VEnv) : Prop where
  | dense (programs : RestoredProjectionDensePrograms view venv)
  | runtime
      (spineSupport : ProjectionFieldSpineSupport
        view.nparams view.fields.length
        constructorInfo.type view.sourceConstructor.type)

theorem RestoredProjectionProgramSupport.mono
    {info : InductiveVal} {constructorInfo : ConstructorVal}
    {view : VRestoredBlockStructureView} {venv venv' : VEnv}
    (self : RestoredProjectionProgramSupport info constructorInfo view venv)
    (hle : venv ≤ venv') :
    RestoredProjectionProgramSupport info constructorInfo view venv' := by
  cases self with
  | dense programs => exact .dense (programs.mono hle)
  | runtime spineSupport => exact .runtime spineSupport

/-- Complete restored projection artifact at the public nested endpoint.
This remains distinct from `ProjectionArtifact`: its registered constructor
is the restored source constructor, and its operational programs are restored
payloads of the paired mutual recursor rather than programs of an ordinary
`VProjectionView.block` registered at this endpoint. -/
structure RestoredProjectionArtifact (env : Environment) (name : Name)
    (info : InductiveVal) (venv : VEnv)
    extends RestoredProjectionArtifactLayout env name info venv where
  /-- The transaction-owned restoration inventory is closed.  Restored
  projector code uses this fact to commute ambient lifting and
  instantiation through `restoreRecAt`; it must not be reconstructed by a
  projection consumer from the final environment. -/
  recEntriesClosed :
    VInductDecl.RestoreEntriesClosed view.nested.recEntries
  /-- Weakening and substitution laws retained from the exact flattened
  generation transaction.  They are syntax facts and therefore survive
  even though the flat registration environment is not the public restored
  endpoint. -/
  codeNaturality : view.flatView.OperationalCodeNaturality
  parameterLayout : view.ConstructorParameterLayoutWF venv
  programs : RestoredProjectionProgramSupport info constructorInfo view venv
  /-- The producer retains the exact future-model reconstruction contract
  needed by persistent structure-eta registration.  Keeping it on the
  artifact prevents registration consumers from re-entering weakening
  inversion merely to recover a fact already established by the restored
  projector producer. -/
  largeRebuilds : view.elimination = .large →
    ∀ {venv' : VEnv}, venv ≤ venv' → venv'.ConversionRegular →
      view.OperationalRebuildWF venv'

def RestoredProjectionArtifact.mono
    {env : Environment} {name : Name} {info : InductiveVal}
    {venv venv' : VEnv}
    (self : RestoredProjectionArtifact env name info venv)
    (hle : venv ≤ venv') :
    RestoredProjectionArtifact env name info venv' where
  view := self.view
  name_eq := self.name_eq
  viewWF := self.viewWF.mono hle
  constructorInfo := self.constructorInfo
  constructor_find := self.constructor_find
  recursorInfo := self.recursorInfo
  recursor_find := self.recursor_find
  recursor_levelParams_length := self.recursor_levelParams_length
  constructor_numParams_eq := self.constructor_numParams_eq
  constructor_numFields_eq := self.constructor_numFields_eq
  levelParams_length := self.levelParams_length
  numParams_eq := self.numParams_eq
  numIndices_eq := self.numIndices_eq
  ctors_eq := self.ctors_eq
  recEntriesClosed := self.recEntriesClosed
  codeNaturality := self.codeNaturality
  parameterLayout := self.parameterLayout.mono hle
  programs := self.programs.mono hle
  largeRebuilds large {_venv''} hle' hregular :=
    self.largeRebuilds large (hle.trans hle') hregular

/-- Migration boundary for projection consumers which can resolve either an
ordinary registered view or the separately registered restored nested
backend.  `ProjectionReady` continues to expose ordinary artifacts until its
inference and eta consumers acquire an explicit restored branch. -/
inductive ProjectionArtifactResolution (env : Environment) (name : Name)
    (info : InductiveVal) (venv : VEnv) where
  | ordinary (artifact : ProjectionArtifact env name info venv)
  | restored (artifact : RestoredProjectionArtifact env name info venv)

/-- Host/Theory coherence needed by primitive projections.

Inference obtains one complete registered artifact from ready family
metadata. Reduction additionally requires every host `ctorInfo` head to come
from a completed Theory inductive transaction, and relies on the positional
host fact that a constructor's cached `numParams` agrees with the registered
Theory view. Ordinary constant translation checks the constructor type but
establishes neither declaration kind nor which leading binders the host
metadata classifies as parameters. -/
structure ProjectionReady (env : Environment) (venv : VEnv) : Prop where
  infer : ∀ name info, env.find? name = some (.inductInfo info) →
    env.isProjectionReadyStructure name = true →
    Nonempty (ProjectionArtifact env name info venv)
  /-- Constructor provenance retains the host's cached parameter count at
  the completed Theory transaction which installed the head.  Projection
  head inversion, rather than an open-world readiness premise, aligns this
  count with the particular typed structure view selected by reduction.
  Ordinary translated constants and definition aliases remain excluded. -/
  constructorHead : ∀ name info,
    env.find? name = some (.ctorInfo info) →
    venv.ConstructorHeadArity name info.numParams

/-- Resolution-aware projection readiness.  This is the migration contract
for inference and reduction: existing environments can embed their ordinary
artifacts, while exact nested transactions may return the separately typed
restored backend at their public endpoint. -/
structure ProjectionResolutionReady (env : Environment) (venv : VEnv) : Prop where
  infer : ∀ name info, env.find? name = some (.inductInfo info) →
    env.isProjectionReadyStructure name = true →
    Nonempty (ProjectionArtifactResolution env name info venv)
  constructorHead : ∀ name info,
    env.find? name = some (.ctorInfo info) →
    venv.ConstructorHeadArity name info.numParams

/-- Data-bearing companion to `ProjectionResolutionReady.infer`.

`ProjectionResolutionReady` is deliberately a proposition because the type
checker consumes projection artifacts only while proving soundness.  Clients
which construct persistent data, such as the structure-eta rule inventory,
must instead receive an owner which retains the selected resolution in
`Type`.  Separating these interfaces prevents such clients from having to
recover data from `Nonempty` with `Classical.choice`. -/
structure ProjectionArtifactResolver (env : Environment) (venv : VEnv) where
  infer : ∀ name info, env.find? name = some (.inductInfo info) →
    env.isProjectionReadyStructure name = true →
    ProjectionArtifactResolution env name info venv

/-- Data-bearing projection resolution restricted to one finite family-name
inventory.  Registration builders only inspect names in their scan domain, so
an exact declaration producer need not reconstruct artifacts for unrelated
families inherited propositionally from the input environment. -/
structure ProjectionArtifactInventoryResolver (env : Environment) (venv : VEnv)
    (familyNames : List Name) where
  infer : ∀ name, name ∈ familyNames → ∀ info,
    env.find? name = some (.inductInfo info) →
    env.isProjectionReadyStructure name = true →
    ProjectionArtifactResolution env name info venv

/-- Restrict a global retained resolver to a finite scan inventory. -/
def ProjectionArtifactResolver.toInventory
    (self : ProjectionArtifactResolver env venv) (familyNames : List Name) :
    ProjectionArtifactInventoryResolver env venv familyNames where
  infer name _member info found ready := self.infer name info found ready

/-- A retained resolver and constructor-head provenance imply the existing
proof-only readiness interface without any choice. -/
theorem ProjectionArtifactResolver.toResolutionReady
    (self : ProjectionArtifactResolver env venv)
    (constructorHead : ∀ name info,
      env.find? name = some (.ctorInfo info) →
      venv.ConstructorHeadArity name info.numParams) :
    ProjectionResolutionReady env venv where
  infer name info found ready := ⟨self.infer name info found ready⟩
  constructorHead := constructorHead

/-- Every ordinary readiness package is resolution-aware by selecting its
ordinary branch. -/
theorem ProjectionReady.toResolution
    (self : ProjectionReady env venv) :
    ProjectionResolutionReady env venv where
  infer name info found ready := by
    obtain ⟨artifact⟩ := self.infer name info found ready
    exact ⟨.ordinary artifact⟩
  constructorHead := self.constructorHead

/-- Projection artifacts required only for host families whose complete
projection-ready observation was not already available in the input host
environment.  Exact inductive transactions retarget the old case and derive
constructor-head provenance independently, so their semantic producer needs
to construct precisely this delta rather than a whole `ProjectionReady`
package. -/
def ProjectionArtifactDeltaReady (before after : Environment)
    (venv : VEnv) : Prop :=
  ∀ name info, after.find? name = some (.inductInfo info) →
    after.isProjectionReadyStructure name = true →
    ¬ (before.find? name = some (.inductInfo info) ∧
      before.isProjectionReadyStructure name = true) →
    Nonempty (ProjectionArtifact after name info venv)

/-- Restored artifacts required only for host families newly activated by a
nested transaction.  This contract parallels `ProjectionArtifactDeltaReady`
without conflating the public restored constructor with an ordinary block
view. -/
def RestoredProjectionArtifactDeltaReady (before after : Environment)
    (venv : VEnv) : Prop :=
  ∀ name info, after.find? name = some (.inductInfo info) →
    after.isProjectionReadyStructure name = true →
    ¬ (before.find? name = some (.inductInfo info) ∧
      before.isProjectionReadyStructure name = true) →
    Nonempty (RestoredProjectionArtifact after name info venv)

/-- Migration delta accepted by consumers which can interpret either the
ordinary block artifact or the restored nested backend. -/
def ProjectionArtifactResolutionDeltaReady (before after : Environment)
    (venv : VEnv) : Prop :=
  ∀ name info, after.find? name = some (.inductInfo info) →
    after.isProjectionReadyStructure name = true →
    ¬ (before.find? name = some (.inductInfo info) ∧
      before.isProjectionReadyStructure name = true) →
    Nonempty (ProjectionArtifactResolution after name info venv)

theorem ProjectionArtifactDeltaReady.toResolution
    {before after : Environment} {venv : VEnv}
    (self : ProjectionArtifactDeltaReady before after venv) :
    ProjectionArtifactResolutionDeltaReady before after venv := by
  intro name info found ready notOld
  obtain ⟨artifact⟩ := self name info found ready notOld
  exact ⟨.ordinary artifact⟩

theorem RestoredProjectionArtifactDeltaReady.toResolution
    {before after : Environment} {venv : VEnv}
    (self : RestoredProjectionArtifactDeltaReady before after venv) :
    ProjectionArtifactResolutionDeltaReady before after venv := by
  intro name info found ready notOld
  obtain ⟨artifact⟩ := self name info found ready notOld
  exact ⟨.restored artifact⟩

/-- Exact host/Theory alignment for one constructor/family pair accepted by
the runtime structure-eta heuristics.  The underlying projection artifact
supplies the registered Theory view and its typed projector programs; the two
equalities identify that artifact with the precise host constructor lookup
which triggered the heuristic. -/
structure StructureEtaArtifact (env : Environment) (familyName : Name)
    (familyInfo : InductiveVal) (constructorName : Name)
    (constructorInfo : ConstructorVal) (venv : VEnv) where
  projection : ProjectionArtifact env familyName familyInfo venv
  constructor_name_eq : projection.view.constructorName = constructorName
  constructor_info_eq : projection.constructorInfo = constructorInfo
  /-- The host large-recursor gate is aligned with the exact Theory backend.
  It is the environment-free admissibility fact used to regenerate projector
  typing in the current well-formed model. -/
  large : projection.view.elimination = .large
  /-- The ordered registry proof fixes the exact descriptor generated from
  the checked view.  It contains no equality oracle: the associated full
  subject-reduction package is recovered from the consumer's `VEnv.WF`
  history. -/
  etaOrdered : venv.Ordered
  etaRegistered : venv.structEtas
    (projection.viewWF.toStructEta etaOrdered)

/-- Structure-eta registration backed by the restored operational projector
inventory of a nested family.  This is intentionally parallel to
`StructureEtaArtifact`: the public constructor and family are restored,
while the registered rule uses the exact restored operational programs. -/
structure RestoredStructureEtaArtifact (env : Environment)
    (familyName : Name) (familyInfo : InductiveVal)
    (constructorName : Name) (constructorInfo : ConstructorVal)
    (venv : VEnv) where
  projection : RestoredProjectionArtifact env familyName familyInfo venv
  constructor_name_eq : projection.view.constructorName = constructorName
  constructor_info_eq : projection.constructorInfo = constructorInfo
  large : projection.view.elimination = .large
  etaOrdered : venv.Ordered
  etaRegistered : venv.structEtas
    (projection.parameterLayout.toStructEta projection.codeNaturality
      projection.recEntriesClosed)

/-- A resolved structure-eta artifact preserves the concrete projection
backend used by the checker. -/
inductive StructureEtaArtifactResolution (env : Environment)
    (familyName : Name) (familyInfo : InductiveVal)
    (constructorName : Name) (constructorInfo : ConstructorVal)
    (venv : VEnv) : Prop where
  | ordinary (artifact : StructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv)
  | restored (artifact : RestoredStructureEtaArtifact env familyName
      familyInfo constructorName constructorInfo venv)

/-- Host-metadata coherence required whenever the executable checker accepts
a family/constructor pair as a nonrecursive structure.  This deliberately
contains no Theory equality: `VEnv.HasStructureEta` is the separate semantic
capability consumed by the verification theorem. -/
structure StructureEtaReady (env : Environment) (venv : VEnv) : Prop where
  resolve : ∀ familyName familyInfo constructorName constructorInfo,
    env.find? familyName = some (.inductInfo familyInfo) →
    env.find? constructorName = some (.ctorInfo constructorInfo) →
    env.isStructureEtaReadyConstructor familyName constructorName = true →
    Nonempty (StructureEtaArtifactResolution env familyName familyInfo
      constructorName constructorInfo venv)

/-- Resolve the family artifact named by a constructor lookup after the
runtime nonrecursive-structure test has succeeded. -/
theorem StructureEtaReady.resolveConstructor
    (self : StructureEtaReady env venv)
    (hctor : env.find? constructorName = some (.ctorInfo constructorInfo))
    (hstructure : env.isStructureEtaReadyConstructor constructorInfo.induct
      constructorName = true) :
    ∃ familyInfo,
      env.find? constructorInfo.induct = some (.inductInfo familyInfo) ∧
      Nonempty (StructureEtaArtifactResolution env constructorInfo.induct
        familyInfo constructorName constructorInfo venv) := by
  have hshape :=
    Kernel.Environment.isStructureEtaReadyConstructor_isNonRec hstructure
  unfold Kernel.Environment.isNonRecStructureConstructor at hshape
  generalize hfamily : env.find? constructorInfo.induct = found at hshape
  cases found with
  | none => simp at hshape
  | some info => cases info with
    | inductInfo familyInfo =>
      exact ⟨familyInfo, rfl,
        self.resolve _ _ _ _ hfamily hctor hstructure⟩
    | axiomInfo _ => simp at hshape
    | defnInfo _ => simp at hshape
    | thmInfo _ => simp at hshape
    | opaqueInfo _ => simp at hshape
    | quotInfo _ => simp at hshape
    | ctorInfo _ => simp at hshape
    | recInfo _ => simp at hshape

/-- Consume the exact registered descriptor retained by a resolved host
structure artifact.  Reconstruction typing comes from the registry's
`VStructEta.WF` certificate; the equality is precisely the primitive Theory
rule. -/
theorem StructureEtaArtifact.eta
    (self : StructureEtaArtifact env familyName familyInfo constructorName
      constructorInfo venv)
    (henv : venv.WF)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {major : VExpr}
    (hΓ : OnCtx Γ (venv.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = self.projection.view.uvars)
    (hparamsLength : params.length = self.projection.view.nparams)
    (hparamsSpine : ∃ resultLevel,
      venv.SpineWF U Γ
        (self.projection.view.familyType.instL levels)
        params (.sort resultLevel))
    (hmajor : venv.HasType U Γ major
      (self.projection.view.structureType levels params)) :
    venv.IsDefEq U Γ
      (self.projection.view.etaRebuild levels params major) major
      (self.projection.view.structureType levels params) := by
  let rule := self.projection.viewWF.toStructEta self.etaOrdered
  have hruleWF : rule.WF venv :=
    henv.structEtaWF self.etaRegistered
  obtain ⟨resultLevel, hparamsSpine⟩ := hparamsSpine
  have hrebuild := hruleWF.rebuild_hasType VEnv.LE.rfl
    henv.conversionRegular hΓ hlevels
    hlevelsLength hparamsLength ⟨resultLevel, hparamsSpine⟩ hmajor
  have heta := VEnv.IsDefEq.structEta self.etaRegistered hlevels
    hlevelsLength hparamsLength hparamsSpine hmajor hrebuild
  simpa [rule] using heta

/-- Consume the registered restored descriptor.  As in the ordinary branch,
reconstruction typing comes from the persistent registry certificate and the
equality itself is the primitive Theory rule. -/
theorem RestoredStructureEtaArtifact.eta
    (self : RestoredStructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv)
    (henv : venv.WF)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {major : VExpr}
    (hΓ : OnCtx Γ (venv.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = self.projection.view.uvars)
    (hparamsLength : params.length = self.projection.view.nparams)
    (hparamsSpine : ∃ resultLevel,
      venv.SpineWF U Γ
        (self.projection.view.familyType.instL levels)
        params (.sort resultLevel))
    (hmajor : venv.HasType U Γ major
      (self.projection.view.structureType levels params)) :
    venv.IsDefEq U Γ
      (self.projection.view.operationalEtaRebuild levels params major) major
      (self.projection.view.structureType levels params) := by
  let rule := self.projection.parameterLayout.toStructEta
    self.projection.codeNaturality self.projection.recEntriesClosed
  have hruleWF : rule.WF venv :=
    henv.structEtaWF self.etaRegistered
  obtain ⟨resultLevel, hparamsSpine⟩ := hparamsSpine
  have hrebuild := hruleWF.rebuild_hasType VEnv.LE.rfl
    henv.conversionRegular hΓ hlevels hlevelsLength hparamsLength
      ⟨resultLevel, hparamsSpine⟩ hmajor
  have heta := VEnv.IsDefEq.structEta self.etaRegistered hlevels
    hlevelsLength hparamsLength hparamsSpine hmajor hrebuild
  simpa [rule] using heta

/-- Environments which contain no constructor metadata satisfy projection
readiness vacuously.  This is the common staging case for validation fixtures:
families may already be present, but their constructors have not been
installed yet. -/
theorem ProjectionReady.of_no_ctorInfo
    (hnoCtor : ∀ name info,
      env.find? name ≠ some (.ctorInfo info)) :
    ProjectionReady env venv where
  infer name _info hfind hready := by
    have hfalse :=
      Kernel.Environment.isProjectionReadyStructure_false_of_no_ctorInfo
        hfind hnoCtor
    rw [hfalse] at hready
    contradiction
  constructorHead name info hfind := (hnoCtor name info hfind).elim

/-- The same constructor-free staging environments satisfy the
resolution-aware readiness contract vacuously. -/
theorem ProjectionResolutionReady.of_no_ctorInfo
    (hnoCtor : ∀ name info,
      env.find? name ≠ some (.ctorInfo info)) :
    ProjectionResolutionReady env venv :=
  (ProjectionReady.of_no_ctorInfo hnoCtor).toResolution

/-- Environments with no constructor metadata also satisfy structure-eta
readiness vacuously. -/
theorem StructureEtaReady.of_no_ctorInfo
    (hnoCtor : ∀ name info,
      env.find? name ≠ some (.ctorInfo info)) :
    StructureEtaReady env venv where
  resolve _ _ constructorName constructorInfo _ hctor _ :=
    (hnoCtor constructorName constructorInfo hctor).elim

/-- A convenient negative readiness witness for staging/indexed environments
where the host recognizes no eta-eligible structure family. -/
theorem StructureEtaReady.of_no_nonRecStructure
    (hnone : ∀ name, env.isNonRecStructure name = false) :
    StructureEtaReady env venv where
  resolve familyName _ constructorName _ _ _ hstructure := by
    have heta :=
      Kernel.Environment.isStructureEtaReadyConstructor_isNonRec hstructure
    have hnonrec :=
      Kernel.Environment.isNonRecStructureConstructor_isNonRecStructure
        (constructor := constructorName) heta
    rw [hnone familyName] at hnonrec
    contradiction

/-- The empty operational projection prefix is always available. -/
theorem VBlockStructureView.OperationalRuntimePrefix.zero
    (view : VBlockStructureView) (env : VEnv) (U : Nat)
    (context : List VExpr) (levels : List VLevel) (params : List VExpr) :
    view.OperationalRuntimePrefix env U context levels params 0 := by
  refine ⟨⟨_, .nil⟩, ⟨_, .nil, .nil _⟩⟩

/-- The restored runtime backend starts from the same two empty sparse
traces.  This fact is independent of program typing and therefore needs no
additional restoration premise. -/
theorem VRestoredBlockStructureView.OperationalRuntimePrefix.zero
    (view : VRestoredBlockStructureView) (env : VEnv) (U : Nat)
    (context : List VExpr) (levels : List VLevel) (params : List VExpr) :
    view.OperationalRuntimePrefix env U context levels params 0 := by
  refine ⟨⟨_, .nil⟩, ⟨_, .nil, .nil _⟩⟩

/-- The selected constructor fully applied to its fields has the lifted
structure type in the canonical field context. -/
theorem VBlockStructureView.LayoutWF.projectionConstructorApp_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.WF)
    {U : Nat} {context : List VExpr} (hcontext :
      OnCtx context (env.IsType U))
    {levels : List VLevel} (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel)) :
    let fields := view.specializedFields levels params
    env.HasType U (fields.reverse ++ context)
      (view.projectionConstructorApp levels params fields)
      ((view.structureType levels params).liftN fields.length) := by
  let fields := view.specializedFields levels params
  let count := fields.length
  have hconstructorPrefix := self.constructorPrefix_hasType henv.ordered
    levels hlevels hlevelsLength params hparamsLength hparamsSpine
  have hconstructorPrefixWeak := hconstructorPrefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := count) (Γ := context) fields.reverse
      (h := by simp [count]))
  have hconstructorPrefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ context)
      ((VExpr.appN (.const view.constructorName levels) params).liftN count)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN count)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [fields, count] using hconstructorPrefixWeak
  have hmajor := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levels params).liftN count)
    (Δ := []) (Γ := context)
    (f := (VExpr.appN (.const view.constructorName levels) params).liftN count)
    hconstructorPrefixSelf
  simpa [fields, count, VBlockStructureView.projectionConstructorApp,
    VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
    Function.comp_def] using hmajor

theorem VExpr.bvarRevRange_succ (offset count : Nat) :
    VExpr.bvarRevRange offset (count + 1) =
      VExpr.bvarRevRange (offset + 1) count ++ [.bvar offset] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [VExpr.bvarRevRange, List.cons_append, List.cons.injEq]
      exact ⟨by simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm], ih⟩

theorem VExpr.bvarRevRange_succ_of_lt
    {limit total : Nat} (bound : limit < total) :
    VExpr.bvarRevRange (total - (limit + 1)) (limit + 1) =
      VExpr.bvarRevRange (total - limit) limit ++
        [.bvar (total - 1 - limit)] := by
  rw [VExpr.bvarRevRange_succ]
  have offsetSucc : total - (limit + 1) + 1 = total - limit := by omega
  have offsetEq : total - (limit + 1) = total - 1 - limit := by omega
  rw [offsetSucc, offsetEq]

/-- A typed operational motive computes to the exact next field domain. -/
theorem VBlockStructureView.operationalField_hasType_of_typeFn
    {view : VBlockStructureView} {env : VEnv}
    (henv : env.ConversionRegular)
    {U : Nat} {context : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hcontext : OnCtx context (env.IsType U))
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code)
    (htypeFn : env.HasType U context code.typeFn
      (.forallE (view.structureType levels params) (.sort code.fieldSort)))
    {major : VExpr}
    (hmajor : env.HasType U context major
      (view.structureType levels params)) :
    ∃ field,
      (view.specializedFields levels params)[idx]? = some field ∧
      env.HasType U context
        (field.instRevAt
          (view.operationalProjectionArgs levels params idx major) 0)
        (.sort code.fieldSort) := by
  obtain ⟨field, typeBody, hfield, htypeFnShape, htypeBody⟩ :=
    view.operationalProjectionCodes_get?_typeFn_beta levels params hcode major
  have happ : env.HasType U context (.app code.typeFn major)
      (.sort code.fieldSort) := by
    simpa only [VExpr.inst] using htypeFn.app hmajor
  rw [htypeFnShape] at happ
  obtain ⟨A, B, hlam, harg⟩ := happ.app_inv henv.ordered hcontext
  obtain ⟨⟨_, hstructType⟩, _, hbodyType⟩ :=
    hlam.lam_inv henv.ordered hcontext
  have hfunTypeEq := henv.hasType_uniqU hcontext hlam
    (hstructType.lam hbodyType)
  obtain ⟨⟨_, hdomainEq⟩, _⟩ := henv.forallE_inv hcontext hfunTypeEq
  have harg' := henv.hasType_defeqU_r hcontext ⟨_, hdomainEq⟩ harg
  have hbeta := VEnv.IsDefEq.beta hbodyType harg'
  have htypeEq := henv.hasType_uniqU hcontext hbeta.hasType.1 happ
  have hout := henv.hasType_defeqU_r hcontext htypeEq hbeta.hasType.2
  rw [htypeBody] at hout
  exact ⟨field, hfield, hout⟩

/-- A typed restored operational motive computes to the exact next source
field domain.  Restoration closure supplies the syntactic beta shape; the
typing argument is otherwise backend-independent. -/
theorem VRestoredBlockStructureView.operationalField_hasType_of_typeFn
    {view : VRestoredBlockStructureView} {env : VEnv}
    (layout : view.LayoutWF env) (henv : env.ConversionRegular)
    (closed : VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr} {levels : List VLevel}
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hcontext : OnCtx context (env.IsType U))
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code)
    (htypeFn : env.HasType U context code.typeFn
      (.forallE (view.structureType levels params) (.sort code.fieldSort)))
    {major : VExpr}
    (hmajor : env.HasType U context major
      (view.structureType levels params)) :
    ∃ field,
      (view.specializedFields levels params)[idx]? = some field ∧
      env.HasType U context
        (field.instRevAt
          (view.operationalProjectionArgs levels params idx major) 0)
        (.sort code.fieldSort) := by
  obtain ⟨field, domain, typeBody, hfield, htypeFnShape, htypeBody⟩ :=
    layout.operationalProjectionCodes_get?_typeFn_beta henv.ordered closed
      levels hlevelsLength params hcode major
  have happ : env.HasType U context (.app code.typeFn major)
      (.sort code.fieldSort) := by
    simpa only [VExpr.inst] using htypeFn.app hmajor
  rw [htypeFnShape] at happ
  obtain ⟨A, B, hlam, harg⟩ := happ.app_inv henv.ordered hcontext
  obtain ⟨⟨_, hstructType⟩, _, hbodyType⟩ :=
    hlam.lam_inv henv.ordered hcontext
  have hfunTypeEq := henv.hasType_uniqU hcontext hlam
    (hstructType.lam hbodyType)
  obtain ⟨⟨_, hdomainEq⟩, _⟩ := henv.forallE_inv hcontext hfunTypeEq
  have harg' := henv.hasType_defeqU_r hcontext ⟨_, hdomainEq⟩ harg
  have hbeta := VEnv.IsDefEq.beta hbodyType harg'
  have htypeEq := henv.hasType_uniqU hcontext hbeta.hasType.1 happ
  have hout := henv.hasType_defeqU_r hcontext htypeEq hbeta.hasType.2
  rw [htypeBody] at hout
  exact ⟨field, hfield, hout⟩

/-- Extend both runtime sparse traces after the checker has constructed and
typed the next operational projector. -/
theorem VBlockStructureView.OperationalRuntimePrefix.snocTyped
    {view : VBlockStructureView} {env : VEnv}
    {U : Nat} {context : List VExpr} {levels : List VLevel}
    {params : List VExpr} {limit : Nat}
    (runtime : view.OperationalRuntimePrefix env U context levels params limit)
    (layout : view.LayoutWF env) (henv : env.WF)
    (hcontext : OnCtx context (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel))
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[limit]? =
      some code)
    (hprojector : env.HasType U context code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))) :
    view.OperationalRuntimePrefix env U context levels params (limit + 1) := by
  obtain ⟨⟨majorCursor, majorSparse⟩,
    ⟨constructorCursor, constructorSparse, constructorPointwise⟩⟩ := runtime
  let fields := view.specializedFields levels params
  let fieldCount := fields.length
  have hlimit : limit < fields.length := by
    simpa [fields] using (List.getElem?_eq_some_iff.1 hcode).1

  let paramsLift := params.map (VExpr.liftN 1)
  have hparamsLiftLength : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hstructureLift : view.structureType levels paramsLift =
      (view.structureType levels params).liftN 1 0 := by
    simpa [paramsLift] using
      (view.structureType_liftN levels params 1 0).symm
  have hcodesLift := layout.operationalProjectionCodes_liftN
    levels params hparamsLength 1 0
  have hcodeLift :
      (view.operationalProjectionCodes levels paramsLift)[limit]? =
        some (code.liftN 1 0) := by
    rw [← hcodesLift, List.getElem?_map, hcode]
    rfl
  have hprojectorWeak := hprojector.weakN henv.ordered
    (Ctx.LiftN.one (A := view.structureType levels params))
  have hprojectorLift : env.HasType U
      (view.structureType levels params :: context)
      (code.liftN 1 0).projector
      (.forallE (view.structureType levels paramsLift)
        (.app (code.liftN 1 0).typeFn.lift (.bvar 0))) := by
    simpa [VStructureView.ProjectionCode.liftN, hstructureLift,
      VExpr.liftN, VExpr.liftN_lift_projection] using hprojectorWeak
  have hmajorLocal : env.HasType U
      (view.structureType levels params :: context) (.bvar 0)
      (view.structureType levels paramsLift) := by
    rw [hstructureLift]
    exact .bvar .zero
  have hstructureIsType : env.IsType U context
      (view.structureType levels params) := by
    obtain ⟨resultLevel, hparams⟩ := hparamsSpine
    have hfamily : env.HasType U context (.const view.name levels)
        (view.familyType.instL levels) := by
      exact layout.familyConst_hasType henv.ordered levels hlevels
        hlevelsLength
    exact ⟨resultLevel, hparams.hasType_appN hfamily⟩
  have hmajorContext : OnCtx
      (view.structureType levels params :: context) (env.IsType U) := by
    simp only [OnCtx]
    exact ⟨hcontext, hstructureIsType⟩
  obtain ⟨majorField, majorTypeBody, hmajorField, hmajorTypeFn,
      hmajorArgument⟩ :=
    operationalProjector_hasType_field_of_type henv.conversionRegular
      hmajorContext hcodeLift hprojectorLift hmajorLocal
  have hmajorConsume := majorSparse.consumeForalls_eq
  have hmajorArgsLength :
      (view.operationalProjectionArgs levels paramsLift limit (.bvar 0)).length =
        limit :=
    view.operationalProjectionArgs_length levels paramsLift limit (.bvar 0)
      (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hcodeLift).1)
  obtain ⟨majorField', majorBody, hmajorField', hmajorConsumeDomain⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (view.specializedFields levels paramsLift) (.sort .zero)
      (view.operationalProjectionArgs levels paramsLift limit (.bvar 0))
      (by
        have := (List.getElem?_eq_some_iff.1 hcodeLift).1
        simpa [hmajorArgsLength] using this)
  have hmajorFieldEq : majorField' = majorField :=
    Option.some.inj (hmajorField'.symm.trans (by
      simpa [hmajorArgsLength] using hmajorField))
  subst majorField'
  have hmajorCursor : majorCursor = .forallE
      (majorField.instRevAt
        (view.operationalProjectionArgs levels paramsLift limit (.bvar 0)) 0)
      majorBody :=
    Option.some.inj (hmajorConsume.symm.trans hmajorConsumeDomain)
  subst majorCursor
  let majorSparse' := majorSparse.snocTyped hmajorArgument

  let paramsFullLift := params.map (VExpr.liftN fieldCount)
  have hparamsFullLiftLength : paramsFullLift.length = view.nparams := by
    simpa [paramsFullLift] using hparamsLength
  have hstructureFullLift : view.structureType levels paramsFullLift =
      (view.structureType levels params).liftN fieldCount 0 := by
    simpa [paramsFullLift] using
      (view.structureType_liftN levels params fieldCount 0).symm
  have hcodesFullLift := layout.operationalProjectionCodes_liftN
    levels params hparamsLength fieldCount 0
  have hcodeFullLift :
      (view.operationalProjectionCodes levels paramsFullLift)[limit]? =
        some (code.liftN fieldCount 0) := by
    rw [← hcodesFullLift, List.getElem?_map, hcode]
    rfl
  have hprojectorFullWeak := hprojector.weakN henv.ordered
    (Ctx.LiftN.zero (n := fieldCount) (Γ := context) fields.reverse
      (h := by simp [fieldCount]))
  have hprojectorFullLift : env.HasType U (fields.reverse ++ context)
      (code.liftN fieldCount 0).projector
      (.forallE (view.structureType levels paramsFullLift)
        (.app (code.liftN fieldCount 0).typeFn.lift (.bvar 0))) := by
    simpa [VStructureView.ProjectionCode.liftN, hstructureFullLift,
      VExpr.liftN, VExpr.liftN_lift_projection] using hprojectorFullWeak
  have hconstructorMajor₀ := layout.projectionConstructorApp_hasType henv
    hcontext hlevels hlevelsLength hparamsLength hparamsSpine
  have hconstructorMajor : env.HasType U (fields.reverse ++ context)
      (view.projectionConstructorApp levels params fields)
      (view.structureType levels paramsFullLift) := by
    rw [hstructureFullLift]
    exact hconstructorMajor₀
  obtain ⟨constructorField, constructorTypeBody, hconstructorField,
      hconstructorTypeFn, hconstructorArgument⟩ :=
    operationalProjector_hasType_field_of_type henv.conversionRegular
      (by
        have hsortTel := layout.specializedFields_onSortTel henv.ordered
          levels hlevels hlevelsLength params hparamsLength hparamsSpine
        exact hsortTel.toOnTel.toOnCtx hcontext)
      hcodeFullLift hprojectorFullLift hconstructorMajor
  have hspecializedFullLift :
      view.specializedFields levels paramsFullLift =
        VExpr.liftTelN fieldCount fields 0 := by
    simpa [paramsFullLift, fields] using
      layout.specializedFields_liftN levels params hparamsLength fieldCount 0
  have hconstructorArgs :
      view.operationalProjectionArgs levels paramsFullLift limit
          (view.projectionConstructorApp levels params fields) =
        ((view.operationalProjectionCodes levels params).take limit).map
          fun prior => .app (prior.projector.liftN fieldCount)
            (view.projectionConstructorApp levels params fields) := by
    unfold VBlockStructureView.operationalProjectionArgs
    rw [← hcodesFullLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  have hconstructorConsume := constructorSparse.consumeForalls_eq
  have hconstructorArgsLength :
      (((view.operationalProjectionCodes levels params).take limit).map
        fun prior => VExpr.app (prior.projector.liftN fieldCount)
          (view.projectionConstructorApp levels params fields)).length = limit := by
    rw [List.length_map, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (by simpa [fields] using hlimit))]
  obtain ⟨constructorField', constructorBody, hconstructorField',
      hconstructorConsumeDomain⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (VExpr.liftTelN fieldCount fields 0) (.sort .zero)
      (((view.operationalProjectionCodes levels params).take limit).map
        fun prior => .app (prior.projector.liftN fieldCount)
          (view.projectionConstructorApp levels params fields))
      (by
        rw [hconstructorArgsLength, VExpr.liftTelN_length]
        exact hlimit)
  have hconstructorFieldEq : constructorField' = constructorField := by
    have hconstructorFieldAt :
        (VExpr.liftTelN fieldCount fields 0)[limit]? =
          some constructorField := by
      rw [← hspecializedFullLift]
      exact hconstructorField
    rw [hconstructorArgsLength] at hconstructorField'
    exact Option.some.inj (hconstructorField'.symm.trans hconstructorFieldAt)
  subst constructorField'
  have hconstructorCursor : constructorCursor = .forallE
      (constructorField.instRevAt
        (((view.operationalProjectionCodes levels params).take limit).map
          fun prior => .app (prior.projector.liftN fieldCount)
            (view.projectionConstructorApp levels params fields)) 0)
      constructorBody :=
    Option.some.inj
      (hconstructorConsume.symm.trans hconstructorConsumeDomain)
  subst constructorCursor
  rw [hconstructorArgs] at hconstructorArgument
  let constructorSparse' := constructorSparse.snocTyped hconstructorArgument
  have hconstructorExact :=
    layout.operationalProjector_constructor_exact_of_program
      henv.conversionRegular hcontext hlevels hlevelsLength hparamsLength
      hparamsSpine hcode hprojector
  have constructorPointwise' := constructorPointwise.snocTyped
    hconstructorArgument hconstructorExact

  let majorCursor' := majorBody.inst
    ((code.liftN 1 0).projector.app (.bvar 0))
  have majorSparseFinal : env.SparseSpineWF U
      (view.structureType levels params :: context)
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero))
      (view.operationalProjectionArgs levels
        (params.map (VExpr.liftN 1)) (limit + 1) (.bvar 0)) majorCursor' := by
    rw [view.operationalProjectionArgs_succ levels paramsLift limit
      (.bvar 0) hcodeLift]
    exact majorSparse'
  refine ⟨⟨majorCursor', majorSparseFinal⟩, ?_⟩
  unfold VBlockStructureView.OperationalSparseConstructorPrefix
  simp only [List.take_add_one, hcode, Option.toList_some,
    List.map_append, List.map_singleton]
  rw [VExpr.bvarRevRange_succ_of_lt hlimit]
  exact ⟨_, constructorSparse', constructorPointwise'⟩

/-- Extend both runtime sparse traces when the next source binder is
syntactically irrelevant in both projection cursors.  No projector typing is
needed at a skipped position. -/
theorem VBlockStructureView.OperationalRuntimePrefix.snocSkip
    {view : VBlockStructureView} {env : VEnv}
    {U : Nat} {context : List VExpr} {levels : List VLevel}
    {params : List VExpr} {limit : Nat}
    (runtime : view.OperationalRuntimePrefix env U context levels params limit)
    (layout : view.LayoutWF env)
    (hparamsLength : params.length = view.nparams)
    {majorDomain majorBody constructorDomain constructorBody : VExpr}
    (hmajorConsume :
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero)).consumeForalls?
          (view.operationalProjectionArgs levels
            (params.map (VExpr.liftN 1)) limit (.bvar 0)) =
        some (.forallE majorDomain majorBody))
    (hmajorSkip : majorBody.Skips 1 0)
    (hconstructorConsume :
      let fields := view.specializedFields levels params
      let fieldCount := fields.length
      (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
        (.sort .zero)).consumeForalls?
          (((view.operationalProjectionCodes levels params).take limit).map
            fun prior => .app (prior.projector.liftN fieldCount)
              (view.projectionConstructorApp levels params fields)) =
        some (.forallE constructorDomain constructorBody))
    (hconstructorSkip : constructorBody.Skips 1 0)
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[limit]? =
      some code) :
    view.OperationalRuntimePrefix env U context levels params (limit + 1) := by
  obtain ⟨⟨majorCursor, majorSparse⟩,
    ⟨constructorCursor, constructorSparse, constructorPointwise⟩⟩ := runtime
  let fields := view.specializedFields levels params
  let fieldCount := fields.length
  have hlimit : limit < fields.length := by
    simpa [fields] using (List.getElem?_eq_some_iff.1 hcode).1

  let paramsLift := params.map (VExpr.liftN 1)
  have hcodesLift := layout.operationalProjectionCodes_liftN
    levels params hparamsLength 1 0
  have hcodeLift :
      (view.operationalProjectionCodes levels paramsLift)[limit]? =
        some (code.liftN 1 0) := by
    rw [← hcodesLift, List.getElem?_map, hcode]
    rfl
  have hmajorCursor : majorCursor = .forallE majorDomain majorBody :=
    Option.some.inj (majorSparse.consumeForalls_eq.symm.trans hmajorConsume)
  subst majorCursor
  let majorArgument :=
    (code.liftN 1 0).projector.app (.bvar 0)
  let majorSparse' := majorSparse.snocSkip
    (argument := majorArgument) hmajorSkip
  let majorCursor' := majorBody.inst majorArgument
  have majorSparseFinal : env.SparseSpineWF U
      (view.structureType levels params :: context)
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero))
      (view.operationalProjectionArgs levels
        (params.map (VExpr.liftN 1)) (limit + 1) (.bvar 0)) majorCursor' := by
    rw [view.operationalProjectionArgs_succ levels paramsLift limit
      (.bvar 0) hcodeLift]
    exact majorSparse'

  let paramsFullLift := params.map (VExpr.liftN fieldCount)
  have hcodesFullLift := layout.operationalProjectionCodes_liftN
    levels params hparamsLength fieldCount 0
  have hcodeFullLift :
      (view.operationalProjectionCodes levels paramsFullLift)[limit]? =
        some (code.liftN fieldCount 0) := by
    rw [← hcodesFullLift, List.getElem?_map, hcode]
    rfl
  have hconstructorArgs :
      view.operationalProjectionArgs levels paramsFullLift limit
          (view.projectionConstructorApp levels params fields) =
        ((view.operationalProjectionCodes levels params).take limit).map
          fun prior => .app (prior.projector.liftN fieldCount)
            (view.projectionConstructorApp levels params fields) := by
    unfold VBlockStructureView.operationalProjectionArgs
    rw [← hcodesFullLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  have hconstructorCursor : constructorCursor =
      .forallE constructorDomain constructorBody := by
    exact Option.some.inj
      (constructorSparse.consumeForalls_eq.symm.trans hconstructorConsume)
  subst constructorCursor
  let constructorArgument :=
    (code.liftN fieldCount 0).projector.app
      (view.projectionConstructorApp levels params fields)
  let constructorSparse' := constructorSparse.snocSkip
    (argument := constructorArgument) hconstructorSkip
  have constructorPointwise' := constructorPointwise.snocSkip
    (argument := constructorArgument)
    (right := .bvar (fieldCount - 1 - limit)) hconstructorSkip

  refine ⟨⟨majorCursor', majorSparseFinal⟩, ?_⟩
  unfold VBlockStructureView.OperationalSparseConstructorPrefix
  simp only [List.take_add_one, hcode, Option.toList_some,
    List.map_append, List.map_singleton]
  rw [VExpr.bvarRevRange_succ_of_lt hlimit]
  exact ⟨_, constructorSparse', constructorPointwise'⟩

/-- Extend both runtime sparse traces after the checker has constructed and
typed the next operational projector. -/
theorem VRestoredBlockStructureView.OperationalRuntimePrefix.snocTyped
    {view : VRestoredBlockStructureView} {env : VEnv}
    {U : Nat} {context : List VExpr} {levels : List VLevel}
    {params : List VExpr} {limit : Nat}
    (runtime : view.OperationalRuntimePrefix env U context levels params limit)
    (layout : view.ConstructorParameterLayoutWF env)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (recEntriesClosed :
      VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (henv : env.ConversionRegular)
    (hcontext : OnCtx context (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel))
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[limit]? =
      some code)
    (hprojector : env.HasType U context code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))) :
    view.OperationalRuntimePrefix env U context levels params (limit + 1) := by
  obtain ⟨⟨majorCursor, majorSparse⟩,
    ⟨constructorCursor, constructorSparse, constructorPointwise⟩⟩ := runtime
  let fields := view.specializedFields levels params
  let fieldCount := fields.length
  have hlimit : limit < fields.length := by
    simpa [fields] using (List.getElem?_eq_some_iff.1 hcode).1

  let paramsLift := params.map (VExpr.liftN 1)
  have hparamsLiftLength : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hstructureLift : view.structureType levels paramsLift =
      (view.structureType levels params).liftN 1 0 := by
    simpa [paramsLift] using
      (view.structureType_liftN levels params 1 0).symm
  have hcodesLift := view.operationalProjectionCodes_liftN codeNaturality recEntriesClosed
    levels params hparamsLength 1 0
  have hcodeLift :
      (view.operationalProjectionCodes levels paramsLift)[limit]? =
        some (code.liftN 1 0) := by
    rw [← hcodesLift, List.getElem?_map, hcode]
    rfl
  have hprojectorWeak := hprojector.weakN henv.ordered
    (Ctx.LiftN.one (A := view.structureType levels params))
  have hprojectorLift : env.HasType U
      (view.structureType levels params :: context)
      (code.liftN 1 0).projector
      (.forallE (view.structureType levels paramsLift)
        (.app (code.liftN 1 0).typeFn.lift (.bvar 0))) := by
    simpa [VStructureView.ProjectionCode.liftN, hstructureLift,
      VExpr.liftN, VExpr.liftN_lift_projection] using hprojectorWeak
  have hmajorLocal : env.HasType U
      (view.structureType levels params :: context) (.bvar 0)
      (view.structureType levels paramsLift) := by
    rw [hstructureLift]
    exact .bvar .zero
  have hstructureIsType : env.IsType U context
      (view.structureType levels params) := by
    obtain ⟨resultLevel, hparams⟩ := hparamsSpine
    have hfamily : env.HasType U context (.const view.name levels)
        (view.familyType.instL levels) := by
      exact layout.familyConst_hasType henv.ordered levels hlevels
        hlevelsLength
    exact ⟨resultLevel, hparams.hasType_appN hfamily⟩
  have hmajorContext : OnCtx
      (view.structureType levels params :: context) (env.IsType U) := by
    simp only [OnCtx]
    exact ⟨hcontext, hstructureIsType⟩
  obtain ⟨majorField, majorDomain, majorTypeBody, hmajorField,
      hmajorTypeFn, hmajorArgument⟩ :=
    layout.toLayoutWF.operationalProjector_hasType_field_of_type
      henv recEntriesClosed hlevelsLength
      hmajorContext hcodeLift hprojectorLift hmajorLocal
  have hmajorConsume := majorSparse.consumeForalls_eq
  have hmajorArgsLength :
      (view.operationalProjectionArgs levels paramsLift limit (.bvar 0)).length =
        limit :=
    view.operationalProjectionArgs_length levels paramsLift limit (.bvar 0)
      (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hcodeLift).1)
  obtain ⟨majorField', majorBody, hmajorField', hmajorConsumeDomain⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (view.specializedFields levels paramsLift) (.sort .zero)
      (view.operationalProjectionArgs levels paramsLift limit (.bvar 0))
      (by
        have := (List.getElem?_eq_some_iff.1 hcodeLift).1
        simpa [hmajorArgsLength] using this)
  have hmajorFieldEq : majorField' = majorField :=
    Option.some.inj (hmajorField'.symm.trans (by
      simpa [hmajorArgsLength] using hmajorField))
  subst majorField'
  have hmajorCursor : majorCursor = .forallE
      (majorField.instRevAt
        (view.operationalProjectionArgs levels paramsLift limit (.bvar 0)) 0)
      majorBody :=
    Option.some.inj (hmajorConsume.symm.trans hmajorConsumeDomain)
  subst majorCursor
  let majorSparse' := majorSparse.snocTyped hmajorArgument

  let paramsFullLift := params.map (VExpr.liftN fieldCount)
  have hparamsFullLiftLength : paramsFullLift.length = view.nparams := by
    simpa [paramsFullLift] using hparamsLength
  have hstructureFullLift : view.structureType levels paramsFullLift =
      (view.structureType levels params).liftN fieldCount 0 := by
    simpa [paramsFullLift] using
      (view.structureType_liftN levels params fieldCount 0).symm
  have hcodesFullLift := view.operationalProjectionCodes_liftN codeNaturality recEntriesClosed
    levels params hparamsLength fieldCount 0
  have hcodeFullLift :
      (view.operationalProjectionCodes levels paramsFullLift)[limit]? =
        some (code.liftN fieldCount 0) := by
    rw [← hcodesFullLift, List.getElem?_map, hcode]
    rfl
  have hprojectorFullWeak := hprojector.weakN henv.ordered
    (Ctx.LiftN.zero (n := fieldCount) (Γ := context) fields.reverse
      (h := by simp [fieldCount]))
  have hprojectorFullLift : env.HasType U (fields.reverse ++ context)
      (code.liftN fieldCount 0).projector
      (.forallE (view.structureType levels paramsFullLift)
        (.app (code.liftN fieldCount 0).typeFn.lift (.bvar 0))) := by
    simpa [VStructureView.ProjectionCode.liftN, hstructureFullLift,
      VExpr.liftN, VExpr.liftN_lift_projection] using hprojectorFullWeak
  have hconstructorMajor₀ := layout.projectionConstructorApp_hasType henv
    recEntriesClosed hcontext hlevels hlevelsLength hparamsLength
      hparamsSpine
  have hconstructorMajor : env.HasType U (fields.reverse ++ context)
      (view.projectionConstructorApp levels params fields)
      (view.structureType levels paramsFullLift) := by
    rw [hstructureFullLift]
    exact hconstructorMajor₀
  obtain ⟨constructorField, constructorDomain, constructorTypeBody,
      hconstructorField, hconstructorTypeFn, hconstructorArgument⟩ :=
    layout.toLayoutWF.operationalProjector_hasType_field_of_type
      henv recEntriesClosed hlevelsLength
      (by
        have hsortTel := layout.specializedFields_onSortTel henv.ordered
          levels hlevels hlevelsLength params hparamsLength hparamsSpine
        exact hsortTel.toOnTel.toOnCtx hcontext)
      hcodeFullLift hprojectorFullLift hconstructorMajor
  have hspecializedFullLift :
      view.specializedFields levels paramsFullLift =
        VExpr.liftTelN fieldCount fields 0 := by
    simpa [paramsFullLift, fields] using
      layout.toLayoutWF.specializedFields_liftN henv.ordered levels params
        hparamsLength fieldCount 0
  have hconstructorArgs :
      view.operationalProjectionArgs levels paramsFullLift limit
          (view.projectionConstructorApp levels params fields) =
        ((view.operationalProjectionCodes levels params).take limit).map
          fun prior => .app (prior.projector.liftN fieldCount)
            (view.projectionConstructorApp levels params fields) := by
    unfold VRestoredBlockStructureView.operationalProjectionArgs
    rw [← hcodesFullLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  have hconstructorConsume := constructorSparse.consumeForalls_eq
  have hconstructorArgsLength :
      (((view.operationalProjectionCodes levels params).take limit).map
        fun prior => VExpr.app (prior.projector.liftN fieldCount)
          (view.projectionConstructorApp levels params fields)).length = limit := by
    rw [List.length_map, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (by simpa [fields] using hlimit))]
  obtain ⟨constructorField', constructorBody, hconstructorField',
      hconstructorConsumeDomain⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (VExpr.liftTelN fieldCount fields 0) (.sort .zero)
      (((view.operationalProjectionCodes levels params).take limit).map
        fun prior => .app (prior.projector.liftN fieldCount)
          (view.projectionConstructorApp levels params fields))
      (by
        rw [hconstructorArgsLength, VExpr.liftTelN_length]
        exact hlimit)
  have hconstructorFieldEq : constructorField' = constructorField := by
    have hconstructorFieldAt :
        (VExpr.liftTelN fieldCount fields 0)[limit]? =
          some constructorField := by
      rw [← hspecializedFullLift]
      exact hconstructorField
    rw [hconstructorArgsLength] at hconstructorField'
    exact Option.some.inj (hconstructorField'.symm.trans hconstructorFieldAt)
  subst constructorField'
  have hconstructorCursor : constructorCursor = .forallE
      (constructorField.instRevAt
        (((view.operationalProjectionCodes levels params).take limit).map
          fun prior => .app (prior.projector.liftN fieldCount)
            (view.projectionConstructorApp levels params fields)) 0)
      constructorBody :=
    Option.some.inj
      (hconstructorConsume.symm.trans hconstructorConsumeDomain)
  subst constructorCursor
  rw [hconstructorArgs] at hconstructorArgument
  let constructorSparse' := constructorSparse.snocTyped hconstructorArgument
  have hconstructorExact :=
    layout.operationalProjector_constructor_exact_of_program henv
      recEntriesClosed codeNaturality hcontext hlevels hlevelsLength
      hparamsLength hparamsSpine hcode hprojector
  have constructorPointwise' := constructorPointwise.snocTyped
    hconstructorArgument hconstructorExact

  let majorCursor' := majorBody.inst
    ((code.liftN 1 0).projector.app (.bvar 0))
  have majorSparseFinal : env.SparseSpineWF U
      (view.structureType levels params :: context)
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero))
      (view.operationalProjectionArgs levels
        (params.map (VExpr.liftN 1)) (limit + 1) (.bvar 0)) majorCursor' := by
    rw [view.operationalProjectionArgs_succ levels paramsLift limit
      (.bvar 0) hcodeLift]
    exact majorSparse'
  refine ⟨⟨majorCursor', majorSparseFinal⟩, ?_⟩
  unfold VRestoredBlockStructureView.OperationalSparseConstructorPrefix
  simp only [List.take_add_one, hcode, Option.toList_some,
    List.map_append, List.map_singleton]
  rw [VExpr.bvarRevRange_succ_of_lt hlimit]
  exact ⟨_, constructorSparse', constructorPointwise'⟩

/-- Universal restored elimination admissibility constructs every
operational projector in source order.  Each successor is typed from the
runtime traces for the preceding projectors, then extends those traces using
the projector's exact constructor computation. -/
theorem VRestoredBlockStructureView.ConstructorParameterLayoutWF.operationalProgramsWF_of_admissible
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env)
    (henv : env.ConversionRegular)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (admissible : view.OperationalMotiveAdmissible) :
    view.OperationalProgramsWF env := by
  intro U context levels params index code hcontext hlevels
    hlevelsLength hparamsLength hparamsSpine hcode
  have runtimePrefix : ∀ limit,
      limit ≤ (view.operationalProjectionCodes levels params).length →
      view.OperationalRuntimePrefix env U context levels params limit := by
    intro limit hlimit
    induction limit with
    | zero =>
        exact VRestoredBlockStructureView.OperationalRuntimePrefix.zero
          view env U context levels params
    | succ limit ih =>
        have hcodeIdx : limit <
            (view.operationalProjectionCodes levels params).length := by
          omega
        let nextCode :=
          (view.operationalProjectionCodes levels params)[limit]
        have hnextCode :
            (view.operationalProjectionCodes levels params)[limit]? =
              some nextCode :=
          List.getElem?_eq_getElem hcodeIdx
        have runtime := ih (Nat.le_of_lt hcodeIdx)
        have hnextProjector :=
          self.operationalProjector_hasType_of_runtimePrefix henv
            codeNaturality closed runtime hcontext hlevels hlevelsLength
              hparamsLength hparamsSpine hnextCode
                (admissible hnextCode)
        exact runtime.snocTyped self codeNaturality closed henv hcontext
          hlevels hlevelsLength hparamsLength hparamsSpine hnextCode
            hnextProjector
  have hindexBound : index <
      (view.operationalProjectionCodes levels params).length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  have runtime := runtimePrefix index (Nat.le_of_lt hindexBound)
  exact self.operationalProjector_hasType_of_runtimePrefix henv
    codeNaturality closed runtime hcontext hlevels hlevelsLength
      hparamsLength hparamsSpine hcode (admissible hcode)

/-- The host large-elimination gate makes every restored operational motive
admissible, so an exact restored layout constructs the complete projector
inventory even when runtime projection inference used its sparse backend. -/
theorem VRestoredBlockStructureView.ConstructorParameterLayoutWF.operationalProgramsWF_of_large
    {view : VRestoredBlockStructureView} {venv : VEnv}
    (self : view.ConstructorParameterLayoutWF venv)
    (henv : venv.ConversionRegular)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (recEntriesClosed :
      VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (large : view.elimination = .large) :
    view.OperationalProgramsWF venv := by
  apply self.operationalProgramsWF_of_admissible henv codeNaturality
    recEntriesClosed
  intro levels params index code _found
  exact view.motiveLevel_projectionLevels_of_large large code.fieldSort levels

/-- Restored generation establishes the persistent reconstruction contract
once at the producer boundary.  Later registration consumers project this
field instead of replaying the weakening-inversion argument. -/
theorem VRestoredBlockStructureView.ConstructorParameterLayoutWF.largeRebuilds
    {view : VRestoredBlockStructureView} {venv : VEnv}
    (self : view.ConstructorParameterLayoutWF venv)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (recEntriesClosed :
      VInductDecl.RestoreEntriesClosed view.nested.recEntries) :
    view.elimination = .large →
      ∀ {venv' : VEnv}, venv ≤ venv' → venv'.ConversionRegular →
        view.OperationalRebuildWF venv' := by
  intro large venv' hle hregular
  let layout := self.mono hle
  intro U context levels params major hcontext hlevels hlevelsLength
    hparamsLength hparamsSpine hmajor
  exact (layout.toOperationalRebuildWF_of_programs hregular recEntriesClosed
    (layout.operationalProgramsWF_of_large hregular codeNaturality
      recEntriesClosed large)) hcontext hlevels hlevelsLength hparamsLength
        hparamsSpine hmajor

/-- A restored artifact exposes the complete large-elimination projector
inventory in its current model. -/
theorem RestoredProjectionArtifact.operationalProgramsWF_of_large
    (self : RestoredProjectionArtifact env name info venv)
    (henv : venv.ConversionRegular)
    (large : self.view.elimination = .large) :
    self.view.OperationalProgramsWF venv :=
  self.parameterLayout.operationalProgramsWF_of_large henv
    self.codeNaturality self.recEntriesClosed large

/-- A restored artifact therefore supplies rule-independent eta
reconstruction in every well-formed model where it is retained. -/
theorem RestoredProjectionArtifact.operationalRebuildWF_of_large
    (self : RestoredProjectionArtifact env name info venv)
    (henv : venv.ConversionRegular)
    (large : self.view.elimination = .large) :
    self.view.OperationalRebuildWF venv :=
  self.largeRebuilds large VEnv.LE.rfl henv

/-- Complete a restored artifact with the sparse runtime backend.  The exact
layout establishes the persistent large-rebuild contract at this producer
boundary; consumers retain it without replaying the proof. -/
def RestoredProjectionArtifact.ofRuntime
    {env : Environment} {name : Name} {info : InductiveVal} {venv : VEnv}
    (layout : RestoredProjectionArtifactLayout env name info venv)
    (recEntriesClosed :
      VInductDecl.RestoreEntriesClosed layout.view.nested.recEntries)
    (codeNaturality : layout.view.flatView.OperationalCodeNaturality)
    (parameterLayout : layout.view.ConstructorParameterLayoutWF venv)
    (spineSupport : ProjectionFieldSpineSupport
      layout.view.nparams layout.view.fields.length
      layout.constructorInfo.type layout.view.sourceConstructor.type) :
    RestoredProjectionArtifact env name info venv where
  toRestoredProjectionArtifactLayout := layout
  recEntriesClosed := recEntriesClosed
  codeNaturality := codeNaturality
  parameterLayout := parameterLayout
  programs := .runtime spineSupport
  largeRebuilds :=
    parameterLayout.largeRebuilds codeNaturality recEntriesClosed

/-- Complete a restored artifact with persistently typed dense programs. -/
def RestoredProjectionArtifact.ofDense
    {env : Environment} {name : Name} {info : InductiveVal} {venv : VEnv}
    (layout : RestoredProjectionArtifactLayout env name info venv)
    (recEntriesClosed :
      VInductDecl.RestoreEntriesClosed layout.view.nested.recEntries)
    (codeNaturality : layout.view.flatView.OperationalCodeNaturality)
    (parameterLayout : layout.view.ConstructorParameterLayoutWF venv)
    (programs : RestoredProjectionDensePrograms layout.view venv) :
    RestoredProjectionArtifact env name info venv where
  toRestoredProjectionArtifactLayout := layout
  recEntriesClosed := recEntriesClosed
  codeNaturality := codeNaturality
  parameterLayout := parameterLayout
  programs := .dense programs
  largeRebuilds :=
    parameterLayout.largeRebuilds codeNaturality recEntriesClosed


/-- The restored sparse runtime can skip a dependency-irrelevant field using
only the producer-retained code naturality and restoration closure.  No flat
registration or restored projector typing is needed at a skipped position. -/
theorem VRestoredBlockStructureView.OperationalRuntimePrefix.snocSkip
    {view : VRestoredBlockStructureView} {env : VEnv}
    {U : Nat} {context : List VExpr} {levels : List VLevel}
    {params : List VExpr} {limit : Nat}
    (runtime : view.OperationalRuntimePrefix env U context levels params limit)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (recEntriesClosed :
      VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (hparamsLength : params.length = view.nparams)
    {majorDomain majorBody constructorDomain constructorBody : VExpr}
    (hmajorConsume :
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero)).consumeForalls?
          (view.operationalProjectionArgs levels
            (params.map (VExpr.liftN 1)) limit (.bvar 0)) =
        some (.forallE majorDomain majorBody))
    (hmajorSkip : majorBody.Skips 1 0)
    (hconstructorConsume :
      let fields := view.specializedFields levels params
      let fieldCount := fields.length
      (VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
        (.sort .zero)).consumeForalls?
          (((view.operationalProjectionCodes levels params).take limit).map
            fun prior => .app (prior.projector.liftN fieldCount)
              (view.projectionConstructorApp levels params fields)) =
        some (.forallE constructorDomain constructorBody))
    (hconstructorSkip : constructorBody.Skips 1 0)
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[limit]? =
      some code) :
    view.OperationalRuntimePrefix env U context levels params (limit + 1) := by
  obtain ⟨⟨majorCursor, majorSparse⟩,
    ⟨constructorCursor, constructorSparse, constructorPointwise⟩⟩ := runtime
  let fields := view.specializedFields levels params
  let fieldCount := fields.length
  have hlimit : limit < fields.length := by
    simpa [fields] using (List.getElem?_eq_some_iff.1 hcode).1

  let paramsLift := params.map (VExpr.liftN 1)
  have hcodesLift := view.operationalProjectionCodes_liftN codeNaturality
    recEntriesClosed levels params hparamsLength 1 0
  have hcodeLift :
      (view.operationalProjectionCodes levels paramsLift)[limit]? =
        some (code.liftN 1 0) := by
    rw [← hcodesLift, List.getElem?_map, hcode]
    rfl
  have hmajorCursor : majorCursor = .forallE majorDomain majorBody :=
    Option.some.inj (majorSparse.consumeForalls_eq.symm.trans hmajorConsume)
  subst majorCursor
  let majorArgument :=
    (code.liftN 1 0).projector.app (.bvar 0)
  let majorSparse' := majorSparse.snocSkip
    (argument := majorArgument) hmajorSkip
  let majorCursor' := majorBody.inst majorArgument
  have majorSparseFinal : env.SparseSpineWF U
      (view.structureType levels params :: context)
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero))
      (view.operationalProjectionArgs levels
        (params.map (VExpr.liftN 1)) (limit + 1) (.bvar 0)) majorCursor' := by
    rw [view.operationalProjectionArgs_succ levels paramsLift limit
      (.bvar 0) hcodeLift]
    exact majorSparse'

  let paramsFullLift := params.map (VExpr.liftN fieldCount)
  have hcodesFullLift := view.operationalProjectionCodes_liftN codeNaturality
    recEntriesClosed levels params hparamsLength fieldCount 0
  have hcodeFullLift :
      (view.operationalProjectionCodes levels paramsFullLift)[limit]? =
        some (code.liftN fieldCount 0) := by
    rw [← hcodesFullLift, List.getElem?_map, hcode]
    rfl
  have hconstructorArgs :
      view.operationalProjectionArgs levels paramsFullLift limit
          (view.projectionConstructorApp levels params fields) =
        ((view.operationalProjectionCodes levels params).take limit).map
          fun prior => .app (prior.projector.liftN fieldCount)
            (view.projectionConstructorApp levels params fields) := by
    unfold VRestoredBlockStructureView.operationalProjectionArgs
    rw [← hcodesFullLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  have hconstructorCursor : constructorCursor =
      .forallE constructorDomain constructorBody := by
    exact Option.some.inj
      (constructorSparse.consumeForalls_eq.symm.trans hconstructorConsume)
  subst constructorCursor
  let constructorArgument :=
    (code.liftN fieldCount 0).projector.app
      (view.projectionConstructorApp levels params fields)
  let constructorSparse' := constructorSparse.snocSkip
    (argument := constructorArgument) hconstructorSkip
  have constructorPointwise' := constructorPointwise.snocSkip
    (argument := constructorArgument)
    (right := .bvar (fieldCount - 1 - limit)) hconstructorSkip

  refine ⟨⟨majorCursor', majorSparseFinal⟩, ?_⟩
  unfold VRestoredBlockStructureView.OperationalSparseConstructorPrefix
  simp only [List.take_add_one, hcode, Option.toList_some,
    List.map_append, List.map_singleton]
  rw [VExpr.bvarRevRange_succ_of_lt hlimit]
  exact ⟨_, constructorSparse', constructorPointwise'⟩

namespace TypeChecker

inductive MLCtx where
  | nil : MLCtx
  | vlam (id : FVarId) (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo) : MLCtx → MLCtx
  | vlet (id : FVarId) (name : Name) (ty v : Expr) (ty' v' : VExpr) : MLCtx → MLCtx

@[simp] def MLCtx.vlctx : MLCtx → VLCtx
  | .nil => []
  | .vlam id _ ty ty' _ c => (some (id, ty.fvarsList), .vlam ty') :: c.vlctx
  | .vlet id _ ty v ty' v' c => (some (id, ty.fvarsList ++ v.fvarsList), .vlet ty' v') :: c.vlctx

def MLCtx.lctx : MLCtx → LocalContext
  | .nil => {}
  | .vlam id name ty _ bi c => c.lctx.mkLocalDecl id name ty bi
  | .vlet id name ty val _ _ c => c.lctx.mkLetDecl id name ty val

@[simp] def MLCtx.length : MLCtx → Nat
  | .nil => 0
  | .vlam _ _ _ _ _ c
  | .vlet _ _ _ _ _ _ c => c.length + 1

def MLCtx.decls : MLCtx → List LocalDecl
  | .nil => {}
  | .vlam x name ty _ bi c => .cdecl c.length x name ty bi .default :: c.decls
  | .vlet x name ty v _ _ c => .ldecl c.length x name ty v false default :: c.decls

@[simp] def MLCtx.fvarRevList (c : MLCtx) (n) (hn : n ≤ c.length) : List FVarId :=
  match n, c, hn with
  | 0, _, _ => []
  | n+1, .vlam id _ _ _ _ c, h
  | n+1, .vlet id _ _ _ _ _ c, h => id :: c.fvarRevList n (Nat.le_of_succ_le_succ h)
termination_by structural n

@[simp] theorem MLCtx.fvarRevList_length {c n hn} : (MLCtx.fvarRevList c n hn).length = n := by
  induction n generalizing c <;> [simp; cases c <;> simp [*] at hn ⊢]

@[simp] def MLCtx.letValList (c : MLCtx) (n) (hn : n ≤ c.length) : List (Option (Expr × Expr)) :=
  match n, c, hn with
  | 0, _, _ => []
  | n+1, .vlam _ _ _ _ _ c, h => none :: c.letValList n (Nat.le_of_succ_le_succ h)
  | n+1, .vlet _ _ ty v _ _ c, h => some (ty, v) :: c.letValList n (Nat.le_of_succ_le_succ h)
termination_by structural n

@[simp] theorem MLCtx.letValList_length {c n hn} : (MLCtx.letValList c n hn).length = n := by
  induction n generalizing c <;> [simp; cases c <;> simp [*] at hn ⊢]

@[simp] def MLCtx.dropN (c : MLCtx) (n) (hn : n ≤ c.length) : MLCtx :=
  match n, c, hn with
  | 0, c, _ => c
  | n+1, .vlam _ _ _ _ _ c, h
  | n+1, .vlet _ _ _ _ _ _ c, h => c.dropN n (Nat.le_of_succ_le_succ h)
termination_by structural n

def MLCtx.WF (env : VEnv) (Us : List Name) : MLCtx → Prop
  | .nil => True
  | .vlam fv _ ty ty' _ c =>
    c.WF env Us ∧ c.lctx.find? fv = none ∧
    TrExprS env Us c.vlctx ty ty' ∧
    env.IsType Us.length c.vlctx.toCtx ty'
  | .vlet fv _ ty v ty' v' c =>
    c.WF env Us ∧ c.lctx.find? fv = none ∧
    TrExprS env Us c.vlctx ty ty' ∧ TrExprS env Us c.vlctx v v' ∧
    env.HasType Us.length c.vlctx.toCtx v' ty'

theorem MLCtx.WF.tr : ∀ {c : MLCtx}, c.WF env Us → TrLCtx env Us c.lctx c.vlctx
  | .nil, _ => ⟨.nil, .nil⟩
  | .vlam .., ⟨h1, h2, h3, h4⟩ => .mkLocalDecl h1.tr h2 h3 h4
  | .vlet .., ⟨h1, h2, h3, h4, h5⟩ => .mkLetDecl h1.tr h2 h3 h4 h5

theorem MLCtx.WF.dropN {c : MLCtx} (n hn) : c.WF env Us → (c.dropN n hn).WF env Us :=
  match n, c, hn with
  | 0, _, _ => id
  | n+1, .vlam .., h
  | n+1, .vlet .., h => fun H => H.1.dropN n (Nat.le_of_succ_le_succ h)

theorem MLCtx.dropN_fvars_subset {c : MLCtx} (n hn) : (c.dropN n hn).vlctx.fvars ⊆ c.vlctx.fvars :=
  match n, c, hn with
  | 0, _, _ => fun _ => id
  | n+1, .vlam .., h
  | n+1, .vlet .., h =>
    List.subset_cons_of_subset _ <| dropN_fvars_subset n (Nat.le_of_succ_le_succ h)

theorem MLCtx.noBV (c : MLCtx) : c.vlctx.NoBV := by
  induction c <;> trivial

structure VContext extends Context where
  venv : VEnv
  hasPrimitives : VEnv.HasPrimitives venv
  safePrimitives : env.find? n = some ci →
    Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = []
  trenv : TrEnv safety env venv
  projectionReady : ProjectionResolutionReady env venv
  structureEtaReady : StructureEtaReady env venv
  mlctx : MLCtx
  mlctx_wf : mlctx.WF venv lparams
  lctx_eq : mlctx.lctx = lctx

@[simp] abbrev VContext.lctx' (c : VContext) := c.mlctx.lctx
@[simp] abbrev VContext.vlctx (c : VContext) := c.mlctx.vlctx

theorem VContext.trlctx (c : VContext) : TrLCtx c.venv c.lparams c.lctx' c.vlctx := c.mlctx_wf.tr
theorem VContext.Ewf (c : VContext) : VEnv.WF c.venv := c.trenv.wf
theorem VContext.Δwf (c : VContext) : c.vlctx.WF c.venv c.lparams.length := c.trlctx.wf

nonrec abbrev VContext.TrExprS (c : VContext) : Expr → VExpr → Prop :=
  TrExprS c.venv c.lparams c.vlctx
nonrec abbrev VContext.TrExpr (c : VContext) : Expr → VExpr → Prop :=
  TrExpr c.venv c.lparams c.vlctx
nonrec abbrev VContext.IsType (c : VContext) : VExpr → Prop :=
  c.venv.IsType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.HasType (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.HasType c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.IsDefEqU (c : VContext) : VExpr → VExpr → Prop :=
  c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx
nonrec abbrev VContext.TrLCtx (c : VContext) : Prop :=
  TrLCtx c.venv c.lparams c.lctx' c.vlctx
nonrec abbrev VContext.FVarsBelow (c : VContext) : Expr → Expr → Prop :=
  FVarsBelow c.vlctx
nonrec abbrev VContext.TrTyping (c : VContext) : Expr → Expr → VExpr → VExpr → Prop :=
  TrTyping c.venv c.lparams c.vlctx

class VContext.MLCWF (c : VContext) (m : MLCtx) : Prop where
  wf : m.WF c.venv c.lparams

instance (c : VContext) : c.MLCWF c.mlctx := ⟨c.mlctx_wf⟩

structure VState extends State where

def _root_.Lean4Lean.InferCache.WF (c : VContext) (s : VState) (m : InferCache) : Prop :=
  ∀ ⦃e ty : Expr⦄, m[e]? = some ty → ConditionallyHasType s.ngen c.venv c.lparams c.vlctx e ty

theorem _root_.Lean4Lean.InferCache.WF.empty : InferCache.WF c s {} := fun _ => by simp

def WHNFCache.WF (c : VContext) (s : VState) (m : InferCache) : Prop :=
  ∀ ⦃e ty : Expr⦄, m[e]? = some ty → ConditionallyWHNF s.ngen c.venv c.lparams c.vlctx e ty

theorem WHNFCache.WF.empty : WHNFCache.WF c s {} := fun _ => by simp

def UnfoldCache.WF (c : VContext) (m : ExprMap Expr) : Prop :=
  ∀ ⦃e e' : Expr⦄, m[e]? = some e' → ∃ n ls ci, e = .const n ls ∧
      c.env.find? n = some ci ∧ e' = Inner.instantiateDeltaValue ci ls

class VState.WF (c : VContext) (s : VState) where
  trctx : c.TrLCtx
  ngen_wf : ∀ fv ∈ c.vlctx.fvars, s.ngen.Reserves fv
  ectx : ∃ Δ' n, Δ'.WF c.venv c.lparams.length ∧ c.vlctx.FVLift' Δ' 0 n 0 ∧
    s.eqvManager.WF c.venv c.lparams Δ' ∧ ∀ fv ∈ Δ'.fvars, s.ngen.Reserves fv
  inferTypeI_wf : s.inferTypeI.WF c s
  inferTypeC_wf : s.inferTypeC.WF c s
  whnfCore_wf : WHNFCache.WF c s s.whnfCoreCache
  whnf_wf : WHNFCache.WF c s s.whnfCache
  unfold_wf : UnfoldCache.WF c s.unfold

theorem VState.WF.find?_eq_none {id}
    (wf : VState.WF c s) (H : ¬s.ngen.Reserves id) : c.lctx'.find? id = none :=
  wf.trctx.find?_eq_none.2 fun h => H (wf.ngen_wf _ h)

def VState.LE (s₁ s₂ : VState) : Prop :=
  s₁.ngen ≤ s₂.ngen

instance : LE VState := ⟨VState.LE⟩

theorem VState.LE.rfl {s : VState} : s ≤ s := NameGenerator.LE.rfl

theorem VState.LE.trans {s₁ s₂ s₃ : VState} (h₁ : s₁ ≤ s₂) (h₂ : s₂ ≤ s₃) : s₁ ≤ s₃ :=
  NameGenerator.LE.trans h₁ h₂

theorem VState.LE.reservesV {s₁ s₂ : VState} (h : s₁ ≤ s₂) {{fv}} :
    s₁.ngen.Reserves fv → s₂.ngen.Reserves fv :=
  (·.mono h)

theorem VState.LE.reserves {s₁ s₂ : VState} (h : s₁ ≤ s₂) {{e}} :
    FVarsIn s₁.ngen.Reserves e → FVarsIn s₂.ngen.Reserves e :=
  (·.mono h.reservesV)

def M.WF (c : VContext) (vs : VState) (x : M α) (Q : α → VState → Prop) : Prop :=
  vs.WF c → ∀ a s', x c.toContext vs.toState = .ok (a, s') →
    ∃ vs', vs'.toState = s' ∧ vs ≤ vs' ∧ vs'.WF c ∧ Q a vs'

theorem M.WF.bind {c : VContext} {s : VState} {x : M α} {f : α → M β} {Q R}
    (h1 : x.WF c s Q)
    (h2 : ∀ a s', s ≤ s' → Q a s' → (f a).WF c s' R) :
    (x >>= f).WF c s R := by
  intro wf₁ a vs₁
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  split; · simp
  intro h; rename_i v eq
  obtain ⟨vs₂, eq1, le1, wf₂, h1⟩ := h1 wf₁ _ _ eq
  obtain ⟨vs₃, rfl, le2, wf₃, h2⟩ := h2 _ _ le1 h1 wf₂ _ _ (eq1 ▸ h)
  exact ⟨_, rfl, le1.trans le2, wf₃, h2⟩

theorem M.WF.pure {c : VContext} {s : VState} {Q} (H : Q a s) :
    (pure a : M α).WF c s Q := by rintro h _ _ ⟨⟩; exact ⟨_, rfl, .rfl, h, H⟩

theorem M.WF.map {c : VContext} {s : VState} {x : M α} {f : α → β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R (f a) s') : (f <$> x).WF c s R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

theorem M.WF.mono {c : VContext} {s : VState} {x : M α} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R a s') : x.WF c s R := by
  simpa using h1.bind fun _ _ a1 a2 => .pure (h2 _ _ a1 a2)

theorem M.WF.throw {c : VContext} {s : VState} {Q} : (throw e : M α).WF c s Q := nofun

/-- Sandboxed discovery cannot invalidate verifier state: a successful run
restores the raw type-checker state with which it started. -/
theorem M.WF.sandbox {c : VContext} {s : VState} {x : M α} :
    (M.sandbox x).WF c s fun _ s' => s' = s := by
  intro wf a st h
  simp only [M.sandbox] at h
  split at h <;> cases h
  exact ⟨s, rfl, .rfl, wf, rfl⟩

theorem M.WF.le {c : VContext} {s : VState} {Q R} {x : M α}
    (h1 : x.WF c s Q) (H : ∀ a s', s ≤ s' → Q a s' → R a s') :
    x.WF c s R := fun wf _ _ e =>
  let ⟨_, a1, a2, a3, a4⟩ := h1 wf _ _ e
  ⟨_, a1, a2, a3, H _ _ a2 a4⟩

structure Methods.WF (m : Methods) where
  isDefEqCore : c.TrExprS e₁ e₁' → c.TrExprS e₂ e₂' →
    (m.isDefEqCore e₁ e₂).WF c s fun b _ => b → c.IsDefEqU e₁' e₂'
  whnfCore : c.TrExprS e e' →
    (m.whnfCore e cheapProj).WF c s fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  whnf : c.TrExprS e e' →
    (m.whnf e).WF c s fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  whnf_forall :
    (m.whnf (.forallE name dom body bi)).WF c s fun e₁ _ =>
      e₁ = .forallE name dom body bi
  inferType : e.FVarsIn (· ∈ c.vlctx.fvars) →
    (inferOnly = true → ∃ e', c.TrExprS e e') →
    (m.inferType e inferOnly).WF c s fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty'

def RecM.WF (c : VContext) (s : VState) (x : RecM α) (Q : α → VState → Prop) : Prop :=
  ∀ m, m.WF → M.WF c s (x m) Q

theorem M.WF.liftExcept {c : VContext} {s : VState} {x : Except Exception α} {Q} (h : x.WF Q) :
    M.WF c s (liftM x) fun a _ => Q a := by
  rintro wf _ _ eq
  cases x <;> cases eq
  exact ⟨s, rfl, .rfl, wf, h _ rfl⟩

theorem M.WF.lift {c : VContext} {s : VState} {x : M α} {Q} (h : x.WF c s Q) :
    RecM.WF c s x Q := fun _ _ => h

instance : Coe (M.WF c s x Q) (RecM.WF c s x Q) := ⟨M.WF.lift⟩

theorem RecM.WF.bind {c : VContext} {s : VState} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → (f a).WF c s' R) : (x >>= f).WF c s R :=
  fun _ h => M.WF.bind (h1 _ h) fun _ _ h1' h2' => h2 _ _ h1' h2' _ h

theorem RecM.WF.bind_le {c : VContext} {s : VState} {x : RecM α} {f : α → RecM β} {Q R}
    (h1 : x.WF c s Q) (hs : s₀ ≤ s)
    (h2 : ∀ a s', s₀ ≤ s' → Q a s' → (f a).WF c s' R) : (x >>= f).WF c s R :=
  RecM.WF.bind h1 fun _ _ h => h2 _ _ (hs.trans h)

theorem RecM.WF.pure {c : VContext} {s : VState} {Q} (H : Q a s) : (pure a : RecM α).WF c s Q :=
  fun _ _ => .pure H

theorem RecM.WF.map {c : VContext} {s : VState} {x : RecM α} {f : α → β} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R (f a) s') : (f <$> x).WF c s R := by
  rw [map_eq_pure_bind]
  exact h1.bind fun _ _ le h => .pure (h2 _ _ le h)

theorem RecM.WF.mono {c : VContext} {s : VState} {x : RecM α} {Q R}
    (h1 : x.WF c s Q) (h2 : ∀ a s', s ≤ s' → Q a s' → R a s') : x.WF c s R := by
  rw [← id_map x]; exact h1.map h2

/-- Intersect two postconditions proved for the same recursive computation.
The execution determines the final state, so both certificates describe that
same endpoint. -/
theorem RecM.WF.and_const
    {x : RecM α} {c : VContext} {s : VState}
    {Q : α → VState → Prop} {R : α → Prop}
    (left : x.WF c s Q)
    (right : x.WF c s fun value _ => R value) :
    x.WF c s fun value state => Q value state ∧ R value := by
  intro methods methodsWF stateWF value finalState execution
  obtain ⟨leftState, leftStateEq, leftLE, leftWF, leftResult⟩ :=
    left methods methodsWF stateWF value finalState execution
  obtain ⟨_, _, _, _, rightResult⟩ :=
    right methods methodsWF stateWF value finalState execution
  exact ⟨leftState, leftStateEq, leftLE, leftWF, leftResult, rightResult⟩

theorem RecM.WF.throw {c : VContext} {s : VState} {Q} : (throw e : RecM α).WF c s Q := nofun

theorem RecM.WF.le {c : VContext} {s : VState} {Q R} {x : RecM α}
    (h1 : x.WF c s Q) (H : ∀ a s', s ≤ s' → Q a s' → R a s') :
    x.WF c s R := fun _ h => (h1 _ h).le H

theorem RecM.WF.pureBind {c : VContext} {s : VState} {f : β → RecM α} {Q}
    {x : β} (H : WF c s (f x) Q) : ((Pure.pure x : RecM β) >>= f).WF c s Q := H

theorem get.WF {c : VContext} {s : VState} :
    M.WF c s get fun a s' => s.toState = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem RecM.WF.get {c : VContext} {s : VState} {f : State → RecM α} {Q}
    (H : WF c s (f s.toState) Q) : (get >>= f).WF c s Q := H

theorem getEnv.WF {c : VContext} {s : VState} :
    M.WF c s getEnv fun a s' => c.env = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem RecM.WF.getEnv {c : VContext} {s : VState} {f : Environment → RecM α} {Q}
    (H : WF c s (f c.env) Q) : (liftM getEnv >>= f).WF c s Q := H

theorem getLCtx.WF {c : VContext} {s : VState} :
    M.WF c s getLCtx fun a s' => c.lctx' = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, c.lctx_eq, rfl⟩

theorem RecM.WF.getLCtx {c : VContext} {s : VState} {f : LocalContext → RecM α} {Q}
    (H : WF c s (f c.lctx') Q) : (getLCtx >>= f).WF c s Q :=
  getLCtx.WF.lift.bind <| by rintro _ _ _ ⟨rfl, rfl⟩; exact H

theorem RecM.WF.readThe {c : VContext} {s : VState} {f : Context → RecM α} {Q}
    (H : WF c s (f c.toContext) Q) : (readThe Context >>= f).WF c s Q := H

theorem getNGen.WF {c : VContext} {s : VState} :
    M.WF c s getNGen fun a s' => s.ngen = a ∧ s = s' := by
  rintro wf _ _ ⟨⟩; exact ⟨_, rfl, .rfl, wf, rfl, rfl⟩

theorem M.WF.getNGen {c : VContext} {s : VState} {f : NameGenerator → M α} {Q}
    (H : WF c s (f s.ngen) Q) : (getNGen >>= f).WF c s Q := H

theorem RecM.WF.getNGen {c : VContext} {s : VState} {f : NameGenerator → RecM α} {Q}
    (H : WF c s (f s.ngen) Q) : (getNGen >>= f).WF c s Q := H

theorem RecM.WF.stateWF {c : VContext} {s : VState} {x : RecM α} {Q}
    (H : s.WF c → WF c s x Q) : WF c s x Q :=
  fun _ h wf => H wf _ h wf

@[simp] theorem toLBool_true {b : Bool} : b.toLBool = .true ↔ b = true := by
  cases b <;> simp [Bool.toLBool]

theorem RecM.WF.toLBoolM {Q : VState → Prop} {x : RecM Bool}
    (H : x.WF c s fun b s => b → Q s) : (toLBoolM x).WF c s fun b s => b = .true → Q s :=
  H.bind fun _ _ _ H => .pure fun h => H (by simpa using h)

def VContext.withMLC (c : VContext) (m : MLCtx) [wf : c.MLCWF m] : VContext :=
  { c with
    mlctx := m
    mlctx_wf := wf.1
    lctx := m.lctx
    lctx_eq := rfl }

@[simp] theorem VContext.withMLC_self (c : VContext) : c.withMLC c.mlctx = c := by
  simp [withMLC, c.lctx_eq]

def VState.next (s : VState) : VState := { s with ngen := s.ngen.next }

protected theorem RecM.WF.withLocalDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : VState} {f : Expr → RecM α} {Q name ty ty' bi}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty')
    (hs : s₀ ≤ s)
    (H : ∀ id cwf' s', s₀ ≤ s' → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf')) s' (f (.fvar id)) Q) :
    (withLocalDecl name bi ty f).WF (c.withMLC m) s Q := by
  intro _ mwf wf a s' e
  let id := s.ngen.curr
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have h1' := wf.find?_eq_none h1
  let m' := m.vlam ⟨id⟩ name ty ty' bi
  have cwf' : c.MLCWF m' := ⟨cwf.1, h1', hty, hty'⟩
  have : VState.WF (c.withMLC m') s.next :=
    have trctx := wf.trctx.mkLocalDecl h1' hty hty'
    have hic {ic} (H : InferCache.WF (c.withMLC m) s ic) : InferCache.WF (c.withMLC m') s.next ic :=
      fun _ _ h => ((H h).fresh c.Ewf.ordered trctx.wf).mono le
    have hwc {wc} (H : WHNFCache.WF (c.withMLC m) s wc) : WHNFCache.WF (c.withMLC m') s.next wc :=
      fun _ _ h => ((H h).fresh c.Ewf trctx.wf).mono le
    { ngen_wf := by
        simp [m', VContext.withMLC]; exact ⟨h0, fun _ h => le.reservesV (wf.ngen_wf _ h)⟩
      ectx := by
        let ⟨_, _, a1, a2, a3, a4⟩ := wf.ectx
        refine
          have b1 := ⟨a1, ?_, hty'.weak' c.Ewf.ordered a2.toCtx⟩
          ⟨_, _, b1, a2.cons_fvar _ _ hty.fvarsList, a3.weak' c.Ewf (.skip_fvar _ _ .refl) b1,
            fun _ h => by obtain _ | ⟨_, h⟩ := h <;> [exact h0; exact (a4 _ h).mono le]⟩
        rintro _ _ ⟨⟩; exact ⟨mt (a4 _) h1, hty.fvarsList.trans a2.fvars_sublist.subset⟩
      trctx, inferTypeI_wf := hic wf.inferTypeI_wf, inferTypeC_wf := hic wf.inferTypeC_wf
      whnfCore_wf := hwc wf.whnfCore_wf, whnf_wf := hwc wf.whnf_wf, unfold_wf := wf.unfold_wf }
  let ⟨s', hs1, hs2, wf', hs4⟩ := H _ _ _ (hs.trans le) h1 _ mwf this a s' e
  refine have le' := le.trans hs2; ⟨s', hs1, le', ?_, hs4⟩
  have hic {ic} (H : InferCache.WF (c.withMLC m') s' ic) :
      InferCache.WF (c.withMLC m) s' ic := fun _ _ h => (H h).weakN_inv c.Ewf wf'.trctx.wf
  have hwc {wc} (H : WHNFCache.WF (c.withMLC m') s' wc) :
      WHNFCache.WF (c.withMLC m) s' wc := fun _ _ h => (H h).weakN_inv c.Ewf wf'.trctx.wf
  let ⟨_, _, a1, a2, a3⟩ := wf'.ectx
  exact {
    ngen_wf := (by simpa [VContext.withMLC] using wf'.ngen_wf :).2
    ectx := ⟨_, _, a1, .comp (.skip_fvar _ _ .refl) a2, a3⟩
    trctx := wf.trctx
    inferTypeI_wf := hic wf'.inferTypeI_wf, inferTypeC_wf := hic wf'.inferTypeC_wf
    whnfCore_wf := hwc wf'.whnfCore_wf, whnf_wf := hwc wf'.whnf_wf, unfold_wf := wf'.unfold_wf
  }

protected theorem M.WF.withLocalDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : VState} {f : Expr → M α} {Q name ty ty' bi}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hty' : (c.withMLC m).IsType ty')
    (hs : s₀ ≤ s)
    (H : ∀ id cwf' s', s₀ ≤ s' → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlam id name ty ty' bi m) (wf := cwf')) s' (f (.fvar id)) Q) :
    (withLocalDecl name bi ty f).WF (c.withMLC m) s Q := by
  intro wf a s' e
  let id := s.ngen.curr
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have h1' := wf.find?_eq_none h1
  let m' := m.vlam ⟨id⟩ name ty ty' bi
  have cwf' : c.MLCWF m' := ⟨cwf.1, h1', hty, hty'⟩
  have : VState.WF (c.withMLC m') s.next :=
    have trctx := wf.trctx.mkLocalDecl h1' hty hty'
    have hic {ic} (H : InferCache.WF (c.withMLC m) s ic) :
        InferCache.WF (c.withMLC m') s.next ic :=
      fun _ _ h => ((H h).fresh c.Ewf.ordered trctx.wf).mono le
    have hwc {wc} (H : WHNFCache.WF (c.withMLC m) s wc) :
        WHNFCache.WF (c.withMLC m') s.next wc :=
      fun _ _ h => ((H h).fresh c.Ewf trctx.wf).mono le
    { ngen_wf := by
        simp [m', VContext.withMLC]
        exact ⟨h0, fun _ h => le.reservesV (wf.ngen_wf _ h)⟩
      ectx := by
        let ⟨_, _, a1, a2, a3, a4⟩ := wf.ectx
        refine
          have b1 := ⟨a1, ?_, hty'.weak' c.Ewf.ordered a2.toCtx⟩
          ⟨_, _, b1, a2.cons_fvar _ _ hty.fvarsList,
            a3.weak' c.Ewf (.skip_fvar _ _ .refl) b1,
            fun _ h => by
              obtain _ | ⟨_, h⟩ := h
              · exact h0
              · exact (a4 _ h).mono le⟩
        rintro _ _ ⟨⟩
        exact ⟨mt (a4 _) h1,
          hty.fvarsList.trans a2.fvars_sublist.subset⟩
      trctx
      inferTypeI_wf := hic wf.inferTypeI_wf
      inferTypeC_wf := hic wf.inferTypeC_wf
      whnfCore_wf := hwc wf.whnfCore_wf
      whnf_wf := hwc wf.whnf_wf
      unfold_wf := wf.unfold_wf }
  let ⟨s', hs1, hs2, wf', hs4⟩ := H _ _ _ (hs.trans le) h1 this a s' e
  refine have le' := le.trans hs2; ⟨s', hs1, le', ?_, hs4⟩
  have hic {ic} (H : InferCache.WF (c.withMLC m') s' ic) :
      InferCache.WF (c.withMLC m) s' ic :=
    fun _ _ h => (H h).weakN_inv c.Ewf wf'.trctx.wf
  have hwc {wc} (H : WHNFCache.WF (c.withMLC m') s' wc) :
      WHNFCache.WF (c.withMLC m) s' wc :=
    fun _ _ h => (H h).weakN_inv c.Ewf wf'.trctx.wf
  let ⟨_, _, a1, a2, a3⟩ := wf'.ectx
  exact {
    ngen_wf := (by simpa [VContext.withMLC] using wf'.ngen_wf :).2
    ectx := ⟨_, _, a1, .comp (.skip_fvar _ _ .refl) a2, a3⟩
    trctx := wf.trctx
    inferTypeI_wf := hic wf'.inferTypeI_wf
    inferTypeC_wf := hic wf'.inferTypeC_wf
    whnfCore_wf := hwc wf'.whnfCore_wf
    whnf_wf := hwc wf'.whnf_wf
    unfold_wf := wf'.unfold_wf
  }

protected theorem RecM.WF.withLetDecl {c : VContext} {m} [cwf : c.MLCWF m]
    {s : VState} {f : Expr → RecM α} {Q name ty ty'}
    (hty : (c.withMLC m).TrExprS ty ty')
    (hval : (c.withMLC m).TrExprS val val')
    (hval' : (c.withMLC m).HasType val' ty')
    (hs : s₀ ≤ s)
    (H : ∀ id cwf' s', s₀ ≤ s' → ¬s.ngen.Reserves id →
      WF (c.withMLC (.vlet id name ty val ty' val' m) (wf := cwf')) s' (f (.fvar id)) Q) :
    (withLetDecl name ty val f).WF (c.withMLC m) s Q := by
  intro _ mwf wf a s' e
  let id := s.ngen.curr
  have h0 := s.ngen.next_reserves_self
  have h1 := s.ngen.not_reserves_self
  have le : s ≤ s.next := .next
  have h1' := wf.find?_eq_none h1
  let m' := m.vlet ⟨id⟩ name ty val ty' val'
  have cwf' : c.MLCWF m' := ⟨cwf.1, h1', hty, hval, hval'⟩
  have : VState.WF (c.withMLC m') s.next :=
    have trctx := wf.trctx.mkLetDecl h1' hty hval hval'
    have hic {ic} (H : InferCache.WF (c.withMLC m) s ic) :
        InferCache.WF (c.withMLC m') s.next ic :=
      fun _ _ h => ((H h).fresh c.Ewf.ordered trctx.wf).mono le
    have hwc {wc} (H : WHNFCache.WF (c.withMLC m) s wc) : WHNFCache.WF (c.withMLC m') s.next wc :=
      fun _ _ h => ((H h).fresh c.Ewf trctx.wf).mono le
    { ngen_wf := by
        simp [m', VContext.withMLC]; exact ⟨h0, fun _ h => le.reservesV (wf.ngen_wf _ h)⟩
      ectx := by
        let ⟨_, _, a1, a2, a3, a4⟩ := wf.ectx
        have hv := List.append_subset.2 ⟨hty.fvarsList, hval.fvarsList⟩
        refine
          have b1 := ⟨a1, ?_, hval'.weak' c.Ewf.ordered a2.toCtx⟩
          ⟨_, _, b1, a2.cons_fvar _ _ hv, a3.weak' c.Ewf (.skip_fvar _ _ .refl) b1,
            fun _ h => by obtain _ | ⟨_, h⟩ := h <;> [exact h0; exact (a4 _ h).mono le]⟩
        rintro _ _ ⟨⟩; exact ⟨mt (a4 _) h1, hv.trans a2.fvars_sublist.subset⟩
      trctx, inferTypeI_wf := hic wf.inferTypeI_wf, inferTypeC_wf := hic wf.inferTypeC_wf
      whnfCore_wf := hwc wf.whnfCore_wf, whnf_wf := hwc wf.whnf_wf, unfold_wf := wf.unfold_wf }
  let ⟨s', hs1, hs2, wf', hs4⟩ := H _ _ _ (hs.trans le) h1 _ mwf this a s' e
  refine ⟨s', hs1, le.trans hs2, ?_, hs4⟩
  have hic {ic} (H : InferCache.WF (c.withMLC m') s' ic) :
      InferCache.WF (c.withMLC m) s' ic := fun _ _ h => (H h).weakN_inv c.Ewf wf'.trctx.wf
  have hwc {wc} (H : WHNFCache.WF (c.withMLC m') s' wc) :
      WHNFCache.WF (c.withMLC m) s' wc := fun _ _ h => (H h).weakN_inv c.Ewf wf'.trctx.wf
  let ⟨_, _, a1, a2, a3⟩ := wf'.ectx
  exact {
    ngen_wf := (by simpa [VContext.withMLC] using wf'.ngen_wf :).2
    ectx := ⟨_, _, a1, .comp (.skip_fvar _ _ .refl) a2, a3⟩
    trctx := wf.trctx
    inferTypeI_wf := hic wf'.inferTypeI_wf, inferTypeC_wf := hic wf'.inferTypeC_wf
    whnfCore_wf := hwc wf'.whnfCore_wf, whnf_wf := hwc wf'.whnf_wf, unfold_wf := wf'.unfold_wf
  }

@[simp] def MLCtx.mkForall (c : MLCtx) (n) (hn : n ≤ c.length) (e : Expr) : Expr :=
  match n, c, hn with
  | 0, _, _ => e
  | n+1, .vlam x name ty _ bi c, h =>
    c.mkForall n (Nat.le_of_succ_le_succ h) (.forallE name ty (.abstract1 x e) bi)
  | n+1, .vlet x name ty val _ _ c, h =>
    c.mkForall n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstract1 x e
      if e'.hasLooseBVar' 0 then
        .letE name ty val e' false
      else
        e'.lowerLooseBVars' 1 1
termination_by structural n

def AllAbove (Δ : VLCtx) (P : FVarId → Prop) (fv : FVarId) : Prop := fv ∈ Δ.fvars → P fv

theorem AllAbove.wf (H : Δ.FVWF) : IsFVarUpSet (AllAbove Δ P) Δ ↔ IsFVarUpSet P Δ :=
  IsFVarUpSet.congr H fun _ h => by simp [h, AllAbove]

@[simp] def MLCtx.mkForall' (c : MLCtx) (n) (hn : n ≤ c.length) (e : VExpr) : VExpr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam _ _ _ ty _ c, h, e => c.mkForall' n (Nat.le_of_succ_le_succ h) (.forallE ty e)
  | n+1, .vlet _ _ _ _ _ _ c, h, e => c.mkForall' n (Nat.le_of_succ_le_succ h) e
termination_by structural n

@[simp] def MLCtx.mkLambda (c : MLCtx) (n) (hn : n ≤ c.length) (e : Expr) : Expr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam x name ty _ bi c, h, e =>
    c.mkLambda n (Nat.le_of_succ_le_succ h) (.lam name ty (.abstract1 x e) bi)
  | n+1, .vlet x name ty val _ _ c, h, e =>
    c.mkLambda n (Nat.le_of_succ_le_succ h) <|
      let e' := Expr.abstract1 x e
      if e'.hasLooseBVar' 0 then
        .letE name ty val e' false
      else
        e'.lowerLooseBVars' 1 1
termination_by structural n

@[simp] def MLCtx.mkLambda' (c : MLCtx) (n) (hn : n ≤ c.length) (e : VExpr) : VExpr :=
  match n, c, hn, e with
  | 0, _, _, e => e
  | n+1, .vlam _ _ _ ty _ c, h, e => c.mkLambda' n (Nat.le_of_succ_le_succ h) (.lam ty e)
  | n+1, .vlet _ _ _ _ _ _ c, h, e => c.mkLambda' n (Nat.le_of_succ_le_succ h) e
termination_by structural n

-- HACK: MLCtx.mkLet equation generation fails if this is inlined
def MLCtx.mkLetArg (x : FVarId) (name : Name)
    (ty val : Expr) (nd : Option Bool) (e : Expr) : Expr :=
  let e' := Expr.abstract1 x e
  if e'.hasLooseBVar' 0 then
    .letE name ty val e' (nd.getD false)
  else if let some nd := nd then
    .letE name ty val e' nd
  else
    e'.lowerLooseBVars' 1 1

@[simp] def MLCtx.mkLet (c : MLCtx) (n) (hn : n ≤ c.length)
    (nds : List (Option Bool)) (eq : nds.length = n) (e : Expr) (asForall := false) : Expr :=
  match n, c, hn, nds, eq, e with
  | 0, _, _, _, _, e => e
  | n+1, .vlam x name ty _ bi c, h, _ :: nds, eq, e =>
    c.mkLet n (Nat.le_of_succ_le_succ h) nds (Nat.succ_inj.1 eq) <|
      if asForall then .forallE name ty (.abstract1 x e) bi else .lam name ty (.abstract1 x e) bi
  | n+1, .vlet x name ty val _ _ c, h, nd :: nds, eq, e =>
    c.mkLet n (Nat.le_of_succ_le_succ h) nds (Nat.succ_inj.1 eq) <| mkLetArg x name ty val nd e
termination_by structural n

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkForall_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.IsType Us.length c.vlctx.toCtx e') (n hn) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkForall n hn e) (c.mkForall' n hn e') ∧
    env.IsType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') := by
  induction n generalizing c e e' with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, h4⟩ := wf
      refine ih h1 ?_ (.forallE h4 H2) _
      exact .forallE h4 H2 h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf
      refine ih h1 ?_ H2 _; dsimp; split
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem mkForall_hasType {c : MLCtx}
    (hus : us.Forall₂ (VLevel.ofLevel Us · = some ·) us')
    (hΔ : c.vlctx.SortList env Us.length us')
    (hu : VLevel.ofLevel Us u = some u')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' (.sort u')) (n hn)
    (hus : us.length = n) :
    ∃ u₀', VLevel.ofLevel Us (List.foldl (fun x y => mkLevelIMaxCpp y x) u us) = some u₀' ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') (.sort u₀') := by
  subst hus
  induction hus generalizing c e' u u' with
  | nil => exact ⟨_, hu, H2⟩
  | cons h _ ih =>
    match c, hΔ with
    | .vlam x name ty ty' bi c, .cons hΔ hu₁ =>
      have ⟨_, h5, h6⟩ := ofLevel_mkLevelIMaxCpp h hu
      refine ih hΔ h5 ?_ (Nat.le_of_succ_le_succ hn)
      refine .defeq (.sortDF ?_ (.of_ofLevel h5) h6.symm) (hu₁.forallE H2)
      exact ⟨.of_ofLevel h, .of_ofLevel hu⟩

theorem MLCtx.WF.mkForall'_congr {c : MLCtx} (wf : c.WF env Us)
    (H : env.IsDefEq Us.length c.vlctx.toCtx e₁ e₂ (.sort u)) (n hn) :
    ∃ u, env.IsDefEq Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkForall' n hn e₁) (c.mkForall' n hn e₂) (.sort u) := by
  induction n generalizing c e₁ e₂ u with
  | zero => exact ⟨_, H⟩
  | succ n ih =>
    match c with
    | .vlam .. => let ⟨_, h⟩ := wf.2.2.2; exact ih wf.1 (.forallEDF h H) _
    | .vlet .. => exact ih wf.1 H _

theorem MLCtx.WF.mkForall_tr (henv : VEnv.WF env) {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExpr env Us c.vlctx e e')
    (H2 : env.IsType Us.length c.vlctx.toCtx e') (n hn) :
    TrExpr env Us (c.dropN n hn).vlctx (c.mkForall n hn e) (c.mkForall' n hn e') ∧
    env.IsType Us.length (c.dropN n hn).vlctx.toCtx (c.mkForall' n hn e') := by
  let ⟨_, H1, eq⟩ := H1
  let ⟨_, H2⟩ := H2
  have eq := eq.of_r henv wf.tr.wf H2
  have ⟨_, H⟩ := wf.mkForall'_congr eq n hn
  have := wf.mkForall_trS henv H1 ⟨_, eq.hasType.1⟩ n hn
  exact ⟨⟨_, this.1, _, H⟩, this.2.defeqU_l henv (wf.dropN n hn).tr.wf ⟨_, H⟩⟩

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkLambda_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkLambda n hn e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  induction n generalizing c e e' ty' with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, _, h4⟩ := wf
      refine ih h1 ?_ (.lam h4 H2) _
      exact .lam ⟨_, h4⟩ h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf
      refine ih h1 ?_ H2 _; dsimp; split
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem MLCtx.WF.mkLambda'_congr {c : MLCtx} (wf : c.WF env Us)
    (H : env.IsDefEq Us.length c.vlctx.toCtx e₁ e₂ ty) (n hn) :
    env.IsDefEq Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e₁) (c.mkLambda' n hn e₂) (c.mkForall' n hn ty) := by
  induction n generalizing c e₁ e₂ ty with
  | zero => exact H
  | succ n ih =>
    match c with
    | .vlam .. => let ⟨_, h⟩ := wf.2.2.2; exact ih wf.1 (.lamDF h H) _
    | .vlet .. => exact ih wf.1 H _

theorem MLCtx.WF.mkLambda_tr (henv : VEnv.WF env) {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExpr env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn) :
    TrExpr env Us (c.dropN n hn).vlctx (c.mkLambda n hn e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  let ⟨_, H1, eq⟩ := H1
  have eq := eq.of_r henv wf.tr.wf H2
  have H := wf.mkLambda'_congr eq n hn
  have := wf.mkLambda_trS henv H1 eq.hasType.1 n hn
  exact ⟨⟨_, this.1, _, H⟩, this.2.defeqU_l henv (wf.dropN n hn).tr.wf ⟨_, H⟩⟩

variable! (henv : VEnv.WF env) in
theorem MLCtx.WF.mkLet_trS {c : MLCtx} (wf : c.WF env Us)
    (H1 : TrExprS env Us c.vlctx e e')
    (H2 : env.HasType Us.length c.vlctx.toCtx e' ty') (n hn nds hnds) :
    TrExprS env Us (c.dropN n hn).vlctx (c.mkLet n hn nds hnds e) (c.mkLambda' n hn e') ∧
    env.HasType Us.length (c.dropN n hn).vlctx.toCtx
      (c.mkLambda' n hn e') (c.mkForall' n hn ty') := by
  induction n generalizing c e e' ty' nds with
  | zero => exact ⟨H1, H2⟩
  | succ n ih =>
    match c with
    | .vlam x name ty ty' bi c =>
      let ⟨h1, _, h3, _, h4⟩ := wf; let _ :: _ := nds
      refine ih h1 ?_ (.lam h4 H2) ..
      exact .lam ⟨_, h4⟩ h3 (.abstract .zero H1)
    | .vlet x name ty val ty' val' c =>
      let ⟨h1, _, h3, h4, h5⟩ := wf; let _ :: _ := nds
      refine ih h1 ?_ H2 ..; dsimp [mkLetArg]; split <;> [skip; split]
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · exact .letE h5 h3 h4 (.abstract .zero H1)
      · rename_i h _ _; simp at h
        rw [Expr.lowerLooseBVars_eq_instantiate h (v := val)]
        exact .inst_let henv (.abstract .zero H1) h4

theorem MLCtx.fvarRevList_prefix (c : MLCtx)
    {n hn} : c.fvarRevList n hn <+: c.vlctx.fvars := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => match c with | .vlam .. | .vlet .. => simp [ih]

theorem MLCtx.WF.fvars_nodup : ∀ {c : MLCtx}, c.WF env Us → c.vlctx.fvars.Nodup
  | .nil, _ => .nil
  | .vlam _ _ _ _ _ c, ⟨h1, h2, _⟩
  | .vlet _ _ _ _ _ _ c, ⟨h1, h2, _⟩ => by simp [h1.fvars_nodup, h1.tr.find?_eq_none.1 h2]

theorem MLCtx.WF.fvarRevList_nodup {c : MLCtx} (wf : c.WF env Us)
    (n hn) : (c.fvarRevList n hn).Nodup :=
  c.fvarRevList_prefix.sublist.nodup wf.fvars_nodup

theorem MLCtx.WF.decls_size {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.decls.size = c.length := by
  rw [← wf.tr.1.decls_wf.toList'_length]
  induction c with
  | nil => rfl
  | vlam _ _ _ _ _ _ ih =>
    simp [lctx, LocalContext.mkLocalDecl, ih wf.1,
      wf.1.tr.1.decls_wf.toList'_push]
  | vlet _ _ _ _ _ _ _ ih =>
    simp [lctx, LocalContext.mkLetDecl, ih wf.1,
      wf.1.tr.1.decls_wf.toList'_push]

theorem MLCtx.WF.toList_eq {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.toList = c.decls := by
  simp [LocalContext.toList]
  induction c with
  | nil => rfl
  | vlam _ _ _ _ _ _ ih =>
    simp [lctx, LocalContext.mkLocalDecl, decls, ih wf.1, wf.1.decls_size,
      wf.1.tr.1.decls_wf.toList'_push]
  | vlet _ _ _ _ _ _ _ ih =>
    simp [lctx, LocalContext.mkLetDecl, decls, ih wf.1, wf.1.decls_size,
      wf.1.tr.1.decls_wf.toList'_push]

theorem MLCtx.WF.find?_eq {c : MLCtx} (wf : c.WF env Us) :
    c.lctx.find? x = c.decls.find? (x == ·.fvarId) := by
  simp [wf.tr.1.find?_eq_find?_toList, wf.toList_eq]

inductive MLCtx.PartialForall : MLCtx → Nat → List FVarId → Expr → Prop where
  | nil : PartialForall c 0 [] e
  | vlam : PartialForall c n fvs (.forallE x ty (.abstract1 fv e) bi) →
    PartialForall (c.vlam fv x ty ty' bi) (n+1) (fv :: fvs) e
  | vlet : PartialForall c n fvs (
      let e' := Expr.abstract1 fv e
      if e'.hasLooseBVar' 0 then .letE x ty v e' false
      else e'.lowerLooseBVars' 1 1) →
    PartialForall (c.vlet fv x ty v ty' v') (n+1) (fv :: fvs) e
  | skip : e.looseBVarRange' = 0 → e' = Expr.abstract1 fv e → e'.hasLooseBVar' 0 = false →
    PartialForall c n fvs e →
    PartialForall (c.vlet fv x ty v ty' v') (n+1) fvs e

theorem MLCtx.PartialForall.full : MLCtx.PartialForall c n (c.fvarRevList n hn) e := by
  induction n generalizing c e with
  | zero => exact .nil
  | succ n ih => match c with | .vlam .. | .vlet .. => constructor; apply ih

theorem MLCtx.PartialForall.sublist (H : MLCtx.PartialForall c n l e) : l <+ c.vlctx.fvars := by
  induction H with
  | nil => simp
  | vlam _ ih | vlet _ ih => simp [ih]
  | skip _ _ _ _ ih => exact ih.trans (List.sublist_cons_self ..)

theorem MLCtx.WF.mkForall_partial {c : MLCtx} (wf : c.WF env Us) (n hn)
    (he : e.looseBVarRange' = 0)
    (harr : arr.toList.reverse = l.map .fvar) (hp : MLCtx.PartialForall c n l e) :
    c.lctx.mkForall arr e = c.mkForall n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkForall, this, ← List.map_reverse,
    LocalContext.mkBinding_eq he
      (List.nodup_reverse.2 (hp.sublist.nodup wf.fvars_nodup))
      (fun _ _ _ h => wf.tr.closed_of_find? h),
    LocalContext.mkBindingList_eq_fold, List.foldr_reverse]
  · clear harr this he
    induction hp with
    | nil => simp
    | vlam hp ih | vlet hp ih =>
      simp
      refine (List.foldl_congr fun _ y h => ?_).trans <|
        .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _)
      · refine LocalContext.mkBindingList1_congr ?_
        rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
        simp [LocalDecl.fvarId]; rintro ⟨⟩
        have := (List.cons_sublist_cons.2 hp.sublist).nodup wf.fvars_nodup; simp_all
      · simp [LocalContext.mkBindingList1, wf.find?_eq, decls, LocalDecl.fvarId]
    | skip h1 h2 h3 hp ih =>
      subst h2; simp [h3]
      rw [Expr.lowerLooseBVars_eq_instantiate h3 (v := default),
        Expr.abstract1_eq_liftLooseBVars h3, Expr.liftLooseBVars_eq_self (by simp [h1]),
        Expr.instantiate1_eq_self h1]
      refine (List.foldl_congr fun _ y h => ?_).trans (ih wf.1 _)
      refine LocalContext.mkBindingList1_congr ?_
      rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
      simp [LocalDecl.fvarId]; rintro ⟨⟩
      have := (List.cons_sublist_cons.2 hp.sublist).nodup wf.fvars_nodup; simp_all
  · intro _ h
    exact wf.tr.find?_eq_some.2 (hp.sublist.subset (List.mem_reverse.1 h))
  · exact List.nodup_reverse.2 (hp.sublist.nodup wf.fvars_nodup)

theorem MLCtx.WF.mkForall_eq {c : MLCtx} (wf : c.WF env Us) (n hn)
    (he : e.looseBVarRange' = 0)
    (harr : arr.toList.reverse = (c.fvarRevList n hn).map .fvar) :
    c.lctx.mkForall arr e = c.mkForall n hn e :=
  mkForall_partial wf n hn he harr .full

/-!
`LocalContext.mkForall` is also used with a selected list of free variables
which is not a suffix of the ambient local context.  Recursor synthesis is
the important example: constructor fields and induction hypotheses remain in
the producer context as scratch declarations, while only parameters,
motives, minors, indices, and the major are abstracted into the emitted type.

`SelectedForall` records the compressed semantic telescope selected by such
an array.  The implementation local context is consulted only for the source
binder metadata; scratch declarations need not occur in either semantic
context index.
-/
inductive MLCtx.SelectedForall (env : VEnv) (Us : List Name)
    (implementationLCtx : LocalContext) :
    VLCtx → List FVarId → List VExpr → VLCtx → Prop where
  | nil : SelectedForall env Us implementationLCtx base [] [] base
  | cons
      (find : implementationLCtx.find? fv = some
        (.cdecl index fv name type binderInfo kind))
      (domainTr : TrExprS env Us base type type')
      (domainType : env.IsType Us.length base.toCtx type')
      (tail : SelectedForall env Us implementationLCtx
        ((some (fv, deps), .vlam type') :: base) fvars types final) :
      SelectedForall env Us implementationLCtx base (fv :: fvars)
        (type' :: types) final

namespace MLCtx.SelectedForall

/-- Every selected source identifier is an actual declaration in the
implementation local context. -/
theorem find_exists
    (selection : MLCtx.SelectedForall env Us implementationLCtx base fvars
      types final) :
    ∀ fv ∈ fvars,
      ∃ declaration, implementationLCtx.find? fv = some declaration := by
  induction selection with
  | nil => intro fv member; nomatch member
  | cons find domainTr domainType tail ih =>
      intro current member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, find⟩
      · exact ih current member

/-- A selected free-variable telescope preserves the absence of de Bruijn
declarations in its compressed semantic context. -/
theorem final_noBV
    (selection : MLCtx.SelectedForall env Us implementationLCtx base fvars
      types final)
    (baseNoBV : base.NoBV) : final.NoBV := by
  induction selection with
  | nil => exact baseNoBV
  | cons find domainTr domainType tail ih =>
      exact ih baseNoBV

/-- Types read for selected declarations are closed implementation
expressions.  This is precisely the side condition needed by the verified
list model of `LocalContext.mkBinding`. -/
theorem lookup_closed
    (selection : MLCtx.SelectedForall env Us implementationLCtx base fvars
      types final)
    (baseNoBV : base.NoBV) :
    ∀ fv ∈ fvars, ∀ declaration,
      implementationLCtx.find? fv = some declaration →
        declaration.type.looseBVarRange' = 0 ∧
          ∀ value ∈ declaration.value? true,
            value.looseBVarRange' = 0 := by
  induction selection with
  | nil => intro fv member; nomatch member
  | cons find domainTr domainType tail ih =>
      intro current member declaration found
      rcases List.mem_cons.mp member with rfl | member
      · rw [find] at found
        cases found
        refine ⟨(baseNoBV ▸ domainTr.closed).looseBVarRange_zero, ?_⟩
        intro value present
        simp [LocalDecl.value?] at present
      · exact ih baseNoBV current member declaration found

/-- Translate the explicit fold used by `LocalContext.mkBindingList`.  Each
selected source free variable becomes one Theory Pi binder; declarations not
listed by the selection are invisible to this fold. -/
theorem fold_trS
    (selection : MLCtx.SelectedForall env Us implementationLCtx base fvars
      types final)
    (bodyTr : TrExprS env Us final body body')
    (bodyType : env.IsType Us.length final.toCtx body') :
    TrExprS env Us base
      (fvars.foldr (fun fv result =>
        LocalContext.mkBindingList1 false implementationLCtx [] fv
          (result.abstract1 fv)) body)
      (VExpr.forallN types body') ∧
    env.IsType Us.length base.toCtx (VExpr.forallN types body') := by
  induction selection with
  | nil => exact ⟨bodyTr, bodyType⟩
  | @cons fv index name type binderInfo kind base type' deps fvars types
      final find domainTr domainType tail ih =>
      obtain ⟨tailTr, tailType⟩ := ih bodyTr bodyType
      have translated := TrExprS.forallE (name := name)
        (bi := binderInfo) domainType tailType domainTr
          (tailTr.abstract VLCtx.Abstract.zero)
      refine ⟨?_, .forallE domainType tailType⟩
      simpa [LocalContext.mkBindingList1, find, VExpr.forallN] using
        translated

/-- Strict translation of an implementation `mkForall` over an arbitrary
selected free-variable telescope.  Unlike `MLCtx.WF.mkForall_eq`, this
theorem permits unselected lambda declarations to be interspersed throughout
the ambient implementation context. -/
theorem mkForall_trS
    (selection : MLCtx.SelectedForall env Us implementationLCtx base fvars
      types final)
    (fvarsNodup : fvars.Nodup)
    (baseNoBV : base.NoBV)
    (bodyTr : TrExprS env Us final body body')
    (bodyType : env.IsType Us.length final.toCtx body') :
    TrExprS env Us base
      (implementationLCtx.mkForall ⟨fvars.map Expr.fvar⟩ body)
      (VExpr.forallN types body') ∧
    env.IsType Us.length base.toCtx (VExpr.forallN types body') := by
  have finalNoBV := selection.final_noBV baseNoBV
  have bodyClosed : body.looseBVarRange' = 0 :=
    (finalNoBV ▸ bodyTr.closed).looseBVarRange_zero
  rw [LocalContext.mkForall]
  change TrExprS env Us base
      (LocalContext.mkBinding false implementationLCtx
        ⟨fvars.map Expr.fvar⟩ body)
        (VExpr.forallN types body') ∧
    env.IsType Us.length base.toCtx (VExpr.forallN types body')
  rw [LocalContext.mkBinding_eq bodyClosed fvarsNodup
      (selection.lookup_closed baseNoBV),
    LocalContext.mkBindingList_eq_fold selection.find_exists fvarsNodup]
  exact selection.fold_trS bodyTr bodyType

/-- Array-indexed form of `mkForall_trS`.  Producer records retain their
selected locals as arrays, so this wrapper avoids rebuilding an artificial
array equality at every recursor-synthesis phase. -/
theorem mkForall_array_trS
    (selection : MLCtx.SelectedForall env Us implementationLCtx base fvars
      types final)
    (arraySources : arr.toList = fvars.map Expr.fvar)
    (fvarsNodup : fvars.Nodup)
    (baseNoBV : base.NoBV)
    (bodyTr : TrExprS env Us final body body')
    (bodyType : env.IsType Us.length final.toCtx body') :
    TrExprS env Us base
      (implementationLCtx.mkForall arr body)
      (VExpr.forallN types body') ∧
    env.IsType Us.length base.toCtx (VExpr.forallN types body') := by
  have arrayEq : arr = ⟨fvars.map Expr.fvar⟩ := by
    rw [← Array.toList_inj]
    exact arraySources
  rw [arrayEq]
  exact selection.mkForall_trS fvarsNodup baseNoBV bodyTr bodyType

/-- Producer-facing packaging of an arbitrary selected `mkForall` array.
The source identifiers are retained existentially, while the public fields
record exactly the two operational facts needed by `mkForall_array_trS`. -/
structure ArrayRun (env : VEnv) (Us : List Name)
    (implementationLCtx : LocalContext) (base : VLCtx) (sources : Array Expr)
    (types : List VExpr) (final : VLCtx) : Type where
  fvars : List FVarId
  selection : MLCtx.SelectedForall env Us implementationLCtx base fvars
    types final
  sources_eq : sources.toList = fvars.map Expr.fvar
  nodup : fvars.Nodup

/-- Apply a packaged selected-array run to a translated type body. -/
theorem ArrayRun.mkForall_trS
    (run : ArrayRun (env := env) (Us := Us)
      (implementationLCtx := implementationLCtx) base sources types final)
    (baseNoBV : base.NoBV)
    (bodyTr : TrExprS env Us final body body')
    (bodyType : env.IsType Us.length final.toCtx body') :
    TrExprS env Us base
      (implementationLCtx.mkForall sources body)
      (VExpr.forallN types body') ∧
    env.IsType Us.length base.toCtx (VExpr.forallN types body') :=
  run.selection.mkForall_array_trS run.sources_eq run.nodup baseNoBV bodyTr
    bodyType

/-- The endpoint of a packaged selected-array run remains free of bound
local declarations whenever its starting context is. -/
theorem ArrayRun.final_noBV
    (run : ArrayRun (env := env) (Us := Us)
      (implementationLCtx := implementationLCtx) base sources types final)
    (baseNoBV : base.NoBV) : final.NoBV :=
  run.selection.final_noBV baseNoBV

/-- Reindex a selected implementation telescope along an exact translation
of its universe slots.  The implementation local context and selected free
variables are unchanged; only the compressed Theory contexts and binder
types are instantiated. -/
theorem relevel
    (selection : MLCtx.SelectedForall env ps implementationLCtx base fvars
      types final)
    (levelsWF : ∀ level ∈ extra, level.WF Us.length)
    (levels : ∀ {source target},
      VLevel.ofLevel ps source = some target →
        VLevel.ofLevel Us source = some (target.inst extra)) :
    MLCtx.SelectedForall env Us implementationLCtx (base.instL extra) fvars
      (types.map (VExpr.instL extra)) (final.instL extra) := by
  induction selection with
  | nil => exact .nil
  | @cons fv index name type binderInfo kind base type' deps fvars types
      final find domainTr domainType tail ih =>
      exact .cons find
        (domainTr.relevel levelsWF levels)
        (VLCtx.instL_toCtx _ ▸ domainType.instL levelsWF)
        (by simpa [VLCtx.instL, VLocalDecl.instL] using ih)

/-- Array-packaged selected telescopes inherit exact universe reindexing. -/
def ArrayRun.relevel
    (run : ArrayRun (env := env) (Us := ps)
      (implementationLCtx := implementationLCtx) base sources types final)
    (levelsWF : ∀ level ∈ extra, level.WF Us.length)
    (levels : ∀ {source target},
      VLevel.ofLevel ps source = some target →
        VLevel.ofLevel Us source = some (target.inst extra)) :
    ArrayRun (env := env) (Us := Us)
      (implementationLCtx := implementationLCtx) (base.instL extra) sources
      (types.map (VExpr.instL extra)) (final.instL extra) where
  fvars := run.fvars
  selection := run.selection.relevel levelsWF levels
  sources_eq := run.sources_eq
  nodup := run.nodup

end MLCtx.SelectedForall

theorem MLCtx.WF.mkLambda_eq {c : MLCtx} (wf : c.WF env Us) (n hn)
    (he : e.looseBVarRange' = 0)
    (harr : arr.toList.reverse = (c.fvarRevList n hn).map .fvar) :
    c.lctx.mkLambda arr e = c.mkLambda n hn e := by
  have := congrArg (Array.mk ·.reverse) harr; simp at this
  rw [LocalContext.mkLambda, this, ← List.map_reverse,
    LocalContext.mkBinding_eq he
      (List.nodup_reverse.2 (wf.fvarRevList_nodup ..))
      (fun _ _ _ h => wf.tr.closed_of_find? h),
    LocalContext.mkBindingList_eq_fold, List.foldr_reverse]
  · clear harr this he
    induction n generalizing c e with
    | zero => simp
    | succ n ih =>
      match c with
      | .vlam .. | .vlet .. =>
        simp
        refine (List.foldl_congr fun _ y h => ?_).trans <|
          .trans (congrFun (congrArg _ ?_) _) (ih wf.1 _)
        · refine LocalContext.mkBindingList1_congr ?_
          rw [wf.find?_eq, wf.1.find?_eq, decls, List.find?, (?_ : (y == _) = false)]
          simp [LocalDecl.fvarId]; rintro ⟨⟩
          have := wf.fvarRevList_nodup (n+1) hn; simp_all
        · simp [LocalContext.mkBindingList1, wf.find?_eq, decls, LocalDecl.fvarId]
  · intro _ h
    exact wf.tr.find?_eq_some.2 ((MLCtx.fvarRevList_prefix ..).subset (List.mem_reverse.1 h))
  · exact List.nodup_reverse.2 (wf.fvarRevList_nodup ..)

namespace Inner

/-- A successful host-environment lookup returns exactly the constant found
at the requested name.  Kept in the common checker layer so both inference
and WHNF reduction can consume the same lookup certificate. -/
theorem envGet.WF {c : VContext} :
    (c.env.get name).WF fun ci => c.env.find? name = some ci := by
  simp [Environment.get]; split <;> [refine .pure ‹_›; exact .throw]

theorem whnf.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnf e) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  fun _ wf => wf.whnf he

theorem isDefEqCore.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    RecM.WF c s (isDefEqCore e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂' :=
  fun _ wf => wf.isDefEqCore he₁ he₂

theorem inferType.WF' {c : VContext} {s : VState} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars))
    (hinf : inferOnly = true → ∃ e', c.TrExprS e e') :
    RecM.WF c s (inferType e inferOnly) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  fun _ wf => wf.inferType h1 hinf

theorem inferType.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (inferType e true) fun ty _ => ∃ ty', c.TrTyping e ty e' ty' := by
  refine .stateWF fun wf => ?_
  refine (inferType.WF' he.fvarsIn fun _ => ⟨_, he⟩).le
    fun _ _ _ ⟨_, _, h1, h2, h3, h4⟩ => ⟨_, h1, he, h3, ?_⟩
  have := h2.uniq c.Ewf (.refl c.Ewf c.Δwf) he
  exact h4.defeqU_l c.Ewf c.Δwf this

theorem inferType.WF_uniq {c : VContext} {s : VState}
    (he : c.TrExprS e e') (hty : c.HasType e' ty') :
    RecM.WF c s (inferType e true) fun ty _ => c.TrExpr ty ty' :=
  (inferType.WF he).le fun _ _ _ ⟨_, _, _, h1, h2⟩ =>
  ⟨_, h1, h2.uniqU c.Ewf c.Δwf hty⟩

theorem checkType.WF {c : VContext} {s : VState} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars)) :
    RecM.WF c s (inferType e false) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty' :=
  inferType.WF' h1 nofun

theorem whnfCore.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (whnfCore e cheapProj) fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' :=
  fun _ wf => wf.whnfCore he

theorem isDelta_is_some : isDelta env e = some ci ↔
    ∃ n, env.find? n = some ci ∧ (∃ v, ci.deltaValue? = some v) ∧
      ∃ ls, e.getAppFn = .const n ls ∧ ls.length = ci.numLevelParams := by
  simp only [isDelta]
  split <;> [split <;> [split; skip]; skip] <;>
    simp_all [Option.isSome_iff_exists] <;> grind

def UnfoldDefinition.WF (c : VContext) (e e₀ : Expr) (e' : VExpr) : Option Expr → Prop
  | some e₁ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e'
  | none => ∀ {{n ci v ls}}, c.env.find? n = some ci → ci.deltaValue? = some v →
    e₀ = .const n ls → ls.length = ci.numLevelParams → False

theorem unfoldDefinitionCore.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (unfoldDefinitionCore e) fun oe _ => UnfoldDefinition.WF c e e e' oe := by
  dsimp [unfoldDefinitionCore]
  split <;> [refine .getEnv ?_; (rename_i H; exact .pure fun _ _ _ _ _ _ h => nomatch H _ _ h)]
  split; rotate_left
  · rename_i H; refine .pure ?_; rintro _ _ _ _ h1 h2 ⟨⟩ hlen
    cases H _ (isDelta_is_some.2 ⟨_, h1, ⟨_, h2⟩, _, rfl, hlen⟩)
  rename_i n ls oci ci h1
  obtain ⟨_, h3, ⟨_, h4⟩, _, ⟨⟩, hlen⟩ := isDelta_is_some.1 h1
  have : UnfoldDefinition.WF c (.const n ls) (.const n ls) e'
      (some (instantiateDeltaValue ci ls)) := by
    let .const a1 a2 a3 := he
    have ⟨rfl, b1, b2, b3⟩ := c.trenv.find?_uniq h3 a1
    simp [instantiateDeltaValue, h4]
    have c1 := c.trenv.of_value h3 b1 h4
      |>.instLCpp c.Ewf (by trivial) a2 (b2.trans a3.symm)
    have := c1.weakFV c.Ewf (.from_nil c.mlctx.noBV) c.Δwf
    rw [c1.wf.closedN c.Ewf trivial |>.liftN_eq (Nat.zero_le _)] at this
    simp [VExpr.instL] at this; rw [VLevel.inst_map_id] at this
    · exact ⟨fun _ _ _ => c1.fvarsIn.mono nofun, this⟩
    · exact (List.mapM_eq_some.1 a2).length_eq.symm.trans <| a3.trans b2.symm
  split <;> [rename_i h5; exact .pure this]
  refine .pureBind <| .get ?_
  split <;> [rename_i eq; skip]
  · refine .stateWF fun wf => .pure ?_
    obtain ⟨_, _, _, ⟨⟩, a1, rfl⟩ := wf.unfold_wf eq
    cases h3.symm.trans a1; exact this
  · refine .bind (Q := fun _ _ => True) ?_ fun _ _ _ _ => .pure this
    rintro _ mwf wf _ _ ⟨⟩
    refine ⟨{ s with toState := _ }, rfl, .rfl, { wf with unfold_wf := ?_ }, ⟨⟩⟩
    intro e e'; simp only [Std.HashMap.getElem?_insert]
    split <;> [rintro ⟨⟩; exact (wf.unfold_wf ·)]
    rename_i eq; rw [BEq.comm, Expr.eqv_const] at eq
    exact ⟨_, _, _, eq, h3, rfl⟩

theorem unfoldDefinition.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (unfoldDefinition e) fun oe _ => UnfoldDefinition.WF c e e.getAppFn e' oe := by
  simp [unfoldDefinition]; split; rotate_left
  · rename_i h; refine (unfoldDefinitionCore.WF he).mono fun _ _ _ H => ?_
    rwa [show e.getAppFn = e by revert h; unfold Expr.isApp Expr.getAppFn; split <;> simp]
  have ⟨f', stk⟩ := AppStack.build (e.mkAppList_getAppArgsList ▸ he)
  refine (unfoldDefinitionCore.WF stk.tr).bind fun oe _ _ H => ?_
  cases oe <;> [exact .pure H; refine .pure ?_]
  have ⟨h1, h2⟩ := H
  rw [Expr.mkAppRevRange_eq (l₁ := []) (l₂ := e.getAppArgsRevList) (l₃ := [])
    (by simp [Expr.getAppRevArgs_toList]) (by rfl) (by simp [Expr.getAppRevArgs_eq])]
  simp only [Expr.getAppArgsRevList_reverse]; constructor
  · exact (e.mkAppList_getAppArgsList ▸ h1.mkAppList :)
  · exact h2.rebuild_mkAppList c.Ewf c.Δwf stk.tr (e.mkAppList_getAppArgsList ▸ he :)

theorem ensureSortCore.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    RecM.WF c s (ensureSortCore e e₀) fun e1 _ =>
      (∃ u, e1 = .sort u) ∧ c.TrExpr e1 e' ∧ c.FVarsBelow e e1 := by
  simp [ensureSortCore]; split
  · let .sort _ := e
    exact .pure ⟨⟨_, rfl⟩, he.trExpr c.Ewf c.Δwf, .rfl⟩
  refine (whnf.WF he).bind fun e _ _ ⟨hb, he⟩ => ?_; split
  · let .sort _ := e
    exact .pure ⟨⟨_, rfl⟩, he, hb⟩
  exact .getEnv <| .getLCtx .throw

theorem getSortLevel.WF
    (he : c.TrExprS e e') : (getSortLevel e).WF c s fun l _ =>
      ∃ u', VLevel.ofLevel c.lparams l = some u' ∧ c.HasType e' (.sort u') := by
  refine (inferType.WF he).bind fun ty _ le ⟨ty', _, _, h1, h2⟩ => ?_
  refine (ensureSortCore.WF h1).bind fun ty _ le h => ?_
  obtain ⟨⟨u, rfl⟩, ⟨ty₂, h3, h4⟩, _⟩ := h
  let .sort hu := h3
  exact .pure ⟨_, hu, h2.defeqU_r c.Ewf c.Δwf h4.symm⟩

theorem isProp.WF
    (he : c.TrExprS e e') : (isProp e).WF c s fun b _ =>
      b → c.HasType e' (.sort .zero) := by
  refine (getSortLevel.WF he).bind fun l _ le ⟨u', hu, h⟩ => .pure fun H => ?_
  exact h.defeqU_r c.Ewf c.Δwf
    ⟨_, .sortDF (.of_ofLevel hu) trivial (ofLevel_isAlwaysZero hu H)⟩
