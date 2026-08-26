/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.NatModReflect

/-!
# Generic-state well-founded primitive certificates

This module verifies the independently checked equation bundle recovered from
`WellFounded.Nat.fix`. It adapts upstream lean4lean PR #32 while retaining the
compiler-selected state packer, rather than restricting accepted definitions
to a concrete `PSigma` representation.
-/

namespace Lean4Lean.Environment

open Lean hiding Environment Exception
open Kernel TypeChecker

theorem withLambda.WF {c : VContext} {s : VState}
    {name : Name} {dom body : Expr} {bi : BinderInfo} {dom' body' : VExpr}
    {fail : ∀ {α}, M α} {k : Expr → Expr → M α} {Q}
    (he : c.TrExprS (.lam name dom body bi) (.lam dom' body'))
    (H : ∀ id cwf' s', s ≤ s' → ¬s.ngen.Reserves id →
      let c' := c.withMLC (.vlam id name dom dom' bi c.mlctx) (wf := cwf')
      c'.TrExprS (body.instantiate1 (.fvar id)) body' →
      M.WF c' s' (k (.fvar id) (body.instantiate1 (.fvar id))) Q) :
    M.WF c s (withLambda (.lam name dom body bi) fail k) Q := by
  let .lam hdomTy hdom hbody := he
  simp only [withLambda]
  have hw : M.WF (c.withMLC c.mlctx) s
      (withLocalDecl name bi dom fun fv =>
        k fv (body.instantiate1 fv)) Q := by
    refine .withLocalDecl hdom hdomTy .rfl fun id cwf' s' hs' hres => ?_
    have hbody' := hbody.inst_fvar c.Ewf.ordered cwf'.1.tr.wf
    rw [← Expr.instantiate1_eq] at hbody'
    exact H id cwf' s' hs' hres hbody'
  simpa using hw

/-- The explicit unfold/WHNF sequence used by the legacy zero check preserves
the translated meaning of its one-binder source expression. -/
theorem reduceNatWellFoundedLam1.WF {c : VContext} {s : VState}
    {name : Name} {ty body : Expr} {bi : BinderInfo} {ty' body' : VExpr}
    {fail : ∀ {α}, M α}
    (he : c.TrExprS (.lam name ty body bi) (.lam ty' body')) :
    M.WF c s (reduceNatWellFoundedLam1 (.lam name ty body bi) fail)
      fun out _ => c.TrExpr out (.lam ty' body') := by
  simp only [reduceNatWellFoundedLam1]
  refine withLambda.WF he ?_
  intro id cwf' s' hs' hres c' hbody
  refine (whnfCore.WF hbody).bind fun _ _ _ h₁ => ?_
  refine (unfoldDefinition.WF' h₁).bind fun _ _ _ h₂ => ?_
  refine (whnfCore.WF' h₂).bind fun _ _ _ h₃ => ?_
  refine (unfoldDefinition.WF' h₃).bind fun _ _ _ h₄ => ?_
  refine (whnfCore.WF' h₄).bind fun out _ _ hout => ?_
  refine getLCtx.WF.bind fun lctx _ _ hctx => ?_
  obtain ⟨rfl, rfl⟩ := hctx
  let ⟨_, _, heq⟩ := hout
  let ⟨_, heq'⟩ := heq
  have hlen : 1 ≤ c'.mlctx.length := by simp [c', VContext.withMLC]
  have hclosed := cwf'.1.mkLambda_tr c.Ewf hout
    heq'.hasType.2 1 hlen
  have hlctx : c'.lctx'.mkLambda #[.fvar id] out =
      c'.mlctx.mkLambda 1 hlen out := by
    apply cwf'.1.mkLambda_eq
    · exact (c'.mlctx.noBV ▸ hout.closed).looseBVarRange_zero
    · simp
  rw [hlctx]
  exact .pure (by simpa [c', VContext.withMLC] using hclosed.1)

private theorem closedExpr_fvarsIn {c : VContext} {e : Expr}
    (hf : e.hasFVar = false) (hm : e.hasMVar = false) :
    e.FVarsIn (· ∈ c.vlctx.fvars) := by
  apply fvarsIn_iff.mpr
  refine ⟨?_, fvarsIn_iff_hasMVar hm⟩
  intro fv hfv
  rw [fvarsList_eq_nil hf] at hfv
  simp at hfv

/-- Proof-relevant alpha-equivalence corresponding to `exprShapeEq`.
Binder names, annotations, and metadata payloads are intentionally ignored,
matching the information erased by `TrExprS`. -/
inductive ExprShapeEq : Expr → Expr → Prop
  | bvar : ExprShapeEq (.bvar i) (.bvar i)
  | fvar : ExprShapeEq (.fvar i) (.fvar i)
  | mvar : ExprShapeEq (.mvar i) (.mvar i)
  | sort : ExprShapeEq (.sort u) (.sort u)
  | const : ExprShapeEq (.const n us) (.const n us)
  | app : ExprShapeEq f f' → ExprShapeEq a a' →
      ExprShapeEq (.app f a) (.app f' a')
  | lam : ExprShapeEq ty ty' → ExprShapeEq body body' →
      ExprShapeEq (.lam n ty body bi) (.lam n' ty' body' bi')
  | forallE : ExprShapeEq ty ty' → ExprShapeEq body body' →
      ExprShapeEq (.forallE n ty body bi) (.forallE n' ty' body' bi')
  | letE : ExprShapeEq ty ty' → ExprShapeEq val val' →
      ExprShapeEq body body' →
      ExprShapeEq (.letE n ty val body nondep)
        (.letE n' ty' val' body' nondep')
  | lit : ExprShapeEq (.lit l) (.lit l)
  | mdata : ExprShapeEq e e' → ExprShapeEq (.mdata d e) (.mdata d' e')
  | proj : ExprShapeEq e e' → ExprShapeEq (.proj s i e) (.proj s i e')

theorem exprShapeEq_sound (h : exprShapeEq e e' = true) :
    ExprShapeEq e e' := by
  induction e generalizing e' with
  | bvar i =>
    cases e' <;> simp [exprShapeEq] at h
    subst_vars; exact .bvar
  | fvar i =>
    cases e' <;> simp [exprShapeEq] at h
    subst_vars; exact .fvar
  | mvar i =>
    cases e' <;> simp [exprShapeEq] at h
    subst_vars; exact .mvar
  | sort u =>
    cases e' <;> simp [exprShapeEq] at h
    subst_vars; exact .sort
  | const n us =>
    cases e' <;> simp [exprShapeEq] at h
    rcases h with ⟨rfl, rfl⟩; exact .const
  | app f a ihf iha =>
    cases e' <;> simp [exprShapeEq] at h
    exact .app (ihf h.1) (iha h.2)
  | lam n ty body bi ihty ihbody =>
    cases e' <;> simp [exprShapeEq] at h
    exact .lam (ihty h.1) (ihbody h.2)
  | forallE n ty body bi ihty ihbody =>
    cases e' <;> simp [exprShapeEq] at h
    exact .forallE (ihty h.1) (ihbody h.2)
  | letE n ty val body nondep ihty ihval ihbody =>
    cases e' <;> simp [exprShapeEq] at h
    exact .letE (ihty h.1.1) (ihval h.1.2) (ihbody h.2)
  | lit l =>
    cases e' <;> simp [exprShapeEq] at h
    subst_vars; exact .lit
  | mdata d e ih =>
    cases e' <;> simp [exprShapeEq] at h
    exact .mdata (ih h)
  | proj s i e ih =>
    cases e' <;> simp [exprShapeEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, he⟩
    exact .proj (ih he)

@[simp] theorem exprLooseBVarRange_eq (e : Expr) :
    exprLooseBVarRange e = e.looseBVarRange' := by
  induction e <;>
    simp [exprLooseBVarRange, Expr.looseBVarRange', *]

theorem ExprShapeEq.eq_const (h : ExprShapeEq e (.const n us)) :
    e = .const n us := by
  cases e <;> cases h
  rfl

theorem TrExprS.of_exprShapeEq {env : VEnv} {Us Δ e e' v}
    (hs : ExprShapeEq e e') (h : TrExprS env Us Δ e v) :
    TrExprS env Us Δ e' v := by
  induction hs generalizing Δ v with
  | bvar | fvar | mvar | sort | const | lit => exact h
  | app _ _ ihf iha =>
    cases h with
    | app hft hat hf ha => exact .app hft hat (ihf hf) (iha ha)
  | lam _ _ ihty ihbody =>
    cases h with
    | lam hty htrTy hbody => exact .lam hty (ihty htrTy) (ihbody hbody)
  | forallE _ _ ihty ihbody =>
    cases h with
    | forallE hty hbodyTy htrTy hbody =>
      exact .forallE hty hbodyTy (ihty htrTy) (ihbody hbody)
  | letE _ _ _ ihty ihval ihbody =>
    cases h with
    | letE hvalTy htrTy htrVal hbody =>
      exact .letE hvalTy (ihty htrTy) (ihval htrVal) (ihbody hbody)
  | mdata _ ih =>
    cases h with
    | mdata he => exact .mdata (ih he)
  | proj _ ih =>
    cases h with
    | proj he hp => exact .proj (ih he) hp

theorem checkNatWellFoundedEquation.WF {c : VContext} {s : VState}
    {lhs rhs : Expr} :
    M.WF c s (checkNatWellFoundedEquation lhs rhs) fun _ _ =>
      ∃ lhs' rhs', c.TrExprS lhs lhs' ∧ c.TrExprS rhs rhs' ∧
        c.IsDefEqU lhs' rhs' := by
  simp only [checkNatWellFoundedEquation]
  split
  · rename_i hclosed
    simp only [Bool.and_eq_true] at hclosed
    have hlhs := closedExpr_fvarsIn (c := c)
      (by simpa using hclosed.1.1.1) (by simpa using hclosed.1.1.2)
    have hrhs := closedExpr_fvarsIn (c := c)
      (by simpa using hclosed.1.2) (by simpa using hclosed.2)
    refine (checkType.WF hlhs).bind fun _ _ _ hl => ?_
    let ⟨lhs', _, _, hlhs', _, _⟩ := hl
    refine (checkType.WF hrhs).bind fun _ _ _ hr => ?_
    let ⟨rhs', _, _, hrhs', _, _⟩ := hr
    refine (isDefEq.WF hlhs' hrhs').bind fun b _ _ heq => ?_
    split
    · exact .pure ⟨lhs', rhs', hlhs', hrhs', heq (by assumption)⟩
    · exact .throw
  · exact .throw

def NatWellFoundedCoreResult.Valid (c : VContext)
    (r : NatWellFoundedCoreResult) : Prop :=
  r.auxShape = true ∧
  (∃ lhs' rhs', c.TrExprS r.callLhs lhs' ∧ c.TrExprS r.callRhs rhs' ∧
    c.IsDefEqU lhs' rhs') ∧
  (∃ lhs' rhs', c.TrExprS r.entryLhs lhs' ∧ c.TrExprS r.entryRhs rhs' ∧
    c.IsDefEqU lhs' rhs') ∧
  (∃ lhs' rhs', c.TrExprS r.topLhs lhs' ∧ c.TrExprS r.topRhs rhs' ∧
    c.IsDefEqU lhs' rhs') ∧
  (∃ lhs' rhs', c.TrExprS r.eagerLhs lhs' ∧ c.TrExprS r.eagerRhs rhs' ∧
    c.IsDefEqU lhs' rhs') ∧
  (∃ lhs' rhs', c.TrExprS r.boolTrueLhs lhs' ∧
    c.TrExprS r.boolTrueRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
  (∃ lhs' rhs', c.TrExprS r.boolFalseLhs lhs' ∧
    c.TrExprS r.boolFalseRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
  (∃ lhs' rhs', c.TrExprS r.stepLhs lhs' ∧ c.TrExprS r.stepRhs rhs' ∧
    c.IsDefEqU lhs' rhs') ∧
  ∃ lhs' rhs', c.TrExprS r.specStepLhs lhs' ∧
    c.TrExprS r.specStepRhs rhs' ∧ c.IsDefEqU lhs' rhs'

def NatWellFoundedCoreResult.AuxValid (c : VContext)
    (r : NatWellFoundedCoreResult) : Prop :=
  (∃ lhs' rhs', c.TrExprS r.expectedEagerLhs lhs' ∧
    c.TrExprS r.expectedEagerRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
  (∃ lhs' rhs', c.TrExprS r.expectedBoolTrueLhs lhs' ∧
    c.TrExprS r.expectedBoolTrueRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
  ∃ lhs' rhs', c.TrExprS r.expectedBoolFalseLhs lhs' ∧
    c.TrExprS r.expectedBoolFalseRhs rhs' ∧ c.IsDefEqU lhs' rhs'

theorem NatWellFoundedCoreResult.Valid.normalizeAux {c : VContext}
    {r : NatWellFoundedCoreResult} (hv : r.Valid c) : r.AuxValid c := by
  rcases hv with ⟨hs, _, _, _, heager, htrue, hfalse, _, _⟩
  rcases heager with ⟨el, er, hel, her, heeq⟩
  rcases htrue with ⟨tl, tr, htl, htr, hteq⟩
  rcases hfalse with ⟨fl, fr, hfl, hfr, hfeq⟩
  simp only [NatWellFoundedCoreResult.auxShape, Bool.and_eq_true] at hs
  rcases hs with
    ⟨⟨⟨⟨⟨⟨⟨⟨hels, hers⟩, htls⟩, htrs⟩, hfls⟩, hfrs⟩, _⟩, _⟩, _⟩
  exact ⟨
    ⟨el, er, TrExprS.of_exprShapeEq (exprShapeEq_sound hels) hel,
      TrExprS.of_exprShapeEq (exprShapeEq_sound hers) her, heeq⟩,
    ⟨tl, tr, TrExprS.of_exprShapeEq (exprShapeEq_sound htls) htl,
      TrExprS.of_exprShapeEq (exprShapeEq_sound htrs) htr, hteq⟩,
    ⟨fl, fr, TrExprS.of_exprShapeEq (exprShapeEq_sound hfls) hfl,
      TrExprS.of_exprShapeEq (exprShapeEq_sound hfrs) hfr, hfeq⟩⟩

theorem NatWellFoundedCoreResult.Valid.eagerFn_eq {c : VContext}
    {r : NatWellFoundedCoreResult} (hv : r.Valid c) :
    r.eagerFn = q(WellFounded.Nat.eager) := by
  have hs := hv.1
  simp only [NatWellFoundedCoreResult.auxShape, Bool.and_eq_true] at hs
  exact (exprShapeEq_sound hs.1.1.2).eq_const

theorem NatWellFoundedCoreResult.Valid.goFn_closed {c : VContext}
    {r : NatWellFoundedCoreResult} (hv : r.Valid c) :
    r.goFn.looseBVarRange' = 0 := by
  have hs := hv.1
  simp only [NatWellFoundedCoreResult.auxShape, Bool.and_eq_true] at hs
  simpa using hs.1.2

theorem NatWellFoundedCoreResult.Valid.stateFn_closed {c : VContext}
    {r : NatWellFoundedCoreResult} (hv : r.Valid c) :
    r.stateFn.looseBVarRange' = 0 := by
  have hs := hv.1
  simp only [NatWellFoundedCoreResult.auxShape, Bool.and_eq_true] at hs
  simpa using hs.2

theorem checkNatWellFoundedCertificate.WF {c : VContext} {s : VState}
    {r : NatWellFoundedCoreResult} :
    M.WF c s (checkNatWellFoundedCertificate r) fun _ _ => r.Valid c := by
  simp only [checkNatWellFoundedCertificate]
  split
  · rename_i hshape
    exact checkNatWellFoundedEquation.WF.bind fun _ _ _ hcall =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hentry =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ htop =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ heager =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ htrue =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hfalse =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hstep =>
      checkNatWellFoundedEquation.WF.mono fun _ _ _ hspec =>
        ⟨hshape, hcall, hentry, htop, heager, htrue, hfalse,
          hstep, hspec⟩
  · exact .throw

def NatGcdFixCertificate.Valid
    (c : VContext) (r : NatGcdFixCertificate) : Prop :=
  r.core.Valid c ∧
  (∃ lhs' rhs', c.TrExprS r.topLhs lhs' ∧ c.TrExprS r.topRhs rhs' ∧
    c.IsDefEqU lhs' rhs') ∧
  (∃ lhs' rhs', c.TrExprS r.zeroLhs lhs' ∧ c.TrExprS r.zeroRhs rhs' ∧
    c.IsDefEqU lhs' rhs') ∧
  ∃ lhs' rhs', c.TrExprS r.succLhs lhs' ∧ c.TrExprS r.succRhs rhs' ∧
    c.IsDefEqU lhs' rhs'

def NatGcdFixCertificate.NormalizedValid (c : VContext)
    (r : NatGcdFixCertificate) (gcd : Expr) : Prop :=
  r.core.Valid c ∧
  (∃ lhs' rhs', c.TrExprS (r.expectedTopLhs gcd) lhs' ∧
    c.TrExprS r.expectedTopRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
  (∃ lhs' rhs', c.TrExprS r.expectedZeroLhs lhs' ∧
    c.TrExprS r.expectedZeroRhs rhs' ∧ c.IsDefEqU lhs' rhs') ∧
  ∃ lhs' rhs', c.TrExprS r.expectedSuccLhs lhs' ∧
    c.TrExprS r.expectedSuccRhs rhs' ∧ c.IsDefEqU lhs' rhs'

theorem NatGcdFixCertificate.Valid.normalize {c : VContext}
    {r : NatGcdFixCertificate} {gcd : Expr} (hv : r.Valid c)
    (hs : r.shape gcd = true) : r.NormalizedValid c gcd := by
  rcases hv with ⟨hcore, htop, hzero, hsucc⟩
  rcases htop with ⟨tl, tr, htl, htr, hteq⟩
  rcases hzero with ⟨zl, zr, hzl, hzr, hzeq⟩
  rcases hsucc with ⟨sl, sr, hsl, hsr, hseq⟩
  simp only [NatGcdFixCertificate.shape, Bool.and_eq_true] at hs
  rcases hs with ⟨⟨⟨⟨⟨htls, htrs⟩, hzls⟩, hzrs⟩, hsls⟩, hsrs⟩
  exact ⟨hcore,
    ⟨tl, tr, TrExprS.of_exprShapeEq (exprShapeEq_sound htls) htl,
      TrExprS.of_exprShapeEq (exprShapeEq_sound htrs) htr, hteq⟩,
    ⟨zl, zr, TrExprS.of_exprShapeEq (exprShapeEq_sound hzls) hzl,
      TrExprS.of_exprShapeEq (exprShapeEq_sound hzrs) hzr, hzeq⟩,
    ⟨sl, sr, TrExprS.of_exprShapeEq (exprShapeEq_sound hsls) hsl,
      TrExprS.of_exprShapeEq (exprShapeEq_sound hsrs) hsr, hseq⟩⟩

theorem checkNatGcdFixCertificate.WF {c : VContext} {s : VState}
    {core : NatWellFoundedCoreResult} {gcd : Expr}
    {fail : ∀ {α}, M α} :
    M.WF c s (checkNatGcdFixCertificate core gcd fail) fun out _ =>
      out.Valid c ∧ out.shape gcd = true := by
  simp only [checkNatGcdFixCertificate]
  refine M.WF.sandbox.bind fun cert _ _ _ => ?_
  split
  · rename_i hshape
    exact checkNatWellFoundedCertificate.WF.bind fun _ _ _ hcore =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ htop =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hzero =>
      checkNatWellFoundedEquation.WF.bind fun _ _ _ hsucc =>
        .pure ⟨⟨hcore, htop, hzero, hsucc⟩, hshape⟩
  · exact .throw

theorem unfoldNatWellFoundedNat2Cert.WF {c : VContext} {s : VState}
    {e eq_def equation : Expr} {fail : ∀ {α}, M α}
    (hnat : c.TrExprS q(Nat) .nat) (hnatTy : c.IsType .nat)
    (heq : natWellFoundedEquation e eq_def = some equation) :
    M.WF c s (unfoldNatWellFoundedNat2Cert e eq_def fail) fun out _ =>
      out.equation == equation ∧ out.Valid c := by
  simp only [unfoldNatWellFoundedNat2Cert, heq]
  have hraw : M.WF (c.withMLC c.mlctx) s
      (withLocalDecl `m .default q(Nat) fun m =>
        withLocalDecl `n .default q(Nat) fun n =>
          M.sandbox (unfoldNatWellFoundedCore e #[m, n] eq_def fail))
      (fun _ _ => True) := by
    refine .withLocalDecl hnat hnatTy .rfl fun m cwf₁ s₁ hs₁ hres₁ => ?_
    let c₁ := c.withMLC (.vlam m `m q(Nat) .nat .default c.mlctx)
      (wf := cwf₁)
    have hnat₁ : c₁.TrExprS q(Nat) .nat := by
      let .const h₁ h₂ h₃ := hnat
      exact .const h₁ h₂ h₃
    have hnatTy₁ : c₁.IsType .nat :=
      hnatTy.weakN c.Ewf (VLCtx.FVLift.skip_fvar _ _ .refl).toCtx
    refine .withLocalDecl hnat₁ hnatTy₁ .rfl
      fun n cwf₂ s₂ hs₂ hres₂ => ?_
    exact M.WF.sandbox.mono fun _ _ _ _ => trivial
  have hraw' : M.WF c s
      (withLocalDecl `m .default q(Nat) fun m =>
        withLocalDecl `n .default q(Nat) fun n =>
          M.sandbox (unfoldNatWellFoundedCore e #[m, n] eq_def fail))
      (fun _ _ => True) := by simpa using hraw
  refine hraw'.bind fun cert _ _ _ => ?_
  split
  · rename_i hequation
    exact checkNatWellFoundedCertificate.WF.bind fun _ _ _ hvalid =>
      .pure ⟨hequation, hvalid⟩
  · exact .throw

end Lean4Lean.Environment
