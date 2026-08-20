import Lean4Lean.Experimental.SExprClassified

/-!
# L4L-16N1: proof-carrying reducibility candidates

The observational `WShape` relation is deliberately not reused as the
normalization relation.  The definitions below retain operational weak-head
steps together with their evidence-rich equality certificate, and quantify
normalization over every typed context lift.  The recursive candidate index is
therefore a semantic step index; it is independent of the tree depth chosen by
`IsDefEqStrong.stratify` and cannot impose a false uniform bound on transitivity
middles.
-/

namespace Lean4Lean
namespace SExpr

open Lean4Lean

variable [Params]

namespace Reducibility

/-! ## Typed weak-head reduction -/

/-- One operational weak-head step paired with its evidence-rich equality at
the type preserved by the step.  In particular, a pattern contraction enters
this relation only through its finite `Pattern.Action` certificate. -/
structure WHStep (Γ : List SExpr) (M N A : SExpr) : Prop where
  red : WHRed Γ M N
  sound : IsDefEqStrong Γ M N A

/-- Lift a proof-carrying step through a genuine context extension. -/
theorem WHStep.weak' [Params.Semantic] (W : Ctx.Lift' ρ Γ Δ)
    (H : WHStep Γ M N A) :
    WHStep Δ (M.lift' ρ) (N.lift' ρ) (A.lift' ρ) :=
  ⟨H.red.weak' W, H.sound.weak' W⟩

/-- Congruence in the function position preserves the dependent result type. -/
theorem WHStep.app
    (H : WHStep Γ f f' (.forallE A B))
    (hA : IsDefEqStrong Γ A A (.sort u))
    (hB : IsDefEqStrong (A :: Γ) B B (.sort v))
    (ha : IsDefEqStrong Γ a a A)
    (hResult : IsDefEqStrong Γ (B.inst a) (B.inst a) (.sort v)) :
    WHStep Γ (.app f a) (.app f' a) (B.inst a) :=
  ⟨.app H.red, .appDF hA hB H.sound ha hResult⟩

/-- Congruence in a registered pattern's major argument, retaining the
dependent result conversion selected by the argument equality. -/
theorem WHStep.major
    (major : IsMajorPremise f)
    (H : WHStep Γ a a' A)
    (hA : IsDefEqStrong Γ A A (.sort u))
    (hB : IsDefEqStrong (A :: Γ) B B (.sort v))
    (hf : IsDefEqStrong Γ f f (.forallE A B))
    (hResult : IsDefEqStrong Γ (B.inst a) (B.inst a') (.sort v)) :
    WHStep Γ (.app f a) (.app f a') (B.inst a) :=
  ⟨.major major H.red, .appDF hA hB hf H.sound hResult⟩

/-- A beta contraction with both endpoint typings retained. -/
theorem WHStep.beta
    (hBody : IsDefEqStrong (A :: Γ) body body B)
    (hArg : IsDefEqStrong Γ arg arg A)
    (hApp : IsDefEqStrong Γ (.app (.lam A body) arg)
      (.app (.lam A body) arg) (B.inst arg))
    (hInst : IsDefEqStrong Γ (body.inst arg) (body.inst arg) (B.inst arg)) :
    WHStep Γ (.app (.lam A body) arg) (body.inst arg) (B.inst arg) :=
  ⟨.beta, .beta hBody hArg hApp hInst⟩

/-- A local extension contraction enters typed reduction through the same
action and endpoint evidence used by `IsDefEqStrong.extra`. -/
theorem WHStep.extra
    (action : Pattern.Action Γ r e m₁ m₂ A)
    (hLeft : IsDefEqStrong Γ e e A)
    (hRight : IsDefEqStrong Γ (r.1.applyS m₁ m₂)
      (r.1.applyS m₁ m₂) A) :
    WHStep Γ e (r.1.applyS m₁ m₂) A :=
  ⟨.extra action, .extra action hLeft hRight⟩

/-- Reflexive-transitive closure of proof-carrying weak-head steps.  Unlike
`WHRedS`, its type index makes subject preservation true by construction. -/
inductive WHSteps (Γ : List SExpr) : SExpr → SExpr → SExpr → Prop where
  | refl (typed : IsDefEqStrong Γ M M A) : WHSteps Γ M M A
  | tail (run : WHSteps Γ M N A) (step : WHStep Γ N P A) :
      WHSteps Γ M P A

/-- Forget the certificates and recover ordinary multi-step reduction. -/
theorem WHSteps.red (H : WHSteps Γ M N A) : WHRedS Γ M N := by
  induction H with
  | refl => exact .rfl
  | tail _ step ih => exact .tail ih step.red

/-- Compose the equality certificates retained by a typed reduction run. -/
theorem WHSteps.sound (H : WHSteps Γ M N A) : IsDefEqStrong Γ M N A := by
  induction H with
  | refl typed => exact typed
  | tail _ step ih => exact ih.trans step.sound

/-- A single typed step as a typed run. -/
theorem WHStep.toSteps (H : WHStep Γ M N A) : WHSteps Γ M N A :=
  .tail (.refl H.sound.hasType.1) H

/-- Typed runs compose without re-establishing subject reduction. -/
theorem WHSteps.trans (H₁ : WHSteps Γ M N A) (H₂ : WHSteps Γ N P A) :
    WHSteps Γ M P A := by
  induction H₂ with
  | refl => exact H₁
  | tail _ step ih => exact .tail (ih H₁) step

/-- Typed reduction is stable under context lifting. -/
theorem WHSteps.weak' [Params.Semantic] (W : Ctx.Lift' ρ Γ Δ)
    (H : WHSteps Γ M N A) :
    WHSteps Δ (M.lift' ρ) (N.lift' ρ) (A.lift' ρ) := by
  induction H with
  | refl typed => exact .refl (typed.weak' W)
  | tail _ step ih => exact .tail ih (step.weak' W)

/-- A typed run out of a weak-head normal subject is definitionally empty. -/
theorem WHSteps.eq_of_normal (normal : WHNF Γ M)
    (H : WHSteps Γ M N A) : M = N :=
  normal.whRedS H.red

/-- A proof-carrying weak-head normal form of `M` at `A`. -/
def WHResult (Γ : List SExpr) (M A : SExpr) : Prop :=
  ∃ result, WHSteps Γ M result A ∧ WHNF Γ result

/-- Prepend a typed reduction run to an already normalized result. -/
theorem WHResult.expand (run : WHSteps Γ M M' A)
    (H : WHResult Γ M' A) : WHResult Γ M A := by
  obtain ⟨result, steps, normal⟩ := H
  exact ⟨result, run.trans steps, normal⟩

/-! ## Kripke base and step-indexed layers -/

/-- Both endpoints normalize after every genuine context lift.  Quantifying
here, rather than trying to invert an arbitrary action produced only after a
lift, is the Kripke discipline used by the fundamental theorem. -/
def KripkeNormalizes (Γ : List SExpr) (M N A : SExpr) : Prop :=
  ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    WHResult Δ (M.lift' ρ) (A.lift' ρ) ∧
      WHResult Δ (N.lift' ρ) (A.lift' ρ)

/-- The non-recursive content of every candidate layer: a judgmental edge
and proof-carrying weak-head normalization in every future context. -/
structure Base (Γ : List SExpr) (M N A : SExpr) : Prop where
  edge : IsDefEqStrong Γ M N A
  normalizes : KripkeNormalizes Γ M N A

/-- Extract endpoint normalization in the current context. -/
theorem Base.results (H : Base Γ M N A) :
    WHResult Γ M A ∧ WHResult Γ N A :=
  by simpa using H.normalizes Ctx.Lift'.refl

/-- The Kripke base remains a base after a context lift. -/
theorem Base.weak' [Params.Semantic] (W : Ctx.Lift' ρ Γ Δ)
    (H : Base Γ M N A) :
    Base Δ (M.lift' ρ) (N.lift' ρ) (A.lift' ρ) where
  edge := H.edge.weak' W
  normalizes := by
    intro Θ ρ' W'
    simpa only [SExpr.lift'_comp] using H.normalizes (W.comp W')

/-- Backward expansion of the base candidate along certified reductions. -/
theorem Base.expand
    [Params.Semantic]
    (left : WHSteps Γ M M' A) (right : WHSteps Γ N N' A)
    (H : Base Γ M' N' A) : Base Γ M N A where
  edge := left.sound.trans (H.edge.trans right.sound.symm)
  normalizes := by
    intro Δ ρ W
    obtain ⟨hM, hN⟩ := H.normalizes W
    exact ⟨hM.expand (left.weak' W), hN.expand (right.weak' W)⟩

/-- The common type is proof-valued.  Candidate inhabitants at such a type
form a singleton by `IsDefEqStrong.proofIrrel`; no function observation may
extract data from them in the classified fragment. -/
def IsProofType (Γ : List SExpr) (A : SExpr) : Prop :=
  IsDefEqStrong Γ A A (.sort .zero)

/-- A four-place relation over contexts, endpoints, and their common type. -/
abbrev Rel := List SExpr → SExpr → SExpr → SExpr → Prop

/-- A heterogeneous type path whose individual edges are already related at
the preceding candidate index.  This is the PER-aware form consumed by the
Pi escape; forgetting the semantic payload recovers `TypeDefEqPath`. -/
inductive RelatedPath (R : Rel) (Γ : List SExpr) :
    SExpr → SExpr → SLevel → Prop where
  | single (edge : IsDefEqStrong Γ A B (.sort u))
      (related : R Γ A B (.sort u)) : RelatedPath R Γ A B u
  | trans (left : RelatedPath R Γ A B u)
      (right : RelatedPath R Γ B C v) : RelatedPath R Γ A C u

/-- Forget candidate evidence on a related heterogeneous path. -/
theorem RelatedPath.toTypeDefEqPath
    (H : RelatedPath R Γ A B u) : TypeDefEqPath Γ A B u := by
  induction H with
  | single edge => exact .single edge.defeq
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- The Kripke function clause.  It is present even at proof-valued function
types: singleton interpretation erases observable data, but normalization of
an application still needs the function candidate's action. -/
structure ActionLayer (R : Rel) (Γ : List SExpr) (M N A : SExpr) : Prop where
  apply :
    ∀ {Δ : List SExpr} {ρ : Lift} {D C : SExpr} {s : SLevel},
      Ctx.Lift' ρ Γ Δ →
      WHSteps Δ (A.lift' ρ) (.forallE D C) (.sort s) →
      ∀ {a b : SExpr}, R Δ a b D →
        R Δ ((M.lift' ρ).app a) ((N.lift' ρ).app b) (C.inst a)

/-- Matching weak-head observations for related type expressions.  Recursive
component paths use only the strictly preceding semantic index, never a bound
on the typing derivation. -/
structure HeadLayer (R : Rel) (Γ : List SExpr) (M N A : SExpr) : Prop where
  piHead :
    ∀ {Δ : List SExpr} {ρ : Lift} {D C : SExpr},
      Ctx.Lift' ρ Γ Δ →
      WHRedS Δ (M.lift' ρ) (.forallE D C) →
      ∃ D' C',
        WHSteps Δ (N.lift' ρ) (.forallE D' C') (A.lift' ρ) ∧
          ∃ u v,
            RelatedPath R Δ D D' u ∧
              RelatedPath R (D :: Δ) C C' v
  sortHead :
    ∀ {Δ : List SExpr} {ρ : Lift} {u : SLevel},
      Ctx.Lift' ρ Γ Δ →
      WHRedS Δ (M.lift' ρ) (.sort u) →
      WHSteps Δ (N.lift' ρ) (.sort u) (A.lift' ρ)

/-- Step-indexed typed reducibility.  Index zero records only judgmental
soundness and Kripke weak-head normalization.  At a successor, every type
exposes function action; proof-valued types then use the singleton branch,
while all other types expose matching type-head observations through the
preceding index. -/
def Candidate : Nat → Rel
  | 0 => Base
  | depth + 1 => fun Γ M N A =>
      Candidate depth Γ M N A ∧
        ActionLayer (Candidate depth) Γ M N A ∧
          (IsProofType Γ A ∨ HeadLayer (Candidate depth) Γ M N A)

/-- Every successor candidate retains the preceding observation. -/
theorem Candidate.lower
    (H : Candidate (depth + 1) Γ M N A) : Candidate depth Γ M N A :=
  H.1

/-- Every candidate contains the Kripke normalization base. -/
theorem Candidate.base :
    Candidate depth Γ M N A → Base Γ M N A := by
  induction depth with
  | zero => exact id
  | succ depth ih => exact fun H => ih H.1

/-- Reducibility is Kripke: every candidate edge survives a typed context
lift.  The successor clauses compose the requested future lift with the one
already taken; no normalization result itself has to be inverted. -/
theorem Candidate.weak' [Params.Semantic] :
    ∀ depth, Ctx.Lift' ρ Γ Δ → Candidate depth Γ M N A →
      Candidate depth Δ (M.lift' ρ) (N.lift' ρ) (A.lift' ρ)
  | 0, W, H => Base.weak' W H
  | depth + 1, W, H => by
      refine ⟨Candidate.weak' depth W H.1, ?_, ?_⟩
      · refine {
          apply := ?_ }
        intro Θ ρ' D C s W' hA a b hab
        have hA' : WHSteps Θ (A.lift' (ρ.comp ρ'))
            (.forallE D C) (.sort s) := by
          simpa only [SExpr.lift'_comp] using hA
        simpa only [SExpr.lift'_comp] using
          H.2.1.apply (W.comp W') hA' hab
      cases H.2.2 with
      | inl proofType => exact .inl (proofType.weak' W)
      | inr heads =>
        refine .inr {
          piHead := ?_
          sortHead := ?_ }
        · intro Θ ρ' D C W' hM
          have hM' : WHRedS Θ (M.lift' (ρ.comp ρ'))
              (.forallE D C) := by
            simpa only [SExpr.lift'_comp] using hM
          simpa only [SExpr.lift'_comp] using
            heads.piHead (W.comp W') hM'
        · intro Θ ρ' u W' hM
          have hM' : WHRedS Θ (M.lift' (ρ.comp ρ')) (.sort u) := by
            simpa only [SExpr.lift'_comp] using hM
          simpa only [SExpr.lift'_comp] using
            heads.sortHead (W.comp W') hM'

/-- Proof-valued candidates are singleton layers at every semantic index. -/
theorem Candidate.ofProof (base : Base Γ M N A)
    (proofType : IsProofType Γ A)
    (actions : ∀ depth, ActionLayer (Candidate depth) Γ M N A) :
    ∀ depth, Candidate depth Γ M N A
  | 0 => base
  | depth + 1 =>
      ⟨Candidate.ofProof base proofType actions depth,
        actions depth, .inl proofType⟩

/-- Construct the base edge of a proof singleton from endpoint typings and
Kripke normalization. -/
theorem Base.ofProof
    (proofType : IsDefEqStrong Γ A A (.sort .zero))
    (left : IsDefEqStrong Γ M M A) (right : IsDefEqStrong Γ N N A)
    (normalizes : KripkeNormalizes Γ M N A) : Base Γ M N A :=
  ⟨.proofIrrel proofType left right, normalizes⟩

/-- Every successor candidate exposes its Kripke function action. -/
theorem Candidate.action
    (H : Candidate (depth + 1) Γ M N A) :
    ActionLayer (Candidate depth) Γ M N A :=
  H.2.1

/-- A successor data candidate exposes matching head observations once the
proof singleton alternative is ruled out. -/
theorem Candidate.heads
    (H : Candidate (depth + 1) Γ M N A)
    (notProof : ¬IsProofType Γ A) :
    HeadLayer (Candidate depth) Γ M N A :=
  H.2.2.resolve_left notProof

/-! ## Canonical universe candidates -/

/-- A universe is never itself proof-valued.  Shape soundness sees the
nonzero successor level of its intrinsic type against the zero bit demanded
by `Prop`. -/
theorem IsProofType.sort_false (u : SLevel) :
    ¬IsProofType Γ (.sort u) := by
  intro H
  have sound := (LE_Interp.strongSound H).left
  cases sound with
  | mk _ _ core typeEq =>
    cases core with
    | sort =>
      have hz := SoundEq.sort.1 typeEq
      exact (hz.mp (by simp)) (by simp)

/-- The canonical universe normalizes in every future context. -/
theorem Base.sort : Base Γ (.sort u) (.sort u) (.sort u.succ) where
  edge := .sort
  normalizes := by
    intro Δ ρ W
    simp only [SExpr.lift']
    exact ⟨⟨.sort u, .refl .sort, WHNF.sort⟩,
      ⟨.sort u, .refl .sort, WHNF.sort⟩⟩

/-- Canonical universes inhabit every semantic index. -/
theorem Candidate.sort : ∀ depth,
    Candidate depth Γ (.sort u) (.sort u) (.sort u.succ)
  | 0 => Base.sort
  | depth + 1 => by
      refine ⟨Candidate.sort depth, ?_, .inr ?_⟩
      · refine { apply := ?_ }
        intro Δ ρ D C s W hA a b hab
        have bad : (.sort u.succ : SExpr) = .forallE D C := by
          simpa only [SExpr.lift'] using hA.eq_of_normal WHNF.sort
        cases bad
      · refine {
          piHead := ?_
          sortHead := ?_ }
        · intro Δ ρ D C W hM
          have bad : (.sort u : SExpr) = .forallE D C := by
            simpa only [SExpr.lift'] using WHNF.sort.whRedS hM
          cases bad
        · intro Δ ρ u' W hM
          have hu : (.sort u : SExpr) = .sort u' := by
            simpa only [SExpr.lift'] using WHNF.sort.whRedS hM
          cases hu
          simpa only [SExpr.lift'] using
            (WHSteps.refl (Γ := Δ) (M := .sort u)
              (A := .sort u.succ) IsDefEqStrong.sort)

/-- Canonical Pi formation preserves reducibility at every index when its
domain and codomain do.  The Pi-head clause records one related singleton
edge for each component after any future context lift. -/
theorem Candidate.forallE
    [Params.Semantic]
    (domain : ∀ depth, Candidate depth Γ A A (.sort u))
    (codomain : ∀ depth, Candidate depth (A :: Γ) B B (.sort v)) :
    ∀ depth, Candidate depth Γ (.forallE A B) (.forallE A B)
      (.sort (.imax u v))
  | 0 => by
      let typed : IsDefEqStrong Γ (.forallE A B) (.forallE A B)
          (.sort (.imax u v)) :=
        .forallEDF (domain 0).edge (codomain 0).edge (codomain 0).edge
      exact {
        edge := typed
        normalizes := by
          intro Δ ρ W
          let typed' := typed.weak' W
          exact ⟨⟨_, .refl typed', WHNF.forallE⟩,
            ⟨_, .refl typed', WHNF.forallE⟩⟩ }
  | depth + 1 => by
      refine ⟨Candidate.forallE domain codomain depth, ?_, .inr ?_⟩
      · refine { apply := ?_ }
        intro Δ ρ D C s W hType a b hab
        have bad : (.sort (.imax u v) : SExpr) = .forallE D C := by
          simpa only [SExpr.lift'] using hType.eq_of_normal WHNF.sort
        cases bad
      · refine {
          piHead := ?_
          sortHead := ?_ }
        · intro Δ ρ D C W hLeft
          have eqLeft :
              (.forallE (A.lift' ρ) (B.lift' ρ.cons) : SExpr) =
                .forallE D C := by
            simpa only [SExpr.lift'] using WHNF.forallE.whRedS hLeft
          injection eqLeft with hD hC
          subst D
          subst C
          have domain' := Candidate.weak' depth W (domain depth)
          have codomain' := Candidate.weak' depth W.cons (codomain depth)
          have domainRel : Candidate depth Δ (A.lift' ρ) (A.lift' ρ)
              (.sort u) := by simpa only [SExpr.lift'] using domain'
          have codomainRel : Candidate depth (A.lift' ρ :: Δ)
              (B.lift' ρ.cons) (B.lift' ρ.cons) (.sort v) := by
            simpa only [SExpr.lift'] using codomain'
          let rightTyped : IsDefEqStrong Δ
              (.forallE (A.lift' ρ) (B.lift' ρ.cons))
              (.forallE (A.lift' ρ) (B.lift' ρ.cons))
              (.sort (.imax u v)) :=
            .forallEDF domainRel.base.edge codomainRel.base.edge
              codomainRel.base.edge
          exact ⟨A.lift' ρ, B.lift' ρ.cons,
            by simpa only [SExpr.lift'] using
              (WHSteps.refl (Γ := Δ) (M := .forallE (A.lift' ρ) (B.lift' ρ.cons))
                (A := .sort (.imax u v)) rightTyped),
            u, v,
            .single domainRel.base.edge domainRel,
            .single codomainRel.base.edge codomainRel⟩
        · intro Δ ρ u' W hLeft
          have bad :
              (.forallE (A.lift' ρ) (B.lift' ρ.cons) : SExpr) = .sort u' := by
            simpa only [SExpr.lift'] using WHNF.forallE.whRedS hLeft
          cases bad

/-! ## Fundamental-theorem interface and Pi escape -/

/-- The N3 target at one semantic index.  The statement is intentionally
context-generic; context validity is needed only when a weak edge is upgraded
to its evidence-rich form at a consumer. -/
def Fundamental (depth : Nat) : Prop :=
  ∀ {Γ : List SExpr} {M N A : SExpr},
    IsDefEqStrong Γ M N A → Candidate depth Γ M N A

/-- Propagate one observed Pi head through a heterogeneous type path.  Each
edge's candidate produces the next typed weak-head run.  Only the untyped
reduction trace is passed to the following edge, so adjacent universe indices
need not be identified. -/
theorem TypeDefEqPath.piForward
    [Params.Semantic]
    (fundamental : Fundamental 1) (hΓ : Ctx.WF Γ)
    (H : TypeDefEqPath Γ X Y s)
    (head : WHRedS Γ X (.forallE D C)) :
    ∃ D' C', WHRedS Γ Y (.forallE D' C') ∧
      ∃ u v, TypeDefEqPath Γ D D' u ∧
        TypeDefEqPath (D :: Γ) C C' v := by
  induction H generalizing D C with
  | @single A B u edge =>
    have candidate := fundamental (edge.strong hΓ)
    have layer := candidate.heads (IsProofType.sort_false u)
    have observed : WHRedS Γ A (.forallE D C) := by
      simpa using head
    have observed' : WHRedS Γ (A.lift' Lift.refl) (.forallE D C) := by
      simpa using observed
    obtain ⟨D', C', run, du, cu, domain, codomain⟩ :=
      layer.piHead Ctx.Lift'.refl observed'
    have runRed : WHRedS Γ B (.forallE D' C') := by
      simpa using run.red
    refine ⟨D', C', runRed, du, cu, ?_, ?_⟩
    · exact domain.toTypeDefEqPath
    · exact codomain.toTypeDefEqPath
  | @trans A B Z u v left right ihLeft ihRight =>
    obtain ⟨D₁, C₁, red₁, du₁, cu₁, domain₁, codomain₁⟩ :=
      ihLeft head
    obtain ⟨D₂, C₂, red₂, du₂, cu₂, domain₂, codomain₂⟩ :=
      ihRight red₁
    obtain ⟨_, domain₁Symm⟩ := domain₁.symm
    have codomain₂' := domain₁Symm.defeqDF_l_path codomain₂
    exact ⟨D₂, C₂, red₂, du₁, cu₁,
      domain₁.trans domain₂, codomain₁.trans codomain₂'⟩

/-- A candidate fundamental theorem at index one is already sufficient to
escape related Pi heads to the path-valued injectivity leaf. -/
theorem LRS.PiPathInv.of_candidateFundamental
    [Params.Semantic]
    (fundamental : Fundamental 1) : LRS.PiPathInv := by
  intro Γ A B A' B' s hΓ path
  obtain ⟨D, C, red, u, v, domain, codomain⟩ :=
    TypeDefEqPath.piForward fundamental hΓ path
      (.rfl : WHRedS Γ (.forallE A B) (.forallE A B))
  have headEq : (.forallE A' B' : SExpr) = .forallE D C :=
    WHNF.forallE.whRedS red
  injection headEq with hD hC
  subst D
  subst C
  exact ⟨u, v, domain, codomain⟩

/-! Axiom pins: N1's relation kernel uses only the accepted logical baseline. -/

/-- info: 'Lean4Lean.SExpr.Reducibility.WHSteps.sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WHSteps.sound

/-- info: 'Lean4Lean.SExpr.Reducibility.Base.expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Base.expand

/-- info: 'Lean4Lean.SExpr.Reducibility.RelatedPath.toTypeDefEqPath' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RelatedPath.toTypeDefEqPath

/--
info: 'Lean4Lean.SExpr.Reducibility.LRS.PiPathInv.of_candidateFundamental' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LRS.PiPathInv.of_candidateFundamental

end Reducibility
end SExpr
end Lean4Lean
