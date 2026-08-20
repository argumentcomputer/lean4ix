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

/-- Retype a certified run along an evidence-rich type equality. -/
theorem WHSteps.defeqDF (typeEq : IsDefEqStrong Γ A B (.sort u))
    (H : WHSteps Γ M N A) : WHSteps Γ M N B := by
  induction H with
  | refl typed => exact .refl (.defeqDF typeEq typed)
  | tail _ step ih =>
    exact .tail (ih typeEq) ⟨step.red, .defeqDF typeEq step.sound⟩

/-- Congruence of a typed run in function position, with the function type
kept as a variable so induction can refine the indexed closure. -/
private theorem WHSteps.appAux
    (H : WHSteps Γ f f' T) (hT : T = SExpr.forallE A B)
    (hA : IsDefEqStrong Γ A A (.sort u))
    (hB : IsDefEqStrong (A :: Γ) B B (.sort v))
    (ha : IsDefEqStrong Γ a a A)
    (hResult : IsDefEqStrong Γ (B.inst a) (B.inst a) (.sort v)) :
    WHSteps Γ (.app f a) (.app f' a) (B.inst a) := by
  induction H generalizing A B a with
  | refl typed =>
    cases hT
    exact .refl (.appDF hA hB typed ha hResult)
  | tail _ step ih =>
    cases hT
    exact .tail (ih rfl hA hB ha hResult) (step.app hA hB ha hResult)

/-- Congruence of a typed run in function position. -/
theorem WHSteps.app
    (H : WHSteps Γ f f' (.forallE A B))
    (hA : IsDefEqStrong Γ A A (.sort u))
    (hB : IsDefEqStrong (A :: Γ) B B (.sort v))
    (ha : IsDefEqStrong Γ a a A)
    (hResult : IsDefEqStrong Γ (B.inst a) (B.inst a) (.sort v)) :
    WHSteps Γ (.app f a) (.app f' a) (B.inst a) :=
  H.appAux rfl hA hB ha hResult

/-- Instantiate a codomain along an evidence-rich argument equality.  The
weak heterogeneous substitution theorem supplies the equation and target
context validity upgrades it without invoking type uniqueness. -/
theorem IsDefEqStrong.instCongr [Params.Semantic]
    (hΓ : Ctx.WF Γ)
    (hD : IsDefEqStrong Γ D D (.sort u))
    (hC : IsDefEqStrong (D :: Γ) C C (.sort v))
    (hab : IsDefEqStrong Γ a b D) :
    IsDefEqStrong Γ (C.inst a) (C.inst b) (.sort v) := by
  let W : Ctx.SubstEq Γ (.one a) (.one b) (D :: Γ) := by
    refine .cons (u := u) ?_ hD.defeq ?_
    · exact .nil
    · simpa only [Subst.head_cons, Subst.tail_cons, SExpr.subst_id] using
        hab.defeq
  have weak := hC.subst W
  change IsDefEq Γ (C.inst a) (C.inst b) (.sort v) at weak
  exact weak.strong hΓ

/-- A typed run out of a weak-head normal subject is definitionally empty. -/
theorem WHSteps.eq_of_normal (normal : WHNF Γ M)
    (H : WHSteps Γ M N A) : M = N :=
  normal.whRedS H.red

/-- A non-reflexive certified run exposes a certified first step.  This
small elimination principle is used below to state the exact circularity of
subject-preserving normalization without depending on the representation of
`ReflTransGen`. -/
theorem WHSteps.eq_or_first (H : WHSteps Γ M N A) :
    M = N ∨ ∃ P, WHStep Γ M P A := by
  induction H with
  | refl => exact .inl rfl
  | tail _ step ih =>
    cases ih with
    | inl eq =>
      subst eq
      exact .inr ⟨_, step⟩
    | inr first => exact .inr first

/-- An operational weak-head normal form of `M`.

The displayed type remains an index so callers do not lose their candidate
orientation, but the reduction trace itself is intentionally untyped.
Demanding a `WHSteps` trace here would already demand `LRS.BetaFire`: a beta
redex may be typed through a heterogeneous path between its abstraction's Pi
and its application's Pi, and certifying that contraction at the displayed
type is exactly the Pi-inversion leaf being proved.  Proof evidence therefore
lives on `Base.edge` and on each local `Pattern.Action`, not on every link of
the normalization trace. -/
def WHResult (Γ : List SExpr) (M _A : SExpr) : Prop :=
  ∃ result, WHRedS Γ M result ∧ WHNF Γ result

/-- Prepend a typed reduction run to an already normalized result. -/
theorem WHResult.expand (run : WHSteps Γ M M' A)
    (H : WHResult Γ M' A) : WHResult Γ M A := by
  obtain ⟨result, steps, normal⟩ := H
  exact ⟨result, run.red.trans steps, normal⟩

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

/-- The base relation is a PER.  Endpoint projections retain precisely the
normalization half selected by their evidence-rich self-typing. -/
theorem Base.left (H : Base Γ M N A) : Base Γ M M A where
  edge := H.edge.hasType.1
  normalizes := by
    intro Δ ρ W
    exact ⟨(H.normalizes W).1, (H.normalizes W).1⟩

theorem Base.right (H : Base Γ M N A) : Base Γ N N A where
  edge := H.edge.hasType.2
  normalizes := by
    intro Δ ρ W
    exact ⟨(H.normalizes W).2, (H.normalizes W).2⟩

theorem Base.symm (H : Base Γ M N A) : Base Γ N M A where
  edge := H.edge.symm
  normalizes := by
    intro Δ ρ W
    exact ⟨(H.normalizes W).2, (H.normalizes W).1⟩

theorem Base.trans (H₁ : Base Γ M N A) (H₂ : Base Γ N P A) :
    Base Γ M P A where
  edge := H₁.edge.trans H₂.edge
  normalizes := by
    intro Δ ρ W
    exact ⟨(H₁.normalizes W).1, (H₂.normalizes W).2⟩

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
inductive RelatedPath (R : Rel) :
    List SExpr → SExpr → SExpr → SLevel → Prop where
  | single (edge : IsDefEqStrong Γ A B (.sort u))
      (related : R Γ A B (.sort u)) : RelatedPath R Γ A B u
  | trans (left : RelatedPath R Γ A B u)
      (right : RelatedPath R Γ B C v) : RelatedPath R Γ A C u
  | defeqDF_l (context : TypeDefEqPath Γ A B u)
      (path : RelatedPath R (A :: Γ) C D v) :
      RelatedPath R (B :: Γ) C D v

/-- Forget candidate evidence on a related heterogeneous path. -/
theorem RelatedPath.toTypeDefEqPath
    (H : RelatedPath R Γ A B u) : TypeDefEqPath Γ A B u := by
  induction H with
  | single edge => exact .single edge.defeq
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | defeqDF_l context _ ih => exact context.defeqDF_l_path ih

/-- Reverse a related path whenever its edge relation is symmetric.  As for
`TypeDefEqPath.symm`, the last native edge selects the returned universe. -/
theorem RelatedPath.symm
    (symmR : ∀ {Δ X Y T}, R Δ X Y T → R Δ Y X T)
    (H : RelatedPath R Γ A B u) : ∃ v, RelatedPath R Γ B A v := by
  induction H with
  | single edge related => exact ⟨_, .single edge.symm (symmR related)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨v₂, right⟩ := ih₂
    obtain ⟨_, left⟩ := ih₁
    exact ⟨v₂, .trans right left⟩
  | defeqDF_l context _ ih =>
    obtain ⟨v, path⟩ := ih
    exact ⟨v, .defeqDF_l context path⟩

/-- The Kripke function clause.  It is present even at proof-valued function
types: singleton interpretation erases observable data, but normalization of
an application still needs the function candidate's action. -/
structure ActionLayer (R : Rel) (Γ : List SExpr) (M N A : SExpr) : Prop where
  apply :
    ∀ {Δ : List SExpr} {ρ : Lift} {D C : SExpr} {s : SLevel},
      Ctx.Lift' ρ Γ Δ →
      Ctx.WF Δ →
      WHSteps Δ (A.lift' ρ) (.forallE D C) (.sort s) →
      ∀ {a b : SExpr} {u v : SLevel}, R Δ a b D →
        IsDefEqStrong Δ D D (.sort u) →
        IsDefEqStrong (D :: Δ) C C (.sort v) →
        IsDefEqStrong Δ (C.inst a) (C.inst b) (.sort v) →
        R Δ ((M.lift' ρ).app a) ((N.lift' ρ).app b) (C.inst a)

/-- Matching weak-head observations for related type expressions.  Recursive
component paths use only the strictly preceding semantic index, never a bound
on the typing derivation. -/
structure HeadLayer (R : Rel) (Γ : List SExpr) (M N A : SExpr) : Prop where
  piHead :
    ∀ {Δ : List SExpr} {ρ : Lift} {D C : SExpr} {s t : SLevel},
      Ctx.Lift' ρ Γ Δ →
      WHSteps Δ (A.lift' ρ) (.sort s) (.sort t) →
      WHRedS Δ (M.lift' ρ) (.forallE D C) →
      ∃ D' C',
        WHRedS Δ (N.lift' ρ) (.forallE D' C') ∧
          ∃ u v,
            RelatedPath R Δ D D' u ∧
              RelatedPath R (D :: Δ) C C' v
  sortHead :
    ∀ {Δ : List SExpr} {ρ : Lift} {s t u : SLevel},
      Ctx.Lift' ρ Γ Δ →
      WHSteps Δ (A.lift' ρ) (.sort s) (.sort t) →
      WHRedS Δ (M.lift' ρ) (.sort u) →
      WHRedS Δ (N.lift' ρ) (.sort u)

/-- A successor candidate records both orientations explicitly.  This makes
the PER symmetry case structural and prevents the fundamental theorem from
trying to recover reverse head normalization from an oriented observation. -/
structure Layer (R : Rel) (Γ : List SExpr) (M N A : SExpr) : Prop where
  forwardAction : ActionLayer R Γ M N A
  reverseAction : ActionLayer R Γ N M A
  heads : IsProofType Γ A ∨
    (HeadLayer R Γ M N A ∧ HeadLayer R Γ N M A)

/-- Pointwise partial-equivalence laws for a typed four-place relation. -/
structure RelPER (R : Rel) : Prop where
  left : ∀ {Γ M N A}, R Γ M N A → R Γ M M A
  right : ∀ {Γ M N A}, R Γ M N A → R Γ N N A
  symm : ∀ {Γ M N A}, R Γ M N A → R Γ N M A
  trans : ∀ {Γ M N P A}, R Γ M N A → R Γ N P A → R Γ M P A

/-- Compose oriented head observations.  The second codomain path is moved
back to the first domain context through an explicit path constructor; no
universe equality or path collapse is used. -/
theorem HeadLayer.trans
    (left : HeadLayer R Γ M N A) (right : HeadLayer R Γ N P A) :
    HeadLayer R Γ M P A where
  piHead := by
    intro Δ ρ D C s t W typeRun observed
    obtain ⟨D₁, C₁, run₁, du₁, cu₁, domain₁, codomain₁⟩ :=
      left.piHead W typeRun observed
    obtain ⟨D₂, C₂, run₂, du₂, cu₂, domain₂, codomain₂⟩ :=
      right.piHead W typeRun run₁
    obtain ⟨_, domain₁Symm⟩ := domain₁.toTypeDefEqPath.symm
    exact ⟨D₂, C₂, run₂, du₁, cu₁,
      .trans domain₁ domain₂,
      .trans codomain₁ (.defeqDF_l domain₁Symm codomain₂)⟩
  sortHead := by
    intro Δ ρ s t u W typeRun observed
    have run₁ := left.sortHead W typeRun observed
    exact right.sortHead W typeRun run₁

/-- Step-indexed typed reducibility.  Index zero records only judgmental
soundness and Kripke weak-head normalization.  At a successor, every type
exposes function action; proof-valued types then use the singleton branch,
while all other types expose matching type-head observations through the
preceding index. -/
def Candidate : Nat → Rel
  | 0 => Base
  | depth + 1 => fun Γ M N A =>
      Candidate depth Γ M N A ∧
        Layer (Candidate depth) Γ M N A

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
      refine ⟨Candidate.weak' depth W H.1, ?_⟩
      let weakAction : ∀ {X Y : SExpr},
          ActionLayer (Candidate depth) Γ X Y A →
          ActionLayer (Candidate depth) Δ (X.lift' ρ) (Y.lift' ρ)
            (A.lift' ρ) := by
        intro X Y action
        refine { apply := ?_ }
        intro Θ ρ' D C s W' hTheta hA a b u v hab hD hC hResult
        have hA' : WHSteps Θ (A.lift' (ρ.comp ρ'))
            (.forallE D C) (.sort s) := by
          simpa only [SExpr.lift'_comp] using hA
        simpa only [SExpr.lift'_comp] using
          action.apply (W.comp W') hTheta hA' hab hD hC hResult
      let weakHeads : ∀ {X Y : SExpr},
          HeadLayer (Candidate depth) Γ X Y A →
          HeadLayer (Candidate depth) Δ (X.lift' ρ) (Y.lift' ρ)
            (A.lift' ρ) := by
        intro X Y heads
        refine {
          piHead := ?_
          sortHead := ?_ }
        · intro Θ ρ' D C s t W' hType hM
          have hType' : WHSteps Θ (A.lift' (ρ.comp ρ'))
              (.sort s) (.sort t) := by
            simpa only [SExpr.lift'_comp] using hType
          have hM' : WHRedS Θ (X.lift' (ρ.comp ρ'))
              (.forallE D C) := by
            simpa only [SExpr.lift'_comp] using hM
          simpa only [SExpr.lift'_comp] using
            heads.piHead (W.comp W') hType' hM'
        · intro Θ ρ' s t u W' hType hM
          have hType' : WHSteps Θ (A.lift' (ρ.comp ρ'))
              (.sort s) (.sort t) := by
            simpa only [SExpr.lift'_comp] using hType
          have hM' : WHRedS Θ (X.lift' (ρ.comp ρ')) (.sort u) := by
            simpa only [SExpr.lift'_comp] using hM
          simpa only [SExpr.lift'_comp] using
            heads.sortHead (W.comp W') hType' hM'
      refine {
        forwardAction := weakAction H.2.forwardAction
        reverseAction := weakAction H.2.reverseAction
        heads := ?_ }
      cases H.2.heads with
      | inl proofType => exact .inl (proofType.weak' W)
      | inr heads => exact .inr ⟨weakHeads heads.1, weakHeads heads.2⟩

/-- Proof-valued candidates are singleton layers at every semantic index. -/
theorem Candidate.ofProof (base : Base Γ M N A)
    (proofType : IsProofType Γ A)
    (forward : ∀ depth, ActionLayer (Candidate depth) Γ M N A)
    (reverse : ∀ depth, ActionLayer (Candidate depth) Γ N M A) :
    ∀ depth, Candidate depth Γ M N A
  | 0 => base
  | depth + 1 =>
      ⟨Candidate.ofProof base proofType forward reverse depth,
        ⟨forward depth, reverse depth, .inl proofType⟩⟩

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
  H.2.forwardAction

/-- The reverse Kripke function action is stored at the same layer. -/
theorem Candidate.reverseAction
    (H : Candidate (depth + 1) Γ M N A) :
    ActionLayer (Candidate depth) Γ N M A :=
  H.2.reverseAction

/-- A successor data candidate exposes matching head observations once the
proof singleton alternative is ruled out. -/
theorem Candidate.heads
    (H : Candidate (depth + 1) Γ M N A)
    (notProof : ¬IsProofType Γ A) :
    HeadLayer (Candidate depth) Γ M N A :=
  (H.2.heads.resolve_left notProof).1

/-- Matching observations in the reverse orientation. -/
theorem Candidate.reverseHeads
    (H : Candidate (depth + 1) Γ M N A)
    (notProof : ¬IsProofType Γ A) :
    HeadLayer (Candidate depth) Γ N M A :=
  (H.2.heads.resolve_left notProof).2

/-- Candidate symmetry is structural because every successor stores both
orientations of its observable layer. -/
theorem Candidate.symm (H : Candidate depth Γ M N A) :
    Candidate depth Γ N M A := by
  induction depth with
  | zero =>
      change Base Γ M N A at H
      change Base Γ N M A
      exact H.symm
  | succ depth ih =>
      refine ⟨ih H.1, ?_⟩
      refine {
        forwardAction := H.2.reverseAction
        reverseAction := H.2.forwardAction
        heads := ?_ }
      cases H.2.heads with
      | inl proofType => exact .inl proofType
      | inr heads => exact .inr ⟨heads.2, heads.1⟩

/-- Every semantic index is a partial equivalence relation.  At a successor,
application transitivity factors through the left argument endpoint at the
preceding index, while head transitivity uses `HeadLayer.trans`. -/
theorem Candidate.relPER : ∀ depth, RelPER (Candidate depth) := by
  intro depth
  induction depth with
  | zero =>
      exact {
        left := Base.left
        right := Base.right
        symm := Base.symm
        trans := Base.trans }
  | succ depth lower =>
      let leftCandidate : ∀ {Γ M N A},
          Candidate (depth + 1) Γ M N A →
          Candidate (depth + 1) Γ M M A := by
        intro Γ M N A H
        let action : ActionLayer (Candidate depth) Γ M M A := {
          apply := by
            intro Δ ρ D C s W hDelta hType a b u v hab hD hC hResult
            have first := H.2.forwardAction.apply W hDelta hType
              (lower.left hab) hD hC hResult.hasType.1
            have second := H.2.reverseAction.apply W hDelta hType hab
              hD hC hResult
            exact lower.trans first second }
        refine ⟨lower.left H.1, {
          forwardAction := action
          reverseAction := action
          heads := ?_ }⟩
        cases H.2.heads with
        | inl proofType => exact .inl proofType
        | inr heads =>
          let self := heads.1.trans heads.2
          exact .inr ⟨self, self⟩
      let transCandidate : ∀ {Γ M N P A},
          Candidate (depth + 1) Γ M N A →
          Candidate (depth + 1) Γ N P A →
          Candidate (depth + 1) Γ M P A := by
        intro Γ M N P A H₁ H₂
        let forward : ActionLayer (Candidate depth) Γ M P A := {
          apply := by
            intro Δ ρ D C s W hDelta hType a b u v hab hD hC hResult
            have first := H₁.2.forwardAction.apply W hDelta hType
              (lower.left hab) hD hC hResult.hasType.1
            have second := H₂.2.forwardAction.apply W hDelta hType hab
              hD hC hResult
            exact lower.trans first second }
        let reverse : ActionLayer (Candidate depth) Γ P M A := {
          apply := by
            intro Δ ρ D C s W hDelta hType a b u v hab hD hC hResult
            have first := H₂.2.reverseAction.apply W hDelta hType
              (lower.left hab) hD hC hResult.hasType.1
            have second := H₁.2.reverseAction.apply W hDelta hType hab
              hD hC hResult
            exact lower.trans first second }
        refine ⟨lower.trans H₁.1 H₂.1, {
          forwardAction := forward
          reverseAction := reverse
          heads := ?_ }⟩
        cases h₁ : H₁.2.heads with
        | inl proofType => exact .inl proofType
        | inr heads₁ =>
          cases h₂ : H₂.2.heads with
          | inl proofType => exact .inl proofType
          | inr heads₂ =>
            exact .inr ⟨heads₁.1.trans heads₂.1,
              heads₂.2.trans heads₁.2⟩
      exact {
        left := leftCandidate
        right := fun H => leftCandidate H.symm
        symm := Candidate.symm
        trans := transCandidate }

theorem Candidate.left (H : Candidate depth Γ M N A) :
    Candidate depth Γ M M A :=
  (Candidate.relPER depth).left H

theorem Candidate.right (H : Candidate depth Γ M N A) :
    Candidate depth Γ N N A :=
  (Candidate.relPER depth).right H

theorem Candidate.trans (H₁ : Candidate depth Γ M N A)
    (H₂ : Candidate depth Γ N P A) : Candidate depth Γ M P A :=
  (Candidate.relPER depth).trans H₁ H₂

/-! ## Neutral candidates -/

/-- A variable-headed application spine.  Such a term cannot match a
registered constant-headed pattern or become a major premise. -/
inductive Neutral : SExpr → Prop where
  | bvar : Neutral (.bvar i)
  | app : Neutral f → Neutral (.app f a)

theorem Neutral.lift' (H : Neutral M) : Neutral (M.lift' ρ) := by
  induction H with
  | bvar => exact .bvar
  | app _ ih => exact .app ih

theorem Neutral.noMatches (H : Neutral M) {p : Pattern}
    {m₁ : List SLevel} {m₂ : p.Path → SExpr} :
    ¬ Pattern.MatchesS p M m₁ m₂ := by
  intro matched
  induction H generalizing p m₁ m₂ with
  | bvar => nomatch matched
  | app _ ih =>
    cases matched with
    | var head => exact ih head
    | app head _ => exact ih head

theorem Neutral.notMajor (H : Neutral M) : ¬IsMajorPremise M := by
  rintro ⟨p, ⟨r, hpat⟩, p₁, p₂, sub, m₁, m₂, matched⟩
  exact H.noMatches matched

theorem Neutral.notLam (H : Neutral M) : M ≠ .lam A body := by
  cases H <;> intro eq <;> cases eq

theorem Neutral.notForallE (H : Neutral M) : M ≠ .forallE A B := by
  cases H <;> intro eq <;> cases eq

theorem Neutral.notSort (H : Neutral M) : M ≠ .sort u := by
  cases H <;> intro eq <;> cases eq

theorem Neutral.whnf (H : Neutral M) : WHNF Γ M := by
  induction H with
  | @bvar i =>
    intro result red
    cases red with
    | extra action => exact (Neutral.bvar (i := i)).noMatches action.matched
  | @app f a neutral ih =>
    intro result red
    cases red with
    | app step => exact ih _ step
    | major major _ => exact neutral.notMajor major
    | beta => exact neutral.notLam rfl
    | extra action => exact (Neutral.app neutral).noMatches action.matched

/-- Variable-headed neutral spines inhabit every semantic index.  Their
action merely extends the spine; all head observations are impossible once
the common type is not proof-valued. -/
theorem Candidate.neutral [Params.Semantic]
    (leftNeutral : Neutral M) (rightNeutral : Neutral N)
    (edge : IsDefEqStrong Γ M N A) :
    ∀ depth, Candidate depth Γ M N A
  | 0 => {
      edge := edge
      normalizes := by
        intro Δ ρ W
        have edge' := edge.weak' W
        exact ⟨⟨M.lift' ρ, .rfl,
            leftNeutral.lift'.whnf⟩,
          ⟨N.lift' ρ, .rfl,
            rightNeutral.lift'.whnf⟩⟩ }
  | depth + 1 => by
      let forward : ActionLayer (Candidate depth) Γ M N A := {
        apply := by
          intro Δ ρ D C s W hDelta hType a b u v hab hD hC hResult
          have functionEdge : IsDefEqStrong Δ (M.lift' ρ) (N.lift' ρ)
              (.forallE D C) :=
            .defeqDF hType.sound (edge.weak' W)
          exact Candidate.neutral (leftNeutral.lift'.app)
            (rightNeutral.lift'.app)
            (.appDF hD hC functionEdge hab.base.edge hResult) depth }
      let reverse : ActionLayer (Candidate depth) Γ N M A := {
        apply := by
          intro Δ ρ D C s W hDelta hType a b u v hab hD hC hResult
          have functionEdge : IsDefEqStrong Δ (N.lift' ρ) (M.lift' ρ)
              (.forallE D C) :=
            .defeqDF hType.sound (edge.weak' W).symm
          exact Candidate.neutral (rightNeutral.lift'.app)
            (leftNeutral.lift'.app)
            (.appDF hD hC functionEdge hab.base.edge hResult) depth }
      by_cases proofType : IsProofType Γ A
      · exact ⟨Candidate.neutral leftNeutral rightNeutral edge depth,
          ⟨forward, reverse, .inl proofType⟩⟩
      · let forwardHeads : HeadLayer (Candidate depth) Γ M N A := {
          piHead := by
            intro Δ ρ D C s t W typeRun observed
            have eq : M.lift' ρ = .forallE D C :=
              leftNeutral.lift'.whnf.whRedS observed
            exact (leftNeutral.lift'.notForallE eq).elim
          sortHead := by
            intro Δ ρ s t u W typeRun observed
            have eq : M.lift' ρ = .sort u :=
              leftNeutral.lift'.whnf.whRedS observed
            exact (leftNeutral.lift'.notSort eq).elim }
        let reverseHeads : HeadLayer (Candidate depth) Γ N M A := {
          piHead := by
            intro Δ ρ D C s t W typeRun observed
            have eq : N.lift' ρ = .forallE D C :=
              rightNeutral.lift'.whnf.whRedS observed
            exact (rightNeutral.lift'.notForallE eq).elim
          sortHead := by
            intro Δ ρ s t u W typeRun observed
            have eq : N.lift' ρ = .sort u :=
              rightNeutral.lift'.whnf.whRedS observed
            exact (rightNeutral.lift'.notSort eq).elim }
        exact ⟨Candidate.neutral leftNeutral rightNeutral edge depth,
          ⟨forward, reverse, .inr ⟨forwardHeads, reverseHeads⟩⟩⟩

/-! ## Logical substitutions -/

/-- A Kripke logical substitution, stated lookup-wise so weakening and binder
extension do not depend on a particular `Subst.cons` normal form.  Every
variable pair is related at all semantic indices; its displayed type is
oriented by the left substitution, as is `Ctx.SubstEq`. -/
structure Env (Delta : List SExpr) (sigma sigma' : Subst)
    (Gamma : List SExpr) : Prop where
  related : ∀ {i A}, Lookup Gamma i A → ∀ depth,
    Candidate depth Delta (sigma i) (sigma' i) (A.subst sigma)
  substEq : Ctx.SubstEq Delta sigma sigma' Gamma
  rightTyped : Ctx.Subst (fun Gamma e A => IsDefEq Gamma e e A)
    Delta sigma' Gamma

/-- Logical substitutions are Kripke. -/
theorem Env.weak' [Params.Semantic] (W : Ctx.Lift' rho Delta Theta)
    (H : Env Delta sigma sigma' Gamma) :
    Env Theta (sigma.lift_r rho) (sigma'.lift_r rho) Gamma where
  related := by
    intro i A lookup depth
    simpa only [Subst.lift_r, SExpr.lift'_subst] using
      Candidate.weak' depth W (H.related lookup depth)
  substEq := H.substEq.weak' W
  rightTyped := H.rightTyped.lift_r IsDefEq.weakCore W

/-- Keep only the left endpoint of every variable pair. -/
theorem Env.left (H : Env Delta sigma sigma' Gamma) :
    Env Delta sigma sigma Gamma where
  related := fun lookup depth => (H.related lookup depth).left
  substEq := H.substEq.leftEq
  rightTyped := by
    apply Ctx.Subst.ofLookup
    intro i A lookup
    exact (H.related lookup 0).base.edge.defeq.hasType.1

/-- Extend a logical substitution by one related pair. -/
theorem Env.cons (H : Env Delta sigma sigma' Gamma)
    (head : ∀ depth, Candidate depth Delta a b (A.subst sigma))
    (sourceType : IsDefEqStrong Gamma A A (.sort w))
    (typeEq : IsDefEqStrong Delta (A.subst sigma) (A.subst sigma')
      (.sort u)) :
    Env Delta (sigma.cons a) (sigma'.cons b) (A :: Gamma) where
  related := by
    intro i T lookup depth
    cases lookup with
    | zero =>
      simpa only [Subst.cons, SExpr.lift_subst_cons] using head depth
    | succ lookup =>
      simpa only [Subst.cons, SExpr.lift_subst_cons] using
        H.related lookup depth
  substEq := .cons H.substEq sourceType.defeq (head 0).base.edge.defeq
  rightTyped := by
    refine .cons H.rightTyped ?_
    exact typeEq.defeq.defeqDF (head 0).base.edge.defeq.hasType.2

/-- Enter a binder using the canonical weakened tail and neutral bound
variable. -/
theorem Env.lift [Params.Semantic]
    (H : Env Delta sigma sigma' Gamma)
    (sourceType : IsDefEqStrong Gamma A A (.sort w))
    (hA : IsDefEqStrong Delta (A.subst sigma) (A.subst sigma) (.sort u))
    (typeEq : IsDefEqStrong Delta (A.subst sigma) (A.subst sigma')
      (.sort u)) :
    Env (A.subst sigma :: Delta) sigma.lift sigma'.lift (A :: Gamma) where
  related := by
    intro i T lookup depth
    have htail : sigma.lift.tail = sigma.lift_r (.skip .refl) := by
      funext j
      rfl
    cases lookup with
    | zero =>
      have typed : IsDefEqStrong (A.subst sigma :: Delta)
          (.bvar 0) (.bvar 0) ((A.subst sigma).lift) :=
        .bvar .zero (hA.weak' Ctx.Lift'.one)
      change Candidate depth (A.subst sigma :: Delta)
        (.bvar 0) (.bvar 0) ((A.lift).subst sigma.lift)
      rw [SExpr.lift_subst, htail, ← SExpr.lift'_subst]
      exact Candidate.neutral (Neutral.bvar (i := 0))
        (Neutral.bvar (i := 0)) typed depth
    | succ lookup =>
      have related := Candidate.weak' depth
        (Ctx.Lift'.one (Γ := Delta) (A := A.subst sigma))
        (H.related lookup depth)
      simpa only [Subst.lift, SExpr.lift_subst, htail,
        ← SExpr.lift'_subst] using related
  substEq := H.substEq.lift sourceType.defeq.hasType.1
  rightTyped := by
    apply Ctx.Subst.ofLookup
    intro i T lookup
    have htail' : sigma'.lift.tail = sigma'.lift_r (.skip .refl) := by
      funext j
      rfl
    cases lookup with
    | zero =>
      have bvarTyped : IsDefEq (A.subst sigma :: Delta)
          (.bvar 0) (.bvar 0) ((A.subst sigma).lift) :=
        .bvar .zero
      have converted := (typeEq.defeq.weak' Ctx.Lift'.one).defeqDF bvarTyped
      change IsDefEq (A.subst sigma :: Delta) (.bvar 0) (.bvar 0)
        ((A.lift).subst sigma'.lift)
      rw [SExpr.lift_subst, htail', ← SExpr.lift'_subst]
      exact converted
    | succ lookup =>
      have native := (H.rightTyped.lookup lookup).weak'
        (Ctx.Lift'.one (Γ := Delta) (A := A.subst sigma))
      simpa only [Subst.lift, SExpr.lift_subst, htail',
        ← SExpr.lift'_subst] using native

/-- The left projection is an ordinary well-typed substitution. -/
theorem Env.toSubst (H : Env Delta sigma sigma' Gamma) :
    Ctx.Subst (fun Gamma e A => IsDefEq Gamma e e A) Delta sigma Gamma := by
  apply Ctx.Subst.ofLookup
  intro i A lookup
  exact (H.related lookup 0).base.edge.defeq.hasType.1

/-- Upgrade heterogeneous substitution of a strong source judgment in the
valid target context. -/
theorem Env.substStrong [Params.Semantic]
    (env : Env Delta sigma sigma' Gamma) (hDelta : Ctx.WF Delta)
    (H : IsDefEqStrong Gamma M N A) :
    IsDefEqStrong Delta (M.subst sigma) (N.subst sigma')
      (A.subst sigma) :=
  (H.subst env.substEq).strong hDelta

/-- A well-formed context's identity substitution is reducible: variables
and all of their future applications are neutral candidates. -/
theorem Env.id [Params.Semantic] (hGamma : Ctx.WF Gamma) :
    Env Gamma .id .id Gamma where
  related := by
    intro i A lookup depth
    have typed : IsDefEqStrong Gamma (.bvar i) (.bvar i) A :=
      (IsDefEq.bvar lookup).strong hGamma
    change Candidate depth Gamma (.bvar i) (.bvar i) (A.subst .id)
    rw [SExpr.subst_id]
    exact Candidate.neutral (Neutral.bvar (i := i))
      (Neutral.bvar (i := i)) typed depth
  substEq := .nil
  rightTyped := Ctx.Subst.id IsDefEq.weakCore IsDefEq.bvar

/-! ## Substitutional fundamental interface -/

/-- The three sides needed by structural equality induction.  `same` is the
left-substitution interpretation of the judgmental edge, `cross` uses the
logical pair, and `left` relates the first endpoint across substitutions.
The fourth side is derivable by PER composition. -/
structure Interpretation (depth : Nat) (Delta : List SExpr)
    (sigma sigma' : Subst) (M N A : SExpr) : Prop where
  same : Candidate depth Delta (M.subst sigma) (N.subst sigma)
    (A.subst sigma)
  cross : Candidate depth Delta (M.subst sigma) (N.subst sigma')
    (A.subst sigma)
  left : Candidate depth Delta (M.subst sigma) (M.subst sigma')
    (A.subst sigma)

/-- The second endpoint across substitutions. -/
theorem Interpretation.right
    (H : Interpretation depth Delta sigma sigma' M N A) :
    Candidate depth Delta (N.subst sigma) (N.subst sigma')
      (A.subst sigma) :=
  H.same.symm.trans H.cross

/-- Logical interpretation of one strong equality under every valid related
substitution and at every semantic index. -/
def SubstFundamental
    (_H : IsDefEqStrong Gamma M N A) : Prop :=
  ∀ {Delta : List SExpr} {sigma sigma' : Subst}, Ctx.WF Delta →
    Env Delta sigma sigma' Gamma → ∀ depth,
      Interpretation depth Delta sigma sigma' M N A

/-- The only non-structural producer consumed by the equality induction:
reducibility of a registered constant at its declared type.  N2 supplies
this through delta rank and classified pattern descent. -/
def ConstFundamental : Prop :=
  ∀ {Gamma : List SExpr} {c : Name} {ls : List SLevel} {A : SExpr},
    (H : IsDefEqStrong Gamma (.const c ls) (.const c ls) A) →
      SubstFundamental H

theorem SubstFundamental.symm
    (fundamental : SubstFundamental H) : SubstFundamental H.symm := by
  intro Delta sigma sigma' hDelta env depth
  have out := fundamental hDelta env depth
  exact {
    same := out.same.symm
    cross := out.same.symm.trans out.left
    left := out.right }

theorem SubstFundamental.trans
    (left : SubstFundamental H₁) (right : SubstFundamental H₂) :
    SubstFundamental (H₁.trans H₂) := by
  intro Delta sigma sigma' hDelta env depth
  have out₁ := left hDelta env depth
  have out₂ := right hDelta env depth
  exact {
    same := out₁.same.trans out₂.same
    cross := out₁.same.trans out₂.cross
    left := out₁.left }

theorem SubstFundamental.bvar [Params.Semantic]
    (lookup : Lookup Gamma i A)
    (hA : IsDefEqStrong Gamma A A (.sort u)) :
    SubstFundamental (.bvar lookup hA) := by
  intro Delta sigma sigma' hDelta env depth
  have related := env.related lookup depth
  exact ⟨related.left, related, related⟩

/-- Reducibility is closed under backward certified weak-head expansion.
At successor indices, function applications are expanded by congruence at
the explicitly supplied dependent result certificate; head observations use
determinism to skip the prepended run. -/
theorem Candidate.expand [Params.Semantic]
    (left : WHSteps Γ M M' A) (right : WHSteps Γ N N' A)
    (H : Candidate depth Γ M' N' A) : Candidate depth Γ M N A := by
  induction depth generalizing Γ M M' N N' A with
  | zero => exact Base.expand left right H
  | succ depth ih =>
      refine ⟨ih left right H.1, ?_⟩
      let expandAction : ∀ {X X' Y Y' : SExpr},
          WHSteps Γ X X' A → WHSteps Γ Y Y' A →
          ActionLayer (Candidate depth) Γ X' Y' A →
          ActionLayer (Candidate depth) Γ X Y A := by
        intro X X' Y Y' runX runY action
        refine { apply := ?_ }
        intro Δ ρ D C s W hDelta hType a b u v hab hD hC hResult
        have runXPi : WHSteps Δ (X.lift' ρ) (X'.lift' ρ)
            (.forallE D C) :=
          (runX.weak' W).defeqDF hType.sound
        have runYPi : WHSteps Δ (Y.lift' ρ) (Y'.lift' ρ)
            (.forallE D C) :=
          (runY.weak' W).defeqDF hType.sound
        have leftApp := runXPi.app hD hC hab.base.edge.hasType.1
          hResult.hasType.1
        have rightAppNative := runYPi.app hD hC hab.base.edge.hasType.2
          hResult.hasType.2
        have rightApp : WHSteps Δ ((Y.lift' ρ).app b)
            ((Y'.lift' ρ).app b) (C.inst a) :=
          rightAppNative.defeqDF hResult.symm
        exact ih leftApp rightApp
          (action.apply W hDelta hType hab hD hC hResult)
      let expandHeads : ∀ {X X' Y Y' : SExpr},
          WHSteps Γ X X' A → WHSteps Γ Y Y' A →
          HeadLayer (Candidate depth) Γ X' Y' A →
          HeadLayer (Candidate depth) Γ X Y A := by
        intro X X' Y Y' runX runY heads
        refine {
          piHead := ?_
          sortHead := ?_ }
        · intro Δ ρ D C s t W typeRun observed
          have after : WHRedS Δ (X'.lift' ρ) (.forallE D C) :=
            (runX.weak' W).red.determ_l observed WHNF.forallE
          obtain ⟨D', C', out, u, v, domain, codomain⟩ :=
            heads.piHead W typeRun after
          exact ⟨D', C', (runY.weak' W).red.trans out,
            u, v, domain, codomain⟩
        · intro Δ ρ s t u W typeRun observed
          have after : WHRedS Δ (X'.lift' ρ) (.sort u) :=
            (runX.weak' W).red.determ_l observed WHNF.sort
          exact (runY.weak' W).red.trans (heads.sortHead W typeRun after)
      refine {
        forwardAction := expandAction left right H.2.forwardAction
        reverseAction := expandAction right left H.2.reverseAction
        heads := ?_ }
      cases H.2.heads with
      | inl proofType => exact .inl proofType
      | inr heads =>
        exact .inr ⟨expandHeads left right heads.1,
          expandHeads right left heads.2⟩

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
    exact ⟨⟨.sort u, .rfl, WHNF.sort⟩,
      ⟨.sort u, .rfl, WHNF.sort⟩⟩

/-- Canonical universes inhabit every semantic index. -/
theorem Candidate.sort : ∀ depth,
    Candidate depth Γ (.sort u) (.sort u) (.sort u.succ)
  | 0 => Base.sort
  | depth + 1 => by
      let action : ActionLayer (Candidate depth) Γ (.sort u) (.sort u)
          (.sort u.succ) := {
        apply := by
          intro Δ ρ D C s W hDelta hA a b w v hab hD hC hResult
          have bad : (.sort u.succ : SExpr) = .forallE D C := by
            simpa only [SExpr.lift'] using hA.eq_of_normal WHNF.sort
          cases bad }
      let heads : HeadLayer (Candidate depth) Γ (.sort u) (.sort u)
        (.sort u.succ) := {
        piHead := by
          intro Δ ρ D C s t W hType hM
          have bad : (.sort u : SExpr) = .forallE D C := by
            simpa only [SExpr.lift'] using WHNF.sort.whRedS hM
          cases bad
        sortHead := by
          intro Δ ρ s t u' W hType hM
          have hu : (.sort u : SExpr) = .sort u' := by
            simpa only [SExpr.lift'] using WHNF.sort.whRedS hM
          cases hu
          change WHRedS Δ (.sort u) (.sort u)
          exact .rfl }
      exact ⟨Candidate.sort depth,
        ⟨action, action, .inr ⟨heads, heads⟩⟩⟩

theorem SubstFundamental.sort [Params.Semantic] :
    @SubstFundamental _ Gamma (.sort u) (.sort u) (.sort u.succ)
      IsDefEqStrong.sort := by
  intro Delta sigma sigma' hDelta env depth
  simpa only [SExpr.subst] using
    (show Interpretation depth Delta sigma sigma' (.sort u) (.sort u)
      (.sort u.succ) from
      ⟨Candidate.sort depth, Candidate.sort depth, Candidate.sort depth⟩)

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
          exact ⟨⟨_, .rfl, WHNF.forallE⟩,
            ⟨_, .rfl, WHNF.forallE⟩⟩ }
  | depth + 1 => by
      let action : ActionLayer (Candidate depth) Γ (.forallE A B)
          (.forallE A B) (.sort (.imax u v)) := {
        apply := by
          intro Δ ρ D C s W hDelta hType a b w z hab hD hC hResult
          have bad : (.sort (.imax u v) : SExpr) = .forallE D C := by
            simpa only [SExpr.lift'] using hType.eq_of_normal WHNF.sort
          cases bad }
      let heads : HeadLayer (Candidate depth) Γ (.forallE A B)
          (.forallE A B) (.sort (.imax u v)) := {
        piHead := by
          intro Δ ρ D C s t W hType hLeft
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
            by
              simp only [SExpr.lift']
              exact .rfl,
            u, v,
            .single domainRel.base.edge domainRel,
            .single codomainRel.base.edge codomainRel⟩
        sortHead := by
          intro Δ ρ s t u' W hType hLeft
          have bad :
              (.forallE (A.lift' ρ) (B.lift' ρ.cons) : SExpr) = .sort u' := by
            simpa only [SExpr.lift'] using WHNF.forallE.whRedS hLeft
          cases bad }
      exact ⟨Candidate.forallE domain codomain depth,
        ⟨action, action, .inr ⟨heads, heads⟩⟩⟩

/-- Relational Pi formation.  The codomain candidate is native to the left
binder; the reverse head transports its symmetric path to the right binder
explicitly. -/
theorem Candidate.forallERel [Params.Semantic]
    (domain : ∀ depth, Candidate depth Gamma A A' (.sort u))
    (codomain : ∀ depth, Candidate depth (A :: Gamma) B B' (.sort v))
    (edge : IsDefEqStrong Gamma (.forallE A B) (.forallE A' B')
      (.sort (.imax u v))) :
    ∀ depth, Candidate depth Gamma (.forallE A B) (.forallE A' B')
      (.sort (.imax u v))
  | 0 => by
      exact {
        edge := edge
        normalizes := by
          intro Delta rho W
          exact ⟨⟨_, .rfl, WHNF.forallE⟩,
            ⟨_, .rfl, WHNF.forallE⟩⟩ }
  | depth + 1 => by
      let action : ActionLayer (Candidate depth) Gamma (.forallE A B)
          (.forallE A' B') (.sort (.imax u v)) := {
        apply := by
          intro Delta rho D C s W hDelta hType a b w z hab hD hC hResult
          have bad : (.sort (.imax u v) : SExpr) = .forallE D C := by
            simpa only [SExpr.lift'] using hType.eq_of_normal WHNF.sort
          cases bad }
      let reverseAction : ActionLayer (Candidate depth) Gamma (.forallE A' B')
          (.forallE A B) (.sort (.imax u v)) := {
        apply := by
          intro Delta rho D C s W hDelta hType a b w z hab hD hC hResult
          have bad : (.sort (.imax u v) : SExpr) = .forallE D C := by
            simpa only [SExpr.lift'] using hType.eq_of_normal WHNF.sort
          cases bad }
      let forwardHeads : HeadLayer (Candidate depth) Gamma (.forallE A B)
          (.forallE A' B') (.sort (.imax u v)) := {
        piHead := by
          intro Delta rho D C s t W hType observed
          have eqLeft :
              (.forallE (A.lift' rho) (B.lift' rho.cons) : SExpr) =
                .forallE D C := by
            simpa only [SExpr.lift'] using WHNF.forallE.whRedS observed
          injection eqLeft with hD hC
          subst D
          subst C
          have domainRel := Candidate.weak' depth W (domain depth)
          have codomainRel := Candidate.weak' depth W.cons (codomain depth)
          have run : WHRedS Delta
              (.forallE (A'.lift' rho) (B'.lift' rho.cons))
              (.forallE (A'.lift' rho) (B'.lift' rho.cons)) := .rfl
          exact ⟨A'.lift' rho, B'.lift' rho.cons,
            by simpa only [SExpr.lift'] using run,
            u, v,
            .single domainRel.base.edge domainRel,
            .single codomainRel.base.edge codomainRel⟩
        sortHead := by
          intro Delta rho s t w W hType observed
          have bad :
              (.forallE (A.lift' rho) (B.lift' rho.cons) : SExpr) = .sort w := by
            simpa only [SExpr.lift'] using WHNF.forallE.whRedS observed
          cases bad }
      let reverseHeads : HeadLayer (Candidate depth) Gamma (.forallE A' B')
          (.forallE A B) (.sort (.imax u v)) := {
        piHead := by
          intro Delta rho D C s t W hType observed
          have eqRight :
              (.forallE (A'.lift' rho) (B'.lift' rho.cons) : SExpr) =
                .forallE D C := by
            simpa only [SExpr.lift'] using WHNF.forallE.whRedS observed
          injection eqRight with hD hC
          subst D
          subst C
          have domainRel := Candidate.weak' depth W (domain depth)
          have codomainRel := Candidate.weak' depth W.cons (codomain depth)
          let domainPath : TypeDefEqPath Delta (A.lift' rho) (A'.lift' rho) u :=
            .single domainRel.base.edge.defeq
          let codomainNative : RelatedPath (Candidate depth)
              (A.lift' rho :: Delta) (B'.lift' rho.cons) (B.lift' rho.cons) v :=
            .single codomainRel.base.edge.symm codomainRel.symm
          have run : WHRedS Delta
              (.forallE (A.lift' rho) (B.lift' rho.cons))
              (.forallE (A.lift' rho) (B.lift' rho.cons)) := .rfl
          exact ⟨A.lift' rho, B.lift' rho.cons,
            by simpa only [SExpr.lift'] using run,
            u, v,
            .single domainRel.base.edge.symm domainRel.symm,
            .defeqDF_l domainPath codomainNative⟩
        sortHead := by
          intro Delta rho s t w W hType observed
          have bad :
              (.forallE (A'.lift' rho) (B'.lift' rho.cons) : SExpr) = .sort w := by
            simpa only [SExpr.lift'] using WHNF.forallE.whRedS observed
          cases bad }
      exact ⟨Candidate.forallERel domain codomain edge depth,
        ⟨action, reverseAction, .inr ⟨forwardHeads, reverseHeads⟩⟩⟩

/-- Lambda endpoints with externally supplied semantic actions inhabit every
index.  Their own common type is a syntactic Pi, so type-head observations
are vacuous by the explicit universe-observation premise. -/
theorem Candidate.lamRel [Params.Semantic]
    (edge : IsDefEqStrong Gamma (.lam A body) (.lam A' body')
      (.forallE D C))
    (forward : ∀ depth, ActionLayer (Candidate depth) Gamma
      (.lam A body) (.lam A' body') (.forallE D C))
    (reverse : ∀ depth, ActionLayer (Candidate depth) Gamma
      (.lam A' body') (.lam A body) (.forallE D C)) :
    ∀ depth, Candidate depth Gamma (.lam A body) (.lam A' body')
      (.forallE D C)
  | 0 => {
      edge := edge
      normalizes := by
        intro Delta rho W
        exact ⟨⟨_, .rfl, WHNF.lam⟩,
          ⟨_, .rfl, WHNF.lam⟩⟩ }
  | depth + 1 => by
      let headsLeft : HeadLayer (Candidate depth) Gamma (.lam A body)
          (.lam A' body') (.forallE D C) := {
        piHead := by
          intro Delta rho X Y s t W hType observed
          have bad :
              (.forallE (D.lift' rho) (C.lift' rho.cons) : SExpr) = .sort s := by
            simpa only [SExpr.lift'] using hType.eq_of_normal WHNF.forallE
          cases bad
        sortHead := by
          intro Delta rho s t u W hType observed
          have bad :
              (.forallE (D.lift' rho) (C.lift' rho.cons) : SExpr) = .sort s := by
            simpa only [SExpr.lift'] using hType.eq_of_normal WHNF.forallE
          cases bad }
      let headsRight : HeadLayer (Candidate depth) Gamma (.lam A' body')
          (.lam A body) (.forallE D C) := {
        piHead := by
          intro Delta rho X Y s t W hType observed
          have bad :
              (.forallE (D.lift' rho) (C.lift' rho.cons) : SExpr) = .sort s := by
            simpa only [SExpr.lift'] using hType.eq_of_normal WHNF.forallE
          cases bad
        sortHead := by
          intro Delta rho s t u W hType observed
          have bad :
              (.forallE (D.lift' rho) (C.lift' rho.cons) : SExpr) = .sort s := by
            simpa only [SExpr.lift'] using hType.eq_of_normal WHNF.forallE
          cases bad }
      exact ⟨Candidate.lamRel edge forward reverse depth,
        ⟨forward depth, reverse depth, .inr ⟨headsLeft, headsRight⟩⟩⟩

/-- The substitutional fundamental application case.  Instantiated result
equality is rebuilt from the logical argument edge and codomain validity;
the right codomain substitution never has to be identified with the left. -/
theorem SubstFundamental.appDF [Params.Semantic]
    (hA : IsDefEqStrong Gamma A A (.sort u))
    (hB : IsDefEqStrong (A :: Gamma) B B (.sort v))
    (hf : IsDefEqStrong Gamma f f' (.forallE A B))
    (ha : IsDefEqStrong Gamma a a' A)
    (hResult : IsDefEqStrong Gamma (B.inst a) (B.inst a') (.sort v))
    (fundA : SubstFundamental hA)
    (fundB : SubstFundamental hB)
    (fundF : SubstFundamental hf)
    (fundArg : SubstFundamental ha) :
    SubstFundamental (.appDF hA hB hf ha hResult) := by
  intro Delta sigma sigma' hDelta env depth
  have domainOut := fundA hDelta env 0
  have hD : IsDefEqStrong Delta (A.subst sigma) (A.subst sigma)
      (.sort u) := domainOut.same.base.edge.hasType.1
  have domainEq : IsDefEqStrong Delta (A.subst sigma) (A.subst sigma')
      (.sort u) := domainOut.cross.base.edge
  let envLift := env.lift hA hD domainEq
  have hExtended : Ctx.WF (A.subst sigma :: Delta) :=
    ⟨hDelta, ⟨u, hD.defeq⟩⟩
  have codomainOut := fundB hExtended envLift 0
  have hC : IsDefEqStrong (A.subst sigma :: Delta)
      (B.subst sigma.lift) (B.subst sigma.lift) (.sort v) :=
    codomainOut.same.base.edge.hasType.1
  let piTyped : IsDefEqStrong Delta
      (.forallE (A.subst sigma) (B.subst sigma.lift))
      (.forallE (A.subst sigma) (B.subst sigma.lift))
      (.sort (.imax u v)) :=
    .forallEDF hD hC hC
  let typeRun : WHSteps Delta
      (.forallE (A.subst sigma) (B.subst sigma.lift))
      (.forallE (A.subst sigma) (B.subst sigma.lift))
      (.sort (.imax u v)) := .refl piTyped
  have functionOut := fundF hDelta env (depth + 1)
  have argumentOut := fundArg hDelta env depth
  let applyOne {F G X Y : SExpr}
      (function : Candidate (depth + 1) Delta F G
        (.forallE (A.subst sigma) (B.subst sigma.lift)))
      (argument : Candidate depth Delta X Y (A.subst sigma)) :
      Candidate depth Delta (.app F X) (.app G Y)
        ((B.subst sigma.lift).inst X) := by
    have result := IsDefEqStrong.instCongr hDelta hD hC argument.base.edge
    have bodyRefl : (B.subst sigma.lift).lift' Lift.refl.cons =
        B.subst sigma.lift :=
      SExpr.lift'_depth_zero (by rfl)
    have typeRun' : WHSteps Delta
        ((SExpr.forallE (A.subst sigma) (B.subst sigma.lift)).lift' Lift.refl)
        (.forallE (A.subst sigma) (B.subst sigma.lift))
        (.sort (.imax u v)) := by
      simpa only [SExpr.lift', SExpr.lift'_refl, bodyRefl] using typeRun
    simpa only [SExpr.lift'_refl] using
      function.action.apply Ctx.Lift'.refl hDelta typeRun' argument
        hD hC result
  have same := applyOne functionOut.same argumentOut.same
  have cross := applyOne functionOut.cross argumentOut.cross
  have left := applyOne functionOut.left argumentOut.left
  refine {
    same := ?_
    cross := ?_
    left := ?_ }
  · simpa only [SExpr.subst, SExpr.subst_inst] using same
  · simpa only [SExpr.subst, SExpr.subst_inst] using cross
  · simpa only [SExpr.subst, SExpr.subst_inst] using left

/-- The substitutional fundamental Pi-formation case.  Domain relations for
the Pi endpoints and for the logical binder environment are deliberately
different: the latter follows the left source binder, while the external
strong edge records the heterogeneous right binder. -/
theorem SubstFundamental.forallEDF [Params.Semantic]
    (hA : IsDefEqStrong Gamma A A' (.sort u))
    (hBody : IsDefEqStrong (A :: Gamma) B B' (.sort v))
    (hBody' : IsDefEqStrong (A' :: Gamma) B B' (.sort v))
    (fundA : SubstFundamental hA)
    (fundBody : SubstFundamental hBody) :
    SubstFundamental (.forallEDF hA hBody hBody') := by
  intro Delta sigma sigma' hDelta env depth
  let whole : IsDefEqStrong Gamma (.forallE A B) (.forallE A' B')
      (.sort (.imax u v)) := .forallEDF hA hBody hBody'
  have domainAtZero := fundA hDelta env 0
  have hD : IsDefEqStrong Delta (A.subst sigma) (A.subst sigma)
      (.sort u) := domainAtZero.same.base.edge.hasType.1
  have domainLeftEq : IsDefEqStrong Delta (A.subst sigma)
      (A.subst sigma') (.sort u) := domainAtZero.left.base.edge
  let envSame := env.left.lift hA.hasType.1 hD hD
  let envCross := env.lift hA.hasType.1 hD domainLeftEq
  have hExtended : Ctx.WF (A.subst sigma :: Delta) :=
    ⟨hDelta, ⟨u, hD.defeq⟩⟩
  let domainSame : ∀ d, Candidate d Delta (A.subst sigma)
      (A'.subst sigma) (.sort u) := fun d =>
    (fundA hDelta env.left d).same
  let domainCross : ∀ d, Candidate d Delta (A.subst sigma)
      (A'.subst sigma') (.sort u) := fun d =>
    (fundA hDelta env d).cross
  let domainLeft : ∀ d, Candidate d Delta (A.subst sigma)
      (A.subst sigma') (.sort u) := fun d =>
    (fundA hDelta env d).left
  let bodySame : ∀ d, Candidate d (A.subst sigma :: Delta)
      (B.subst sigma.lift) (B'.subst sigma.lift) (.sort v) := fun d =>
    (fundBody hExtended envSame d).same
  let bodyCross : ∀ d, Candidate d (A.subst sigma :: Delta)
      (B.subst sigma.lift) (B'.subst sigma'.lift) (.sort v) := fun d =>
    (fundBody hExtended envCross d).cross
  let bodyLeft : ∀ d, Candidate d (A.subst sigma :: Delta)
      (B.subst sigma.lift) (B.subst sigma'.lift) (.sort v) := fun d =>
    (fundBody hExtended envCross d).left
  have edgeSame := env.left.substStrong hDelta whole
  have edgeCross := env.substStrong hDelta whole
  have edgeLeft := env.substStrong hDelta whole.hasType.1
  have same := Candidate.forallERel domainSame bodySame
    (by simpa only [SExpr.subst] using edgeSame) depth
  have cross := Candidate.forallERel domainCross bodyCross
    (by simpa only [SExpr.subst] using edgeCross) depth
  have left := Candidate.forallERel domainLeft bodyLeft
    (by simpa only [SExpr.subst] using edgeLeft) depth
  refine {
    same := ?_
    cross := ?_
    left := ?_ }
  · simpa only [SExpr.subst] using same
  · simpa only [SExpr.subst] using cross
  · simpa only [SExpr.subst] using left

/-! ## Fundamental-theorem interface and Pi escape -/

/-- The N3 target at one semantic index.  The statement is intentionally
context-generic; context validity is needed only when a weak edge is upgraded
to its evidence-rich form at a consumer. -/
def Fundamental (depth : Nat) : Prop :=
  ∀ {Γ : List SExpr} {M N A : SExpr},
    IsDefEqStrong Γ M N A → Candidate depth Γ M N A

/-! ### The normalization/fundamental seam

The finite candidate index is an observation index, not a typing-substitution
index.  In particular, a `Candidate depth` argument is deliberately not
strong enough to interpret an arbitrary higher-order binder body at every
larger index.  The fundamental theorem therefore does not bootstrap its
lambda case from `Env.cons`.  N2 instead proves weak-head normalization
directly from stratified typing; level zero consumes that theorem, and every
successor action is reconstructed from the already available lower
fundamental theorem and the exact typed application edge.

This factorization is important for the recursion argument: dynamic beta and
iota reducts are handled once by N2's well-founded normalization proof, while
the candidate index decreases structurally here. -/

/-- N2's exact output, before any logical-relation observations are added.
The input is evidence-rich, while the operational trace deliberately carries
no displayed-type subject-reduction claim. -/
def TypedWHNormalization : Prop :=
  ∀ {Γ : List SExpr} {M A : SExpr},
    IsDefEqStrong Γ M M A → WHResult Γ M A

/-- The rejected stronger N2 interface.  Requiring every normalization link
to preserve the displayed type is not an innocent strengthening: beta under
a heterogeneous Pi conversion already needs the Pi-inversion leaf. -/
def SubjectPreservingWHNormalization : Prop :=
  ∀ {Γ : List SExpr} {M A : SExpr},
    IsDefEqStrong Γ M M A →
      ∃ result, WHSteps Γ M result A ∧ WHNF Γ result

/-- A subject-preserving weak-head normalizer discharges the isolated beta
contraction residual.  Thus using such a normalizer to prove Pi inversion
would be circular; N2 must return the untyped operational trace in
`TypedWHNormalization`. -/
theorem SubjectPreservingWHNormalization.betaFire [Params.Semantic]
    (normalization : SubjectPreservingWHNormalization) : LRS.BetaFire := by
  intro Γ A A₀ B₀ B₁ e e' w hΓ path bodyTyped argumentTyped
  obtain ⟨⟨u, domainTyped⟩, v, codomainTyped⟩ :=
    (path.leftType.strong hΓ).forallE_inv' (.inl rfl)
  have lambdaTyped : IsDefEq Γ (.lam A e) (.lam A e)
      (.forallE A B₁) :=
    .lamDF domainTyped.defeq bodyTyped
  have applicationTyped : IsDefEq Γ
      (.app (.lam A e) e') (.app (.lam A e) e') (B₀.inst e') :=
    .appDF (path.defeqDF lambdaTyped) argumentTyped
  obtain ⟨result, run, normal⟩ :=
    normalization (applicationTyped.strong hΓ)
  cases run.eq_or_first with
  | inl eq =>
    subst result
    exact False.elim (normal _ WHRed.beta)
  | inr first =>
    obtain ⟨next, step⟩ := first
    have nextEq : next = e.inst e' := step.red.determ .beta
    subst next
    exact step.sound.defeq

/-- Typed weak-head normalization supplies the non-recursive candidate
layer, including its full Kripke quantification. -/
theorem TypedWHNormalization.base [Params.Semantic]
    (normalization : TypedWHNormalization)
    (edge : IsDefEqStrong Γ M N A) : Base Γ M N A where
  edge := edge
  normalizes := by
    intro Δ ρ W
    have lifted := edge.weak' W
    exact ⟨normalization lifted.hasType.1,
      normalization lifted.hasType.2⟩

/-- N2 is precisely the base case of the indexed fundamental theorem. -/
theorem Fundamental.zero [Params.Semantic]
    (normalization : TypedWHNormalization) : Fundamental 0 :=
  fun edge => normalization.base edge

/-- Once the preceding fundamental level is available, every function
action is just typed application congruence followed by that level.  No
logical substitution for a lambda body is used here. -/
theorem ActionLayer.of_fundamental [Params.Semantic]
    (fundamental : Fundamental depth)
    (edge : IsDefEqStrong Γ M N A) :
    ActionLayer (Candidate depth) Γ M N A where
  apply := by
    intro Δ ρ D C s W hΔ typeRun a b u v argument hD hC hResult
    have functionAtPi : IsDefEqStrong Δ (M.lift' ρ) (N.lift' ρ)
        (.forallE D C) :=
      .defeqDF typeRun.sound (edge.weak' W)
    exact fundamental
      (.appDF hD hC functionAtPi argument.base.edge hResult)

/-- The remaining successor obligation is only head compatibility.  It is
named separately so N3 can prove exactly this fragment by induction on
strong equality after N2 has supplied normalization. -/
def HeadFundamental (depth : Nat) : Prop :=
  ∀ {Γ : List SExpr} {M N A : SExpr},
    IsDefEqStrong Γ M N A →
      IsProofType Γ A ∨
        (HeadLayer (Candidate depth) Γ M N A ∧
          HeadLayer (Candidate depth) Γ N M A)

/-- One head-compatibility layer extends the fundamental theorem by one
candidate index. -/
theorem Fundamental.succ [Params.Semantic]
    (lower : Fundamental depth) (heads : HeadFundamental depth) :
    Fundamental (depth + 1) := by
  intro Γ M N A edge
  exact ⟨lower edge, {
    forwardAction := ActionLayer.of_fundamental lower edge
    reverseAction := ActionLayer.of_fundamental lower edge.symm
    heads := heads edge }⟩

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
    let typeRun : WHSteps Γ (.sort u) (.sort u) (.sort u.succ) :=
      .refl .sort
    obtain ⟨D', C', run, du, cu, domain, codomain⟩ :=
      layer.piHead Ctx.Lift'.refl typeRun observed'
    have runRed : WHRedS Γ B (.forallE D' C') := by
      simpa using run
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
