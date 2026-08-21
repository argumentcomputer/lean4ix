import Lean4Lean.Experimental.SExprNormalizationFailure
import Lean4Lean.Experimental.SExprParamsD2

/-!
# L4L-16N′0: mutual-inductive reducibility candidates

The candidate architecture of the L4L-16N′ route, landed from probe Z16
(`plans/probes/probeZ16-indcand.lean`).  | succ n hn ih =>
    exact ⟨_, .rfl, WHNF.ctorSpine hs [n],
      foldr_app_ne_forallE [n] _ _, foldr_app_ne_sort [n] _ _⟩| zero =>
    exact ⟨_, .rfl, WHNF.ctorSpine hz [],
      foldr_app_ne_forallE [] _ _, foldr_app_ne_sort [] _ _⟩The candidate at an inductive type
stops degenerating to `Base` (edge + assumed `KripkeNormalizes`) and becomes
constructor-generated membership: a term is in the candidate of a family iff
it is neutral, or is a classified constructor spine whose recursive fields
(applied under their Pi telescopes) are members of the sibling families'
candidates, or weak-head expands (untyped `WHRed`) to a member.  The
fundamental theorem's iota case then runs by structural induction on the
membership *derivation* — no term measure, no family rank — which closes the
exact `Tree.branch` transition that killed the L4L-16N/N2 measures
(`L4L16NFailure.treeBranch_primaryMeasure_fails`,
`L4L16NFailure.tree_familyOrdinalFallback_false`).

*The Kripke reshaping (this rung's one design decision, probe finding 3).*
The probe's naive branch clause `∀ a, P a → InCandTreeList (f.app a)` is not
stable under context lift: a lifted membership goal quantifies over
arguments that are not lift images.  Landed here in the preferred shape
(option (a)): the recursive-field clause itself is Kripke-quantified,
following the `ActionLayer.apply` discipline —

  `hf : ∀ {Δ ρ}, Ctx.Lift' ρ Γ Δ → ∀ a, P Δ a →
     InCandTreeList H P Δ (α.lift' ρ) ((f.lift' ρ).app a)`

so the context and the block parameter become *indices* of the mutual
family, the domain-candidate parameter `P` becomes a context-indexed
predicate, and membership is lift-stable by construction
(`InCandTree.lift'`, the rung's new content vs the probe).  Recursive
occurrences stay strictly positive — they are right of every arrow — and
the domain-candidate-as-parameter form still covers the whole
kernel-accepted non-nested class; the genuinely negative
sibling-in-quantifier-domain form remains rejected and pinned (K1).

*The betaFire boundary.*  Nothing here consumes a typed trace: the
definitions mention only `WHRed`/`WHRedS`/`WHNF`/`Neutral`, and the seam
compatibility emits the untyped observation `WHResult` (phantom type index).
No `IsDefEqStrong`, `WHSteps`, `LRS.PiPathInv`, `LR.MajorLinkRect`, or
adequacy input is referenced — the permanent
`SubjectPreservingWHNormalization.betaFire` boundary is respected by
construction.  Typed data may ride on clause *arguments* in later rungs;
this rung needs none.

*What N′1 owes.*  `TreeRules`/`NatRules` abstract the five (respectively
two) generated iota steps as Kripke families of untyped `WHRed` steps plus
the two stuck-major facts.  Producing them at `d2Params` — the
`Pattern.Action`s of the registered block rules (`treeRule_registered`) via
the `Pattern.IotaReductionSite` assembly, and the stuck facts from the
`WHNF.subpattern`/pattern-uniqueness suite — is rung N′1, not this one.
The head-dictionary and classification facts *are* discharged here at the
production `d2Params`/`d0Params` instances (`d2Discharge`, `d0Discharge`),
so the seam-facing normalization theorems fire on the real environments.

*The N′1 record (see the `-- ### L4L-16N′1` sections below).*  Landed:

* **Stuck majors, unconditional.**  `IsMajorPremise.stuckApp` /
  `stuck_major_kripke` prove the `stuckT`/`stuckL`/`stuckN` field families
  outright from the pattern-uniqueness suite (`IsMajorPremise.whnf`,
  `Neutral.whnf`/`.noMatches`, `Params.pat_not_varS`), and the assemblers
  `TreeRules.ofSteps`/`NatRules.ofSteps` close the stuck half of both
  structures, reducing their inhabitation to the step families alone.
* **The generated `WHRed.extra` steps.**  `Pattern.IotaReductionSite.whRed`
  turns any reduction-site certificate into the untyped operational step;
  `d0IotaWHRed` fires it at the production D0 instance for both Nat rules
  outright (the landed `d0IotaSite` supplies the site from the typed-redex
  premises the `Params.Semantic.iotaSite` interface already carries), and
  `d2IotaWHRed`/`d2IotaWHRed_ofBlockStep`/`d2TreeIotaWHRed`/
  `d2NatEntryIotaWHRed` fire it at the production D2 instance for all
  seven rules — the five Tree/TreeList steps
  conditional on `D2TreeCheckedStep` (the 18A′-gated `Pattern.Check`
  discharge, routed through `D2CheckedStep.of_tree` exactly as
  `d2SortInvSExact`'s regime already is; no regime change) plus the
  per-rule capture-spine/collapse data that the generic engine takes as its
  interface, while the two inherited Nat steps need no check premise at all
  (`d2NatChecked`).
* **Membership ⇒ `KripkeNormalizes`.**  `InCandTree.kripkeNormalizes` (and
  the `TreeList`/`Nat` versions) prove the `Base.normalizes` field as a
  theorem for candidate members, from `InCand*.lift'` + `toWHResult`; the
  `Base`-assembly corollaries (`InCandTree.toBase`, …) take the judgmental
  edge as a hypothesis — no typed-trace content is produced here, per the
  betaFire boundary.  Instance forms: `d2InCandTree_kripkeNormalizes`,
  `d0InCandNat_kripkeNormalizes`.

*The N′1 finding (pinned).*  The one-step step fields of the landed
`TreeRules`/`NatRules` above are **mock-shaped**: at a generated registry
the unique available step out of a live redex is `WHRed.extra`, whose
target is the applied right tower `r.1.applyS` — the registered closed
lambda tower applied to the ordered captures (commons, then constructor
fields; `captureArgs`).  For the `node`/`branch`/`cons`/`succ` shapes the
landed single-step target (`(minorNd·ts)·(recL·ts)`, …) differs from every
such tower application — its outermost argument *contains* the last capture
instead of being it — so by `WHRed.determ` the two targets exclude each
other (`tower_target_ne_nodeShape`/`oneStep_nodeShape_refuted`, stated at
the representative `node` shape; `succ`/`cons` fail the same size test and
`branch`'s lambda-packaged argument likewise).  Separately, the fields
quantify over *raw* `SExpr` arguments, while a `Pattern.Action` carries
`sound : IsDefEq`, so a step at an untypable argument has no certificate to
fire.  The production interface is therefore the site step plus the
untyped multi-beta collapse: `whRedS_foldl_app`/`whRedS_foldl_beta` walk
the applied tower down one binder at a time, and the generated tower
bodies (`BlockGenerationChecked.rule`) instantiate to exactly the landed
contractum shapes — the captured minor premise applied to the fields and
the lambda-packaged recursive calls — whose per-rule computation is the
Lane-D-adjacent mechanical volume N′2 consumes.  Threading the
typed/candidate argument restriction through the membership induction is
N′2/N′3 content, where the landed `TreeRules`/`NatRules` engines remain
the abstract interface.  A fully concrete premise-free production step is
exhibited (`d0DefWHRed`: `d0def ⤳ Nat.zero` at `d0Params`, `sorryAx`-free).
-/

set_option maxHeartbeats 1000000

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

variable [Params]

/-! ## The block heads and constructor spines

The five D2 constructor-application spines, over an abstract head dictionary
so the definitions are instance-generic; the D2 instance discharge is at the
end of this file.  `ls` is the (single-element, for the checked block) level
list. -/

/-- The five D2 constructor heads and their level instantiation. -/
structure TreeHeads : Type where
  leafC : Name
  nodeC : Name
  branchC : Name
  nilC : Name
  consC : Name
  ls : List SLevel

/-- `Tree.leaf α x` as a spine. -/
def leafApp (H : TreeHeads) (α x : SExpr) : SExpr :=
  ((SExpr.const H.leafC H.ls).app α).app x

/-- `Tree.node α ts` as a spine. -/
def nodeApp (H : TreeHeads) (α ts : SExpr) : SExpr :=
  ((SExpr.const H.nodeC H.ls).app α).app ts

/-- `Tree.branch α f` as a spine — the recursion-under-Pi constructor. -/
def branchApp (H : TreeHeads) (α f : SExpr) : SExpr :=
  ((SExpr.const H.branchC H.ls).app α).app f

/-- `TreeList.nil α` as a spine. -/
def nilApp (H : TreeHeads) (α : SExpr) : SExpr :=
  (SExpr.const H.nilC H.ls).app α

/-- `TreeList.cons α t ts` as a spine. -/
def consApp (H : TreeHeads) (α t ts : SExpr) : SExpr :=
  (((SExpr.const H.consC H.ls).app α).app t).app ts

/-! Constructor spines commute with context lifting definitionally; the
five equations are recorded so lift-stability proofs can rewrite by name. -/

theorem leafApp_lift' {H : TreeHeads} {α x : SExpr} {ρ : Lift} :
    (leafApp H α x).lift' ρ = leafApp H (α.lift' ρ) (x.lift' ρ) := rfl

theorem nodeApp_lift' {H : TreeHeads} {α ts : SExpr} {ρ : Lift} :
    (nodeApp H α ts).lift' ρ = nodeApp H (α.lift' ρ) (ts.lift' ρ) := rfl

theorem branchApp_lift' {H : TreeHeads} {α f : SExpr} {ρ : Lift} :
    (branchApp H α f).lift' ρ = branchApp H (α.lift' ρ) (f.lift' ρ) := rfl

theorem nilApp_lift' {H : TreeHeads} {α : SExpr} {ρ : Lift} :
    (nilApp H α).lift' ρ = nilApp H (α.lift' ρ) := rfl

theorem consApp_lift' {H : TreeHeads} {α t ts : SExpr} {ρ : Lift} :
    (consApp H α t ts).lift' ρ =
      consApp H (α.lift' ρ) (t.lift' ρ) (ts.lift' ρ) := rfl

/-- Moving a plain weakening past a binder: lifting under `.cons` after the
canonical one-step weakening is the one-step weakening after the lift.  Used
to discharge the Kripke branch clause of concrete lambda-field witnesses. -/
theorem lift_lift'_cons (e : SExpr) (ρ : Lift) :
    (e.lift).lift' ρ.cons = (e.lift' ρ).lift := by
  show (e.lift' (.skip .refl)).lift' ρ.cons = (e.lift' ρ).lift' (.skip .refl)
  rw [← SExpr.lift'_comp, ← SExpr.lift'_comp]
  simp only [Lift.comp, Lift.refl_comp]

/-- A context-indexed predicate: the type of domain-candidate parameters and
of result candidates. -/
abbrev CtxPred := List SExpr → SExpr → Prop

/-! ## The mutual-inductive candidates for the D2 block

The context `Γ` and the block parameter `α` are *indices*, not parameters:
the Kripke branch clause relates memberships across a genuine context
extension, so a single derivation spans many contexts.  The domain-candidate
parameter `P` is the context-indexed predicate interpreting the block
parameter; the raw-argument form of the probe is its instance
`P := fun _ _ => True`. -/

mutual

/-- The least-fixed-point reducibility candidate of the `Tree` family.  A
term is a member iff it is neutral, or is a constructor spine whose
recursive fields (under their Pi telescopes, applied in every future context
to arguments satisfying the domain candidate `P`) are members of the sibling
candidates, or weak-head expands (one untyped `WHRed` step) to a member.
The `branch` clause is the recursion-under-Pi clause, stated Kripke-style
from the start: the captured functional field is observed through all of its
applications in all future contexts, which is exactly what keeps membership
stable under `Ctx.Lift'` (`InCandTree.lift'` below). -/
inductive InCandTree (H : TreeHeads) (P : CtxPred) :
    List SExpr → SExpr → SExpr → Prop where
  | leaf {Γ : List SExpr} {α : SExpr} (x : SExpr) (hx : P Γ x) :
      InCandTree H P Γ α (leafApp H α x)
  | node {Γ : List SExpr} {α : SExpr} (ts : SExpr)
      (hts : InCandTreeList H P Γ α ts) :
      InCandTree H P Γ α (nodeApp H α ts)
  | branch {Γ : List SExpr} {α : SExpr} (f : SExpr)
      (hf : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
        ∀ a : SExpr, P Δ a →
          InCandTreeList H P Δ (α.lift' ρ) ((f.lift' ρ).app a)) :
      InCandTree H P Γ α (branchApp H α f)
  | neutral {Γ : List SExpr} {α : SExpr} (t : SExpr) (hn : Neutral t) :
      InCandTree H P Γ α t
  | expand {Γ : List SExpr} {α : SExpr} (t t' : SExpr) (step : WHRed Γ t t')
      (ht : InCandTree H P Γ α t') : InCandTree H P Γ α t

/-- The least-fixed-point reducibility candidate of the `TreeList` family.
`cons` carries the two-way mutual edge back into `Tree`. -/
inductive InCandTreeList (H : TreeHeads) (P : CtxPred) :
    List SExpr → SExpr → SExpr → Prop where
  | nil {Γ : List SExpr} {α : SExpr} : InCandTreeList H P Γ α (nilApp H α)
  | cons {Γ : List SExpr} {α : SExpr} (t ts : SExpr)
      (ht : InCandTree H P Γ α t) (hts : InCandTreeList H P Γ α ts) :
      InCandTreeList H P Γ α (consApp H α t ts)
  | neutral {Γ : List SExpr} {α : SExpr} (ts : SExpr) (hn : Neutral ts) :
      InCandTreeList H P Γ α ts
  | expand {Γ : List SExpr} {α : SExpr} (ts ts' : SExpr)
      (step : WHRed Γ ts ts') (hts : InCandTreeList H P Γ α ts') :
      InCandTreeList H P Γ α ts

end

/-- D0 calibration: the `Nat` candidate.  No higher-order field, so the
context stays a parameter and no Kripke clause is needed; lift-stability
(`InCandNat.lift'`) is nevertheless proved below, calibrating the reshaping
against the first-order case. -/
inductive InCandNat (zeroC succC : Name) (ls : List SLevel)
    (Γ : List SExpr) : SExpr → Prop where
  | zero : InCandNat zeroC succC ls Γ (.const zeroC ls)
  | succ (n : SExpr) (hn : InCandNat zeroC succC ls Γ n) :
      InCandNat zeroC succC ls Γ ((SExpr.const succC ls).app n)
  | neutral (n : SExpr) (hn : Neutral n) : InCandNat zeroC succC ls Γ n
  | expand (n n' : SExpr) (step : WHRed Γ n n')
      (hn : InCandNat zeroC succC ls Γ n') : InCandNat zeroC succC ls Γ n

/-- Multi-step expansion closure is derivable from the single-step clause. -/
theorem InCandTree.expandS {H : TreeHeads} {P : CtxPred} {Γ : List SExpr}
    {α t t' : SExpr} (run : WHRedS Γ t t') (ht : InCandTree H P Γ α t') :
    InCandTree H P Γ α t := by
  induction run using ReflTransGen.headIndOn with
  | rfl => exact ht
  | head step _ ih => exact .expand _ _ step ih

/-- `TreeList` side of the derived multi-step expansion closure. -/
theorem InCandTreeList.expandS {H : TreeHeads} {P : CtxPred}
    {Γ : List SExpr} {α ts ts' : SExpr} (run : WHRedS Γ ts ts')
    (hts : InCandTreeList H P Γ α ts') : InCandTreeList H P Γ α ts := by
  induction run using ReflTransGen.headIndOn with
  | rfl => exact hts
  | head step _ ih => exact .expand _ _ step ih

/-- `Nat` side of the derived multi-step expansion closure. -/
theorem InCandNat.expandS {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} {n n' : SExpr} (run : WHRedS Γ n n')
    (hn : InCandNat zeroC succC ls Γ n') : InCandNat zeroC succC ls Γ n := by
  induction run using ReflTransGen.headIndOn with
  | rfl => exact hn
  | head step _ ih => exact .expand _ _ step ih

/-! ### Kill check K1 — the positivity boundary

The accepted definitions above use the domain-candidate form with the
candidate as a *parameter* (`P`); the raw-argument form is its instance
`P := fun _ _ => True`.  The genuinely dangerous form — the domain candidate
a *sibling of the mutual block itself*, i.e. the classic
candidate-in-negative-position at a higher-order field — is rejected by
Lean, pinned here.  This form corresponds to a source constructor whose
Pi-field *domain* mentions a sibling family (e.g.
`branch : (Tree α → TreeList α) → Tree α`), which the kernel's own
strict-positivity check refuses; the checked D2 block has all field domains
at the block parameter `α`, so the route never needs it. -/

/--
error: (kernel) arg #6 of 'Lean4Lean.SExpr.Reducibility.IndCand.BadInCandTree.branch' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
mutual
inductive BadInCandTree (H : TreeHeads) (Γ : List SExpr) (α : SExpr) :
    SExpr → Prop where
  | branch (f : SExpr)
      (hf : ∀ a : SExpr, BadInCandTree H Γ α a →
        BadInCandTreeList H Γ α (f.app a)) :
      BadInCandTree H Γ α (branchApp H α f)
inductive BadInCandTreeList (H : TreeHeads) (Γ : List SExpr) (α : SExpr) :
    SExpr → Prop where
  | mk (t : SExpr) (h : BadInCandTree H Γ α t) : BadInCandTreeList H Γ α t
end

/-! ## Basic nonvacuity witnesses

Every clause is exercised before anything consumes the candidates: a neutral
member, normal constructor members, the higher-order `branch` member with a
genuine lambda field (whose Kripke clause is discharged at every future
context), and non-normal members through the expansion clause. -/

section Witnesses

variable {H : TreeHeads} {P : CtxPred} {Γ : List SExpr} {α : SExpr}

/-- A neutral member. -/
theorem witness_neutral : InCandTree H P Γ α (.bvar 0) :=
  .neutral _ .bvar

/-- Normal constructor members. -/
theorem witness_nil : InCandTreeList H P Γ α (nilApp H α) := .nil

theorem witness_leaf {x : SExpr} (hx : P Γ x) :
    InCandTree H P Γ α (leafApp H α x) := .leaf x hx

theorem witness_node : InCandTree H P Γ α (nodeApp H α (nilApp H α)) :=
  .node _ .nil

theorem witness_cons :
    InCandTreeList H P Γ α (consApp H α (.bvar 0) (nilApp H α)) :=
  .cons _ _ witness_neutral witness_nil

/-- A higher-order `branch` member whose field is a genuine lambda: in every
future context, every application beta-reduces to the lifted `nil` spine, so
the Kripke under-Pi clause is discharged through the expansion closure at
every argument. -/
theorem witness_branch :
    InCandTree H (fun _ _ => True) Γ α
      (branchApp H α (.lam α (nilApp H α).lift)) := by
  refine .branch _ ?_
  intro Δ ρ W a _
  refine .expand _ _ WHRed.beta ?_
  rw [show (((nilApp H α).lift).lift' ρ.cons).inst a = nilApp H (α.lift' ρ) by
    rw [lift_lift'_cons, SExpr.lift_inst, nilApp_lift']]
  exact .nil

/-- A non-normal member, obtained through the expansion clause: a beta redex
whose reduct is the `nil` spine. -/
theorem witness_nonNormal (a : SExpr) :
    InCandTreeList H P Γ α ((SExpr.lam α (nilApp H α).lift).app a) := by
  refine .expand _ _ WHRed.beta ?_
  rw [show ((nilApp H α).lift).inst a = nilApp H α from SExpr.lift_inst _]
  exact .nil

/-- The witness above is genuinely non-normal: it still takes a step. -/
theorem witness_nonNormal_steps (a : SExpr) :
    ¬WHNF Γ ((SExpr.lam α (nilApp H α).lift).app a) :=
  fun h => h _ WHRed.beta

/-- `Nat` witnesses: `succ (succ zero)`, a neutral, and a non-normal member. -/
theorem witness_nat_two {zeroC succC : Name} {ls : List SLevel} :
    InCandNat zeroC succC ls Γ
      ((SExpr.const succC ls).app ((SExpr.const succC ls).app
        (.const zeroC ls))) :=
  .succ _ (.succ _ .zero)

theorem witness_nat_neutral {zeroC succC : Name} {ls : List SLevel} :
    InCandNat zeroC succC ls Γ (.bvar 2) :=
  .neutral _ .bvar

theorem witness_nat_nonNormal {zeroC succC : Name} {ls : List SLevel}
    (a : SExpr) :
    InCandNat zeroC succC ls Γ
      ((SExpr.lam (.sort .zero) (SExpr.const zeroC ls).lift).app a) := by
  refine .expand _ _ WHRed.beta ?_
  rw [show ((SExpr.const zeroC ls).lift).inst a = .const zeroC ls from
    SExpr.lift_inst _]
  exact .zero

end Witnesses

/-! ## Lift stability — the rung's new content

The very property the probe's naive branch clause lacked.  With the Kripke
clause, the branch case needs no induction hypothesis at all: the clause is
self-weakening by lift composition, exactly as `ActionLayer` weakening in
`Candidate.weak'`. -/

/-- A Kripke domain predicate: closed under context lift.  This is the only
hypothesis under which membership is lift-stable; the trivial and the
neutral domains are instances. -/
def KripkeDomain (P : CtxPred) : Prop :=
  ∀ {Γ Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    ∀ {a : SExpr}, P Γ a → P Δ (a.lift' ρ)

/-- The raw-argument domain is Kripke. -/
theorem KripkeDomain.trivial : KripkeDomain fun _ _ => True := by
  intro Γ Δ ρ W a _
  exact _root_.trivial

/-- The neutral domain is Kripke. -/
theorem KripkeDomain.neutral : KripkeDomain fun _ a => Neutral a := by
  intro Γ Δ ρ W a ha
  exact ha.lift'

/-- **Lift stability of membership**, jointly for the mutual block.  The
constructor cases rewrite spines through the definitional lift equations;
the branch case composes the requested future lift with the clause's own
Kripke quantifier — no inversion of a lifted derivation is ever needed. -/
theorem inCand_lift' {H : TreeHeads} {P : CtxPred} (hP : KripkeDomain P) :
    (∀ {Γ : List SExpr} {α t : SExpr}, InCandTree H P Γ α t →
      ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
        InCandTree H P Δ (α.lift' ρ) (t.lift' ρ)) ∧
      (∀ {Γ : List SExpr} {α ts : SExpr}, InCandTreeList H P Γ α ts →
        ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
          InCandTreeList H P Δ (α.lift' ρ) (ts.lift' ρ)) := by
  have caseLeaf : ∀ {Γ' : List SExpr} {β : SExpr} (x : SExpr), P Γ' x →
      ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTree H P Δ (β.lift' ρ) ((leafApp H β x).lift' ρ) := by
    intro Γ' β x hx Δ ρ W
    rw [leafApp_lift']
    exact .leaf _ (hP W hx)
  have caseNode : ∀ {Γ' : List SExpr} {β : SExpr} (ts : SExpr),
      InCandTreeList H P Γ' β ts →
      (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTreeList H P Δ (β.lift' ρ) (ts.lift' ρ)) →
      ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTree H P Δ (β.lift' ρ) ((nodeApp H β ts).lift' ρ) := by
    intro Γ' β ts _ ih Δ ρ W
    rw [nodeApp_lift']
    exact .node _ (ih W)
  have caseBranch : ∀ {Γ' : List SExpr} {β : SExpr} (f : SExpr),
      (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ → ∀ a : SExpr,
        P Δ a → InCandTreeList H P Δ (β.lift' ρ) ((f.lift' ρ).app a)) →
      (∀ {Δ : List SExpr} {ρ : Lift} (_ : Ctx.Lift' ρ Γ' Δ) (a : SExpr)
        (_ : P Δ a), ∀ {Θ : List SExpr} {ρ' : Lift}, Ctx.Lift' ρ' Δ Θ →
          InCandTreeList H P Θ ((β.lift' ρ).lift' ρ')
            (((f.lift' ρ).app a).lift' ρ')) →
      ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTree H P Δ (β.lift' ρ) ((branchApp H β f).lift' ρ) := by
    intro Γ' β f hf _ Δ ρ W
    rw [branchApp_lift']
    refine .branch _ ?_
    intro Θ ρ' W' a ha
    rw [← SExpr.lift'_comp, ← SExpr.lift'_comp]
    exact hf (W.comp W') a ha
  have caseNeuT : ∀ {Γ' : List SExpr} {β : SExpr} (t : SExpr), Neutral t →
      ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTree H P Δ (β.lift' ρ) (t.lift' ρ) := by
    intro Γ' β t hn Δ ρ W
    exact .neutral _ hn.lift'
  have caseExpT : ∀ {Γ' : List SExpr} {β : SExpr} (t t' : SExpr),
      WHRed Γ' t t' → InCandTree H P Γ' β t' →
      (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTree H P Δ (β.lift' ρ) (t'.lift' ρ)) →
      ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTree H P Δ (β.lift' ρ) (t.lift' ρ) := by
    intro Γ' β t t' step _ ih Δ ρ W
    exact .expand _ _ (step.weak' W) (ih W)
  have caseNil : ∀ {Γ' : List SExpr} {β : SExpr},
      ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTreeList H P Δ (β.lift' ρ) ((nilApp H β).lift' ρ) := by
    intro Γ' β Δ ρ W
    rw [nilApp_lift']
    exact .nil
  have caseCons : ∀ {Γ' : List SExpr} {β : SExpr} (t ts : SExpr),
      InCandTree H P Γ' β t → InCandTreeList H P Γ' β ts →
      (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTree H P Δ (β.lift' ρ) (t.lift' ρ)) →
      (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTreeList H P Δ (β.lift' ρ) (ts.lift' ρ)) →
      ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTreeList H P Δ (β.lift' ρ) ((consApp H β t ts).lift' ρ) := by
    intro Γ' β t ts _ _ ih₁ ih₂ Δ ρ W
    rw [consApp_lift']
    exact .cons _ _ (ih₁ W) (ih₂ W)
  have caseNeuL : ∀ {Γ' : List SExpr} {β : SExpr} (ts : SExpr), Neutral ts →
      ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTreeList H P Δ (β.lift' ρ) (ts.lift' ρ) := by
    intro Γ' β ts hn Δ ρ W
    exact .neutral _ hn.lift'
  have caseExpL : ∀ {Γ' : List SExpr} {β : SExpr} (ts ts' : SExpr),
      WHRed Γ' ts ts' → InCandTreeList H P Γ' β ts' →
      (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTreeList H P Δ (β.lift' ρ) (ts'.lift' ρ)) →
      ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ →
        InCandTreeList H P Δ (β.lift' ρ) (ts.lift' ρ) := by
    intro Γ' β ts ts' step _ ih Δ ρ W
    exact .expand _ _ (step.weak' W) (ih W)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact InCandTree.rec
      (motive_1 := fun Γ' β t _ => ∀ {Δ : List SExpr} {ρ : Lift},
        Ctx.Lift' ρ Γ' Δ → InCandTree H P Δ (β.lift' ρ) (t.lift' ρ))
      (motive_2 := fun Γ' β ts _ => ∀ {Δ : List SExpr} {ρ : Lift},
        Ctx.Lift' ρ Γ' Δ → InCandTreeList H P Δ (β.lift' ρ) (ts.lift' ρ))
      caseLeaf caseNode caseBranch caseNeuT caseExpT
      caseNil caseCons caseNeuL caseExpL h
  · exact InCandTreeList.rec
      (motive_1 := fun Γ' β t _ => ∀ {Δ : List SExpr} {ρ : Lift},
        Ctx.Lift' ρ Γ' Δ → InCandTree H P Δ (β.lift' ρ) (t.lift' ρ))
      (motive_2 := fun Γ' β ts _ => ∀ {Δ : List SExpr} {ρ : Lift},
        Ctx.Lift' ρ Γ' Δ → InCandTreeList H P Δ (β.lift' ρ) (ts.lift' ρ))
      caseLeaf caseNode caseBranch caseNeuT caseExpT
      caseNil caseCons caseNeuL caseExpL h

/-- **The acceptance-test lemma of the reshaping**: `Tree`-candidate
membership is stable under `Ctx.Lift'` — the very property the probe's
naive branch clause lacked. -/
theorem InCandTree.lift' {H : TreeHeads} {P : CtxPred}
    {Γ Δ : List SExpr} {ρ : Lift} {α t : SExpr} (hP : KripkeDomain P)
    (W : Ctx.Lift' ρ Γ Δ) (h : InCandTree H P Γ α t) :
    InCandTree H P Δ (α.lift' ρ) (t.lift' ρ) :=
  (inCand_lift' hP).1 h W

/-- `TreeList` side of lift stability. -/
theorem InCandTreeList.lift' {H : TreeHeads} {P : CtxPred}
    {Γ Δ : List SExpr} {ρ : Lift} {α ts : SExpr} (hP : KripkeDomain P)
    (W : Ctx.Lift' ρ Γ Δ) (h : InCandTreeList H P Γ α ts) :
    InCandTreeList H P Δ (α.lift' ρ) (ts.lift' ρ) :=
  (inCand_lift' hP).2 h W

/-- `Nat` calibration of lift stability: with no higher-order field the
proof is an ordinary structural induction. -/
theorem InCandNat.lift' {zeroC succC : Name} {ls : List SLevel}
    {Γ Δ : List SExpr} {ρ : Lift} {n : SExpr} (W : Ctx.Lift' ρ Γ Δ)
    (h : InCandNat zeroC succC ls Γ n) :
    InCandNat zeroC succC ls Δ (n.lift' ρ) := by
  induction h with
  | zero => exact .zero
  | succ n _ ih => exact .succ _ ih
  | neutral n hn => exact .neutral _ hn.lift'
  | expand n n' step _ ih => exact .expand _ _ (step.weak' W) ih

/-! ## The seam observation and result candidates -/

/-- The seam observation, context-local (definitionally `WHResult` with the
phantom type index dropped). -/
def WHReaches (Γ : List SExpr) (s : SExpr) : Prop :=
  ∃ r, WHRedS Γ s r ∧ WHNF Γ r

theorem whReaches_eq_whResult {Γ : List SExpr} {s A : SExpr} :
    WHReaches Γ s = WHResult Γ s A := rfl

/-- The abstract result candidate consumed by the fundamental iota case:
a context-indexed predicate closed under single-step untyped weak-head
expansion and containing every weak-head-normal term.  Both closure laws
hold of the seam's own observation (`WHReaches`), which is the intended
instance. -/
structure ResultCand (S : CtxPred) : Prop where
  expand : ∀ {Δ : List SExpr} {s s' : SExpr}, WHRed Δ s s' → S Δ s' → S Δ s
  whnf : ∀ {Δ : List SExpr} {s : SExpr}, WHNF Δ s → S Δ s

/-- The seam observation is a result candidate (its nonvacuity witness). -/
theorem WHReaches.resultCand : ResultCand WHReaches where
  expand := fun st h => by
    obtain ⟨r, run, nf⟩ := h
    exact ⟨r, ReflTransGen.trans (.tail .rfl st) run, nf⟩
  whnf := fun h => ⟨_, .rfl, h⟩

/-! ## The block rules, production-shaped

The five generated rules of the block, abstracted at one applied recursor
pair.  `recT`/`recL` stand for the two recursor spines with every argument
except the major applied (in production: `Tree.rec ls α M₁ M₂ m₁ … m₅` and
its `TreeList` twin — both major premises, both weak-head normal).  The step
fields are untyped `WHRed` steps at the exact generated contractum shapes,
stated in every future context: production steps are `WHRed.extra` on
`Pattern.Action`s for the registered rules (`ParamsD2.treeRule_registered`),
which exist uniformly at every context where the redex lives — producing
them is rung N′1 (header).  The Kripke fields are what lets the fundamental
iota case follow a membership derivation into the future contexts entered by
the branch clause. -/
structure TreeRules (H : TreeHeads) (Γ : List SExpr) (α : SExpr) :
    Type where
  recT : SExpr
  recL : SExpr
  minorLf : SExpr
  minorNd : SExpr
  minorBr : SExpr
  minorNl : SExpr
  minorCs : SExpr
  recT_major : IsMajorPremise recT
  recL_major : IsMajorPremise recL
  stuckT : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    ∀ {t : SExpr}, Neutral t → WHNF Δ ((recT.lift' ρ).app t)
  stuckL : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    ∀ {ts : SExpr}, Neutral ts → WHNF Δ ((recL.lift' ρ).app ts)
  leafStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ x,
    WHRed Δ ((recT.lift' ρ).app (leafApp H (α.lift' ρ) x))
      ((minorLf.lift' ρ).app x)
  nodeStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts,
    WHRed Δ ((recT.lift' ρ).app (nodeApp H (α.lift' ρ) ts))
      (((minorNd.lift' ρ).app ts).app ((recL.lift' ρ).app ts))
  branchStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ f,
    WHRed Δ ((recT.lift' ρ).app (branchApp H (α.lift' ρ) f))
      (((minorBr.lift' ρ).app f).app
        (.lam (α.lift' ρ)
          (((recL.lift' ρ).lift).app ((f.lift).app (.bvar 0)))))
  nilStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    WHRed Δ ((recL.lift' ρ).app (nilApp H (α.lift' ρ))) (minorNl.lift' ρ)
  consStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t ts,
    WHRed Δ ((recL.lift' ρ).app (consApp H (α.lift' ρ) t ts))
      (((((minorCs.lift' ρ).app t).app ts).app ((recT.lift' ρ).app t)).app
        ((recL.lift' ρ).app ts))

/-- The `branch` contractum at the base context. -/
def TreeRules.branchRHS {H : TreeHeads} {Γ : List SExpr} {α : SExpr}
    (R : TreeRules H Γ α) (f : SExpr) : SExpr :=
  (R.minorBr.app f).app (.lam α ((R.recL.lift).app ((f.lift).app (.bvar 0))))

/-! ### The tie to the killed transition

The two production pins carried from the probe: the under-Pi recursive major
is literally the production generated major of the `Tree.branch` descriptor,
and the branch step grows the syntax measure — the exact shape that defeated
the `(rank, size, depth)` order and every family-ordinal repair. -/

/-- Transparent syntax-node count on `SExpr`, mirroring
`L4L16NFailure.exprNodes`. -/
def sNodes : SExpr → Nat
  | .bvar _ | .sort _ | .const _ _ => 1
  | .app f a => sNodes f + sNodes a + 1
  | .lam A e => sNodes A + sNodes e + 1
  | .forallE A B => sNodes A + sNodes B + 1

theorem sNodes_lift' (e : SExpr) (ρ : Lift) :
    sNodes (e.lift' ρ) = sNodes e := by
  induction e generalizing ρ <;> simp [SExpr.lift', sNodes, *]

/-- The under-Pi recursive major at a bound-variable field is literally the
production generated major `app (bvar 1) (bvar 0)` of the `Tree.branch`
descriptor, through the semantic syntax map. -/
theorem underPi_major_eq_generatedMajor :
    (SExpr.bvar 0).lift.app (.bvar 0) =
      SExpr.mk (L4L16NFailure.generatedMajor 1
        L4L16NFailure.treeBranchRecursive) := by
  rw [L4L16NFailure.treeBranch_generatedMajor]
  rfl

/-- The branch step grows the syntax measure whenever the two recursor
spines have equal size (they do in production: both are the same captured
7-argument spine over a constant head).  This is the exact shape that
defeated the `(rank, size, depth)` order; the membership induction below
closes it anyway. -/
theorem branch_step_grows {H : TreeHeads} {Γ : List SExpr} {α : SExpr}
    (R : TreeRules H Γ α) (hsize : sNodes R.recT = sNodes R.recL)
    (f : SExpr) :
    sNodes (R.recT.app (branchApp H α f)) < sNodes (R.branchRHS f) := by
  simp only [TreeRules.branchRHS, branchApp, sNodes, SExpr.lift,
    sNodes_lift', hsize]
  omega

/-- Instantiating a lifted application spine under one binder: the under-Pi
recursive call applied to an argument beta-computes to the recursor applied
to the grown term `f · a`. -/
theorem underPi_inst (g h a : SExpr) :
    ((g.lift).app ((h.lift).app (.bvar 0))).inst a = g.app (h.app a) := by
  have unfold : ((g.lift).app ((h.lift).app (.bvar 0))).inst a =
      SExpr.app (g.lift.inst a) (SExpr.app (h.lift.inst a) a) := rfl
  rw [unfold, SExpr.lift_inst, SExpr.lift_inst]

/-- The under-Pi discharge: the lambda-packaged recursive call applied to an
argument takes one real `WHRed.beta` step to the recursor at the grown term. -/
theorem underPi_beta {Γ : List SExpr} (α g h a : SExpr) :
    WHRed Γ ((SExpr.lam α ((g.lift).app ((h.lift).app (.bvar 0)))).app a)
      (g.app (h.app a)) := by
  have step : WHRed Γ
      ((SExpr.lam α ((g.lift).app ((h.lift).app (.bvar 0)))).app a)
      (((g.lift).app ((h.lift).app (.bvar 0))).inst a) := .beta
  rwa [underPi_inst] at step

/-! ## The fundamental iota case, with no syntactic measure -/

/-- **The discriminating theorem, re-proved against the Kripke-style
definitions.**  The fundamental theorem's iota case for the whole block, by
one structural induction on the candidate-membership derivation — no term
measure, no family rank.  The minor-premise hypotheses are the semantic
inputs the real fundamental theorem obtains from the minor premises' own
(Kripke) candidacy; `mBr` receives the recursive-call function
observationally, exactly as the production rule passes
`fun y => TreeList.rec … (f y)`.

In the `branch` case the induction hypothesis is available at every future
context the Kripke clause reaches; instantiated at the reflexive lift it
gives `S Δ (recL↑ρ · (f · a))` — the term that **grew** — because that
term's membership is a sub-derivation premise of the `branch` membership
constructor.  In the `cons` case the `Tree`-motive IH is used inside a
`TreeList`-motive case: the reverse mutual edge that refuted every family
rank is handled structurally.  The derivation-spanning contexts are absorbed
by the motive, which carries the lift that reached each node. -/
theorem TreeRules.fundamental_iota {H : TreeHeads} {Γ : List SExpr}
    {α : SExpr} {P S : CtxPred}
    (R : TreeRules H Γ α) (SC : ResultCand S)
    (mLf : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ x, P Δ x →
      S Δ ((R.minorLf.lift' ρ).app x))
    (mNd : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts,
      InCandTreeList H P Δ (α.lift' ρ) ts → S Δ ((R.recL.lift' ρ).app ts) →
      S Δ (((R.minorNd.lift' ρ).app ts).app ((R.recL.lift' ρ).app ts)))
    (mBr : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ f,
      (∀ {Δ' : List SExpr} {ρ' : Lift}, Ctx.Lift' ρ' Δ Δ' → ∀ a, P Δ' a →
        InCandTreeList H P Δ' ((α.lift' ρ).lift' ρ') ((f.lift' ρ').app a)) →
      ∀ g, (∀ a, P Δ a → S Δ (g.app a)) →
        S Δ (((R.minorBr.lift' ρ).app f).app g))
    (mNl : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      S Δ (R.minorNl.lift' ρ))
    (mCs : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t ts,
      InCandTree H P Δ (α.lift' ρ) t → InCandTreeList H P Δ (α.lift' ρ) ts →
      S Δ ((R.recT.lift' ρ).app t) → S Δ ((R.recL.lift' ρ).app ts) →
      S Δ (((((R.minorCs.lift' ρ).app t).app ts).app
        ((R.recT.lift' ρ).app t)).app ((R.recL.lift' ρ).app ts))) :
    (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t : SExpr,
        InCandTree H P Δ (α.lift' ρ) t → S Δ ((R.recT.lift' ρ).app t)) ∧
      (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts : SExpr,
        InCandTreeList H P Δ (α.lift' ρ) ts →
          S Δ ((R.recL.lift' ρ).app ts)) := by
  have caseLeaf : ∀ {Δ : List SExpr} {β : SExpr} (x : SExpr), P Δ x →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app (leafApp H β x)) := by
    intro Δ β x hx ρ W hβ
    subst hβ
    exact SC.expand (R.leafStep W x) (mLf W x hx)
  have caseNode : ∀ {Δ : List SExpr} {β : SExpr} (ts : SExpr),
      InCandTreeList H P Δ β ts →
      (∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app ts)) →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app (nodeApp H β ts)) := by
    intro Δ β ts hts ih ρ W hβ
    subst hβ
    exact SC.expand (R.nodeStep W ts) (mNd W ts hts (ih ρ W rfl))
  have caseBranch : ∀ {Δ : List SExpr} {β : SExpr} (f : SExpr),
      (∀ {Δ' : List SExpr} {ρ' : Lift}, Ctx.Lift' ρ' Δ Δ' → ∀ a : SExpr,
        P Δ' a → InCandTreeList H P Δ' (β.lift' ρ') ((f.lift' ρ').app a)) →
      (∀ {Δ' : List SExpr} {ρ' : Lift} (_ : Ctx.Lift' ρ' Δ Δ') (a : SExpr)
        (_ : P Δ' a), ∀ ρ'' : Lift, Ctx.Lift' ρ'' Γ Δ' →
          β.lift' ρ' = α.lift' ρ'' →
          S Δ' ((R.recL.lift' ρ'').app ((f.lift' ρ').app a))) →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app (branchApp H β f)) := by
    intro Δ β f hf ih ρ W hβ
    subst hβ
    refine SC.expand (R.branchStep W f) (mBr W f hf _ fun a ha => ?_)
    refine SC.expand (underPi_beta (α.lift' ρ) (R.recL.lift' ρ) f a) ?_
    have := ih Ctx.Lift'.refl a ha ρ W SExpr.lift'_refl
    simpa only [SExpr.lift'_refl] using this
  have caseNeuT : ∀ {Δ : List SExpr} {β : SExpr} (t : SExpr), Neutral t →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app t) := by
    intro Δ β t hn ρ W _
    exact SC.whnf (R.stuckT W hn)
  have caseExpT : ∀ {Δ : List SExpr} {β : SExpr} (t t' : SExpr),
      WHRed Δ t t' → InCandTree H P Δ β t' →
      (∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app t')) →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app t) := by
    intro Δ β t t' step _ ih ρ W hβ
    exact SC.expand
      (WHRed.major (IsMajorPremise.lift'.2 R.recT_major) step) (ih ρ W hβ)
  have caseNil : ∀ {Δ : List SExpr} {β : SExpr},
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app (nilApp H β)) := by
    intro Δ β ρ W hβ
    subst hβ
    exact SC.expand (R.nilStep W) (mNl W)
  have caseCons : ∀ {Δ : List SExpr} {β : SExpr} (t ts : SExpr),
      InCandTree H P Δ β t → InCandTreeList H P Δ β ts →
      (∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app t)) →
      (∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app ts)) →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app (consApp H β t ts)) := by
    intro Δ β t ts ht hts ih₁ ih₂ ρ W hβ
    subst hβ
    exact SC.expand (R.consStep W t ts)
      (mCs W t ts ht hts (ih₁ ρ W rfl) (ih₂ ρ W rfl))
  have caseNeuL : ∀ {Δ : List SExpr} {β : SExpr} (ts : SExpr), Neutral ts →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app ts) := by
    intro Δ β ts hn ρ W _
    exact SC.whnf (R.stuckL W hn)
  have caseExpL : ∀ {Δ : List SExpr} {β : SExpr} (ts ts' : SExpr),
      WHRed Δ ts ts' → InCandTreeList H P Δ β ts' →
      (∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app ts')) →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app ts) := by
    intro Δ β ts ts' step _ ih ρ W hβ
    exact SC.expand
      (WHRed.major (IsMajorPremise.lift'.2 R.recL_major) step) (ih ρ W hβ)
  refine ⟨fun {Δ ρ} W t h => ?_, fun {Δ ρ} W ts h => ?_⟩
  · exact InCandTree.rec
      (motive_1 := fun Δ' β t _ => ∀ ρ' : Lift, Ctx.Lift' ρ' Γ Δ' →
        β = α.lift' ρ' → S Δ' ((R.recT.lift' ρ').app t))
      (motive_2 := fun Δ' β ts _ => ∀ ρ' : Lift, Ctx.Lift' ρ' Γ Δ' →
        β = α.lift' ρ' → S Δ' ((R.recL.lift' ρ').app ts))
      caseLeaf caseNode caseBranch caseNeuT caseExpT
      caseNil caseCons caseNeuL caseExpL h ρ W rfl
  · exact InCandTreeList.rec
      (motive_1 := fun Δ' β t _ => ∀ ρ' : Lift, Ctx.Lift' ρ' Γ Δ' →
        β = α.lift' ρ' → S Δ' ((R.recT.lift' ρ').app t))
      (motive_2 := fun Δ' β ts _ => ∀ ρ' : Lift, Ctx.Lift' ρ' Γ Δ' →
        β = α.lift' ρ' → S Δ' ((R.recL.lift' ρ').app ts))
      caseLeaf caseNode caseBranch caseNeuT caseExpT
      caseNil caseCons caseNeuL caseExpL h ρ W rfl

/-- The pointed form of the discriminating case: from the premise of a
`branch` membership node, the exact contracted RHS — which applies the
recursor to the grown term under the Pi binder — is again in the result
candidate. -/
theorem TreeRules.branchRHS_in_candidate {H : TreeHeads} {Γ : List SExpr}
    {α : SExpr} {P S : CtxPred}
    (R : TreeRules H Γ α) (SC : ResultCand S)
    (mLf : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ x, P Δ x →
      S Δ ((R.minorLf.lift' ρ).app x))
    (mNd : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts,
      InCandTreeList H P Δ (α.lift' ρ) ts → S Δ ((R.recL.lift' ρ).app ts) →
      S Δ (((R.minorNd.lift' ρ).app ts).app ((R.recL.lift' ρ).app ts)))
    (mBr : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ f,
      (∀ {Δ' : List SExpr} {ρ' : Lift}, Ctx.Lift' ρ' Δ Δ' → ∀ a, P Δ' a →
        InCandTreeList H P Δ' ((α.lift' ρ).lift' ρ') ((f.lift' ρ').app a)) →
      ∀ g, (∀ a, P Δ a → S Δ (g.app a)) →
        S Δ (((R.minorBr.lift' ρ).app f).app g))
    (mNl : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      S Δ (R.minorNl.lift' ρ))
    (mCs : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t ts,
      InCandTree H P Δ (α.lift' ρ) t → InCandTreeList H P Δ (α.lift' ρ) ts →
      S Δ ((R.recT.lift' ρ).app t) → S Δ ((R.recL.lift' ρ).app ts) →
      S Δ (((((R.minorCs.lift' ρ).app t).app ts).app
        ((R.recT.lift' ρ).app t)).app ((R.recL.lift' ρ).app ts)))
    (f : SExpr)
    (hf : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ a, P Δ a →
      InCandTreeList H P Δ (α.lift' ρ) ((f.lift' ρ).app a)) :
    S Γ (R.branchRHS f) := by
  have halves := R.fundamental_iota SC mLf mNd mBr mNl mCs
  have hf' : ∀ {Δ' : List SExpr} {ρ' : Lift}, Ctx.Lift' ρ' Γ Δ' →
      ∀ a, P Δ' a → InCandTreeList H P Δ'
        ((α.lift' Lift.refl).lift' ρ') ((f.lift' ρ').app a) := by
    intro Δ' ρ' W' a ha
    simpa only [SExpr.lift'_refl] using hf W' a ha
  have out := mBr Ctx.Lift'.refl f hf'
    (.lam α ((R.recL.lift).app ((f.lift).app (.bvar 0))))
    (fun a ha => by
      refine SC.expand (underPi_beta α R.recL f a) ?_
      have := halves.2 Ctx.Lift'.refl (f.app a)
        (by simpa only [SExpr.lift'_refl] using hf Ctx.Lift'.refl a ha)
      simpa only [SExpr.lift'_refl] using this)
  simpa only [SExpr.lift'_refl, TreeRules.branchRHS] using out

/-- The two `Nat` rules, production-shaped the same way. -/
structure NatRules (zeroC succC : Name) (ls : List SLevel)
    (Γ : List SExpr) : Type where
  recN : SExpr
  minorZ : SExpr
  minorS : SExpr
  recN_major : IsMajorPremise recN
  stuckN : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    ∀ {n : SExpr}, Neutral n → WHNF Δ ((recN.lift' ρ).app n)
  zeroStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    WHRed Δ ((recN.lift' ρ).app (.const zeroC ls)) (minorZ.lift' ρ)
  succStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ n,
    WHRed Δ ((recN.lift' ρ).app ((SExpr.const succC ls).app n))
      (((minorS.lift' ρ).app n).app ((recN.lift' ρ).app n))

/-- The `Nat` fundamental iota case against the Kripke-style rules, by
ordinary structural induction on membership: the derivation never leaves its
context, so the lift is fixed outside the induction. -/
theorem NatRules.fundamental_iota {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} {S : CtxPred}
    (R : NatRules zeroC succC ls Γ) (SC : ResultCand S)
    (mZ : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      S Δ (R.minorZ.lift' ρ))
    (mS : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ n,
      InCandNat zeroC succC ls Δ n → S Δ ((R.recN.lift' ρ).app n) →
      S Δ (((R.minorS.lift' ρ).app n).app ((R.recN.lift' ρ).app n)))
    {Δ : List SExpr} {ρ : Lift} (W : Ctx.Lift' ρ Γ Δ)
    {n : SExpr} (h : InCandNat zeroC succC ls Δ n) :
    S Δ ((R.recN.lift' ρ).app n) := by
  induction h with
  | zero => exact SC.expand (R.zeroStep W) (mZ W)
  | succ n hn ih => exact SC.expand (R.succStep W n) (mS W n hn ih)
  | neutral n hn => exact SC.whnf (R.stuckN W hn)
  | expand n n' step _ ih =>
    exact SC.expand
      (WHRed.major (IsMajorPremise.lift'.2 R.recN_major) step) ih

/-! ## Seam compatibility

The seam (`TypedWHNormalization`) demands, for typed terms, the untyped
observation `WHResult Γ M A` (whnf existence on the `WHRedS` trace; the type
index is phantom).  Candidate membership yields exactly that observation,
given the block heads classify as constructors (so constructor spines are
weak-head normal, `WHNF.ctorSpine`). -/

/-- The head dictionary's classification facts (the block heads are
classified constructors of their production arities). -/
structure TreeClassified (H : TreeHeads) : Prop where
  leaf_cl : Params.classify H.leafC = some (.ctor 2)
  node_cl : Params.classify H.nodeC = some (.ctor 2)
  branch_cl : Params.classify H.branchC = some (.ctor 2)
  nil_cl : Params.classify H.nilC = some (.ctor 1)
  cons_cl : Params.classify H.consC = some (.ctor 3)

/-- Candidate membership yields the seam's untyped weak-head normalization
observation, by the same membership induction (constructor spines are
already normal; neutrals are normal; expansion prepends its real step to the
reduct's trace). -/
theorem inCand_whReaches {H : TreeHeads} {P : CtxPred}
    (C : TreeClassified H) :
    (∀ {Γ : List SExpr} {α t : SExpr}, InCandTree H P Γ α t →
        WHReaches Γ t) ∧
      (∀ {Γ : List SExpr} {α ts : SExpr}, InCandTreeList H P Γ α ts →
        WHReaches Γ ts) := by
  have caseLeaf : ∀ {Γ' : List SExpr} {β : SExpr} (x : SExpr), P Γ' x →
      WHReaches Γ' (leafApp H β x) :=
    fun x _ => ⟨_, .rfl, WHNF.ctorSpine C.leaf_cl [x, _]⟩
  have caseNode : ∀ {Γ' : List SExpr} {β : SExpr} (ts : SExpr),
      InCandTreeList H P Γ' β ts → WHReaches Γ' ts →
      WHReaches Γ' (nodeApp H β ts) :=
    fun ts _ _ => ⟨_, .rfl, WHNF.ctorSpine C.node_cl [ts, _]⟩
  have caseBranch : ∀ {Γ' : List SExpr} {β : SExpr} (f : SExpr),
      (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ → ∀ a, P Δ a →
        InCandTreeList H P Δ (β.lift' ρ) ((f.lift' ρ).app a)) →
      (∀ {Δ : List SExpr} {ρ : Lift} (_ : Ctx.Lift' ρ Γ' Δ) (a : SExpr)
        (_ : P Δ a), WHReaches Δ ((f.lift' ρ).app a)) →
      WHReaches Γ' (branchApp H β f) :=
    fun f _ _ => ⟨_, .rfl, WHNF.ctorSpine C.branch_cl [f, _]⟩
  have caseExpT : ∀ {Γ' : List SExpr} {β : SExpr} (t t' : SExpr),
      WHRed Γ' t t' → InCandTree H P Γ' β t' → WHReaches Γ' t' →
      WHReaches Γ' t :=
    fun t t' step _ ih => WHReaches.resultCand.expand step ih
  have caseNil : ∀ {Γ' : List SExpr} {β : SExpr},
      WHReaches Γ' (nilApp H β) :=
    ⟨_, .rfl, WHNF.ctorSpine C.nil_cl [_]⟩
  have caseCons : ∀ {Γ' : List SExpr} {β : SExpr} (t ts : SExpr),
      InCandTree H P Γ' β t → InCandTreeList H P Γ' β ts →
      WHReaches Γ' t → WHReaches Γ' ts →
      WHReaches Γ' (consApp H β t ts) :=
    fun t ts _ _ _ _ => ⟨_, .rfl, WHNF.ctorSpine C.cons_cl [ts, t, _]⟩
  have caseExpL : ∀ {Γ' : List SExpr} {β : SExpr} (ts ts' : SExpr),
      WHRed Γ' ts ts' → InCandTreeList H P Γ' β ts' → WHReaches Γ' ts' →
      WHReaches Γ' ts :=
    fun ts ts' step _ ih => WHReaches.resultCand.expand step ih
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact InCandTree.rec
      (motive_1 := fun Γ' β t _ => WHReaches Γ' t)
      (motive_2 := fun Γ' β ts _ => WHReaches Γ' ts)
      caseLeaf caseNode caseBranch
      (fun {Γ' β} t hn => ⟨t, .rfl, hn.whnf⟩) caseExpT
      caseNil caseCons
      (fun {Γ' β} ts hn => ⟨ts, .rfl, hn.whnf⟩) caseExpL h
  · exact InCandTreeList.rec
      (motive_1 := fun Γ' β t _ => WHReaches Γ' t)
      (motive_2 := fun Γ' β ts _ => WHReaches Γ' ts)
      caseLeaf caseNode caseBranch
      (fun {Γ' β} t hn => ⟨t, .rfl, hn.whnf⟩) caseExpT
      caseNil caseCons
      (fun {Γ' β} ts hn => ⟨ts, .rfl, hn.whnf⟩) caseExpL h

/-- The seam-facing corollary, in the seam's own vocabulary: every candidate
member has a `WHResult` at every displayed type. -/
theorem InCandTree.toWHResult {H : TreeHeads} {P : CtxPred}
    {Γ : List SExpr} {α A : SExpr} (C : TreeClassified H) {t : SExpr}
    (h : InCandTree H P Γ α t) : WHResult Γ t A :=
  (inCand_whReaches C).1 h

/-- `TreeList` side of the seam-facing corollary. -/
theorem InCandTreeList.toWHResult {H : TreeHeads} {P : CtxPred}
    {Γ : List SExpr} {α A : SExpr} (C : TreeClassified H) {ts : SExpr}
    (h : InCandTreeList H P Γ α ts) : WHResult Γ ts A :=
  (inCand_whReaches C).2 h

/-- `Nat` calibration of the seam-facing corollary. -/
theorem InCandNat.toWHResult {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} {A : SExpr}
    (hz : Params.classify zeroC = some (.ctor 0))
    (hs : Params.classify succC = some (.ctor 1))
    {n : SExpr} (h : InCandNat zeroC succC ls Γ n) :
    WHResult Γ n A := by
  induction h with
  | zero => exact ⟨_, .rfl, WHNF.ctorSpine hz []⟩
  | succ n hn ih => exact ⟨_, .rfl, WHNF.ctorSpine hs [n]⟩
  | neutral n hn => exact ⟨n, .rfl, hn.whnf⟩
  | expand n n' step _ ih =>
    obtain ⟨r, run, nf⟩ := ih
    exact ⟨r, ReflTransGen.trans (.tail .rfl step) run, nf⟩

/-- The end-to-end composition at the seam observation: the fundamental
iota case instantiated at `S := WHReaches` emits `WHResult` for every
recursor application at a candidate major — the Tait-core statement shape
for the route, on the untyped trace. -/
theorem TreeRules.recT_whResult {H : TreeHeads} {Γ : List SExpr}
    {α A : SExpr} {P : CtxPred} (R : TreeRules H Γ α)
    (mLf : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ x, P Δ x →
      WHReaches Δ ((R.minorLf.lift' ρ).app x))
    (mNd : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts,
      InCandTreeList H P Δ (α.lift' ρ) ts →
      WHReaches Δ ((R.recL.lift' ρ).app ts) →
      WHReaches Δ
        (((R.minorNd.lift' ρ).app ts).app ((R.recL.lift' ρ).app ts)))
    (mBr : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ f,
      (∀ {Δ' : List SExpr} {ρ' : Lift}, Ctx.Lift' ρ' Δ Δ' → ∀ a, P Δ' a →
        InCandTreeList H P Δ' ((α.lift' ρ).lift' ρ') ((f.lift' ρ').app a)) →
      ∀ g, (∀ a, P Δ a → WHReaches Δ (g.app a)) →
        WHReaches Δ (((R.minorBr.lift' ρ).app f).app g))
    (mNl : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      WHReaches Δ (R.minorNl.lift' ρ))
    (mCs : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t ts,
      InCandTree H P Δ (α.lift' ρ) t → InCandTreeList H P Δ (α.lift' ρ) ts →
      WHReaches Δ ((R.recT.lift' ρ).app t) →
      WHReaches Δ ((R.recL.lift' ρ).app ts) →
      WHReaches Δ (((((R.minorCs.lift' ρ).app t).app ts).app
        ((R.recT.lift' ρ).app t)).app ((R.recL.lift' ρ).app ts)))
    {t : SExpr} (h : InCandTree H P Γ α t) :
    WHResult Γ (R.recT.app t) A := by
  have out := (R.fundamental_iota WHReaches.resultCand
      mLf mNd mBr mNl mCs).1 Ctx.Lift'.refl t
    (by simpa only [SExpr.lift'_refl] using h)
  have out' : WHReaches Γ (R.recT.app t) := by
    simpa only [SExpr.lift'_refl] using out
  exact out'

/-! ### Kill check K3 — expansion closure vs. untyped determinism

The `expand` clauses consume `WHRed` itself — no candidate-invented steps —
so the deterministic trace structure the seam assumes is inherited: the
normal form reached from any member is unique.  No conflict. -/

theorem k3_member_normal_form_unique {H : TreeHeads} {P : CtxPred}
    {Γ : List SExpr} {α t r₁ r₂ : SExpr}
    (_h : InCandTree H P Γ α t)
    (run₁ : WHRedS Γ t r₁) (nf₁ : WHNF Γ r₁)
    (run₂ : WHRedS Γ t r₂) (nf₂ : WHNF Γ r₂) : r₁ = r₂ :=
  WHRedS.determ run₁ nf₁ run₂ nf₂

/-! ## The D2 and D0 instance discharge

The head dictionary and its classification facts hold at the production
block-extended instance `ParamsD2.d2Params`, so the seam-facing
normalization theorems fire on the real D2 environment (and the `Nat` facts
on the same instance, which extends D0, plus separately at the D0 instance
itself).  Bundled as one `Prop` each so the instance application stays a
single `@`. -/

/-- D2 instance-discharge endpoint: at any level instantiation, the
production D2 head dictionary is classified, the `Nat` heads classify as
their D0 constructors, and the concrete higher-order branch witness
normalizes on the untyped trace. -/
def D2DischargePackage : Prop :=
  ∀ l : SLevel, ∃ H : TreeHeads,
    H.leafC = ``Tree.leaf ∧ H.nodeC = ``Tree.node ∧
    H.branchC = ``Tree.branch ∧ H.nilC = ``TreeList.nil ∧
    H.consC = ``TreeList.cons ∧ H.ls = [l] ∧
    TreeClassified H ∧
    Params.classify ``Nat.zero = some (.ctor 0) ∧
    Params.classify ``Nat.succ = some (.ctor 1) ∧
    ∀ (Γ : List SExpr) (α A : SExpr),
      WHResult Γ (branchApp H α (.lam α (nilApp H α).lift)) A

/-- D0 instance-discharge endpoint: the `Nat` heads classify as their
constructors and the concrete `succ (succ zero)` member normalizes on the
untyped trace. -/
def D0DischargePackage : Prop :=
  Params.classify ``Nat.zero = some (.ctor 0) ∧
  Params.classify ``Nat.succ = some (.ctor 1) ∧
  ∀ (ls : List SLevel) (Γ : List SExpr) (A : SExpr),
    WHResult Γ ((SExpr.const ``Nat.succ ls).app
      ((SExpr.const ``Nat.succ ls).app (.const ``Nat.zero ls))) A

end IndCand
end Reducibility
end SExpr
end Lean4Lean

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

/-- The production D2/D0 discharge: every classification fact is a kernel
computation of `d2Classify`, and the witness theorem fires generically. -/
theorem d2Discharge (univs : Nat) :
    @D2DischargePackage (ParamsD2.d2Params univs) := by
  letI : Params := ParamsD2.d2Params univs
  intro l
  refine ⟨⟨``Tree.leaf, ``Tree.node, ``Tree.branch, ``TreeList.nil,
    ``TreeList.cons, [l]⟩, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_⟩
  intro Γ α A
  exact InCandTree.toWHResult ⟨rfl, rfl, rfl, rfl, rfl⟩ witness_branch

/-- The production D0 discharge at `d0Params` itself. -/
theorem d0Discharge (univs : Nat) :
    @D0DischargePackage (ParamsD0.d0Params univs) := by
  letI : Params := ParamsD0.d0Params univs
  exact ⟨rfl, rfl, fun ls Γ A =>
    InCandNat.toWHResult rfl rfl witness_nat_two⟩

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! # L4L-16N′1 — real-rule steps, stuck facts, membership normalization

The rung's generic layer: the stuck-major families, the site-to-step
adapter, the untyped multi-beta collapse, the one-step shape finding, and
membership normalization.  The production-instance layer follows in the
next section. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

variable [Params]

/-! ### L4L-16N′1 stuck majors

A recursor spine missing only its major premise, applied to a neutral term,
is weak-head normal: the spine itself is normal (`IsMajorPremise.whnf`),
the neutral major is normal (`Neutral.whnf`) and matches no registered
pattern (`Neutral.noMatches`), a major-premise spine is never a lambda
(`IsMajorPremise.lam`), and no registered pattern is a bare variable
(`Params.pat_not_varS`).  This is the entire production content of the
`TreeRules.stuckT`/`stuckL` and `NatRules.stuckN` fields, discharged
unconditionally and uniformly — no per-rule case analysis. -/

/-- The pointed stuck-major fact. -/
theorem _root_.Lean4Lean.SExpr.IsMajorPremise.stuckApp
    {Γ : List SExpr} {f t : SExpr}
    (hmaj : IsMajorPremise f) (hn : Neutral t) : WHNF Γ (f.app t) := by
  intro e' hred
  cases hred with
  | app h1 => exact hmaj.whnf _ h1
  | major _ h2 => exact hn.whnf _ h2
  | beta => exact absurd hmaj IsMajorPremise.lam
  | extra action =>
    cases action.matched with
    | var => exact Params.pat_not_varS action.pat
    | app _ harg => exact hn.noMatches harg

/-- The stuck-major family, in exactly the Kripke field shape of
`TreeRules.stuckT`/`stuckL` and `NatRules.stuckN`. -/
theorem stuck_major_kripke {Γ : List SExpr} {f : SExpr}
    (hmaj : IsMajorPremise f) :
    ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      ∀ {t : SExpr}, Neutral t → WHNF Δ ((f.lift' ρ).app t) := by
  intro Δ ρ _ t hn
  exact (IsMajorPremise.lift'.2 hmaj).stuckApp hn

/-- Assemble a `TreeRules` pack from its five step families alone: the two
major-premise facts are inputs and both stuck families are discharged by
`stuck_major_kripke` — the stuck half of the structure is closed
unconditionally.  What the production registry can and cannot supply for
the five step inputs is the subject of the one-step finding below. -/
def TreeRules.ofSteps {H : TreeHeads} {Γ : List SExpr} {α : SExpr}
    {recT recL minorLf minorNd minorBr minorNl minorCs : SExpr}
    (recT_major : IsMajorPremise recT) (recL_major : IsMajorPremise recL)
    (leafStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ x,
      WHRed Δ ((recT.lift' ρ).app (leafApp H (α.lift' ρ) x))
        ((minorLf.lift' ρ).app x))
    (nodeStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts,
      WHRed Δ ((recT.lift' ρ).app (nodeApp H (α.lift' ρ) ts))
        (((minorNd.lift' ρ).app ts).app ((recL.lift' ρ).app ts)))
    (branchStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ f,
      WHRed Δ ((recT.lift' ρ).app (branchApp H (α.lift' ρ) f))
        (((minorBr.lift' ρ).app f).app
          (.lam (α.lift' ρ)
            (((recL.lift' ρ).lift).app ((f.lift).app (.bvar 0))))))
    (nilStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      WHRed Δ ((recL.lift' ρ).app (nilApp H (α.lift' ρ)))
        (minorNl.lift' ρ))
    (consStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t ts,
      WHRed Δ ((recL.lift' ρ).app (consApp H (α.lift' ρ) t ts))
        (((((minorCs.lift' ρ).app t).app ts).app
          ((recT.lift' ρ).app t)).app ((recL.lift' ρ).app ts))) :
    TreeRules H Γ α where
  recT := recT
  recL := recL
  minorLf := minorLf
  minorNd := minorNd
  minorBr := minorBr
  minorNl := minorNl
  minorCs := minorCs
  recT_major := recT_major
  recL_major := recL_major
  stuckT := stuck_major_kripke recT_major
  stuckL := stuck_major_kripke recL_major
  leafStep := leafStep
  nodeStep := nodeStep
  branchStep := branchStep
  nilStep := nilStep
  consStep := consStep

/-- `Nat` side of the step-family assembler: the stuck field is discharged
by `stuck_major_kripke`. -/
def NatRules.ofSteps {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} {recN minorZ minorS : SExpr}
    (recN_major : IsMajorPremise recN)
    (zeroStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      WHRed Δ ((recN.lift' ρ).app (.const zeroC ls)) (minorZ.lift' ρ))
    (succStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ n,
      WHRed Δ ((recN.lift' ρ).app ((SExpr.const succC ls).app n))
        (((minorS.lift' ρ).app n).app ((recN.lift' ρ).app n))) :
    NatRules zeroC succC ls Γ where
  recN := recN
  minorZ := minorZ
  minorS := minorS
  recN_major := recN_major
  stuckN := stuck_major_kripke recN_major
  zeroStep := zeroStep
  succStep := succStep

/-! ### L4L-16N′1 the generated step, generically

A reduction-site certificate immediately yields the *untyped* operational
step: `WHRed.extra` on `IotaReductionSite.action`.  The one-step target is
the applied right tower `r.1.applyS m1 m2` — the registered closed lambda
tower applied to the ordered captures — NOT the collapsed minor-premise
form; the collapse from the tower to the landed contractum shapes is the
pure-syntax multi-beta run below (per-rule instantiation of the generated
tower bodies is the mechanical volume Lane D already scopes). -/

/-- **A generated reduction site steps.**  The untyped operational content
of a site certificate: one `WHRed.extra` step from the matched redex to the
applied registered right tower. -/
theorem _root_.Lean4Lean.Pattern.IotaReductionSite.whRed
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r}
    {Γ : List SExpr} {recLs ctorLs : List SLevel}
    {recArgs ctorArgs : List SExpr} {majorTerm A : SExpr}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {captureTyping : Pattern.CaptureTyping Γ mcap captureType}
    (site : Pattern.IotaReductionSite Γ r rule recLs ctorLs recArgs ctorArgs
      majorTerm A mcap captureType captureTyping) :
    WHRed Γ
      ((recArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ctor ctorLs)))
      (r.1.applyS recLs mcap) :=
  .extra site.action

/-- Weak-head reduction is a congruence under a left application spine. -/
theorem whRedS_foldl_app {Γ : List SExpr} :
    ∀ (args : List SExpr) {e e' : SExpr}, WHRedS Γ e e' →
      WHRedS Γ (args.foldl (fun (f a : SExpr) => f.app a) e)
        (args.foldl (fun (f a : SExpr) => f.app a) e')
  | [], _, _, H => H
  | _ :: args, _, _, H => whRedS_foldl_app args H.app

/-- One beta contraction under a left application spine: the engine of the
applied-tower collapse.  Iterating it (once per tower binder, computing the
instantiation each time) walks the applied right tower down to the fully
collapsed contractum — the landed `TreeRules`/`NatRules` target shapes. -/
theorem whRedS_foldl_beta {Γ : List SExpr} (A e a : SExpr)
    (args : List SExpr) :
    WHRedS Γ
      (args.foldl (fun (f a : SExpr) => f.app a) ((SExpr.lam A e).app a))
      (args.foldl (fun (f a : SExpr) => f.app a) (e.inst a)) :=
  whRedS_foldl_app args (.tail .rfl .beta)

/-! ### L4L-16N′1 the one-step shape finding

The landed `TreeRules`/`NatRules` step fields demand a *single* `WHRed`
step landing on the fully collapsed contractum.  At a generated registry
the unique step out of a live redex is `WHRed.extra` onto the applied right
tower, whose outermost argument is the last capture — a subterm of the
redex — never the packaged recursive call the collapsed `node`/`succ`/
`cons` shapes carry in that position.  `WHRed.determ` therefore refutes the
landed one-step field at any redex whose actual step lands on a tower
application: the landed one-step structures describe the mock registry of
probe Z16, and the production interface is `IotaReductionSite.whRed` plus
the multi-beta collapse above. -/

/-- The collapsed `node` contractum shape is never a one-argument
application ending in the bare capture: its outermost argument `recL·ts`
strictly contains `ts`. -/
theorem tower_target_ne_nodeShape (X mNd recL ts : SExpr) :
    X.app ts ≠ (mNd.app ts).app (recL.app ts) := by
  intro h
  injection h with h1 h2
  have hsize := congrArg sNodes h2
  simp only [sNodes] at hsize
  omega

/-- Determinism turns the shape difference into a refutation: a redex whose
real one-step target is a tower application ending in the capture `ts`
admits no one-step reduction to the landed `nodeStep` contractum shape.
The `succ` and `cons` shapes fail the same size test, and `branch`'s
lambda-packaged second argument likewise differs from every capture. -/
theorem oneStep_nodeShape_refuted {Γ : List SExpr}
    {e X mNd recL ts : SExpr} (htower : WHRed Γ e (X.app ts)) :
    ¬WHRed Γ e ((mNd.app ts).app (recL.app ts)) :=
  fun h => tower_target_ne_nodeShape X mNd recL ts (htower.determ h)

/-! ### L4L-16N′1 membership ⇒ `KripkeNormalizes`

The assumed `Base.normalizes` field becomes a theorem for candidate
members: lift stability (`InCand*.lift'`) carries membership into every
future context, and the seam observation (`toWHResult`) normalizes it
there.  The type index of `WHResult` is phantom, so the statement holds at
every displayed type — exactly the shape `Reducibility.KripkeNormalizes`
demands.  The `Base` corollaries take the judgmental edge as a hypothesis:
no typed-trace content is derived here (betaFire boundary). -/

/-- Members of the `Tree` candidate Kripke-normalize at every displayed
type: `Base.normalizes` as a theorem. -/
theorem InCandTree.kripkeNormalizes {H : TreeHeads} {P : CtxPred}
    {Γ : List SExpr} {α M N A : SExpr} (hP : KripkeDomain P)
    (C : TreeClassified H)
    (hM : InCandTree H P Γ α M) (hN : InCandTree H P Γ α N) :
    KripkeNormalizes Γ M N A := by
  intro Δ ρ W
  exact ⟨(hM.lift' hP W).toWHResult C, (hN.lift' hP W).toWHResult C⟩

/-- `TreeList` side of membership Kripke normalization. -/
theorem InCandTreeList.kripkeNormalizes {H : TreeHeads} {P : CtxPred}
    {Γ : List SExpr} {α M N A : SExpr} (hP : KripkeDomain P)
    (C : TreeClassified H)
    (hM : InCandTreeList H P Γ α M) (hN : InCandTreeList H P Γ α N) :
    KripkeNormalizes Γ M N A := by
  intro Δ ρ W
  exact ⟨(hM.lift' hP W).toWHResult C, (hN.lift' hP W).toWHResult C⟩

/-- `Nat` calibration of membership Kripke normalization. -/
theorem InCandNat.kripkeNormalizes {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} {M N A : SExpr}
    (hz : Params.classify zeroC = some (.ctor 0))
    (hs : Params.classify succC = some (.ctor 1))
    (hM : InCandNat zeroC succC ls Γ M)
    (hN : InCandNat zeroC succC ls Γ N) :
    KripkeNormalizes Γ M N A := by
  intro Δ ρ W
  exact ⟨(hM.lift' W).toWHResult hz hs, (hN.lift' W).toWHResult hz hs⟩

/-- `Base` assembly for `Tree`-candidate members: the edge is supplied as a
hypothesis (betaFire boundary — this rung derives no typed traces), and the
normalization half is the theorem above. -/
theorem InCandTree.toBase {H : TreeHeads} {P : CtxPred}
    {Γ : List SExpr} {α M N A : SExpr} (hP : KripkeDomain P)
    (C : TreeClassified H) (edge : IsDefEqStrong Γ M N A)
    (hM : InCandTree H P Γ α M) (hN : InCandTree H P Γ α N) :
    Base Γ M N A :=
  ⟨edge, InCandTree.kripkeNormalizes hP C hM hN⟩

/-- `TreeList` side of the `Base` assembly. -/
theorem InCandTreeList.toBase {H : TreeHeads} {P : CtxPred}
    {Γ : List SExpr} {α M N A : SExpr} (hP : KripkeDomain P)
    (C : TreeClassified H) (edge : IsDefEqStrong Γ M N A)
    (hM : InCandTreeList H P Γ α M) (hN : InCandTreeList H P Γ α N) :
    Base Γ M N A :=
  ⟨edge, InCandTreeList.kripkeNormalizes hP C hM hN⟩

/-- `Nat` calibration of the `Base` assembly. -/
theorem InCandNat.toBase {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} {M N A : SExpr}
    (hz : Params.classify zeroC = some (.ctor 0))
    (hs : Params.classify succC = some (.ctor 1))
    (edge : IsDefEqStrong Γ M N A)
    (hM : InCandNat zeroC succC ls Γ M)
    (hN : InCandNat zeroC succC ls Γ N) :
    Base Γ M N A :=
  ⟨edge, InCandNat.kripkeNormalizes hz hs hM hN⟩

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! # L4L-16N′1 — the production instances

The step families at the real environments.  D0 discharges outright: the
landed `d0IotaSite` builds the full reduction site from the typed-redex
premises that the `Params.Semantic.iotaSite` interface already carries (the
mechanical capture-spine and collapse content is landed inside it), and the
Nat checks are discharged.  D2 fires for all seven rules of its inventory:
the five Tree/TreeList steps conditional on `D2TreeCheckedStep` — the
18A′-gated `Pattern.Check` discharge, routed through
`D2CheckedStep.of_tree` exactly as `d2SortInvSExact`'s regime — plus the
per-rule capture-spine/β-collapse hypotheses that the generic engine
(`SExpr.iotaSiteOf`) takes as its interface; the two inherited Nat steps
need no check premise (`d2NatChecked`).  The D0 theorems are the discharged
premise-form witnesses for the conditional D2 shape. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

/-- **The two Nat `WHRed.extra` steps at the production D0 instance,
discharged.**  Every premise is part of the landed
`Params.Semantic.iotaSite` interface; the site is `d0IotaSite` and the step
is its action. -/
theorem d0IotaWHRed (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
      {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      (_rule : Pattern.IotaRule r)
      (captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
      (_captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (_hGamma : ParamsD0.D0ContextValid univs Gamma)
      (_typing : Pattern.IotaTyping Gamma rec ctor recLs ctorLs
        recArgs ctorArgs majorTerm A)
      (_matched : (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ctor ctorLs))) recLs mcap)
      (_redexSelf : IsDefEq Gamma
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ctor ctorLs)))
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ctor ctorLs))) A)
      (_AType : ∃ u, IsDefEq Gamma A A (.sort u)),
      WHRed Gamma
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ctor ctorLs)))
        (r.1.applyS recLs mcap) := by
  letI : Params := ParamsD0.d0Params univs
  intro rec major ctor arity r Gamma A majorTerm recLs ctorLs recArgs
    ctorArgs mcap rule captureType captureTyping hGamma typing matched
    redexSelf AType
  exact WHRed.extra (ParamsD0.d0IotaSite univs rule captureType
    captureTyping hGamma typing matched redexSelf AType).action

/-- **The seven D2 `WHRed.extra` steps, generically over the registry.**
Conditional on the 18A′-gated check discharge (`D2TreeCheckedStep`, lifted
to the full inventory by `D2CheckedStep.of_tree` — the two Nat branches
discharge internally) and on the rule's own capture-spine/β-collapse data,
which is the generic engine's interface.  The level-arity field is proved
internally (`d2IotaRule_levelsLength`). -/
theorem d2IotaWHRed (univs : Nat)
    (checked : ParamsD2.D2TreeCheckedStep univs) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
      {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      (rule : Pattern.IotaRule r)
      (_captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (_hGamma : ParamsD2.D2ContextValid univs Gamma)
      (_typing : Pattern.IotaTyping Gamma rec ctor recLs ctorLs
        recArgs ctorArgs majorTerm A)
      (_matched : (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ctor ctorLs))) recLs mcap)
      (_hspine : SpineWF Gamma (SExpr.mkInst recLs rule.df.type)
        (rule.capturePaths.map mcap) A)
      (_hcollapse : IsDefEq Gamma
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ctor ctorLs)))
        ((rule.capturePaths.map mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs rule.df.lhs)) A),
      WHRed Gamma
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ctor ctorLs)))
        (r.1.applyS recLs mcap) := by
  letI : Params := ParamsD2.d2Params univs
  intro rec major ctor arity r Gamma A majorTerm recLs ctorLs recArgs
    ctorArgs mcap captureType rule captureTyping hGamma typing matched
    hspine hcollapse
  have hchecked : ParamsD2.D2CheckedStep univs :=
    ParamsD2.D2CheckedStep.of_tree univs checked
  have hck := hchecked rule.pat captureTyping hGamma typing matched
  exact WHRed.extra (SExpr.iotaSiteOf (ParamsD2.d2Replay univs) rule
    captureTyping hGamma typing matched
    (ParamsD2.d2IotaRule_levelsLength univs rule typing) hspine hcollapse
    hck.choose hck.choose_spec.1 hck.choose_spec.2).action

/-- The bundle-conditioned form: with the full `D2BlockStepExact` premise —
exactly `d2SortInvSExact`'s conditioning — the per-rule capture-spine and
collapse hypotheses discharge internally, and the D2 statement becomes the
precise conditional analogue of the discharged `d0IotaWHRed` (modulo the
`redexSelf`/`AType` inputs D2's engine route does not consume). -/
theorem d2IotaWHRed_ofBlockStep (univs : Nat)
    (h : ParamsD2.D2BlockStepExact univs) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
      {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      {captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
      (_rule : Pattern.IotaRule r)
      (_captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (_hGamma : ParamsD2.D2ContextValid univs Gamma)
      (_typing : Pattern.IotaTyping Gamma rec ctor recLs ctorLs
        recArgs ctorArgs majorTerm A)
      (_matched : (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ctor ctorLs))) recLs mcap),
      WHRed Gamma
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ctor ctorLs)))
        (r.1.applyS recLs mcap) := by
  letI : Params := ParamsD2.d2Params univs
  intro rec major ctor arity r Gamma A majorTerm recLs ctorLs recArgs
    ctorArgs mcap captureType rule captureTyping hGamma typing matched
  exact d2IotaWHRed univs h.checked rule captureTyping hGamma typing
    matched (h.captureSpine rule hGamma typing matched)
    (h.lhsCollapse rule hGamma typing matched)

/-- **The five Tree/TreeList `WHRed.extra` steps, pointed at the literal
block entries.**  `hentry` ranges over exactly `TreeGen.flatCtors[0]?` …
`[4]?` — `Tree.leaf`, `Tree.node`, `Tree.branch`, `TreeList.nil`,
`TreeList.cons` — and the descriptor is the canonical
`d2TreeIotaRule univs hentry`, so the registered equation and capture
inventory compute.  Conditional exactly as `d2IotaWHRed`. -/
theorem d2TreeIotaWHRed (univs : Nat)
    (checked : ParamsD2.D2TreeCheckedStep univs) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {i : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
      (hentry : ParamsD2.TreeGen.flatCtors[i]? = some constructor)
      {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
      {mcap captureType :
        ((ParamsD2.TreeGen.rulePattern constructor).toPattern).Path → SExpr}
      (_captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (_hGamma : ParamsD2.D2ContextValid univs Gamma)
      (_typing : Pattern.IotaTyping Gamma
        (ParamsD2.TreeGen.ruleRecName constructor)
        constructor.ctor.raw.name recLs ctorLs
        recArgs ctorArgs majorTerm A)
      (_matched : ((ParamsD2.TreeGen.rulePattern constructor).toPattern).MatchesS
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName constructor) recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const constructor.ctor.raw.name ctorLs))) recLs mcap)
      (_hspine : SpineWF Gamma
        (SExpr.mkInst recLs
          (ParamsD2.d2TreeIotaRule univs hentry).df.type)
        ((ParamsD2.d2TreeIotaRule univs hentry).capturePaths.map mcap) A)
      (_hcollapse : IsDefEq Gamma
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName constructor) recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const constructor.ctor.raw.name ctorLs)))
        (((ParamsD2.d2TreeIotaRule univs hentry).capturePaths.map mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs
            (ParamsD2.d2TreeIotaRule univs hentry).df.lhs)) A),
      WHRed Gamma
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName constructor) recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const constructor.ctor.raw.name ctorLs)))
        ((ParamsD2.TreeGen.ruleRHS ParamsD2.treeRuleClosure hentry).applyS
          recLs mcap) := by
  letI : Params := ParamsD2.d2Params univs
  intro i constructor hentry Gamma A majorTerm recLs ctorLs recArgs
    ctorArgs mcap captureType captureTyping hGamma typing matched
    hspine hcollapse
  exact d2IotaWHRed univs checked (ParamsD2.d2TreeIotaRule univs hentry)
    captureTyping hGamma typing matched hspine hcollapse

/-- **The two inherited Nat `WHRed.extra` steps at the D2 instance, pointed
at the literal entries, with no check premise.**  The Nat checks are
discharged (`d2NatChecked`); what remains conditional is only the rule's
capture-spine/β-collapse data, which cannot transport down from D0 (the
D2-instance typings may mention the block's constants) and is the generic
engine's interface. -/
theorem d2NatEntryIotaWHRed (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {i : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
      (hentry : ParamsD0.NatGeneration.flatCtors[i]? = some constructor)
      {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
      {mcap captureType :
        ((ParamsD0.NatGeneration.rulePattern constructor).toPattern).Path →
          SExpr}
      (_captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (_hGamma : ParamsD2.D2ContextValid univs Gamma)
      (_typing : Pattern.IotaTyping Gamma
        (ParamsD0.NatGeneration.ruleRecName constructor)
        constructor.ctor.raw.name recLs ctorLs
        recArgs ctorArgs majorTerm A)
      (_matched :
        ((ParamsD0.NatGeneration.rulePattern constructor).toPattern).MatchesS
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName constructor)
              recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const constructor.ctor.raw.name ctorLs))) recLs mcap)
      (_hspine : SpineWF Gamma
        (SExpr.mkInst recLs
          (ParamsD2.d2NatEntryIotaRule univs hentry).df.type)
        ((ParamsD2.d2NatEntryIotaRule univs hentry).capturePaths.map mcap) A)
      (_hcollapse : IsDefEq Gamma
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName constructor)
              recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const constructor.ctor.raw.name ctorLs)))
        (((ParamsD2.d2NatEntryIotaRule univs hentry).capturePaths.map
            mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs
            (ParamsD2.d2NatEntryIotaRule univs hentry).df.lhs)) A),
      WHRed Gamma
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName constructor)
              recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const constructor.ctor.raw.name ctorLs)))
        ((ParamsD0.NatGeneration.ruleRHS ParamsD0.natRuleClosure
            hentry).applyS recLs mcap) := by
  letI : Params := ParamsD2.d2Params univs
  intro i constructor hentry Gamma A majorTerm recLs ctorLs recArgs
    ctorArgs mcap captureType captureTyping hGamma typing matched
    hspine hcollapse
  have hck := ParamsD2.d2NatChecked univs (.mk hentry)
    (Gamma := Gamma) (recLs := recLs) (mcap := mcap)
  exact WHRed.extra (SExpr.iotaSiteOf (ParamsD2.d2Replay univs)
    (ParamsD2.d2NatEntryIotaRule univs hentry)
    captureTyping hGamma typing matched
    (ParamsD2.d2IotaRule_levelsLength univs
      (ParamsD2.d2NatEntryIotaRule univs hentry) typing)
    hspine hcollapse
    hck.choose hck.choose_spec.1 hck.choose_spec.2).action

/-- A fully concrete, premise-free production `WHRed.extra` step: the D0
environment's registered definition rule fires operationally,
`d0def ⤳ Nat.zero`, in every context.  The `.extra` step mechanism the
iota corollaries above run is therefore nonvacuously exhibited at a
production instance with no hypotheses at all; the iota corollaries' own
premise bundles are the landed `Params.Semantic.iotaSite` interface,
exercised end-to-end by the D-ladder's semantic bridges
(`d0Semantic`/`d2Semantic`). -/
theorem d0DefWHRed (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    ∀ Gamma : List SExpr,
      WHRed Gamma (.const ParamsD0.d0DefVal.name [])
        (.const ``Nat.zero []) := by
  letI : Params := ParamsD0.d0Params univs
  intro Gamma
  let r : (Pattern.const ParamsD0.d0DefVal.name).RHS ×
      (Pattern.const ParamsD0.d0DefVal.name).Check :=
    (.fixed ParamsD0.d0DefVal.value ParamsD0.d0DefClosed, .true)
  let action : Pattern.Action Gamma r
      (.const ParamsD0.d0DefVal.name []) [] Empty.elim
      (.const ``Nat []) := {
    pat := ParamsD0.D0Pat.defn
    matched := by
      refine cast ?_ (@Pattern.MatchesS.const (ParamsD0.d0Params univs)
        ParamsD0.d0DefVal.name [])
      congr 1
      funext path
      exact Empty.elim path
    dfs := []
    defeqs := rfl
    checked := by simp
    sound := by
      have H := @IsDefEq.extra (ParamsD0.d0Params univs)
        ParamsD0.d0DefVal.toDefEq Gamma [] VEnv.addDefEq_self rfl
      change IsDefEq Gamma (.const ParamsD0.d0DefVal.name [])
        (.const ``Nat.zero []) (.const ``Nat []) at H
      exact H }
  have step := WHRed.extra action
  change WHRed Gamma (.const ParamsD0.d0DefVal.name [])
    (.const ``Nat.zero []) at step
  exact step

/-! ### The production membership-normalization instances -/

/-- The literal D2 head dictionary at one level instantiation. -/
def d2TreeHeads (univs : Nat)
    (l : @SLevel (ParamsD2.d2Params univs)) :
    @TreeHeads (ParamsD2.d2Params univs) :=
  @TreeHeads.mk (ParamsD2.d2Params univs) ``Tree.leaf ``Tree.node
    ``Tree.branch ``TreeList.nil ``TreeList.cons [l]

/-- The literal D2 head dictionary classifies at the production instance. -/
theorem d2TreeHeads_classified (univs : Nat)
    (l : @SLevel (ParamsD2.d2Params univs)) :
    @TreeClassified (ParamsD2.d2Params univs) (d2TreeHeads univs l) := by
  letI : Params := ParamsD2.d2Params univs
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Membership ⇒ Kripke normalization at the production D2 instance: for
members of the block candidates over the real environment,
`Base.normalizes` is a theorem. -/
theorem d2InCandTree_kripkeNormalizes (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ (l : SLevel) {P : CtxPred} {Γ : List SExpr} {α M N A : SExpr},
      KripkeDomain P →
      InCandTree (d2TreeHeads univs l) P Γ α M →
      InCandTree (d2TreeHeads univs l) P Γ α N →
      KripkeNormalizes Γ M N A := by
  letI : Params := ParamsD2.d2Params univs
  intro l P Γ α M N A hP hM hN
  exact InCandTree.kripkeNormalizes hP (d2TreeHeads_classified univs l)
    hM hN

/-- `TreeList` side of the production D2 membership normalization. -/
theorem d2InCandTreeList_kripkeNormalizes (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ (l : SLevel) {P : CtxPred} {Γ : List SExpr} {α M N A : SExpr},
      KripkeDomain P →
      InCandTreeList (d2TreeHeads univs l) P Γ α M →
      InCandTreeList (d2TreeHeads univs l) P Γ α N →
      KripkeNormalizes Γ M N A := by
  letI : Params := ParamsD2.d2Params univs
  intro l P Γ α M N A hP hM hN
  exact InCandTreeList.kripkeNormalizes hP (d2TreeHeads_classified univs l)
    hM hN

/-- Membership ⇒ Kripke normalization at the production D0 instance. -/
theorem d0InCandNat_kripkeNormalizes (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    ∀ {ls : List SLevel} {Γ : List SExpr} {M N A : SExpr},
      InCandNat ``Nat.zero ``Nat.succ ls Γ M →
      InCandNat ``Nat.zero ``Nat.succ ls Γ N →
      KripkeNormalizes Γ M N A := by
  letI : Params := ParamsD0.d0Params univs
  intro ls Γ M N A hM hN
  exact InCandNat.kripkeNormalizes rfl rfl hM hN

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ## Axiom pins

The generic development stays inside the accepted Experimental baseline:
subsets of `[propext, Classical.choice, Quot.sound]`, zero sorries, zero new
axioms.  The two instance-level endpoints additionally inherit the landed
`d2Params`/`d0Params` constructions' own documented closures (the D-ladder
fixture files prove environment freshness/lookup facts by `native_decide`),
contributed by the fixtures, not by this module's reasoning. -/

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.inCand_lift'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inCand_lift'

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandTree.lift'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InCandTree.lift'

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandNat.lift'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InCandNat.lift'

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.TreeRules.fundamental_iota' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TreeRules.fundamental_iota

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.TreeRules.branchRHS_in_candidate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TreeRules.branchRHS_in_candidate

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.NatRules.fundamental_iota' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NatRules.fundamental_iota

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.inCand_whReaches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inCand_whReaches

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandNat.toWHResult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InCandNat.toWHResult

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.branch_step_grows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms branch_step_grows

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.underPi_major_eq_generatedMajor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms underPi_major_eq_generatedMajor

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.k3_member_normal_form_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms k3_member_normal_form_unique

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2Discharge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Discharge

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0Discharge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0Discharge

/-! ### L4L-16N′1 pins

The generic N′1 layer stays inside the accepted Experimental baseline.  The
production step corollaries additionally inherit, verbatim, the closures of
the landed machinery they fire: the generic engine's recorded `sorryAx`
(through `SExpr.typeUniq` → `VEnv.IsDefEq.uniq`, the 16C′ leaf that
`d0SortInvS`/`d2SortInvSExact` already carry) and the D-ladder fixtures'
documented `native_decide` observations — contributed by those modules, not
by this one's reasoning. -/

/-- info: 'Lean4Lean.SExpr.IsMajorPremise.stuckApp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.SExpr.IsMajorPremise.stuckApp

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.stuck_major_kripke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stuck_major_kripke

/-- info: 'Lean4Lean.Pattern.IotaReductionSite.whRed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.Pattern.IotaReductionSite.whRed

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.whRedS_foldl_app' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms whRedS_foldl_app

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.whRedS_foldl_beta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms whRedS_foldl_beta

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.tower_target_ne_nodeShape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tower_target_ne_nodeShape

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.oneStep_nodeShape_refuted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms oneStep_nodeShape_refuted

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandTree.kripkeNormalizes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InCandTree.kripkeNormalizes

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandTreeList.kripkeNormalizes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InCandTreeList.kripkeNormalizes

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandNat.kripkeNormalizes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InCandNat.kripkeNormalizes

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandTree.toBase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InCandTree.toBase

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandTreeList.toBase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InCandTreeList.toBase

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandNat.toBase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms InCandNat.toBase

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0IotaWHRed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0IotaWHRed

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2IotaWHRed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2IotaWHRed

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2TreeIotaWHRed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2TreeIotaWHRed

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2NatEntryIotaWHRed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2NatEntryIotaWHRed

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2TreeHeads_classified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2TreeHeads_classified

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2InCandTree_kripkeNormalizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2InCandTree_kripkeNormalizes

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2InCandTreeList_kripkeNormalizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2InCandTreeList_kripkeNormalizes

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0InCandNat_kripkeNormalizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0InCandNat_kripkeNormalizes

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0DefWHRed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0DefWHRed

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.TreeRules.ofSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeRules.ofSteps

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.NatRules.ofSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NatRules.ofSteps

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2IotaWHRed_ofBlockStep' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2IotaWHRed_ofBlockStep

/-! # L4L-16N′2 — tower collapse, `ConstFundamental` content, depth-0 heads

Rung N′2 of L4L-16N′ (roadmap §5).  Three deliverables, all additive over
the landed N′0/N′1 substrate:

1. **The inherited N′1 volume — the tower-body instantiation.**  The N′1
   finding recorded that a production step out of a live redex lands on the
   applied right tower, not on the collapsed contractum, and that the
   collapse is a pure-syntax multi-beta run.  This rung executes that run:
   `whRedS_lamTower` drives `whRedS_foldl_beta` through an arbitrary lambda
   tower (σ-generalized so the induction closes), the `lamBodyN` pins
   compute each registered tower body by kernel `decide` (no new
   `native_decide` observations), and the nine per-rule instance theorems
   (`d0ZeroIotaRun` … `d2ConsIotaRun`) compose site step + collapse into
   `WHRedS` runs from redex to the *landed contractum shapes* — the
   `TreeRules`/`NatRules` step-field targets.  Multi-step (`WHRedS`-valued)
   twins `TreeRulesS`/`NatRulesS` of the landed engines, with the same
   assemblers and the same membership-induction `fundamental_iota`, make
   those runs directly consumable: the operational side of `ofSteps` is
   complete at the production step shape.  Conditional exactly as N′1
   conditioned: D0 outright from the `Params.Semantic.iotaSite` premise
   bundle; the five D2 Tree steps on `D2TreeCheckedStep` plus the per-rule
   capture-spine/collapse data; the two inherited D2 Nat steps without a
   check premise.

2. **`ConstFundamental` content — constants via δ-descent.**  The rank
   recursion is landed as `constsReducibleBelow_all`: plain induction on
   the rank bound consuming the named per-step obligation
   `DeltaStepObligation` — an explicit hypothesis interface (its
   nonvacuity: `constsReducibleBelow_zero` outright, and
   `DeltaStepObligation.of_fundamental` exhibits the obligation as a
   consequence of the fundamental theorem it feeds), NOT a new axiom.
   `Candidate.ofDeltaValue` is the pointed consumer: one δ-step plus its
   certificate transfers the value's reducibility to the constant.
   `ConstFundamental.of_deltaStep` closes the seam shape.  Rank-zero
   (irreducible) heads get their depth-0 content outright:
   `Base.const_irreducible` (no registered constant pattern ⇒ the bare
   constant is Kripke-WHNF), `Base.ctorSpine` (partial and full classified
   constructor applications), and `Base.stuckMajor` (recursor spines at
   neutral majors).  Instance discharges: the literal rank certificates
   and strict δ-drops at d0/d1/d2 (`d0DeltaDescent`, `d1DeltaChain`,
   `d2DeltaChain`), head irreducibility at d0/d2, and the operational
   δ-step at both d0 (`d0DefWHRed`, landed) and d2 (`d2DefWHRed`, new).
   *Deferred and recorded:* membership of constant-headed stuck spines in
   the `InCand*` candidates (their neutral clause is bvar-only) and the
   depth-`succ` action content of partial constructor applications — both
   are N′3 membership-induction content; this rung supplies their
   `Base`/head-observation halves.

3. **`HeadFundamental 0` content — head observations from membership.**
   The depth-0 head lemma family: `KripkePiData.headLayer`/`.headLayerRev`
   (both orientations of `HeadLayer Base` from Kripke Pi-targets with
   `Base`-related components, via `WHRedS` determinism and
   `RelatedPath.single`, the reverse via the landed `defeqDF_l` transport),
   `KripkeSortData.headLayer` (sort targets, any `R`), and
   `KripkeNonTypeHead.headLayer` (a normal form that is neither Pi nor
   sort refutes both observations, any `R`, any partner).  Membership
   supplies the third source: `inCand_whnfShape` shows every candidate
   member reaches a neutral or classified-constructor normal form, so
   members' head obligations hold vacuously (`InCandTree.headLayer`, …).
   `headFundamental_zero_of_data` assembles exactly the
   `Fundamental.succ` slot from the per-edge classification
   `HeadObservationData` — the named interface N′3's induction discharges
   case by case.  Every named `Prop` here has a nonvacuity witness before
   any consumption; NO case demanded adequacy-strength input, so the
   rung's kill criterion was not triggered and no isolated conditional
   `Prop` was needed.

The betaFire boundary is respected throughout: every exposed trace is
`WHRed`/`WHRedS`-valued; typed data (`IsDefEqStrong` edges, `Base`
components) rides only on clause arguments. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

variable [Params]

/-! ## N′2.1 — the multi-step engine

The production interface established by the N′1 finding is
`IotaReductionSite.whRed` (one `.extra` step onto the applied tower) plus
the untyped multi-beta collapse, i.e. a `WHRedS` run per rule.  The landed
one-step `TreeRules`/`NatRules` fields cannot receive such runs, so the
multi-step twins below carry `WHRedS`-valued step fields; their stuck
halves, assemblers, membership-induction `fundamental_iota`, and seam
corollary are word-for-word the landed proofs with the run-valued
expansion `ResultCand.expandS` at the six step-consumption sites. -/

/-- Result candidates absorb multi-step untyped expansion. -/
theorem ResultCand.expandS {S : CtxPred} (SC : ResultCand S)
    {Δ : List SExpr} {s s' : SExpr} (run : WHRedS Δ s s') (h : S Δ s') :
    S Δ s := by
  induction run using ReflTransGen.headIndOn with
  | rfl => exact h
  | head step _ ih => exact SC.expand step ih

/-- The five block rules at the production step shape: `WHRedS`-valued step
families from redex to the landed contractum shapes, exactly as the
per-rule collapse theorems below produce them. -/
structure TreeRulesS (H : TreeHeads) (Γ : List SExpr) (α : SExpr) :
    Type where
  recT : SExpr
  recL : SExpr
  minorLf : SExpr
  minorNd : SExpr
  minorBr : SExpr
  minorNl : SExpr
  minorCs : SExpr
  recT_major : IsMajorPremise recT
  recL_major : IsMajorPremise recL
  stuckT : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    ∀ {t : SExpr}, Neutral t → WHNF Δ ((recT.lift' ρ).app t)
  stuckL : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    ∀ {ts : SExpr}, Neutral ts → WHNF Δ ((recL.lift' ρ).app ts)
  leafStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ x,
    WHRedS Δ ((recT.lift' ρ).app (leafApp H (α.lift' ρ) x))
      ((minorLf.lift' ρ).app x)
  nodeStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts,
    WHRedS Δ ((recT.lift' ρ).app (nodeApp H (α.lift' ρ) ts))
      (((minorNd.lift' ρ).app ts).app ((recL.lift' ρ).app ts))
  branchStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ f,
    WHRedS Δ ((recT.lift' ρ).app (branchApp H (α.lift' ρ) f))
      (((minorBr.lift' ρ).app f).app
        (.lam (α.lift' ρ)
          (((recL.lift' ρ).lift).app ((f.lift).app (.bvar 0)))))
  nilStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    WHRedS Δ ((recL.lift' ρ).app (nilApp H (α.lift' ρ))) (minorNl.lift' ρ)
  consStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t ts,
    WHRedS Δ ((recL.lift' ρ).app (consApp H (α.lift' ρ) t ts))
      (((((minorCs.lift' ρ).app t).app ts).app ((recT.lift' ρ).app t)).app
        ((recL.lift' ρ).app ts))

/-- Assemble a multi-step rule pack from its five run families alone; the
stuck half is discharged by `stuck_major_kripke` exactly as in the landed
one-step assembler. -/
def TreeRulesS.ofSteps {H : TreeHeads} {Γ : List SExpr} {α : SExpr}
    {recT recL minorLf minorNd minorBr minorNl minorCs : SExpr}
    (recT_major : IsMajorPremise recT) (recL_major : IsMajorPremise recL)
    (leafStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ x,
      WHRedS Δ ((recT.lift' ρ).app (leafApp H (α.lift' ρ) x))
        ((minorLf.lift' ρ).app x))
    (nodeStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts,
      WHRedS Δ ((recT.lift' ρ).app (nodeApp H (α.lift' ρ) ts))
        (((minorNd.lift' ρ).app ts).app ((recL.lift' ρ).app ts)))
    (branchStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ f,
      WHRedS Δ ((recT.lift' ρ).app (branchApp H (α.lift' ρ) f))
        (((minorBr.lift' ρ).app f).app
          (.lam (α.lift' ρ)
            (((recL.lift' ρ).lift).app ((f.lift).app (.bvar 0))))))
    (nilStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      WHRedS Δ ((recL.lift' ρ).app (nilApp H (α.lift' ρ)))
        (minorNl.lift' ρ))
    (consStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t ts,
      WHRedS Δ ((recL.lift' ρ).app (consApp H (α.lift' ρ) t ts))
        (((((minorCs.lift' ρ).app t).app ts).app
          ((recT.lift' ρ).app t)).app ((recL.lift' ρ).app ts))) :
    TreeRulesS H Γ α where
  recT := recT
  recL := recL
  minorLf := minorLf
  minorNd := minorNd
  minorBr := minorBr
  minorNl := minorNl
  minorCs := minorCs
  recT_major := recT_major
  recL_major := recL_major
  stuckT := stuck_major_kripke recT_major
  stuckL := stuck_major_kripke recL_major
  leafStep := leafStep
  nodeStep := nodeStep
  branchStep := branchStep
  nilStep := nilStep
  consStep := consStep

/-- The fundamental iota case against the multi-step rules: the landed
membership induction verbatim, with `ResultCand.expandS` absorbing the
per-rule runs.  No measure, no rank — the discriminating `branch` case is
unchanged. -/
theorem TreeRulesS.fundamental_iota {H : TreeHeads} {Γ : List SExpr}
    {α : SExpr} {P S : CtxPred}
    (R : TreeRulesS H Γ α) (SC : ResultCand S)
    (mLf : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ x, P Δ x →
      S Δ ((R.minorLf.lift' ρ).app x))
    (mNd : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts,
      InCandTreeList H P Δ (α.lift' ρ) ts → S Δ ((R.recL.lift' ρ).app ts) →
      S Δ (((R.minorNd.lift' ρ).app ts).app ((R.recL.lift' ρ).app ts)))
    (mBr : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ f,
      (∀ {Δ' : List SExpr} {ρ' : Lift}, Ctx.Lift' ρ' Δ Δ' → ∀ a, P Δ' a →
        InCandTreeList H P Δ' ((α.lift' ρ).lift' ρ') ((f.lift' ρ').app a)) →
      ∀ g, (∀ a, P Δ a → S Δ (g.app a)) →
        S Δ (((R.minorBr.lift' ρ).app f).app g))
    (mNl : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      S Δ (R.minorNl.lift' ρ))
    (mCs : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t ts,
      InCandTree H P Δ (α.lift' ρ) t → InCandTreeList H P Δ (α.lift' ρ) ts →
      S Δ ((R.recT.lift' ρ).app t) → S Δ ((R.recL.lift' ρ).app ts) →
      S Δ (((((R.minorCs.lift' ρ).app t).app ts).app
        ((R.recT.lift' ρ).app t)).app ((R.recL.lift' ρ).app ts))) :
    (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t : SExpr,
        InCandTree H P Δ (α.lift' ρ) t → S Δ ((R.recT.lift' ρ).app t)) ∧
      (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts : SExpr,
        InCandTreeList H P Δ (α.lift' ρ) ts →
          S Δ ((R.recL.lift' ρ).app ts)) := by
  have caseLeaf : ∀ {Δ : List SExpr} {β : SExpr} (x : SExpr), P Δ x →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app (leafApp H β x)) := by
    intro Δ β x hx ρ W hβ
    subst hβ
    exact SC.expandS (R.leafStep W x) (mLf W x hx)
  have caseNode : ∀ {Δ : List SExpr} {β : SExpr} (ts : SExpr),
      InCandTreeList H P Δ β ts →
      (∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app ts)) →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app (nodeApp H β ts)) := by
    intro Δ β ts hts ih ρ W hβ
    subst hβ
    exact SC.expandS (R.nodeStep W ts) (mNd W ts hts (ih ρ W rfl))
  have caseBranch : ∀ {Δ : List SExpr} {β : SExpr} (f : SExpr),
      (∀ {Δ' : List SExpr} {ρ' : Lift}, Ctx.Lift' ρ' Δ Δ' → ∀ a : SExpr,
        P Δ' a → InCandTreeList H P Δ' (β.lift' ρ') ((f.lift' ρ').app a)) →
      (∀ {Δ' : List SExpr} {ρ' : Lift} (_ : Ctx.Lift' ρ' Δ Δ') (a : SExpr)
        (_ : P Δ' a), ∀ ρ'' : Lift, Ctx.Lift' ρ'' Γ Δ' →
          β.lift' ρ' = α.lift' ρ'' →
          S Δ' ((R.recL.lift' ρ'').app ((f.lift' ρ').app a))) →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app (branchApp H β f)) := by
    intro Δ β f hf ih ρ W hβ
    subst hβ
    refine SC.expandS (R.branchStep W f) (mBr W f hf _ fun a ha => ?_)
    refine SC.expand (underPi_beta (α.lift' ρ) (R.recL.lift' ρ) f a) ?_
    have := ih Ctx.Lift'.refl a ha ρ W SExpr.lift'_refl
    simpa only [SExpr.lift'_refl] using this
  have caseNeuT : ∀ {Δ : List SExpr} {β : SExpr} (t : SExpr), Neutral t →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app t) := by
    intro Δ β t hn ρ W _
    exact SC.whnf (R.stuckT W hn)
  have caseExpT : ∀ {Δ : List SExpr} {β : SExpr} (t t' : SExpr),
      WHRed Δ t t' → InCandTree H P Δ β t' →
      (∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app t')) →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app t) := by
    intro Δ β t t' step _ ih ρ W hβ
    exact SC.expand
      (WHRed.major (IsMajorPremise.lift'.2 R.recT_major) step) (ih ρ W hβ)
  have caseNil : ∀ {Δ : List SExpr} {β : SExpr},
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app (nilApp H β)) := by
    intro Δ β ρ W hβ
    subst hβ
    exact SC.expandS (R.nilStep W) (mNl W)
  have caseCons : ∀ {Δ : List SExpr} {β : SExpr} (t ts : SExpr),
      InCandTree H P Δ β t → InCandTreeList H P Δ β ts →
      (∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recT.lift' ρ).app t)) →
      (∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app ts)) →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app (consApp H β t ts)) := by
    intro Δ β t ts ht hts ih₁ ih₂ ρ W hβ
    subst hβ
    exact SC.expandS (R.consStep W t ts)
      (mCs W t ts ht hts (ih₁ ρ W rfl) (ih₂ ρ W rfl))
  have caseNeuL : ∀ {Δ : List SExpr} {β : SExpr} (ts : SExpr), Neutral ts →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app ts) := by
    intro Δ β ts hn ρ W _
    exact SC.whnf (R.stuckL W hn)
  have caseExpL : ∀ {Δ : List SExpr} {β : SExpr} (ts ts' : SExpr),
      WHRed Δ ts ts' → InCandTreeList H P Δ β ts' →
      (∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app ts')) →
      ∀ ρ : Lift, Ctx.Lift' ρ Γ Δ → β = α.lift' ρ →
        S Δ ((R.recL.lift' ρ).app ts) := by
    intro Δ β ts ts' step _ ih ρ W hβ
    exact SC.expand
      (WHRed.major (IsMajorPremise.lift'.2 R.recL_major) step) (ih ρ W hβ)
  refine ⟨fun {Δ ρ} W t h => ?_, fun {Δ ρ} W ts h => ?_⟩
  · exact InCandTree.rec
      (motive_1 := fun Δ' β t _ => ∀ ρ' : Lift, Ctx.Lift' ρ' Γ Δ' →
        β = α.lift' ρ' → S Δ' ((R.recT.lift' ρ').app t))
      (motive_2 := fun Δ' β ts _ => ∀ ρ' : Lift, Ctx.Lift' ρ' Γ Δ' →
        β = α.lift' ρ' → S Δ' ((R.recL.lift' ρ').app ts))
      caseLeaf caseNode caseBranch caseNeuT caseExpT
      caseNil caseCons caseNeuL caseExpL h ρ W rfl
  · exact InCandTreeList.rec
      (motive_1 := fun Δ' β t _ => ∀ ρ' : Lift, Ctx.Lift' ρ' Γ Δ' →
        β = α.lift' ρ' → S Δ' ((R.recT.lift' ρ').app t))
      (motive_2 := fun Δ' β ts _ => ∀ ρ' : Lift, Ctx.Lift' ρ' Γ Δ' →
        β = α.lift' ρ' → S Δ' ((R.recL.lift' ρ').app ts))
      caseLeaf caseNode caseBranch caseNeuT caseExpT
      caseNil caseCons caseNeuL caseExpL h ρ W rfl

/-- Seam composition for the multi-step engine: recursor applications at
candidate majors emit `WHResult`, exactly as the landed one-step corollary. -/
theorem TreeRulesS.recT_whResult {H : TreeHeads} {Γ : List SExpr}
    {α A : SExpr} {P : CtxPred} (R : TreeRulesS H Γ α)
    (mLf : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ x, P Δ x →
      WHReaches Δ ((R.minorLf.lift' ρ).app x))
    (mNd : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ ts,
      InCandTreeList H P Δ (α.lift' ρ) ts →
      WHReaches Δ ((R.recL.lift' ρ).app ts) →
      WHReaches Δ
        (((R.minorNd.lift' ρ).app ts).app ((R.recL.lift' ρ).app ts)))
    (mBr : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ f,
      (∀ {Δ' : List SExpr} {ρ' : Lift}, Ctx.Lift' ρ' Δ Δ' → ∀ a, P Δ' a →
        InCandTreeList H P Δ' ((α.lift' ρ).lift' ρ') ((f.lift' ρ').app a)) →
      ∀ g, (∀ a, P Δ a → WHReaches Δ (g.app a)) →
        WHReaches Δ (((R.minorBr.lift' ρ).app f).app g))
    (mNl : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      WHReaches Δ (R.minorNl.lift' ρ))
    (mCs : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ t ts,
      InCandTree H P Δ (α.lift' ρ) t → InCandTreeList H P Δ (α.lift' ρ) ts →
      WHReaches Δ ((R.recT.lift' ρ).app t) →
      WHReaches Δ ((R.recL.lift' ρ).app ts) →
      WHReaches Δ (((((R.minorCs.lift' ρ).app t).app ts).app
        ((R.recT.lift' ρ).app t)).app ((R.recL.lift' ρ).app ts)))
    {t : SExpr} (h : InCandTree H P Γ α t) :
    WHResult Γ (R.recT.app t) A := by
  have out := (R.fundamental_iota WHReaches.resultCand
      mLf mNd mBr mNl mCs).1 Ctx.Lift'.refl t
    (by simpa only [SExpr.lift'_refl] using h)
  have out' : WHReaches Γ (R.recT.app t) := by
    simpa only [SExpr.lift'_refl] using out
  exact out'

/-- The two Nat rules at the production step shape. -/
structure NatRulesS (zeroC succC : Name) (ls : List SLevel)
    (Γ : List SExpr) : Type where
  recN : SExpr
  minorZ : SExpr
  minorS : SExpr
  recN_major : IsMajorPremise recN
  stuckN : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    ∀ {n : SExpr}, Neutral n → WHNF Δ ((recN.lift' ρ).app n)
  zeroStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    WHRedS Δ ((recN.lift' ρ).app (.const zeroC ls)) (minorZ.lift' ρ)
  succStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ n,
    WHRedS Δ ((recN.lift' ρ).app ((SExpr.const succC ls).app n))
      (((minorS.lift' ρ).app n).app ((recN.lift' ρ).app n))

/-- `Nat` side of the multi-step assembler. -/
def NatRulesS.ofSteps {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} {recN minorZ minorS : SExpr}
    (recN_major : IsMajorPremise recN)
    (zeroStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      WHRedS Δ ((recN.lift' ρ).app (.const zeroC ls)) (minorZ.lift' ρ))
    (succStep : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ n,
      WHRedS Δ ((recN.lift' ρ).app ((SExpr.const succC ls).app n))
        (((minorS.lift' ρ).app n).app ((recN.lift' ρ).app n))) :
    NatRulesS zeroC succC ls Γ where
  recN := recN
  minorZ := minorZ
  minorS := minorS
  recN_major := recN_major
  stuckN := stuck_major_kripke recN_major
  zeroStep := zeroStep
  succStep := succStep

/-- The `Nat` fundamental iota case against the multi-step rules. -/
theorem NatRulesS.fundamental_iota {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} {S : CtxPred}
    (R : NatRulesS zeroC succC ls Γ) (SC : ResultCand S)
    (mZ : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
      S Δ (R.minorZ.lift' ρ))
    (mS : ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → ∀ n,
      InCandNat zeroC succC ls Δ n → S Δ ((R.recN.lift' ρ).app n) →
      S Δ (((R.minorS.lift' ρ).app n).app ((R.recN.lift' ρ).app n)))
    {Δ : List SExpr} {ρ : Lift} (W : Ctx.Lift' ρ Γ Δ)
    {n : SExpr} (h : InCandNat zeroC succC ls Δ n) :
    S Δ ((R.recN.lift' ρ).app n) := by
  induction h with
  | zero => exact SC.expandS (R.zeroStep W) (mZ W)
  | succ n hn ih => exact SC.expandS (R.succStep W n) (mS W n hn ih)
  | neutral n hn => exact SC.whnf (R.stuckN W hn)
  | expand n n' step _ ih =>
    exact SC.expand
      (WHRed.major (IsMajorPremise.lift'.2 R.recN_major) step) ih

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ## N′2.2 — the tower-collapse engine

Generic machinery for the applied-tower multi-beta collapse.  `lamBodyN`
decides the lambda-tower decomposition of a registered right-hand side, and
`whRedS_lamTower` drives `whRedS_foldl_beta` once per binder; the
substitution is σ-generalized so the induction closes, with
`SExpr.inst_lift_cons` folding each contraction into one accumulated
parallel substitution.  `iotaSpineCaptureValues` reads the ordered capture
values of a matched iota redex back as the spine arguments, in exactly the
`take`/`drop` shape of the fixture capture-path inventories. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

/-- Strip exactly `n` lambda binders from a registered tower, returning the
body.  Kernel-decidable, so the per-rule shape pins below need no new
`native_decide` observations. -/
def lamBodyN : Nat → VExpr → Option VExpr
  | 0, e => some e
  | n + 1, .lam _ e => lamBodyN n e
  | _ + 1, _ => none

/-- Soundness of the strip: a successful `lamBodyN` exhibits the
lambda-tower decomposition. -/
theorem lamBodyN_eq_some :
    ∀ {n : Nat} {e body : VExpr}, lamBodyN n e = some body →
      ∃ Ts : List VExpr, Ts.length = n ∧ e = VExpr.lamN Ts body := by
  intro n
  induction n with
  | zero =>
    intro e body h
    cases h
    exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    intro e body h
    cases e with
    | lam ty inner =>
      obtain ⟨Ts, hlen, rfl⟩ := ih h
      exact ⟨ty :: Ts, by simp [hlen], rfl⟩
    | bvar i => cases h
    | sort u => cases h
    | const c us => cases h
    | app f a => cases h
    | forallE A B => cases h

variable [Params]

/-- `mkInst` maps a `VExpr` lambda tower to the `SExpr` lambda tower. -/
theorem mkInst_lamN (ls : List SLevel) :
    ∀ (Ts : List VExpr) (body : VExpr),
      SExpr.mkInst ls (VExpr.lamN Ts body) =
        (Ts.map (SExpr.mkInst ls)).foldr .lam (SExpr.mkInst ls body) := by
  intro Ts
  induction Ts with
  | nil => intro body; rfl
  | cons T Ts ih =>
    intro body
    simp only [VExpr.lamN, SExpr.mkInst, List.map_cons, List.foldr_cons, ih]

/-- σ-generalized multi-beta collapse of a fully applied lambda tower: one
`whRedS_foldl_beta` per binder, each contraction folded into the
accumulated substitution by `SExpr.inst_lift_cons`. -/
theorem whRedS_lamTower_subst {Γ : List SExpr} :
    ∀ (Ts : List SExpr) (body : SExpr) (args : List SExpr) (σ : Subst),
      args.length = Ts.length →
      WHRedS Γ
        (args.foldl (fun (f a : SExpr) => f.app a)
          ((Ts.foldr .lam body).subst σ))
        (body.subst (args.foldl Subst.cons σ)) := by
  intro Ts
  induction Ts with
  | nil =>
    intro body args σ h
    obtain rfl := List.length_eq_zero_iff.mp h
    exact .rfl
  | cons T Ts ih =>
    intro body args σ h
    cases args with
    | nil => cases h
    | cons a args =>
      have h' : args.length = Ts.length := Nat.succ.inj h
      have step := whRedS_foldl_beta (Γ := Γ) (T.subst σ)
        ((Ts.foldr .lam body).subst σ.lift) a args
      rw [SExpr.inst_lift_cons] at step
      exact ReflTransGen.trans step (ih body args (σ.cons a) h')

/-- The identity-substitution form: a lambda tower applied to exactly its
binder count multi-beta-collapses onto its instantiated body. -/
theorem whRedS_lamTower {Γ : List SExpr} (Ts : List SExpr) (body : SExpr)
    (args : List SExpr) (h : args.length = Ts.length) :
    WHRedS Γ
      (args.foldl (fun (f a : SExpr) => f.app a) (Ts.foldr .lam body))
      (body.subst (args.foldl Subst.cons Subst.id)) := by
  have := whRedS_lamTower_subst (Γ := Γ) Ts body args Subst.id h
  rwa [SExpr.subst_id] at this

/-- Applying a fixed-body capture tower is the left fold of the capture
values over the level-instantiated body. -/
theorem appN_var_applyS_eq {p : Pattern} (body : VExpr)
    (closed : body.Closed) (paths : List p.Path) (m1 : List SLevel)
    (m2 : p.Path → SExpr) :
    (Pattern.RHS.appN (.fixed body closed)
        (paths.map fun path => .var path)).applyS m1 m2 =
      (paths.map m2).foldl (fun (f a : SExpr) => f.app a)
        (SExpr.mkInst m1 body) := by
  rw [Pattern.RHS.appN_applyS]
  simp only [List.foldl_map, Pattern.RHS.applyS]

/-- The ordered capture values of a matched iota redex are its spine
arguments, in the fixture inventories' `take`/`drop` shape. -/
theorem iotaSpineCaptureValues {rec ctor : Name} {major arity : Nat}
    (common np : Nat)
    {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    (H : (RecursorIotaPattern rec major ctor arity).MatchesS
      ((recArgs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (.const ctor ctorLs)))
      recLs mcap) :
    recArgs.length = major ∧ ctorArgs.length = arity ∧
      ((((Pattern.varNPaths (.const rec) major).take common).map
          Sum.inl ++
        ((Pattern.varNPaths (.const ctor) arity).drop np).map
          Sum.inr).map mcap) =
        recArgs.reverse.take common ++ ctorArgs.reverse.drop np := by
  cases H with
  | app hrec hctor =>
    obtain ⟨-, hrecLen, hrecVals⟩ := ParamsD0.matchesS_varN_foldr hrec
    obtain ⟨-, hctorLen, hctorVals⟩ := ParamsD0.matchesS_varN_foldr hctor
    rename_i g1 g2
    refine ⟨hrecLen, hctorLen, ?_⟩
    have h₁ : (((Pattern.varNPaths (.const rec) major).take common).map
          Sum.inl).map (Sum.elim g1 g2) =
        recArgs.reverse.take common := by
      rw [List.map_map,
        show Sum.elim g1 g2 ∘ Sum.inl = g1 from rfl,
        List.map_take, hrecVals]
    have h₂ : (((Pattern.varNPaths (.const ctor) arity).drop np).map
          Sum.inr).map (Sum.elim g1 g2) =
        ctorArgs.reverse.drop np := by
      rw [List.map_map,
        show Sum.elim g1 g2 ∘ Sum.inr = g2 from rfl,
        List.map_drop, hctorVals]
    exact (List.map_append ..).trans (h₁ ▸ h₂ ▸ rfl)

/-- The D0/D2 `Nat` capture inventory reads back as the spine arguments. -/
theorem natCaptureValues {constructor : VInductDecl.NormalizedBlockCtor}
    {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
    {mcap : ((ParamsD0.NatGeneration.rulePattern constructor).toPattern).Path →
      SExpr}
    (H : ((ParamsD0.NatGeneration.rulePattern constructor).toPattern).MatchesS
      ((recArgs.foldr (fun (a f : SExpr) => f.app a)
          (.const (ParamsD0.NatGeneration.ruleRecName constructor) recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (.const constructor.ctor.raw.name ctorLs)))
      recLs mcap) :
    (ParamsD0.natCapturePaths constructor).map mcap =
      recArgs.reverse.take (InductiveFixtures.natDecl.nparams +
        ParamsD0.NatGeneration.familyCount +
        ParamsD0.NatGeneration.minorCount) ++
      ctorArgs.reverse.drop InductiveFixtures.natDecl.nparams :=
  (iotaSpineCaptureValues _ _ H).2.2

/-- The D2 `Tree`/`TreeList` capture inventory reads back as the spine
arguments. -/
theorem treeCaptureValues {constructor : VInductDecl.NormalizedBlockCtor}
    {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
    {mcap : ((ParamsD2.TreeGen.rulePattern constructor).toPattern).Path →
      SExpr}
    (H : ((ParamsD2.TreeGen.rulePattern constructor).toPattern).MatchesS
      ((recArgs.foldr (fun (a f : SExpr) => f.app a)
          (.const (ParamsD2.TreeGen.ruleRecName constructor) recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (.const constructor.ctor.raw.name ctorLs)))
      recLs mcap) :
    (ParamsD2.treeCapturePaths constructor).map mcap =
      recArgs.reverse.take (MutualInductiveFixtures.treeDecl.nparams +
        ParamsD2.TreeGen.familyCount + ParamsD2.TreeGen.minorCount) ++
      ctorArgs.reverse.drop MutualInductiveFixtures.treeDecl.nparams :=
  (iotaSpineCaptureValues _ _ H).2.2

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ## N′2.3 — the registered tower bodies, pinned

The per-rule tower-body instantiation recorded by N′1 as this rung's
inherited volume.  Each registered right-hand side is a lambda tower whose
binder count and body are pure `VExpr` data (`Params`-free), decided by the
kernel (`decide`, not `native_decide`): the seven pins below are the exact
generated bodies — the captured minor premise applied to the fields and
the lambda-packaged recursive calls.  The count pins fix the fixture spine
arithmetic consumed by the capture-value reading. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

/-- `Nat.zero` rule body: the zero minor. -/
theorem natZeroBody :
    lamBodyN 3 (ParamsD0.NatGeneration.rule 0
      ParamsD0.NatGeneration.flatCtors[0]).rhs = some (.bvar 1) := by
  decide

/-- `Nat.succ` rule body: the successor minor at the field and the
recursive call. -/
theorem natSuccBody :
    lamBodyN 4 (ParamsD0.NatGeneration.rule 1
      ParamsD0.NatGeneration.flatCtors[1]).rhs =
      some (VExpr.bvar 1 |>.app (.bvar 0) |>.app
        (VExpr.const ``Nat.rec [.param 0] |>.app (.bvar 3) |>.app (.bvar 2)
          |>.app (.bvar 1) |>.app (.bvar 0))) := by
  decide

/-- `Tree.leaf` rule body: the leaf minor at the field. -/
theorem treeLeafBody :
    lamBodyN 9 (ParamsD2.TreeGen.rule 0 ParamsD2.TreeGen.flatCtors[0]).rhs =
      some (VExpr.bvar 5 |>.app (.bvar 0)) := by
  decide

/-- `Tree.node` rule body: the node minor at the field and the sibling
recursive call. -/
theorem treeNodeBody :
    lamBodyN 9 (ParamsD2.TreeGen.rule 1 ParamsD2.TreeGen.flatCtors[1]).rhs =
      some (VExpr.bvar 4 |>.app (.bvar 0) |>.app
        (VExpr.const ``TreeList.rec [.param 0, .param 1]
          |>.app (.bvar 8) |>.app (.bvar 7) |>.app (.bvar 6)
          |>.app (.bvar 5) |>.app (.bvar 4) |>.app (.bvar 3)
          |>.app (.bvar 2) |>.app (.bvar 1) |>.app (.bvar 0))) := by
  decide

/-- `Tree.branch` rule body: the branch minor at the functional field and
the lambda-packaged under-Pi recursive call — the killed transition's
contractum, generated. -/
theorem treeBranchBody :
    lamBodyN 9 (ParamsD2.TreeGen.rule 2 ParamsD2.TreeGen.flatCtors[2]).rhs =
      some (VExpr.bvar 3 |>.app (.bvar 0) |>.app
        (VExpr.lam (.bvar 8)
          (VExpr.const ``TreeList.rec [.param 0, .param 1]
            |>.app (.bvar 9) |>.app (.bvar 8) |>.app (.bvar 7)
            |>.app (.bvar 6) |>.app (.bvar 5) |>.app (.bvar 4)
            |>.app (.bvar 3) |>.app (.bvar 2)
            |>.app (VExpr.bvar 1 |>.app (.bvar 0))))) := by
  decide

/-- `TreeList.nil` rule body: the nil minor. -/
theorem treeNilBody :
    lamBodyN 8 (ParamsD2.TreeGen.rule 3 ParamsD2.TreeGen.flatCtors[3]).rhs =
      some (.bvar 1) := by
  decide

/-- `TreeList.cons` rule body: the cons minor at both fields and both
mutual recursive calls — including the reverse `TreeList → Tree` edge. -/
theorem treeConsBody :
    lamBodyN 10 (ParamsD2.TreeGen.rule 4 ParamsD2.TreeGen.flatCtors[4]).rhs =
      some (VExpr.bvar 2 |>.app (.bvar 1) |>.app (.bvar 0)
        |>.app (VExpr.const ``Tree.rec [.param 0, .param 1]
          |>.app (.bvar 9) |>.app (.bvar 8) |>.app (.bvar 7)
          |>.app (.bvar 6) |>.app (.bvar 5) |>.app (.bvar 4)
          |>.app (.bvar 3) |>.app (.bvar 2) |>.app (.bvar 1))
        |>.app (VExpr.const ``TreeList.rec [.param 0, .param 1]
          |>.app (.bvar 9) |>.app (.bvar 8) |>.app (.bvar 7)
          |>.app (.bvar 6) |>.app (.bvar 5) |>.app (.bvar 4)
          |>.app (.bvar 3) |>.app (.bvar 2) |>.app (.bvar 0))) := by
  decide

/-- The Nat spine arithmetic: no parameters, one family, two minors. -/
theorem natSpineCounts :
    InductiveFixtures.natDecl.nparams + ParamsD0.NatGeneration.familyCount +
      ParamsD0.NatGeneration.minorCount = 3 := by
  decide

/-- The Tree spine arithmetic: one parameter, two families, five minors. -/
theorem treeSpineCounts :
    MutualInductiveFixtures.treeDecl.nparams + ParamsD2.TreeGen.familyCount +
      ParamsD2.TreeGen.minorCount = 8 := by
  decide

/-- The five literal block-entry lookups (the `Nat` pair is landed at D0 as
`probeNatFlatCtorZero_lookup`/`probeNatFlatCtorSucc_lookup`). -/
theorem treeFlatCtor0_lookup :
    ParamsD2.TreeGen.flatCtors[0]? = some ParamsD2.TreeGen.flatCtors[0] :=
  List.getElem?_eq_getElem (by decide)

theorem treeFlatCtor1_lookup :
    ParamsD2.TreeGen.flatCtors[1]? = some ParamsD2.TreeGen.flatCtors[1] :=
  List.getElem?_eq_getElem (by decide)

theorem treeFlatCtor2_lookup :
    ParamsD2.TreeGen.flatCtors[2]? = some ParamsD2.TreeGen.flatCtors[2] :=
  List.getElem?_eq_getElem (by decide)

theorem treeFlatCtor3_lookup :
    ParamsD2.TreeGen.flatCtors[3]? = some ParamsD2.TreeGen.flatCtors[3] :=
  List.getElem?_eq_getElem (by decide)

theorem treeFlatCtor4_lookup :
    ParamsD2.TreeGen.flatCtors[4]? = some ParamsD2.TreeGen.flatCtors[4] :=
  List.getElem?_eq_getElem (by decide)

variable [Params]

/-- The `Nat.rec` common spine of the collapse targets. -/
def natRecSpine (recLs : List SLevel) (M mz ms : SExpr) : SExpr :=
  SExpr.const ``Nat.rec [.instV recLs (.param 0)]
    |>.app M |>.app mz |>.app ms

/-- The `Tree.rec` eight-common spine of the D2 collapse targets. -/
def treeRecSpine (recLs : List SLevel)
    (α M₁ M₂ m₁ m₂ m₃ m₄ m₅ : SExpr) : SExpr :=
  SExpr.const ``Tree.rec [.instV recLs (.param 0), .instV recLs (.param 1)]
    |>.app α |>.app M₁ |>.app M₂ |>.app m₁ |>.app m₂ |>.app m₃
    |>.app m₄ |>.app m₅

/-- The `TreeList.rec` eight-common spine of the D2 collapse targets. -/
def treeListRecSpine (recLs : List SLevel)
    (α M₁ M₂ m₁ m₂ m₃ m₄ m₅ : SExpr) : SExpr :=
  SExpr.const ``TreeList.rec
      [.instV recLs (.param 0), .instV recLs (.param 1)]
    |>.app α |>.app M₁ |>.app M₂ |>.app m₁ |>.app m₂ |>.app m₃
    |>.app m₄ |>.app m₅

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ## N′2.4 — the per-rule redex-to-contractum runs at the instances

The nine production runs: site step (`WHRed.extra` onto the applied tower,
via the landed N′1 step theorems) followed by the tower collapse.  Each
lands on the landed `TreeRules`/`NatRules` step-field contractum shape at
the literal spine arguments, i.e. exactly what the multi-step
`TreeRulesS`/`NatRulesS` fields consume.  Conditionality is inherited
verbatim: the D0 runs take the landed `Params.Semantic.iotaSite` premise
bundle and nothing else; the five D2 Tree runs are conditional on
`D2TreeCheckedStep` plus the per-rule capture-spine/collapse data; the two
inherited D2 Nat runs need no check premise. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

set_option linter.unusedVariables false

/-- **`Nat.zero` at D0, redex to contractum.**  One `.extra` step onto the
applied tower, three betas down to the captured zero minor. -/
theorem d0ZeroIotaRun (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {M mz ms : SExpr}
      {mcap : ((ParamsD0.NatGeneration.rulePattern
          ParamsD0.NatGeneration.flatCtors[0]).toPattern).Path → SExpr}
      (rule : Pattern.IotaRule
        (ParamsD0.NatGeneration.ruleRHS ParamsD0.natRuleClosure
            ParamsD0.probeNatFlatCtorZero_lookup,
          ParamsD0.NatGeneration.ruleCheck ParamsD0.natRuleClosure
            (List.mem_of_getElem? ParamsD0.probeNatFlatCtorZero_lookup)))
      (captureType : ((ParamsD0.NatGeneration.rulePattern
          ParamsD0.NatGeneration.flatCtors[0]).toPattern).Path → SExpr)
      (captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (hGamma : ParamsD0.D0ContextValid univs Gamma)
      (typing : Pattern.IotaTyping Gamma
        (ParamsD0.NatGeneration.ruleRecName
          ParamsD0.NatGeneration.flatCtors[0])
        (ParamsD0.NatGeneration.flatCtors[0]).ctor.raw.name recLs ctorLs
        [ms, mz, M] [] majorTerm A)
      (matched : ((ParamsD0.NatGeneration.rulePattern
          ParamsD0.NatGeneration.flatCtors[0]).toPattern).MatchesS
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[0]) recLs)).app
          (([] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[0]).ctor.raw.name ctorLs)))
        recLs mcap)
      (redexSelf : IsDefEq Gamma
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[0]) recLs)).app
          (([] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[0]).ctor.raw.name ctorLs)))
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[0]) recLs)).app
          (([] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[0]).ctor.raw.name ctorLs)))
        A)
      (AType : ∃ u, IsDefEq Gamma A A (.sort u)),
      WHRedS Gamma
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[0]) recLs)).app
          (([] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[0]).ctor.raw.name ctorLs)))
        mz := by
  letI : Params := ParamsD0.d0Params univs
  intro Gamma A majorTerm recLs ctorLs M mz ms mcap rule captureType
    captureTyping hGamma typing matched redexSelf AType
  refine ReflTransGen.trans (ReflTransGen.tail .rfl
    (d0IotaWHRed univs rule captureType captureTyping hGamma typing matched
      redexSelf AType)) ?_
  show WHRedS Gamma
    ((ParamsD0.NatGeneration.ruleRHS ParamsD0.natRuleClosure
      ParamsD0.probeNatFlatCtorZero_lookup).applyS recLs mcap) mz
  rw [ParamsD0.natRuleRHS_tower ParamsD0.probeNatFlatCtorZero_lookup,
    appN_var_applyS_eq, natCaptureValues matched]
  obtain ⟨Ts, hTs, hrhs⟩ := lamBodyN_eq_some natZeroBody
  rw [hrhs, mkInst_lamN]
  exact whRedS_lamTower (Γ := Gamma) (Ts.map (SExpr.mkInst recLs))
    (SExpr.mkInst recLs (.bvar 1)) [M, mz, ms] (by simp [hTs])

/-- **`Nat.succ` at D0, redex to contractum.**  One `.extra` step, four
betas down to the successor minor at the field and the recursive call. -/
theorem d0SuccIotaRun (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {M mz ms n : SExpr}
      {mcap : ((ParamsD0.NatGeneration.rulePattern
          ParamsD0.NatGeneration.flatCtors[1]).toPattern).Path → SExpr}
      (rule : Pattern.IotaRule
        (ParamsD0.NatGeneration.ruleRHS ParamsD0.natRuleClosure
            ParamsD0.probeNatFlatCtorSucc_lookup,
          ParamsD0.NatGeneration.ruleCheck ParamsD0.natRuleClosure
            (List.mem_of_getElem? ParamsD0.probeNatFlatCtorSucc_lookup)))
      (captureType : ((ParamsD0.NatGeneration.rulePattern
          ParamsD0.NatGeneration.flatCtors[1]).toPattern).Path → SExpr)
      (captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (hGamma : ParamsD0.D0ContextValid univs Gamma)
      (typing : Pattern.IotaTyping Gamma
        (ParamsD0.NatGeneration.ruleRecName
          ParamsD0.NatGeneration.flatCtors[1])
        (ParamsD0.NatGeneration.flatCtors[1]).ctor.raw.name recLs ctorLs
        [ms, mz, M] [n] majorTerm A)
      (matched : ((ParamsD0.NatGeneration.rulePattern
          ParamsD0.NatGeneration.flatCtors[1]).toPattern).MatchesS
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[1]) recLs)).app
          (([n] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[1]).ctor.raw.name ctorLs)))
        recLs mcap)
      (redexSelf : IsDefEq Gamma
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[1]) recLs)).app
          (([n] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[1]).ctor.raw.name ctorLs)))
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[1]) recLs)).app
          (([n] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[1]).ctor.raw.name ctorLs)))
        A)
      (AType : ∃ u, IsDefEq Gamma A A (.sort u)),
      WHRedS Gamma
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[1]) recLs)).app
          (([n] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[1]).ctor.raw.name ctorLs)))
        ((ms.app n).app ((natRecSpine recLs M mz ms).app n)) := by
  letI : Params := ParamsD0.d0Params univs
  intro Gamma A majorTerm recLs ctorLs M mz ms n mcap rule captureType
    captureTyping hGamma typing matched redexSelf AType
  refine ReflTransGen.trans (ReflTransGen.tail .rfl
    (d0IotaWHRed univs rule captureType captureTyping hGamma typing matched
      redexSelf AType)) ?_
  show WHRedS Gamma
    ((ParamsD0.NatGeneration.ruleRHS ParamsD0.natRuleClosure
      ParamsD0.probeNatFlatCtorSucc_lookup).applyS recLs mcap)
    ((ms.app n).app ((natRecSpine recLs M mz ms).app n))
  rw [ParamsD0.natRuleRHS_tower ParamsD0.probeNatFlatCtorSucc_lookup,
    appN_var_applyS_eq, natCaptureValues matched]
  obtain ⟨Ts, hTs, hrhs⟩ := lamBodyN_eq_some natSuccBody
  rw [hrhs, mkInst_lamN]
  exact whRedS_lamTower (Γ := Gamma) (Ts.map (SExpr.mkInst recLs))
    (SExpr.mkInst recLs (VExpr.bvar 1 |>.app (.bvar 0) |>.app
      (VExpr.const ``Nat.rec [.param 0] |>.app (.bvar 3) |>.app (.bvar 2)
        |>.app (.bvar 1) |>.app (.bvar 0))))
    [M, mz, ms, n] (by simp [hTs])

end IndCand
end Reducibility
end SExpr
end Lean4Lean

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

set_option linter.unusedVariables false

/-- **`Tree.leaf` at D2, redex to contractum** (conditional on
`D2TreeCheckedStep` and the rule's capture-spine/collapse data, exactly as
`d2TreeIotaWHRed`): one `.extra` step, nine betas down to the leaf minor at
the field. -/
theorem d2LeafIotaRun (univs : Nat)
    (checked : ParamsD2.D2TreeCheckedStep univs) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {α M₁ M₂ m₁ m₂ m₃ m₄ m₅ α' x : SExpr}
      {mcap captureType :
        ((ParamsD2.TreeGen.rulePattern
          ParamsD2.TreeGen.flatCtors[0]).toPattern).Path → SExpr}
      (captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (hGamma : ParamsD2.D2ContextValid univs Gamma)
      (typing : Pattern.IotaTyping Gamma
        (ParamsD2.TreeGen.ruleRecName ParamsD2.TreeGen.flatCtors[0])
        (ParamsD2.TreeGen.flatCtors[0]).ctor.raw.name recLs ctorLs
        [m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] [x, α'] majorTerm A)
      (matched : ((ParamsD2.TreeGen.rulePattern
          ParamsD2.TreeGen.flatCtors[0]).toPattern).MatchesS
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[0]) recLs)).app
          (([x, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[0]).ctor.raw.name ctorLs)))
        recLs mcap)
      (hspine : SpineWF Gamma
        (SExpr.mkInst recLs
          (ParamsD2.d2TreeIotaRule univs treeFlatCtor0_lookup).df.type)
        ((ParamsD2.d2TreeIotaRule univs
          treeFlatCtor0_lookup).capturePaths.map mcap) A)
      (hcollapse : IsDefEq Gamma
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[0]) recLs)).app
          (([x, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[0]).ctor.raw.name ctorLs)))
        (((ParamsD2.d2TreeIotaRule univs
            treeFlatCtor0_lookup).capturePaths.map mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs
            (ParamsD2.d2TreeIotaRule univs treeFlatCtor0_lookup).df.lhs)) A),
      WHRedS Gamma
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[0]) recLs)).app
          (([x, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[0]).ctor.raw.name ctorLs)))
        (m₁.app x) := by
  letI : Params := ParamsD2.d2Params univs
  intro Gamma A majorTerm recLs ctorLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅ α' x mcap
    captureType captureTyping hGamma typing matched hspine hcollapse
  refine ReflTransGen.trans (ReflTransGen.tail .rfl
    (d2TreeIotaWHRed univs checked treeFlatCtor0_lookup captureTyping
      hGamma typing matched hspine hcollapse)) ?_
  show WHRedS Gamma
    ((ParamsD2.TreeGen.ruleRHS ParamsD2.treeRuleClosure
      treeFlatCtor0_lookup).applyS recLs mcap) (m₁.app x)
  rw [ParamsD2.treeRuleRHS_capture_tower treeFlatCtor0_lookup,
    appN_var_applyS_eq, treeCaptureValues matched]
  obtain ⟨Ts, hTs, hrhs⟩ := lamBodyN_eq_some treeLeafBody
  rw [hrhs, mkInst_lamN]
  exact whRedS_lamTower (Γ := Gamma) (Ts.map (SExpr.mkInst recLs))
    (SExpr.mkInst recLs (VExpr.bvar 5 |>.app (.bvar 0)))
    [α, M₁, M₂, m₁, m₂, m₃, m₄, m₅, x] (by simp [hTs])

/-- **`Tree.node` at D2, redex to contractum**: the node minor at the field
and the sibling `TreeList.rec` recursive call. -/
theorem d2NodeIotaRun (univs : Nat)
    (checked : ParamsD2.D2TreeCheckedStep univs) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {α M₁ M₂ m₁ m₂ m₃ m₄ m₅ α' ts : SExpr}
      {mcap captureType :
        ((ParamsD2.TreeGen.rulePattern
          ParamsD2.TreeGen.flatCtors[1]).toPattern).Path → SExpr}
      (captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (hGamma : ParamsD2.D2ContextValid univs Gamma)
      (typing : Pattern.IotaTyping Gamma
        (ParamsD2.TreeGen.ruleRecName ParamsD2.TreeGen.flatCtors[1])
        (ParamsD2.TreeGen.flatCtors[1]).ctor.raw.name recLs ctorLs
        [m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] [ts, α'] majorTerm A)
      (matched : ((ParamsD2.TreeGen.rulePattern
          ParamsD2.TreeGen.flatCtors[1]).toPattern).MatchesS
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[1]) recLs)).app
          (([ts, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[1]).ctor.raw.name ctorLs)))
        recLs mcap)
      (hspine : SpineWF Gamma
        (SExpr.mkInst recLs
          (ParamsD2.d2TreeIotaRule univs treeFlatCtor1_lookup).df.type)
        ((ParamsD2.d2TreeIotaRule univs
          treeFlatCtor1_lookup).capturePaths.map mcap) A)
      (hcollapse : IsDefEq Gamma
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[1]) recLs)).app
          (([ts, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[1]).ctor.raw.name ctorLs)))
        (((ParamsD2.d2TreeIotaRule univs
            treeFlatCtor1_lookup).capturePaths.map mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs
            (ParamsD2.d2TreeIotaRule univs treeFlatCtor1_lookup).df.lhs)) A),
      WHRedS Gamma
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[1]) recLs)).app
          (([ts, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[1]).ctor.raw.name ctorLs)))
        ((m₂.app ts).app
          ((treeListRecSpine recLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅).app ts)) := by
  letI : Params := ParamsD2.d2Params univs
  intro Gamma A majorTerm recLs ctorLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅ α' ts mcap
    captureType captureTyping hGamma typing matched hspine hcollapse
  refine ReflTransGen.trans (ReflTransGen.tail .rfl
    (d2TreeIotaWHRed univs checked treeFlatCtor1_lookup captureTyping
      hGamma typing matched hspine hcollapse)) ?_
  show WHRedS Gamma
    ((ParamsD2.TreeGen.ruleRHS ParamsD2.treeRuleClosure
      treeFlatCtor1_lookup).applyS recLs mcap)
    ((m₂.app ts).app
      ((treeListRecSpine recLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅).app ts))
  rw [ParamsD2.treeRuleRHS_capture_tower treeFlatCtor1_lookup,
    appN_var_applyS_eq, treeCaptureValues matched]
  obtain ⟨Ts, hTs, hrhs⟩ := lamBodyN_eq_some treeNodeBody
  rw [hrhs, mkInst_lamN]
  exact whRedS_lamTower (Γ := Gamma) (Ts.map (SExpr.mkInst recLs))
    (SExpr.mkInst recLs (VExpr.bvar 4 |>.app (.bvar 0) |>.app
      (VExpr.const ``TreeList.rec [.param 0, .param 1]
        |>.app (.bvar 8) |>.app (.bvar 7) |>.app (.bvar 6)
        |>.app (.bvar 5) |>.app (.bvar 4) |>.app (.bvar 3)
        |>.app (.bvar 2) |>.app (.bvar 1) |>.app (.bvar 0))))
    [α, M₁, M₂, m₁, m₂, m₃, m₄, m₅, ts] (by simp [hTs])

/-- **`Tree.branch` at D2, redex to contractum** — the transition that
killed the L4L-16N measures, executed operationally: one `.extra` step and
nine betas land on the branch minor at the functional field together with
the lambda-packaged under-Pi recursive call. -/
theorem d2BranchIotaRun (univs : Nat)
    (checked : ParamsD2.D2TreeCheckedStep univs) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {α M₁ M₂ m₁ m₂ m₃ m₄ m₅ α' f : SExpr}
      {mcap captureType :
        ((ParamsD2.TreeGen.rulePattern
          ParamsD2.TreeGen.flatCtors[2]).toPattern).Path → SExpr}
      (captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (hGamma : ParamsD2.D2ContextValid univs Gamma)
      (typing : Pattern.IotaTyping Gamma
        (ParamsD2.TreeGen.ruleRecName ParamsD2.TreeGen.flatCtors[2])
        (ParamsD2.TreeGen.flatCtors[2]).ctor.raw.name recLs ctorLs
        [m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] [f, α'] majorTerm A)
      (matched : ((ParamsD2.TreeGen.rulePattern
          ParamsD2.TreeGen.flatCtors[2]).toPattern).MatchesS
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[2]) recLs)).app
          (([f, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[2]).ctor.raw.name ctorLs)))
        recLs mcap)
      (hspine : SpineWF Gamma
        (SExpr.mkInst recLs
          (ParamsD2.d2TreeIotaRule univs treeFlatCtor2_lookup).df.type)
        ((ParamsD2.d2TreeIotaRule univs
          treeFlatCtor2_lookup).capturePaths.map mcap) A)
      (hcollapse : IsDefEq Gamma
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[2]) recLs)).app
          (([f, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[2]).ctor.raw.name ctorLs)))
        (((ParamsD2.d2TreeIotaRule univs
            treeFlatCtor2_lookup).capturePaths.map mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs
            (ParamsD2.d2TreeIotaRule univs treeFlatCtor2_lookup).df.lhs)) A),
      WHRedS Gamma
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[2]) recLs)).app
          (([f, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[2]).ctor.raw.name ctorLs)))
        ((m₃.app f).app
          (.lam α
            (((treeListRecSpine recLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅).lift).app
              ((f.lift).app (.bvar 0))))) := by
  letI : Params := ParamsD2.d2Params univs
  intro Gamma A majorTerm recLs ctorLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅ α' f mcap
    captureType captureTyping hGamma typing matched hspine hcollapse
  refine ReflTransGen.trans (ReflTransGen.tail .rfl
    (d2TreeIotaWHRed univs checked treeFlatCtor2_lookup captureTyping
      hGamma typing matched hspine hcollapse)) ?_
  show WHRedS Gamma
    ((ParamsD2.TreeGen.ruleRHS ParamsD2.treeRuleClosure
      treeFlatCtor2_lookup).applyS recLs mcap)
    ((m₃.app f).app
      (.lam α
        (((treeListRecSpine recLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅).lift).app
          ((f.lift).app (.bvar 0)))))
  rw [ParamsD2.treeRuleRHS_capture_tower treeFlatCtor2_lookup,
    appN_var_applyS_eq, treeCaptureValues matched]
  obtain ⟨Ts, hTs, hrhs⟩ := lamBodyN_eq_some treeBranchBody
  rw [hrhs, mkInst_lamN]
  exact whRedS_lamTower (Γ := Gamma) (Ts.map (SExpr.mkInst recLs))
    (SExpr.mkInst recLs (VExpr.bvar 3 |>.app (.bvar 0) |>.app
      (VExpr.lam (.bvar 8)
        (VExpr.const ``TreeList.rec [.param 0, .param 1]
          |>.app (.bvar 9) |>.app (.bvar 8) |>.app (.bvar 7)
          |>.app (.bvar 6) |>.app (.bvar 5) |>.app (.bvar 4)
          |>.app (.bvar 3) |>.app (.bvar 2)
          |>.app (VExpr.bvar 1 |>.app (.bvar 0))))))
    [α, M₁, M₂, m₁, m₂, m₃, m₄, m₅, f] (by simp [hTs])

/-- **`TreeList.nil` at D2, redex to contractum**: eight betas down to the
bare nil minor. -/
theorem d2NilIotaRun (univs : Nat)
    (checked : ParamsD2.D2TreeCheckedStep univs) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {α M₁ M₂ m₁ m₂ m₃ m₄ m₅ α' : SExpr}
      {mcap captureType :
        ((ParamsD2.TreeGen.rulePattern
          ParamsD2.TreeGen.flatCtors[3]).toPattern).Path → SExpr}
      (captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (hGamma : ParamsD2.D2ContextValid univs Gamma)
      (typing : Pattern.IotaTyping Gamma
        (ParamsD2.TreeGen.ruleRecName ParamsD2.TreeGen.flatCtors[3])
        (ParamsD2.TreeGen.flatCtors[3]).ctor.raw.name recLs ctorLs
        [m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] [α'] majorTerm A)
      (matched : ((ParamsD2.TreeGen.rulePattern
          ParamsD2.TreeGen.flatCtors[3]).toPattern).MatchesS
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[3]) recLs)).app
          (([α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[3]).ctor.raw.name ctorLs)))
        recLs mcap)
      (hspine : SpineWF Gamma
        (SExpr.mkInst recLs
          (ParamsD2.d2TreeIotaRule univs treeFlatCtor3_lookup).df.type)
        ((ParamsD2.d2TreeIotaRule univs
          treeFlatCtor3_lookup).capturePaths.map mcap) A)
      (hcollapse : IsDefEq Gamma
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[3]) recLs)).app
          (([α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[3]).ctor.raw.name ctorLs)))
        (((ParamsD2.d2TreeIotaRule univs
            treeFlatCtor3_lookup).capturePaths.map mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs
            (ParamsD2.d2TreeIotaRule univs treeFlatCtor3_lookup).df.lhs)) A),
      WHRedS Gamma
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[3]) recLs)).app
          (([α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[3]).ctor.raw.name ctorLs)))
        m₄ := by
  letI : Params := ParamsD2.d2Params univs
  intro Gamma A majorTerm recLs ctorLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅ α' mcap
    captureType captureTyping hGamma typing matched hspine hcollapse
  refine ReflTransGen.trans (ReflTransGen.tail .rfl
    (d2TreeIotaWHRed univs checked treeFlatCtor3_lookup captureTyping
      hGamma typing matched hspine hcollapse)) ?_
  show WHRedS Gamma
    ((ParamsD2.TreeGen.ruleRHS ParamsD2.treeRuleClosure
      treeFlatCtor3_lookup).applyS recLs mcap) m₄
  rw [ParamsD2.treeRuleRHS_capture_tower treeFlatCtor3_lookup,
    appN_var_applyS_eq, treeCaptureValues matched]
  obtain ⟨Ts, hTs, hrhs⟩ := lamBodyN_eq_some treeNilBody
  rw [hrhs, mkInst_lamN]
  exact whRedS_lamTower (Γ := Gamma) (Ts.map (SExpr.mkInst recLs))
    (SExpr.mkInst recLs (.bvar 1))
    [α, M₁, M₂, m₁, m₂, m₃, m₄, m₅] (by simp [hTs])

/-- **`TreeList.cons` at D2, redex to contractum**: the cons minor at both
fields and both mutual recursive calls — the reverse `TreeList → Tree` edge
that refuted every family rank, as an ordinary run. -/
theorem d2ConsIotaRun (univs : Nat)
    (checked : ParamsD2.D2TreeCheckedStep univs) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {α M₁ M₂ m₁ m₂ m₃ m₄ m₅ α' t ts : SExpr}
      {mcap captureType :
        ((ParamsD2.TreeGen.rulePattern
          ParamsD2.TreeGen.flatCtors[4]).toPattern).Path → SExpr}
      (captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (hGamma : ParamsD2.D2ContextValid univs Gamma)
      (typing : Pattern.IotaTyping Gamma
        (ParamsD2.TreeGen.ruleRecName ParamsD2.TreeGen.flatCtors[4])
        (ParamsD2.TreeGen.flatCtors[4]).ctor.raw.name recLs ctorLs
        [m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] [ts, t, α'] majorTerm A)
      (matched : ((ParamsD2.TreeGen.rulePattern
          ParamsD2.TreeGen.flatCtors[4]).toPattern).MatchesS
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[4]) recLs)).app
          (([ts, t, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[4]).ctor.raw.name ctorLs)))
        recLs mcap)
      (hspine : SpineWF Gamma
        (SExpr.mkInst recLs
          (ParamsD2.d2TreeIotaRule univs treeFlatCtor4_lookup).df.type)
        ((ParamsD2.d2TreeIotaRule univs
          treeFlatCtor4_lookup).capturePaths.map mcap) A)
      (hcollapse : IsDefEq Gamma
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[4]) recLs)).app
          (([ts, t, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[4]).ctor.raw.name ctorLs)))
        (((ParamsD2.d2TreeIotaRule univs
            treeFlatCtor4_lookup).capturePaths.map mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs
            (ParamsD2.d2TreeIotaRule univs treeFlatCtor4_lookup).df.lhs)) A),
      WHRedS Gamma
        ((([m₅, m₄, m₃, m₂, m₁, M₂, M₁, α] : List SExpr).foldr
            (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD2.TreeGen.ruleRecName
              ParamsD2.TreeGen.flatCtors[4]) recLs)).app
          (([ts, t, α'] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD2.TreeGen.flatCtors[4]).ctor.raw.name ctorLs)))
        ((((m₅.app t).app ts).app
            ((treeRecSpine recLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅).app t)).app
          ((treeListRecSpine recLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅).app ts)) := by
  letI : Params := ParamsD2.d2Params univs
  intro Gamma A majorTerm recLs ctorLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅ α' t ts mcap
    captureType captureTyping hGamma typing matched hspine hcollapse
  refine ReflTransGen.trans (ReflTransGen.tail .rfl
    (d2TreeIotaWHRed univs checked treeFlatCtor4_lookup captureTyping
      hGamma typing matched hspine hcollapse)) ?_
  show WHRedS Gamma
    ((ParamsD2.TreeGen.ruleRHS ParamsD2.treeRuleClosure
      treeFlatCtor4_lookup).applyS recLs mcap)
    ((((m₅.app t).app ts).app
        ((treeRecSpine recLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅).app t)).app
      ((treeListRecSpine recLs α M₁ M₂ m₁ m₂ m₃ m₄ m₅).app ts))
  rw [ParamsD2.treeRuleRHS_capture_tower treeFlatCtor4_lookup,
    appN_var_applyS_eq, treeCaptureValues matched]
  obtain ⟨Ts, hTs, hrhs⟩ := lamBodyN_eq_some treeConsBody
  rw [hrhs, mkInst_lamN]
  exact whRedS_lamTower (Γ := Gamma) (Ts.map (SExpr.mkInst recLs))
    (SExpr.mkInst recLs (VExpr.bvar 2 |>.app (.bvar 1) |>.app (.bvar 0)
      |>.app (VExpr.const ``Tree.rec [.param 0, .param 1]
        |>.app (.bvar 9) |>.app (.bvar 8) |>.app (.bvar 7)
        |>.app (.bvar 6) |>.app (.bvar 5) |>.app (.bvar 4)
        |>.app (.bvar 3) |>.app (.bvar 2) |>.app (.bvar 1))
      |>.app (VExpr.const ``TreeList.rec [.param 0, .param 1]
        |>.app (.bvar 9) |>.app (.bvar 8) |>.app (.bvar 7)
        |>.app (.bvar 6) |>.app (.bvar 5) |>.app (.bvar 4)
        |>.app (.bvar 3) |>.app (.bvar 2) |>.app (.bvar 0))))
    [α, M₁, M₂, m₁, m₂, m₃, m₄, m₅, t, ts] (by simp [hTs])

end IndCand
end Reducibility
end SExpr
end Lean4Lean

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

set_option linter.unusedVariables false

/-- **The inherited `Nat.zero` rule at D2, redex to contractum** — no check
premise (`d2NatChecked` discharges internally); conditional only on the
rule's capture-spine/collapse data, exactly as `d2NatEntryIotaWHRed`. -/
theorem d2NatZeroIotaRun (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {M mz ms : SExpr}
      {mcap captureType :
        ((ParamsD0.NatGeneration.rulePattern
          ParamsD0.NatGeneration.flatCtors[0]).toPattern).Path → SExpr}
      (captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (hGamma : ParamsD2.D2ContextValid univs Gamma)
      (typing : Pattern.IotaTyping Gamma
        (ParamsD0.NatGeneration.ruleRecName
          ParamsD0.NatGeneration.flatCtors[0])
        (ParamsD0.NatGeneration.flatCtors[0]).ctor.raw.name recLs ctorLs
        [ms, mz, M] [] majorTerm A)
      (matched : ((ParamsD0.NatGeneration.rulePattern
          ParamsD0.NatGeneration.flatCtors[0]).toPattern).MatchesS
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[0]) recLs)).app
          (([] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[0]).ctor.raw.name ctorLs)))
        recLs mcap)
      (hspine : SpineWF Gamma
        (SExpr.mkInst recLs
          (ParamsD2.d2NatEntryIotaRule univs
            ParamsD0.probeNatFlatCtorZero_lookup).df.type)
        ((ParamsD2.d2NatEntryIotaRule univs
          ParamsD0.probeNatFlatCtorZero_lookup).capturePaths.map mcap) A)
      (hcollapse : IsDefEq Gamma
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[0]) recLs)).app
          (([] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[0]).ctor.raw.name ctorLs)))
        (((ParamsD2.d2NatEntryIotaRule univs
            ParamsD0.probeNatFlatCtorZero_lookup).capturePaths.map
              mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs
            (ParamsD2.d2NatEntryIotaRule univs
              ParamsD0.probeNatFlatCtorZero_lookup).df.lhs)) A),
      WHRedS Gamma
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[0]) recLs)).app
          (([] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[0]).ctor.raw.name ctorLs)))
        mz := by
  letI : Params := ParamsD2.d2Params univs
  intro Gamma A majorTerm recLs ctorLs M mz ms mcap captureType
    captureTyping hGamma typing matched hspine hcollapse
  refine ReflTransGen.trans (ReflTransGen.tail .rfl
    (d2NatEntryIotaWHRed univs ParamsD0.probeNatFlatCtorZero_lookup
      captureTyping hGamma typing matched hspine hcollapse)) ?_
  show WHRedS Gamma
    ((ParamsD0.NatGeneration.ruleRHS ParamsD0.natRuleClosure
      ParamsD0.probeNatFlatCtorZero_lookup).applyS recLs mcap) mz
  rw [ParamsD0.natRuleRHS_tower ParamsD0.probeNatFlatCtorZero_lookup,
    appN_var_applyS_eq, natCaptureValues matched]
  obtain ⟨Ts, hTs, hrhs⟩ := lamBodyN_eq_some natZeroBody
  rw [hrhs, mkInst_lamN]
  exact whRedS_lamTower (Γ := Gamma) (Ts.map (SExpr.mkInst recLs))
    (SExpr.mkInst recLs (.bvar 1)) [M, mz, ms] (by simp [hTs])

/-- **The inherited `Nat.succ` rule at D2, redex to contractum** — no check
premise. -/
theorem d2NatSuccIotaRun (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {M mz ms n : SExpr}
      {mcap captureType :
        ((ParamsD0.NatGeneration.rulePattern
          ParamsD0.NatGeneration.flatCtors[1]).toPattern).Path → SExpr}
      (captureTyping : Pattern.CaptureTyping Gamma mcap captureType)
      (hGamma : ParamsD2.D2ContextValid univs Gamma)
      (typing : Pattern.IotaTyping Gamma
        (ParamsD0.NatGeneration.ruleRecName
          ParamsD0.NatGeneration.flatCtors[1])
        (ParamsD0.NatGeneration.flatCtors[1]).ctor.raw.name recLs ctorLs
        [ms, mz, M] [n] majorTerm A)
      (matched : ((ParamsD0.NatGeneration.rulePattern
          ParamsD0.NatGeneration.flatCtors[1]).toPattern).MatchesS
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[1]) recLs)).app
          (([n] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[1]).ctor.raw.name ctorLs)))
        recLs mcap)
      (hspine : SpineWF Gamma
        (SExpr.mkInst recLs
          (ParamsD2.d2NatEntryIotaRule univs
            ParamsD0.probeNatFlatCtorSucc_lookup).df.type)
        ((ParamsD2.d2NatEntryIotaRule univs
          ParamsD0.probeNatFlatCtorSucc_lookup).capturePaths.map mcap) A)
      (hcollapse : IsDefEq Gamma
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[1]) recLs)).app
          (([n] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[1]).ctor.raw.name ctorLs)))
        (((ParamsD2.d2NatEntryIotaRule univs
            ParamsD0.probeNatFlatCtorSucc_lookup).capturePaths.map
              mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs
            (ParamsD2.d2NatEntryIotaRule univs
              ParamsD0.probeNatFlatCtorSucc_lookup).df.lhs)) A),
      WHRedS Gamma
        ((([ms, mz, M] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const (ParamsD0.NatGeneration.ruleRecName
              ParamsD0.NatGeneration.flatCtors[1]) recLs)).app
          (([n] : List SExpr).foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const
              (ParamsD0.NatGeneration.flatCtors[1]).ctor.raw.name ctorLs)))
        ((ms.app n).app ((natRecSpine recLs M mz ms).app n)) := by
  letI : Params := ParamsD2.d2Params univs
  intro Gamma A majorTerm recLs ctorLs M mz ms n mcap captureType
    captureTyping hGamma typing matched hspine hcollapse
  refine ReflTransGen.trans (ReflTransGen.tail .rfl
    (d2NatEntryIotaWHRed univs ParamsD0.probeNatFlatCtorSucc_lookup
      captureTyping hGamma typing matched hspine hcollapse)) ?_
  show WHRedS Gamma
    ((ParamsD0.NatGeneration.ruleRHS ParamsD0.natRuleClosure
      ParamsD0.probeNatFlatCtorSucc_lookup).applyS recLs mcap)
    ((ms.app n).app ((natRecSpine recLs M mz ms).app n))
  rw [ParamsD0.natRuleRHS_tower ParamsD0.probeNatFlatCtorSucc_lookup,
    appN_var_applyS_eq, natCaptureValues matched]
  obtain ⟨Ts, hTs, hrhs⟩ := lamBodyN_eq_some natSuccBody
  rw [hrhs, mkInst_lamN]
  exact whRedS_lamTower (Γ := Gamma) (Ts.map (SExpr.mkInst recLs))
    (SExpr.mkInst recLs (VExpr.bvar 1 |>.app (.bvar 0) |>.app
      (VExpr.const ``Nat.rec [.param 0] |>.app (.bvar 3) |>.app (.bvar 2)
        |>.app (.bvar 1) |>.app (.bvar 0))))
    [M, mz, ms, n] (by simp [hTs])

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ## N′2.5 — `ConstFundamental` content: constants via δ-descent

The rank-recursion skeleton and the rank-zero head content.  The per-step
obligation (`DeltaStepObligation`) is an explicit hypothesis interface: at
a ranked definition N′3 discharges it by running the fundamental theorem
over the value's `HasTypeStratifiedR` certificate (whose constants sit at
rank strictly below `rank c`, i.e. inside `ConstsReducibleBelow (rank c)`)
and transferring along the δ-step with `Candidate.ofDeltaValue`; at a
rank-zero head it discharges by the irreducible-head content below plus the
action/head layers of the membership induction. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

variable [Params]

/-- A bare constant with no registered constant-headed pattern takes no
step: the only rule that could fire is `extra`, and a constant target is
matched only by the constant pattern itself. -/
theorem _root_.Lean4Lean.SExpr.WHNF.constNoPat {Γ : List SExpr} {c : Name}
    {ls : List SLevel}
    (h : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      ¬Params.Pat (.const c) r) :
    WHNF Γ (.const c ls) := by
  intro e' hred
  cases hred with
  | extra action =>
    cases action.matched with
    | const => exact h action.pat

/-- Weak-head normal after every future lift: the operational half of the
rank-zero constant content. -/
def KripkeWHNF (Γ : List SExpr) (M : SExpr) : Prop :=
  ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ → WHNF Δ (M.lift' ρ)

/-- Irreducible constants are Kripke-WHNF (constants are lift-invariant). -/
theorem KripkeWHNF.constNoPat {Γ : List SExpr} {c : Name} {ls : List SLevel}
    (h : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      ¬Params.Pat (.const c) r) :
    KripkeWHNF Γ (.const c ls) :=
  fun _ => WHNF.constNoPat h

/-- Lifting a constant-headed application spine lifts its arguments. -/
theorem foldr_app_lift' (args : List SExpr) (c : Name) (ls : List SLevel)
    (ρ : Lift) :
    (args.foldr (fun (a f : SExpr) => f.app a) (.const c ls)).lift' ρ =
      (args.map (·.lift' ρ)).foldr (fun (a f : SExpr) => f.app a)
        (.const c ls) := by
  induction args with
  | nil => rfl
  | cons a args ih => simp [ih]

/-- Classified constructor spines — total or partial — are Kripke-WHNF. -/
theorem KripkeWHNF.ctorSpine {Γ : List SExpr} {c : Name} {k : Nat}
    {ls : List SLevel} (hcl : Params.classify c = some (.ctor k))
    (args : List SExpr) :
    KripkeWHNF Γ (args.foldr (fun (a f : SExpr) => f.app a)
      (.const c ls)) := by
  intro Δ ρ W
  rw [foldr_app_lift']
  exact WHNF.ctorSpine hcl _

/-- Recursor spines stuck at a neutral major are Kripke-WHNF. -/
theorem KripkeWHNF.stuckMajor {Γ : List SExpr} {f t : SExpr}
    (hmaj : IsMajorPremise f) (hn : Neutral t) :
    KripkeWHNF Γ (f.app t) := by
  intro Δ ρ W
  show WHNF Δ ((f.lift' ρ).app (t.lift' ρ))
  exact (IsMajorPremise.lift'.2 hmaj).stuckApp hn.lift'

/-- Kripke-WHNF endpoints Kripke-normalize at every displayed type. -/
theorem KripkeNormalizes.ofKripkeWHNF {Γ : List SExpr} {M N A : SExpr}
    (hM : KripkeWHNF Γ M) (hN : KripkeWHNF Γ N) :
    KripkeNormalizes Γ M N A :=
  fun W => ⟨⟨_, .rfl, hM W⟩, ⟨_, .rfl, hN W⟩⟩

/-- `Base` from Kripke-WHNF endpoints; the judgmental edge is a hypothesis
(betaFire boundary — no typed trace is produced). -/
theorem Base.ofKripkeWHNF {Γ : List SExpr} {M N A : SExpr}
    (edge : IsDefEqStrong Γ M N A) (hM : KripkeWHNF Γ M)
    (hN : KripkeWHNF Γ N) : Base Γ M N A :=
  ⟨edge, KripkeNormalizes.ofKripkeWHNF hM hN⟩

/-- **Rank-zero constants, depth 0**: an irreducible constant is
`Base`-reducible at any self-edge. -/
theorem Base.const_irreducible {Γ : List SExpr} {c : Name}
    {ls : List SLevel} {A : SExpr}
    (h : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      ¬Params.Pat (.const c) r)
    (edge : IsDefEqStrong Γ (.const c ls) (.const c ls) A) :
    Base Γ (.const c ls) (.const c ls) A :=
  Base.ofKripkeWHNF edge (KripkeWHNF.constNoPat h) (KripkeWHNF.constNoPat h)

/-- **Partial and total constructor applications, depth 0**: classified
constructor spines of any length are `Base`-reducible at any edge between
them.  (Their depth-`succ` action content — applying a partial constructor
lands in the `InCand*` constructor clause — is N′3 membership content;
recorded as deferred.) -/
theorem Base.ctorSpines {Γ : List SExpr} {c c' : Name} {k k' : Nat}
    {ls ls' : List SLevel} {args args' : List SExpr} {A : SExpr}
    (hc : Params.classify c = some (.ctor k))
    (hc' : Params.classify c' = some (.ctor k'))
    (edge : IsDefEqStrong Γ
      (args.foldr (fun (a f : SExpr) => f.app a) (.const c ls))
      (args'.foldr (fun (a f : SExpr) => f.app a) (.const c' ls')) A) :
    Base Γ
      (args.foldr (fun (a f : SExpr) => f.app a) (.const c ls))
      (args'.foldr (fun (a f : SExpr) => f.app a) (.const c' ls')) A :=
  Base.ofKripkeWHNF edge (KripkeWHNF.ctorSpine hc args) (KripkeWHNF.ctorSpine hc' args')

/-- **Stuck recursor applications, depth 0**: a registered spine at a
neutral major is `Base`-reducible at any edge between two such.  (Their
`InCand*` membership under the landed bvar-only neutral clause is the
recorded N′3 deferral.) -/
theorem Base.stuckMajors {Γ : List SExpr} {f f' t t' : SExpr} {A : SExpr}
    (hmaj : IsMajorPremise f) (hmaj' : IsMajorPremise f')
    (hn : Neutral t) (hn' : Neutral t')
    (edge : IsDefEqStrong Γ (f.app t) (f'.app t') A) :
    Base Γ (f.app t) (f'.app t') A :=
  Base.ofKripkeWHNF edge (KripkeWHNF.stuckMajor hmaj hn) (KripkeWHNF.stuckMajor hmaj' hn')

/-- **The pointed δ-step consumer**: one untyped unfolding step plus its
certificate transfer the value's reducibility to the constant, at every
depth.  This is the lemma the per-step obligation fires after the
fundamental theorem has interpreted the value. -/
theorem Candidate.ofDeltaValue [Params.Semantic] {Γ : List SExpr}
    {c : Name} {ls : List SLevel} {V A : SExpr} {depth : Nat}
    (red : WHRed Γ (.const c ls) V)
    (sound : IsDefEqStrong Γ (.const c ls) V A)
    (hV : Candidate depth Γ V V A) :
    Candidate depth Γ (.const c ls) (.const c ls) A :=
  Candidate.expand (WHStep.toSteps ⟨red, sound⟩)
    (WHStep.toSteps ⟨red, sound⟩) hV

section DeltaDescent

variable [Params.DeltaRank]

/-- The δ-descent recursion invariant: reducibility of every constant of
rank strictly below `n`, at every depth. -/
def ConstsReducibleBelow (n : Nat) : Prop :=
  ∀ {Γ : List SExpr} {c : Name} {ls : List SLevel} {A : SExpr},
    Params.DeltaRank.rank c < n →
    IsDefEqStrong Γ (.const c ls) (.const c ls) A →
    ∀ depth, Candidate depth Γ (.const c ls) (.const c ls) A

/-- Nonvacuity of the invariant: below rank zero there is nothing to
interpret. -/
theorem constsReducibleBelow_zero : ConstsReducibleBelow 0 := by
  intro Γ c ls A hlt
  exact absurd hlt (Nat.not_lt_zero _)

/-- **The per-step obligation of the δ-descent** — an explicit hypothesis
interface, not an axiom: every typed constant is reducible once everything
of strictly smaller rank is.  N′3 discharges it per constant class: ranked
definitions via `DeltaRank.defnCert` + the fundamental theorem over the
value's certificate + `Candidate.ofDeltaValue`; rank-zero heads via the
irreducible-head content above plus membership. -/
def DeltaStepObligation : Prop :=
  ∀ {Γ : List SExpr} {c : Name} {ls : List SLevel} {A : SExpr},
    IsDefEqStrong Γ (.const c ls) (.const c ls) A →
    ConstsReducibleBelow (Params.DeltaRank.rank c) →
    ∀ depth, Candidate depth Γ (.const c ls) (.const c ls) A

/-- Shape nonvacuity of the obligation: it is a consequence of the
fundamental theorem it feeds (so the interface asks for strictly less than
the theorem it produces). -/
theorem DeltaStepObligation.of_fundamental
    (fund : ∀ depth, Fundamental depth) : DeltaStepObligation :=
  fun edge _ depth => fund depth edge

/-- **The well-founded recursion on the rank**: plain induction on the rank
bound turns the per-step obligation into the full invariant.  δ-steps
strictly decrease the rank (`DeltaRank.defnCert`), so this is the entire
termination content of constant unfolding — no term measure. -/
theorem constsReducibleBelow_all (obl : DeltaStepObligation) :
    ∀ n, ConstsReducibleBelow n := by
  intro n
  induction n with
  | zero => exact constsReducibleBelow_zero
  | succ n ih =>
    intro Γ c ls A hlt edge depth
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with h | h
    · exact ih h edge depth
    · exact obl edge (h ▸ ih) depth

/-- Every typed constant is reducible at every depth, from the per-step
obligation alone. -/
theorem candidate_const_of_deltaStep (obl : DeltaStepObligation)
    {Γ : List SExpr} {c : Name} {ls : List SLevel} {A : SExpr}
    (edge : IsDefEqStrong Γ (.const c ls) (.const c ls) A) (depth : Nat) :
    Candidate depth Γ (.const c ls) (.const c ls) A :=
  obl edge (constsReducibleBelow_all obl _) depth

/-- **The seam shape**: the δ-descent skeleton closes `ConstFundamental`
from the per-step obligation.  Constants are substitution-invariant, so all
three interpretation components coincide. -/
theorem ConstFundamental.of_deltaStep [Params.Semantic]
    (obl : DeltaStepObligation) : ConstFundamental := by
  intro Gamma c ls A H Delta sigma sigma' hDelta env depth
  have edge : IsDefEqStrong Delta (.const c ls) (.const c ls)
      (A.subst sigma) :=
    (env.substStrong hDelta H).hasType.1
  have cand := candidate_const_of_deltaStep obl edge depth
  exact ⟨cand, cand, cand⟩

end DeltaDescent

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ### N′2.5 instance discharges — literal ranks, irreducible heads, δ-steps

The D-ladder rank certificates are consumed at their literal values: the
strict δ-drop at d0 with its live operational step, the full three-link d1
chain, and the d2 chain with every block head at rank zero.  Constant
patterns at each instance are exactly the registered definitions, so every
block head, constructor, and recursor is irreducible and its `Base` content
fires outright at any strong self-edge. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

/-- A D0 constant pattern is the registered definition. -/
theorem d0ConstPat_name (univs : Nat) {c : Name}
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (H : (ParamsD0.d0Params univs).Pat (.const c) r) :
    c = ParamsD0.d0DefVal.name := by
  change ParamsD0.D0Pat _ _ at H
  cases H with
  | iota h => exact (ParamsD0.natPat_no_const univs h).elim
  | defn => rfl

/-- A D2 constant pattern is one of the three registered definitions. -/
theorem d2ConstPat_names (univs : Nat) {c : Name}
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (H : (ParamsD2.d2Params univs).Pat (.const c) r) :
    c = ParamsD0.d0DefVal.name ∨ c = ParamsD1.d1MutAVal.name ∨
      c = ParamsD1.d1MutBVal.name := by
  change ParamsD2.D2Pat _ _ at H
  have H1 := ParamsD2.d2Pat_at_const H
  cases H1 with
  | old h0 =>
    cases h0 with
    | iota h => exact (ParamsD0.natPat_no_const univs h).elim
    | defn => exact .inl rfl
  | defnA => exact .inr (.inl rfl)
  | defnB => exact .inr (.inr rfl)

/-- Irreducibility at D0 for any constant other than the definition. -/
theorem d0ConstIrreducible (univs : Nat) {c : Name}
    (hne : c ≠ ParamsD0.d0DefVal.name) :
    ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      ¬(ParamsD0.d0Params univs).Pat (.const c) r :=
  fun H => hne (d0ConstPat_name univs H)

/-- Irreducibility at D2 for any constant other than the three
definitions — in particular for every block head, constructor, and
recursor. -/
theorem d2ConstIrreducible (univs : Nat) {c : Name}
    (h1 : c ≠ ParamsD0.d0DefVal.name) (h2 : c ≠ ParamsD1.d1MutAVal.name)
    (h3 : c ≠ ParamsD1.d1MutBVal.name) :
    ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      ¬(ParamsD2.d2Params univs).Pat (.const c) r := by
  intro r H
  rcases d2ConstPat_names univs H with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

/-- **The literal δ-descent at d0**: the registered definition steps
operationally to its value in every context, and its rank strictly drops
at the literal certificate (`1 → 0`). -/
theorem d0DeltaDescent (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    letI : Params.DeltaRank := ParamsD0.d0DeltaRank univs
    (∀ Gamma : List SExpr,
      WHRed Gamma (.const ParamsD0.d0DefVal.name [])
        (.const ``Nat.zero [])) ∧
      Params.DeltaRank.rank ``Nat.zero <
        Params.DeltaRank.rank ParamsD0.d0DefVal.name := by
  letI : Params := ParamsD0.d0Params univs
  letI : Params.DeltaRank := ParamsD0.d0DeltaRank univs
  refine ⟨d0DefWHRed univs, ?_⟩
  show ParamsD0.d0DeltaRankFn ``Nat.zero <
    ParamsD0.d0DeltaRankFn ParamsD0.d0DefVal.name
  decide

/-- **The literal d1 rank chain**: the live definition chain
`d1mutA ▸ d1mutB ▸ d0def ▸ Nat.zero` strictly descends at the certified
literal ranks `3 > 2 > 1 > 0`. -/
theorem d1DeltaChain (univs : Nat) :
    letI : Params := ParamsD1.d1Params univs
    letI : Params.DeltaRank := ParamsD1.d1DeltaRank univs
    Params.DeltaRank.rank ``Nat.zero <
        Params.DeltaRank.rank ParamsD0.d0DefVal.name ∧
      Params.DeltaRank.rank ParamsD0.d0DefVal.name <
        Params.DeltaRank.rank ParamsD1.d1MutBVal.name ∧
      Params.DeltaRank.rank ParamsD1.d1MutBVal.name <
        Params.DeltaRank.rank ParamsD1.d1MutAVal.name := by
  letI : Params := ParamsD1.d1Params univs
  letI : Params.DeltaRank := ParamsD1.d1DeltaRank univs
  refine ⟨?_, ?_, ?_⟩ <;>
    · show ParamsD1.d1DeltaRankFn _ < ParamsD1.d1DeltaRankFn _
      decide

/-- **The literal d2 rank chain**: the inherited definition chain keeps its
strict descent, and every block head sits at rank zero. -/
theorem d2DeltaChain (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    letI : Params.DeltaRank := ParamsD2.d2DeltaRank univs
    (Params.DeltaRank.rank ``Nat.zero <
        Params.DeltaRank.rank ParamsD0.d0DefVal.name ∧
      Params.DeltaRank.rank ParamsD0.d0DefVal.name <
        Params.DeltaRank.rank ParamsD1.d1MutBVal.name ∧
      Params.DeltaRank.rank ParamsD1.d1MutBVal.name <
        Params.DeltaRank.rank ParamsD1.d1MutAVal.name) ∧
      Params.DeltaRank.rank ``Tree = 0 ∧
      Params.DeltaRank.rank ``TreeList = 0 ∧
      Params.DeltaRank.rank ``Tree.rec = 0 ∧
      Params.DeltaRank.rank ``TreeList.rec = 0 ∧
      Params.DeltaRank.rank ``Tree.leaf = 0 ∧
      Params.DeltaRank.rank ``Tree.node = 0 ∧
      Params.DeltaRank.rank ``Tree.branch = 0 ∧
      Params.DeltaRank.rank ``TreeList.nil = 0 ∧
      Params.DeltaRank.rank ``TreeList.cons = 0 := by
  letI : Params := ParamsD2.d2Params univs
  letI : Params.DeltaRank := ParamsD2.d2DeltaRank univs
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (show ParamsD2.d2DeltaRankFn _ < ParamsD2.d2DeltaRankFn _
         decide)
      | (show ParamsD2.d2DeltaRankFn _ = 0
         decide)

/-- **The operational δ-step at the D2 instance**: the inherited definition
`d0def ≡ Nat.zero` fires as an untyped `WHRed.extra` step over the block
environment, premise-free — the d2 twin of the landed `d0DefWHRed`. -/
theorem d2DefWHRed (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ Gamma : List SExpr,
      WHRed Gamma (.const ParamsD0.d0DefVal.name [])
        (.const ``Nat.zero []) := by
  letI : Params := ParamsD2.d2Params univs
  intro Gamma
  let r : (Pattern.const ParamsD0.d0DefVal.name).RHS ×
      (Pattern.const ParamsD0.d0DefVal.name).Check :=
    (.fixed ParamsD0.d0DefVal.value ParamsD0.d0DefClosed, .true)
  let action : Pattern.Action Gamma r
      (.const ParamsD0.d0DefVal.name []) [] Empty.elim
      (.const ``Nat []) := {
    pat := ParamsD2.d1Pat_to_d2 (.old .defn)
    matched := by
      refine cast ?_ (@Pattern.MatchesS.const (ParamsD2.d2Params univs)
        ParamsD0.d0DefVal.name [])
      congr 1
      funext path
      exact Empty.elim path
    dfs := []
    defeqs := rfl
    checked := by simp
    sound := by
      have H := @IsDefEq.extra (ParamsD2.d2Params univs)
        ParamsD0.d0DefVal.toDefEq Gamma []
        (ParamsD2.d1Env_le_d2Env.defeqs
          (ParamsD1.d0Env_le_d1Env.defeqs VEnv.addDefEq_self)) rfl
      change IsDefEq Gamma (.const ParamsD0.d0DefVal.name [])
        (.const ``Nat.zero []) (.const ``Nat []) at H
      exact H }
  have step := WHRed.extra action
  change WHRed Gamma (.const ParamsD0.d0DefVal.name [])
    (.const ``Nat.zero []) at step
  exact step

/-- **The ranked definition's `Base` content at d0**: the constant's
Kripke normalization is its one δ-step to the irreducible `Nat.zero`; only
the judgmental edge is a hypothesis. -/
theorem d0DefBase (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    ∀ {Gamma : List SExpr} {A : SExpr},
      IsDefEqStrong Gamma (.const ParamsD0.d0DefVal.name [])
        (.const ParamsD0.d0DefVal.name []) A →
      Base Gamma (.const ParamsD0.d0DefVal.name [])
        (.const ParamsD0.d0DefVal.name []) A := by
  letI : Params := ParamsD0.d0Params univs
  intro Gamma A edge
  refine ⟨edge, ?_⟩
  intro Δ ρ W
  have result : WHResult Δ (.const ParamsD0.d0DefVal.name [])
      (A.lift' ρ) :=
    ⟨.const ``Nat.zero [], .tail .rfl (d0DefWHRed univs Δ),
      WHNF.constNoPat (d0ConstIrreducible univs (by decide))⟩
  exact ⟨result, result⟩

/-- The d2 twin of the ranked definition's `Base` content. -/
theorem d2DefBase (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {Gamma : List SExpr} {A : SExpr},
      IsDefEqStrong Gamma (.const ParamsD0.d0DefVal.name [])
        (.const ParamsD0.d0DefVal.name []) A →
      Base Gamma (.const ParamsD0.d0DefVal.name [])
        (.const ParamsD0.d0DefVal.name []) A := by
  letI : Params := ParamsD2.d2Params univs
  intro Gamma A edge
  refine ⟨edge, ?_⟩
  intro Δ ρ W
  have result : WHResult Δ (.const ParamsD0.d0DefVal.name [])
      (A.lift' ρ) :=
    ⟨.const ``Nat.zero [], .tail .rfl (d2DefWHRed univs Δ),
      WHNF.constNoPat (d2ConstIrreducible univs
        (by decide) (by decide) (by decide))⟩
  exact ⟨result, result⟩

/-- **Rank-zero heads at d0**: the `Nat` family head, both constructors,
and the recursor are irreducible, so their `Base` content fires at any
strong self-edge. -/
theorem d0HeadsBase (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    ∀ {Gamma : List SExpr} {c : Name} {ls : List SLevel} {A : SExpr},
      (c = ``Nat ∨ c = ``Nat.zero ∨ c = ``Nat.succ ∨ c = ``Nat.rec) →
      IsDefEqStrong Gamma (.const c ls) (.const c ls) A →
      Base Gamma (.const c ls) (.const c ls) A := by
  letI : Params := ParamsD0.d0Params univs
  intro Gamma c ls A hc edge
  refine Base.const_irreducible (fun {r} => d0ConstIrreducible univs ?_) edge
  rcases hc with rfl | rfl | rfl | rfl <;> decide

/-- **Rank-zero heads at d2**: every block head, constructor, and recursor
of the full inventory — `Nat` and the `Tree`/`TreeList` block — is
irreducible, so its `Base` content fires at any strong self-edge. -/
theorem d2HeadsBase (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ {Gamma : List SExpr} {c : Name} {ls : List SLevel} {A : SExpr},
      (c = ``Nat ∨ c = ``Nat.zero ∨ c = ``Nat.succ ∨ c = ``Nat.rec ∨
        c = ``Tree ∨ c = ``TreeList ∨ c = ``Tree.rec ∨
        c = ``TreeList.rec ∨ c = ``Tree.leaf ∨ c = ``Tree.node ∨
        c = ``Tree.branch ∨ c = ``TreeList.nil ∨ c = ``TreeList.cons) →
      IsDefEqStrong Gamma (.const c ls) (.const c ls) A →
      Base Gamma (.const c ls) (.const c ls) A := by
  letI : Params := ParamsD2.d2Params univs
  intro Gamma c ls A hc edge
  refine Base.const_irreducible
    (fun {r} => d2ConstIrreducible univs ?_ ?_ ?_) edge <;>
    (rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> decide)

/-- **Partial constructor applications at d2**: the one-argument `Tree`
constructor spines (`Tree.leaf α`, …) and two-argument `TreeList.cons`
spines are `Base`-reducible at any strong self-edge — the recorded
instance content of the partial-application statement. -/
theorem d2PartialCtorBase (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ (l : SLevel) {Gamma : List SExpr} {args : List SExpr} {A : SExpr}
      {c : Name},
      (c = ``Tree.leaf ∨ c = ``Tree.node ∨ c = ``Tree.branch ∨
        c = ``TreeList.nil ∨ c = ``TreeList.cons) →
      IsDefEqStrong Gamma
        (args.foldr (fun (a f : SExpr) => f.app a) (.const c [l]))
        (args.foldr (fun (a f : SExpr) => f.app a) (.const c [l])) A →
      Base Gamma
        (args.foldr (fun (a f : SExpr) => f.app a) (.const c [l]))
        (args.foldr (fun (a f : SExpr) => f.app a) (.const c [l])) A := by
  letI : Params := ParamsD2.d2Params univs
  intro l Gamma args A c hc edge
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    exact Base.ctorSpines rfl rfl edge

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ## N′2.6 — `HeadFundamental 0` content: head observations at depth zero

The lemma family filling `Fundamental.succ`'s `HeadFundamental 0` slot from
`Base`-level data.  Three Kripke observation sources — matching Pi targets
with `Base`-related components, matching sort targets, and a normal form
that is neither Pi nor sort — produce both orientations of
`HeadLayer Base`, all by `WHRedS` determinism against the landed
`RelatedPath.single`/`defeqDF_l` shapes.  Membership supplies the third
source: every `InCand*` member reaches a neutral or classified-constructor
normal form, so members' head obligations hold vacuously.  The per-edge
classification `HeadObservationData` is the named interface N′3's
induction discharges case by case; no case needed adequacy-strength input,
so the rung's kill criterion was not triggered. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

variable [Params]

/-- Kripke Pi-observation data: after every future lift both endpoints
reach syntactic Pis with `Base`-related domain and codomain (the codomain
pair in the left-domain context, as `Candidate.forallERel` records it). -/
def KripkePiData (Γ : List SExpr) (M N : SExpr) : Prop :=
  ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    ∃ D C D' C' u v,
      WHRedS Δ (M.lift' ρ) (.forallE D C) ∧
      WHRedS Δ (N.lift' ρ) (.forallE D' C') ∧
      Base Δ D D' (.sort u) ∧ Base (D :: Δ) C C' (.sort v)

/-- Kripke sort-observation data: both endpoints reach the same sort after
every future lift. -/
def KripkeSortData (Γ : List SExpr) (M N : SExpr) : Prop :=
  ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    ∃ u, WHRedS Δ (M.lift' ρ) (.sort u) ∧ WHRedS Δ (N.lift' ρ) (.sort u)

theorem KripkeSortData.symm {Γ : List SExpr} {M N : SExpr}
    (h : KripkeSortData Γ M N) : KripkeSortData Γ N M := by
  intro Δ ρ W
  obtain ⟨u, h1, h2⟩ := h W
  exact ⟨u, h2, h1⟩

/-- A Kripke non-type head: after every future lift the normal form reached
is neither a Pi nor a sort.  Such a term refutes both head observations
against any partner, at any relation. -/
def KripkeNonTypeHead (Γ : List SExpr) (M : SExpr) : Prop :=
  ∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ Δ →
    ∃ r, WHRedS Δ (M.lift' ρ) r ∧ WHNF Δ r ∧
      (∀ D C, r ≠ .forallE D C) ∧ (∀ u, r ≠ .sort u)

/-- **Pi targets give the forward head layer at depth 0**: determinism
identifies the observed Pi with the recorded one, and the recorded `Base`
components enter as `RelatedPath.single` edges. -/
theorem KripkePiData.headLayer {Γ : List SExpr} {M N A : SExpr}
    (h : KripkePiData Γ M N) : HeadLayer Base Γ M N A where
  piHead := by
    intro Δ ρ D C s t W typeRun observed
    obtain ⟨D₀, C₀, D', C', u, v, runM, runN, dom, cod⟩ := h W
    have heq : (.forallE D C : SExpr) = .forallE D₀ C₀ :=
      WHRedS.determ observed WHNF.forallE runM WHNF.forallE
    injection heq with hD hC
    subst hD
    subst hC
    exact ⟨D', C', runN, u, v, .single dom.edge dom, .single cod.edge cod⟩
  sortHead := by
    intro Δ ρ s t u W typeRun observed
    obtain ⟨D₀, C₀, D', C', u', v', runM, runN, dom, cod⟩ := h W
    have bad : (.sort u : SExpr) = .forallE D₀ C₀ :=
      WHRedS.determ observed WHNF.sort runM WHNF.forallE
    cases bad

/-- **Pi targets give the reverse head layer at depth 0**: the symmetric
component edges, with the codomain pair transported to the right-domain
context by the landed `defeqDF_l` constructor. -/
theorem KripkePiData.headLayerRev {Γ : List SExpr} {M N A : SExpr}
    (h : KripkePiData Γ M N) : HeadLayer Base Γ N M A where
  piHead := by
    intro Δ ρ D C s t W typeRun observed
    obtain ⟨D₀, C₀, D', C', u, v, runM, runN, dom, cod⟩ := h W
    have heq : (.forallE D C : SExpr) = .forallE D' C' :=
      WHRedS.determ observed WHNF.forallE runN WHNF.forallE
    injection heq with hD hC
    subst hD
    subst hC
    refine ⟨D₀, C₀, runM, u, v, .single dom.edge.symm dom.symm, ?_⟩
    exact .defeqDF_l (.single dom.edge.defeq)
      (.single cod.edge.symm cod.symm)
  sortHead := by
    intro Δ ρ s t u W typeRun observed
    obtain ⟨D₀, C₀, D', C', u', v', runM, runN, dom, cod⟩ := h W
    have bad : (.sort u : SExpr) = .forallE D' C' :=
      WHRedS.determ observed WHNF.sort runN WHNF.forallE
    cases bad

/-- **Sort targets give the head layer at every relation**: the Pi
observation is refuted by determinism, and the sort observation returns the
recorded twin run at the same level. -/
theorem KripkeSortData.headLayer {R : Rel} {Γ : List SExpr} {M N A : SExpr}
    (h : KripkeSortData Γ M N) : HeadLayer R Γ M N A where
  piHead := by
    intro Δ ρ D C s t W typeRun observed
    obtain ⟨u, runM, runN⟩ := h W
    have bad : (.forallE D C : SExpr) = .sort u :=
      WHRedS.determ observed WHNF.forallE runM WHNF.sort
    cases bad
  sortHead := by
    intro Δ ρ s t u W typeRun observed
    obtain ⟨u₀, runM, runN⟩ := h W
    have heq : (.sort u : SExpr) = .sort u₀ :=
      WHRedS.determ observed WHNF.sort runM WHNF.sort
    injection heq with hu
    subst hu
    exact runN

/-- **A non-type head refutes both observations** — against any partner, at
any relation. -/
theorem KripkeNonTypeHead.headLayer {R : Rel} {Γ : List SExpr}
    {M N A : SExpr} (h : KripkeNonTypeHead Γ M) : HeadLayer R Γ M N A where
  piHead := by
    intro Δ ρ D C s t W typeRun observed
    obtain ⟨r, run, nf, hpi, hsort⟩ := h W
    exact absurd (WHRedS.determ observed WHNF.forallE run nf).symm
      (hpi _ _)
  sortHead := by
    intro Δ ρ s t u W typeRun observed
    obtain ⟨r, run, nf, hpi, hsort⟩ := h W
    exact absurd (WHRedS.determ observed WHNF.sort run nf).symm (hsort _)

/-! ### Non-type-head sources -/

/-- Neutral terms have non-type heads. -/
theorem KripkeNonTypeHead.ofNeutral {Γ : List SExpr} {M : SExpr}
    (hn : Neutral M) : KripkeNonTypeHead Γ M :=
  fun _ => ⟨_, .rfl, hn.lift'.whnf,
    fun _ _ => hn.lift'.notForallE, fun _ => hn.lift'.notSort⟩

/-- A constant-headed application spine is never a Pi. -/
theorem foldr_app_ne_forallE (args : List SExpr) (c : Name)
    (ls : List SLevel) :
    ∀ D C, args.foldr (fun (a f : SExpr) => f.app a) (.const c ls) ≠
      .forallE D C := by
  cases args <;> intro D C h <;> cases h

/-- A constant-headed application spine is never a sort. -/
theorem foldr_app_ne_sort (args : List SExpr) (c : Name)
    (ls : List SLevel) :
    ∀ u, args.foldr (fun (a f : SExpr) => f.app a) (.const c ls) ≠
      .sort u := by
  cases args <;> intro u h <;> cases h

/-- Classified constructor spines — total or partial — have non-type
heads. -/
theorem KripkeNonTypeHead.ofCtorSpine {Γ : List SExpr} {c : Name} {k : Nat}
    {ls : List SLevel} (hcl : Params.classify c = some (.ctor k))
    (args : List SExpr) :
    KripkeNonTypeHead Γ
      (args.foldr (fun (a f : SExpr) => f.app a) (.const c ls)) := by
  intro Δ ρ W
  rw [foldr_app_lift']
  exact ⟨_, .rfl, WHNF.ctorSpine hcl _, foldr_app_ne_forallE _ _ _,
    foldr_app_ne_sort _ _ _⟩

/-- Irreducible constants have non-type heads. -/
theorem KripkeNonTypeHead.ofConstNoPat {Γ : List SExpr} {c : Name}
    {ls : List SLevel}
    (h : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      ¬Params.Pat (.const c) r) :
    KripkeNonTypeHead Γ (.const c ls) := by
  intro Δ ρ W
  refine ⟨_, .rfl, WHNF.constNoPat h, ?_, ?_⟩
  · intro D C h'
    cases h'
  · intro u h'
    cases h'

/-- Lambdas have non-type heads. -/
theorem KripkeNonTypeHead.ofLam {Γ : List SExpr} {A e : SExpr} :
    KripkeNonTypeHead Γ (.lam A e) := by
  intro Δ ρ W
  refine ⟨_, .rfl, WHNF.lam, ?_, ?_⟩
  · intro D C h'
    cases h'
  · intro u h'
    cases h'

/-- Recursor spines stuck at a neutral major have non-type heads. -/
theorem KripkeNonTypeHead.ofStuckMajor {Γ : List SExpr} {f t : SExpr}
    (hmaj : IsMajorPremise f) (hn : Neutral t) :
    KripkeNonTypeHead Γ (f.app t) := by
  intro Δ ρ W
  refine ⟨_, .rfl, KripkeWHNF.stuckMajor hmaj hn W, ?_, ?_⟩
  · intro D C h'
    cases h'
  · intro u h'
    cases h'

/-- Non-type heads absorb backward multi-step untyped expansion. -/
theorem KripkeNonTypeHead.expandS {Γ : List SExpr} {M M' : SExpr}
    (run : WHRedS Γ M M') (h : KripkeNonTypeHead Γ M') :
    KripkeNonTypeHead Γ M := by
  intro Δ ρ W
  obtain ⟨r, run', nf, h1, h2⟩ := h W
  exact ⟨r, (run.weak' W).trans run', nf, h1, h2⟩

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ### Head observations from membership

Candidate members reach only neutral or classified-constructor normal
forms, so their head obligations hold vacuously — this is the membership
half of the rung's `HeadFundamental 0` deliverable. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

variable [Params]

/-- Every candidate member reaches a normal form that is neither a Pi nor a
sort, by the same membership induction as `inCand_whReaches` with the
normal form's shape retained. -/
theorem inCand_nonTypeHead_step {H : TreeHeads} {P : CtxPred}
    (C : TreeClassified H) :
    (∀ {Γ : List SExpr} {α t : SExpr}, InCandTree H P Γ α t →
        ∃ r, WHRedS Γ t r ∧ WHNF Γ r ∧
          (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u)) ∧
      (∀ {Γ : List SExpr} {α ts : SExpr}, InCandTreeList H P Γ α ts →
        ∃ r, WHRedS Γ ts r ∧ WHNF Γ r ∧
          (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u)) := by
  have caseLeaf : ∀ {Γ' : List SExpr} {β : SExpr} (x : SExpr), P Γ' x →
      ∃ r, WHRedS Γ' (leafApp H β x) r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u) :=
    fun x _ => ⟨_, .rfl, WHNF.ctorSpine C.leaf_cl [x, _],
      foldr_app_ne_forallE [x, _] _ _, foldr_app_ne_sort [x, _] _ _⟩
  have caseNode : ∀ {Γ' : List SExpr} {β : SExpr} (ts : SExpr),
      InCandTreeList H P Γ' β ts →
      (∃ r, WHRedS Γ' ts r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u)) →
      ∃ r, WHRedS Γ' (nodeApp H β ts) r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u) :=
    fun ts _ _ => ⟨_, .rfl, WHNF.ctorSpine C.node_cl [ts, _],
      foldr_app_ne_forallE [ts, _] _ _, foldr_app_ne_sort [ts, _] _ _⟩
  have caseBranch : ∀ {Γ' : List SExpr} {β : SExpr} (f : SExpr),
      (∀ {Δ : List SExpr} {ρ : Lift}, Ctx.Lift' ρ Γ' Δ → ∀ a, P Δ a →
        InCandTreeList H P Δ (β.lift' ρ) ((f.lift' ρ).app a)) →
      (∀ {Δ : List SExpr} {ρ : Lift} (_ : Ctx.Lift' ρ Γ' Δ) (a : SExpr)
        (_ : P Δ a),
        ∃ r, WHRedS Δ ((f.lift' ρ).app a) r ∧ WHNF Δ r ∧
          (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u)) →
      ∃ r, WHRedS Γ' (branchApp H β f) r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u) :=
    fun f _ _ => ⟨_, .rfl, WHNF.ctorSpine C.branch_cl [f, _],
      foldr_app_ne_forallE [f, _] _ _, foldr_app_ne_sort [f, _] _ _⟩
  have caseNeu : ∀ {Γ' : List SExpr} (t : SExpr), Neutral t →
      ∃ r, WHRedS Γ' t r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u) :=
    fun t hn => ⟨t, .rfl, hn.whnf,
      fun _ _ => hn.notForallE, fun _ => hn.notSort⟩
  have caseExp : ∀ {Γ' : List SExpr} (t t' : SExpr), WHRed Γ' t t' →
      (∃ r, WHRedS Γ' t' r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u)) →
      ∃ r, WHRedS Γ' t r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u) := by
    intro Γ' t t' step ih
    obtain ⟨r, run, nf, h1, h2⟩ := ih
    exact ⟨r, ReflTransGen.trans (.tail .rfl step) run, nf, h1, h2⟩
  have caseNil : ∀ {Γ' : List SExpr} {β : SExpr},
      ∃ r, WHRedS Γ' (nilApp H β) r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u) :=
    ⟨_, .rfl, WHNF.ctorSpine C.nil_cl [_],
      foldr_app_ne_forallE [_] _ _, foldr_app_ne_sort [_] _ _⟩
  have caseCons : ∀ {Γ' : List SExpr} {β : SExpr} (t ts : SExpr),
      InCandTree H P Γ' β t → InCandTreeList H P Γ' β ts →
      (∃ r, WHRedS Γ' t r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u)) →
      (∃ r, WHRedS Γ' ts r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u)) →
      ∃ r, WHRedS Γ' (consApp H β t ts) r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u) :=
    fun t ts _ _ _ _ => ⟨_, .rfl, WHNF.ctorSpine C.cons_cl [ts, t, _],
      foldr_app_ne_forallE [ts, t, _] _ _, foldr_app_ne_sort [ts, t, _] _ _⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact InCandTree.rec
      (motive_1 := fun Γ' β t _ => ∃ r, WHRedS Γ' t r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u))
      (motive_2 := fun Γ' β ts _ => ∃ r, WHRedS Γ' ts r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u))
      caseLeaf caseNode caseBranch (fun t hn => caseNeu t hn)
      (fun t t' step _ ih => caseExp t t' step ih)
      caseNil caseCons (fun ts hn => caseNeu ts hn)
      (fun ts ts' step _ ih => caseExp ts ts' step ih) h
  · exact InCandTreeList.rec
      (motive_1 := fun Γ' β t _ => ∃ r, WHRedS Γ' t r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u))
      (motive_2 := fun Γ' β ts _ => ∃ r, WHRedS Γ' ts r ∧ WHNF Γ' r ∧
        (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u))
      caseLeaf caseNode caseBranch (fun t hn => caseNeu t hn)
      (fun t t' step _ ih => caseExp t t' step ih)
      caseNil caseCons (fun ts hn => caseNeu ts hn)
      (fun ts ts' step _ ih => caseExp ts ts' step ih) h

/-- `Tree`-candidate members have non-type heads: lift stability carries
membership into every future context, and the shape induction reads the
normal form there. -/
theorem InCandTree.kripkeNonTypeHead {H : TreeHeads} {P : CtxPred}
    {Γ : List SExpr} {α M : SExpr} (hP : KripkeDomain P)
    (C : TreeClassified H) (h : InCandTree H P Γ α M) :
    KripkeNonTypeHead Γ M :=
  fun W => (inCand_nonTypeHead_step C).1 (h.lift' hP W)

/-- `TreeList` side of the member non-type-head observation. -/
theorem InCandTreeList.kripkeNonTypeHead {H : TreeHeads} {P : CtxPred}
    {Γ : List SExpr} {α M : SExpr} (hP : KripkeDomain P)
    (C : TreeClassified H) (h : InCandTreeList H P Γ α M) :
    KripkeNonTypeHead Γ M :=
  fun W => (inCand_nonTypeHead_step C).2 (h.lift' hP W)

/-- The `Nat` member shape step: every member reaches a normal form that
is neither Pi nor sort. -/
theorem inCandNat_nonTypeHead_step {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} {n : SExpr}
    (hz : Params.classify zeroC = some (.ctor 0))
    (hs : Params.classify succC = some (.ctor 1))
    (h : InCandNat zeroC succC ls Γ n) :
    ∃ r, WHRedS Γ n r ∧ WHNF Γ r ∧
      (∀ D C', r ≠ .forallE D C') ∧ (∀ u, r ≠ .sort u) := by
  induction h with
  | zero =>
    exact ⟨_, .rfl, WHNF.ctorSpine hz [],
      foldr_app_ne_forallE [] _ _, foldr_app_ne_sort [] _ _⟩
  | succ n hn ih =>
    exact ⟨_, .rfl, WHNF.ctorSpine hs [n],
      foldr_app_ne_forallE [n] _ _, foldr_app_ne_sort [n] _ _⟩
  | neutral n hn =>
    exact ⟨n, .rfl, hn.whnf, fun _ _ => hn.notForallE, fun _ => hn.notSort⟩
  | expand n n' step _ ih =>
    obtain ⟨r, run, nf, h1, h2⟩ := ih
    exact ⟨r, ReflTransGen.trans (.tail .rfl step) run, nf, h1, h2⟩

/-- `Nat` calibration of the member non-type-head observation. -/
theorem InCandNat.kripkeNonTypeHead {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} {M : SExpr}
    (hz : Params.classify zeroC = some (.ctor 0))
    (hs : Params.classify succC = some (.ctor 1))
    (h : InCandNat zeroC succC ls Γ M) : KripkeNonTypeHead Γ M :=
  fun W => inCandNat_nonTypeHead_step hz hs (h.lift' W)

/-- **Members' head obligations hold vacuously**, against any partner, at
any relation and displayed type — the membership half of the
`HeadFundamental 0` slot. -/
theorem InCandTree.headLayer {H : TreeHeads} {P : CtxPred} {R : Rel}
    {Γ : List SExpr} {α M N A : SExpr} (hP : KripkeDomain P)
    (C : TreeClassified H) (h : InCandTree H P Γ α M) :
    HeadLayer R Γ M N A :=
  KripkeNonTypeHead.headLayer (h.kripkeNonTypeHead hP C)

/-- `TreeList` side of the member head layer. -/
theorem InCandTreeList.headLayer {H : TreeHeads} {P : CtxPred} {R : Rel}
    {Γ : List SExpr} {α M N A : SExpr} (hP : KripkeDomain P)
    (C : TreeClassified H) (h : InCandTreeList H P Γ α M) :
    HeadLayer R Γ M N A :=
  KripkeNonTypeHead.headLayer (h.kripkeNonTypeHead hP C)

/-- `Nat` calibration of the member head layer. -/
theorem InCandNat.headLayer {zeroC succC : Name} {ls : List SLevel}
    {R : Rel} {Γ : List SExpr} {M N A : SExpr}
    (hz : Params.classify zeroC = some (.ctor 0))
    (hs : Params.classify succC = some (.ctor 1))
    (h : InCandNat zeroC succC ls Γ M) : HeadLayer R Γ M N A :=
  KripkeNonTypeHead.headLayer (h.kripkeNonTypeHead hz hs)

/-! ### The `Fundamental.succ` slot assembly -/

/-- The per-edge head-observation classification: exactly the data from
which both orientations of the depth-0 head layer assemble.  This is the
named interface N′3's induction on strong equality discharges case by
case (`sort`/`forallEDF` via the first two sources; neutrals, constants,
lambdas, constructor spines, stuck recursors, and inductive-type members
via the third; proof-valued types via the first disjunct). -/
def HeadObservationData (Γ : List SExpr) (M N A : SExpr) : Prop :=
  IsProofType Γ A ∨ KripkePiData Γ M N ∨ KripkeSortData Γ M N ∨
    (KripkeNonTypeHead Γ M ∧ KripkeNonTypeHead Γ N)

/-- The classification produces both orientations of the depth-0 head
layer. -/
theorem HeadObservationData.headLayers {Γ : List SExpr} {M N A : SExpr}
    (h : HeadObservationData Γ M N A) :
    IsProofType Γ A ∨
      (HeadLayer Base Γ M N A ∧ HeadLayer Base Γ N M A) := by
  rcases h with h | h | h | ⟨h₁, h₂⟩
  · exact .inl h
  · exact .inr ⟨KripkePiData.headLayer h, KripkePiData.headLayerRev h⟩
  · exact .inr ⟨KripkeSortData.headLayer h,
      KripkeSortData.headLayer (KripkeSortData.symm h)⟩
  · exact .inr ⟨KripkeNonTypeHead.headLayer h₁,
      KripkeNonTypeHead.headLayer h₂⟩

/-- **The `HeadFundamental 0` slot, from the classification**: supplying
`HeadObservationData` for every strong edge fills exactly the slot
`Fundamental.succ` consumes at depth zero (`Candidate 0` is `Base`). -/
theorem headFundamental_zero_of_data
    (h : ∀ {Γ : List SExpr} {M N A : SExpr},
      IsDefEqStrong Γ M N A → HeadObservationData Γ M N A) :
    HeadFundamental 0 :=
  fun edge => (h edge).headLayers

/-! ### Nonvacuity witnesses -/

/-- Sorts inhabit the sort-observation source. -/
theorem kripkeSortData_sort {Γ : List SExpr} (u : SLevel) :
    KripkeSortData Γ (.sort u) (.sort u) :=
  fun _ => ⟨u, .rfl, .rfl⟩

/-- Sort-formed Pis inhabit the Pi-observation source, with `Base.sort`
components. -/
theorem kripkePiData_sorts {Γ : List SExpr} (u v : SLevel) :
    KripkePiData Γ (.forallE (.sort u) (.sort v))
      (.forallE (.sort u) (.sort v)) :=
  fun _ => ⟨.sort u, .sort v, .sort u, .sort v, u.succ, v.succ,
    .rfl, .rfl, Base.sort, Base.sort⟩

/-- The classification is inhabited at the sort edge. -/
theorem headObservationData_sort {Γ : List SExpr} (u : SLevel) :
    HeadObservationData Γ (.sort u) (.sort u) (.sort u.succ) :=
  .inr (.inr (.inl (kripkeSortData_sort u)))

/-- The classification is inhabited at a Pi edge. -/
theorem headObservationData_pi {Γ : List SExpr} (u v : SLevel) :
    HeadObservationData Γ (.forallE (.sort u) (.sort v))
      (.forallE (.sort u) (.sort v)) (.sort (.imax u.succ v.succ)) :=
  .inr (.inl (kripkePiData_sorts u v))

/-- The classification is inhabited at a neutral edge. -/
theorem headObservationData_neutral {Γ : List SExpr} {M N A : SExpr}
    (hn : Neutral M) (hn' : Neutral N) :
    HeadObservationData Γ M N A :=
  .inr (.inr (.inr ⟨KripkeNonTypeHead.ofNeutral hn,
    KripkeNonTypeHead.ofNeutral hn'⟩))

/-! ### The production membership instances -/

omit [Params] in
/-- Member head observations at the production D2 instance: for members of
the block candidates over the real environment, the `HeadFundamental 0`
slot's head-layer content holds vacuously against any partner. -/
theorem d2InCandTree_headLayer (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ (l : SLevel) {R : Rel} {P : CtxPred} {Γ : List SExpr}
      {α M N A : SExpr},
      KripkeDomain P →
      InCandTree (d2TreeHeads univs l) P Γ α M →
      HeadLayer R Γ M N A := by
  letI : Params := ParamsD2.d2Params univs
  intro l R P Γ α M N A hP hM
  exact hM.headLayer hP (d2TreeHeads_classified univs l)

omit [Params] in
/-- `TreeList` side of the production D2 member head observations. -/
theorem d2InCandTreeList_headLayer (univs : Nat) :
    letI : Params := ParamsD2.d2Params univs
    ∀ (l : SLevel) {R : Rel} {P : CtxPred} {Γ : List SExpr}
      {α M N A : SExpr},
      KripkeDomain P →
      InCandTreeList (d2TreeHeads univs l) P Γ α M →
      HeadLayer R Γ M N A := by
  letI : Params := ParamsD2.d2Params univs
  intro l R P Γ α M N A hP hM
  exact hM.headLayer hP (d2TreeHeads_classified univs l)

omit [Params] in
/-- Member head observations at the production D0 instance. -/
theorem d0InCandNat_headLayer (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    ∀ {ls : List SLevel} {R : Rel} {Γ : List SExpr} {M N A : SExpr},
      InCandNat ``Nat.zero ``Nat.succ ls Γ M →
      HeadLayer R Γ M N A := by
  letI : Params := ParamsD0.d0Params univs
  intro ls R Γ M N A hM
  exact hM.headLayer rfl rfl

end IndCand
end Reducibility
end SExpr
end Lean4Lean

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

variable [Params]

/-- Every landed one-step rule pack is a multi-step rule pack: the
multi-step interface strictly subsumes the N′0 mock shape (its nonvacuity
transfer — probe Z16's mock registry inhabits `TreeRules`). -/
def TreeRulesS.ofRules {H : TreeHeads} {Γ : List SExpr} {α : SExpr}
    (R : TreeRules H Γ α) : TreeRulesS H Γ α where
  recT := R.recT
  recL := R.recL
  minorLf := R.minorLf
  minorNd := R.minorNd
  minorBr := R.minorBr
  minorNl := R.minorNl
  minorCs := R.minorCs
  recT_major := R.recT_major
  recL_major := R.recL_major
  stuckT := R.stuckT
  stuckL := R.stuckL
  leafStep := fun W x => .tail .rfl (R.leafStep W x)
  nodeStep := fun W ts => .tail .rfl (R.nodeStep W ts)
  branchStep := fun W f => .tail .rfl (R.branchStep W f)
  nilStep := fun W => .tail .rfl (R.nilStep W)
  consStep := fun W t ts => .tail .rfl (R.consStep W t ts)

/-- `Nat` side of the one-step-to-multi-step subsumption. -/
def NatRulesS.ofRules {zeroC succC : Name} {ls : List SLevel}
    {Γ : List SExpr} (R : NatRules zeroC succC ls Γ) :
    NatRulesS zeroC succC ls Γ where
  recN := R.recN
  minorZ := R.minorZ
  minorS := R.minorS
  recN_major := R.recN_major
  stuckN := R.stuckN
  zeroStep := fun W => .tail .rfl (R.zeroStep W)
  succStep := fun W n => .tail .rfl (R.succStep W n)

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ## N′2 axiom pins

The generic N′2 layer (multi-step engine, tower collapse, δ-descent
skeleton, depth-0 head lemma family, membership head observations) stays
inside the accepted Experimental baseline: subsets of
`[propext, Classical.choice, Quot.sound]`.  The seven registered
tower-body pins are kernel `decide` computations — they contribute **no**
new `native_decide` observations.  The nine per-rule runs and the
instance discharges inherit, verbatim, the closures of the landed
machinery they fire: the N′1 step theorems' recorded `sorryAx` (through
`SExpr.typeUniq` → `VEnv.IsDefEq.uniq`, the 16C′ leaf) and the D-ladder
fixtures' documented `native_decide` observations — contributed by those
modules, not by this rung's reasoning. -/

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.ResultCand.expandS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ResultCand.expandS

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.TreeRulesS.ofSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeRulesS.ofSteps

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.TreeRulesS.fundamental_iota' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TreeRulesS.fundamental_iota

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.TreeRulesS.recT_whResult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TreeRulesS.recT_whResult

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.NatRulesS.fundamental_iota' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NatRulesS.fundamental_iota

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.lamBodyN_eq_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms lamBodyN_eq_some

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.whRedS_lamTower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms whRedS_lamTower

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.iotaSpineCaptureValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iotaSpineCaptureValues

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.natZeroBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natZeroBody

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.natSuccBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natSuccBody

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.treeLeafBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeLeafBody

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.treeNodeBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeNodeBody

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.treeBranchBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeBranchBody

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.treeNilBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeNilBody

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.treeConsBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeConsBody

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0ZeroIotaRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0ZeroIotaRun

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0SuccIotaRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0SuccIotaRun

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2LeafIotaRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2LeafIotaRun

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2NodeIotaRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2NodeIotaRun

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2BranchIotaRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2BranchIotaRun

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2NilIotaRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2NilIotaRun

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2ConsIotaRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2ConsIotaRun

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2NatZeroIotaRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2NatZeroIotaRun

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2NatSuccIotaRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2NatSuccIotaRun

/-- info: 'Lean4Lean.SExpr.WHNF.constNoPat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.SExpr.WHNF.constNoPat

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.Base.const_irreducible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Base.const_irreducible

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.Base.ctorSpines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Base.ctorSpines

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.Base.stuckMajors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Base.stuckMajors

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.Candidate.ofDeltaValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Candidate.ofDeltaValue

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.constsReducibleBelow_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms constsReducibleBelow_all

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.candidate_const_of_deltaStep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms candidate_const_of_deltaStep

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.ConstFundamental.of_deltaStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ConstFundamental.of_deltaStep

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.DeltaStepObligation.of_fundamental' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DeltaStepObligation.of_fundamental

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0ConstPat_name' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0ConstPat_name

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2ConstPat_names' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2ConstPat_names

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0DeltaDescent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0DeltaDescent

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d1DeltaChain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_natZero._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d1DeltaChain

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2DeltaChain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2DeltaChain

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2DefWHRed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2DefWHRed

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0DefBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0DefBase

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2DefBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2DefBase

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0HeadsBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0HeadsBase

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2HeadsBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2HeadsBase

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2PartialCtorBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2PartialCtorBase

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.KripkePiData.headLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KripkePiData.headLayer

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.KripkePiData.headLayerRev' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms KripkePiData.headLayerRev

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.KripkeSortData.headLayer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms KripkeSortData.headLayer

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.KripkeNonTypeHead.headLayer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms KripkeNonTypeHead.headLayer

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.inCand_nonTypeHead_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inCand_nonTypeHead_step

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandTree.headLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InCandTree.headLayer

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.InCandNat.headLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms InCandNat.headLayer

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.HeadObservationData.headLayers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms HeadObservationData.headLayers

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.headFundamental_zero_of_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms headFundamental_zero_of_data

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.headObservationData_sort' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms headObservationData_sort

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.headObservationData_pi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms headObservationData_pi

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.headObservationData_neutral' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms headObservationData_neutral

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2InCandTree_headLayer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2InCandTree_headLayer

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0InCandNat_headLayer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0InCandNat_headLayer

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.TreeRulesS.ofRules' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TreeRulesS.ofRules

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.NatRulesS.ofRules' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NatRulesS.ofRules

/-! ## N′3 session 1 — nonvacuity of the irreducible-constant input

The depth-0 restriction of the master file's `IrreducibleConstCandidates`
is exactly this rung's `Base.const_irreducible`: a pattern-less constant
is Kripke-WHNF, so its base content fires at any strong self-edge.  The
successor observation layers — application-spine normalization at
pattern-less heads, including iota firing under recursor heads — remain
the named input, discharged per instance by the membership layer. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

variable [Params]

/-- The depth-0 restriction of `IrreducibleConstCandidates` holds
outright. -/
theorem irreducibleConstCandidates_zero {Γ : List SExpr} {c : Name}
    {ls : List SLevel} {A : SExpr}
    (h : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      ¬Params.Pat (.const c) r)
    (edge : IsDefEqStrong Γ (.const c ls) (.const c ls) A) :
    Candidate 0 Γ (.const c ls) (.const c ls) A :=
  Base.const_irreducible h edge

end IndCand
end Reducibility
end SExpr
end Lean4Lean

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.irreducibleConstCandidates_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms irreducibleConstCandidates_zero

/-! ## N′3 session 2 — the instance staging chains

The master file's assembly (`SubstFundamental.total`) is generically
conditional on exactly four named inputs, and its staging ladder
(`Fundamental.all`) discharges all four from two instance-shaped
obligations: typed weak-head normalization (`TypedWHNormalization`, N2's
seam) and the per-depth head-observation slot (`HeadFundamental`).  The
chains below pin that discharge at the two production environments over
their real semantic bridges (`d0Semantic` unconditionally, `d2Semantic`
on the recorded block step).  Neither obligation is closed this session —
the membership layer covers candidate members
(`InCand*.kripkeNormalizes`, `*_headLayer`) but not yet arbitrary typed
terms — so the chains record exactly what N′4 must supply per instance,
and the depth-0 route additionally factors the head slot through the
landed `HeadObservationData` classification. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

/-- The Pi-inversion leaf from the two depth-0 obligations alone, with the
head slot factored through the landed per-edge classification. -/
theorem LRS.PiPathInv.of_normalization_data [Params] [Params.Semantic]
    (normalization : TypedWHNormalization)
    (data : ∀ {Γ : List SExpr} {M N A : SExpr},
      IsDefEqStrong Γ M N A → HeadObservationData Γ M N A) :
    LRS.PiPathInv :=
  LRS.PiPathInv.of_zero_data normalization
    (headFundamental_zero_of_data data)

/-- **The d0 staging chain**: at the smallest production environment, over
its unconditional semantic bridge, the two recorded N′4 obligations close
the full ladder, all four named inputs of the generic assembly, the total
substitutional interpretation, and the Pi-inversion leaf. -/
theorem d0StagingChain (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    letI : Params.Semantic := ParamsD0.d0Semantic univs
    TypedWHNormalization →
    (∀ depth, HeadFundamental depth) →
    (∀ depth, Fundamental depth) ∧
      CandidateUniformity ∧ CandidateTypeTransport ∧
      IrreducibleConstCandidates ∧ ProofCandidateMerge ∧
      (∀ {Gamma : List SExpr} {M N A : SExpr}
        (H : IsDefEqStrong Gamma M N A), SubstFundamental H) ∧
      LRS.PiPathInv := by
  letI : Params := ParamsD0.d0Params univs
  letI : Params.Semantic := ParamsD0.d0Semantic univs
  intro normalization heads
  have fund := Fundamental.all normalization heads
  exact ⟨fund, CandidateUniformity.of_fundamental fund,
    CandidateTypeTransport.of_fundamental fund,
    IrreducibleConstCandidates.of_fundamental fund,
    ProofCandidateMerge.of_fundamental fund,
    fun H => SubstFundamental.of_ladder normalization heads H,
    LRS.PiPathInv.of_candidateFundamental (fund 1)⟩

/-- **The d2 staging chain**: the full-inventory twin over the conditional
D2 bridge, inheriting exactly the recorded block-step premise. -/
theorem d2StagingChain (univs : Nat) (h : ParamsD2.D2BlockStep univs) :
    letI : Params := ParamsD2.d2Params univs
    letI : Params.Semantic := ParamsD2.d2Semantic univs h
    TypedWHNormalization →
    (∀ depth, HeadFundamental depth) →
    (∀ depth, Fundamental depth) ∧
      CandidateUniformity ∧ CandidateTypeTransport ∧
      IrreducibleConstCandidates ∧ ProofCandidateMerge ∧
      (∀ {Gamma : List SExpr} {M N A : SExpr}
        (H : IsDefEqStrong Gamma M N A), SubstFundamental H) ∧
      LRS.PiPathInv := by
  letI : Params := ParamsD2.d2Params univs
  letI : Params.Semantic := ParamsD2.d2Semantic univs h
  intro normalization heads
  have fund := Fundamental.all normalization heads
  exact ⟨fund, CandidateUniformity.of_fundamental fund,
    CandidateTypeTransport.of_fundamental fund,
    IrreducibleConstCandidates.of_fundamental fund,
    ProofCandidateMerge.of_fundamental fund,
    fun H => SubstFundamental.of_ladder normalization heads H,
    LRS.PiPathInv.of_candidateFundamental (fund 1)⟩

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ## N′3 session-2 instance pins

The generic seam content stays inside the accepted baseline (see the
master file's pins).  The two production chains additionally inherit,
verbatim, their semantic bridges' documented fixture baselines: the
D-ladder `native_decide` observations and the recorded `sorryAx`
through `SExpr.typeUniq` → `VEnv.IsDefEq.uniq` (the 16C′ leaf) carried
by `d0Semantic`/`d2Semantic` — no new axioms and no new `sorry` from
this rung. -/

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.LRS.PiPathInv.of_normalization_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LRS.PiPathInv.of_normalization_data

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0StagingChain' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natClassify_d0Def_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0StagingChain

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2StagingChain' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natClassify_d0Def_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.natRule_rhs_ne_d1MutA._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD1.natRule_rhs_ne_d1MutA._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD1.natRule_rhs_ne_d1MutB._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD1.natRule_rhs_ne_d1MutB._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD2.d1Classify_tree._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeBranch._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeLeaf._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeList._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeListCons._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeListNil._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeListRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeNode._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeBranch_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeLeaf_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeListCons_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeListNil_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeListRec_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeNode_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeRec_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2StagingChain


/-! ## N′4 — the leaf's residual, per instance

Probe N4 (`plans/probes/probeN4-knot.lean`) narrowed the master file's
leaf claim: `LRS.PiPathInv` consumes neither `TypedWHNormalization` nor
the full `HeadFundamental 0` slot — only the forward depth-0 head
observation at sort-typed edges (`SortEdgeHeads`).  At the classification
interface this is the sort-edge restriction of `HeadObservationData`,
recorded below as `SortEdgeData`, and the two production chains now carry
the leaf conditional on that single datum.

The residual is honest, not free: `SortEdgeData.typeWHResult` shows the
restricted classification already implies a Kripke weak-head normal form
for every well-typed type, i.e. type-level weak-head normalization
strength.  The membership layer's sources (members, neutrals, constants,
lambdas, constructor spines, stuck recursors) cover every classification
case except `.appDF`/dynamic β at type level, where the contractum of a
type-level β-redex has no premise in the induction — the same knot,
confined to sort-typed edges.  Probe N4's Cut-2 refutation
(`stratifiedBetaBound_false`) closes the stratified-typing route to that
case. -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

open Lean4Lean.MutualInductiveFixtures

variable [Params]

/-- **The leaf's per-instance residual**: the head classification at
sort-typed strong edges.  Nonvacuity at concrete edges is the landed
witness suite (`headObservationData_sort`, `headObservationData_pi`,
`headObservationData_neutral`). -/
def SortEdgeData : Prop :=
  ∀ {Γ : List SExpr} {A B : SExpr} {u : SLevel},
    IsDefEqStrong Γ A B (.sort u) → HeadObservationData Γ A B (.sort u)

/-- The residual asks strictly less than the full classification recorded
by `LRS.PiPathInv.of_normalization_data`. -/
theorem SortEdgeData.of_full
    (data : ∀ {Γ : List SExpr} {M N A : SExpr},
      IsDefEqStrong Γ M N A → HeadObservationData Γ M N A) :
    SortEdgeData :=
  fun edge => data edge

/-- The classification restricted to sort edges produces the minimized
leaf input. -/
theorem SortEdgeData.sortEdgeHeads (data : SortEdgeData) :
    SortEdgeHeads :=
  fun edge =>
    ((data edge).headLayers.resolve_left (IsProofType.sort_false _)).1

/-- The leaf from the residual alone — no normalization obligation. -/
theorem LRS.PiPathInv.of_sort_edge_data [Params.Semantic]
    (data : SortEdgeData) : LRS.PiPathInv :=
  LRS.PiPathInv.of_sort_edge_heads data.sortEdgeHeads

/-- **Strength characterization**: the sort-edge classification already
implies Kripke weak-head normalization of every well-typed type — each
disjunct hands over a normal form, and the proof-type disjunct is refuted
at a sort.  This is why the residual is not dischargeable from the
depth-0 theorems plus the membership machinery, which normalize members,
not arbitrary typed types. -/
theorem SortEdgeData.typeWHResult (data : SortEdgeData)
    {Γ : List SExpr} {A : SExpr} {u : SLevel}
    (h : IsDefEqStrong Γ A A (.sort u)) : WHResult Γ A (.sort u) := by
  rcases data h with hproof | hpi | hsort | ⟨hM, _⟩
  · exact absurd hproof (IsProofType.sort_false u)
  · obtain ⟨D, C, D', C', u', v', runM, _, _, _⟩ := hpi Ctx.Lift'.refl
    exact ⟨.forallE D C, by simpa using runM, WHNF.forallE⟩
  · obtain ⟨w, runM, _⟩ := hsort Ctx.Lift'.refl
    exact ⟨.sort w, by simpa using runM, WHNF.sort⟩
  · obtain ⟨r, run, nf, _, _⟩ := hM Ctx.Lift'.refl
    exact ⟨r, by simpa using run, nf⟩

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ### The production instances -/

namespace Lean4Lean
namespace SExpr
namespace Reducibility
namespace IndCand

/-- The d0 leaf from the sort-edge residual alone. -/
theorem d0SortEdgeLeaf (univs : Nat) :
    letI : Params := ParamsD0.d0Params univs
    letI : Params.Semantic := ParamsD0.d0Semantic univs
    SortEdgeData → LRS.PiPathInv := by
  letI : Params := ParamsD0.d0Params univs
  letI : Params.Semantic := ParamsD0.d0Semantic univs
  intro data
  exact LRS.PiPathInv.of_sort_edge_data data

/-- The d2 twin over the conditional bridge, inheriting exactly the
recorded block-step premise. -/
theorem d2SortEdgeLeaf (univs : Nat) (h : ParamsD2.D2BlockStep univs) :
    letI : Params := ParamsD2.d2Params univs
    letI : Params.Semantic := ParamsD2.d2Semantic univs h
    SortEdgeData → LRS.PiPathInv := by
  letI : Params := ParamsD2.d2Params univs
  letI : Params.Semantic := ParamsD2.d2Semantic univs h
  intro data
  exact LRS.PiPathInv.of_sort_edge_data data

end IndCand
end Reducibility
end SExpr
end Lean4Lean

/-! ## N′4 pins

The generic residual suite stays inside the accepted baseline; the two
instance leaves inherit, verbatim, their semantic bridges' documented
fixture baselines (D-ladder `native_decide` observations and the recorded
`sorryAx` through `SExpr.typeUniq` carried by `d0Semantic`/`d2Semantic`)
— no new axioms and no new `sorry` from this rung. -/

open Lean4Lean.SExpr.Reducibility.IndCand in
/-- info: 'Lean4Lean.SExpr.Reducibility.IndCand.SortEdgeData.of_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SortEdgeData.of_full

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.SortEdgeData.sortEdgeHeads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SortEdgeData.sortEdgeHeads

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.LRS.PiPathInv.of_sort_edge_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LRS.PiPathInv.of_sort_edge_data

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.SortEdgeData.typeWHResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SortEdgeData.typeWHResult

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d0SortEdgeLeaf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natClassify_d0Def_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0SortEdgeLeaf

open Lean4Lean.SExpr.Reducibility.IndCand in
/--
info: 'Lean4Lean.SExpr.Reducibility.IndCand.d2SortEdgeLeaf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 Lean4Lean.SExpr.ParamsD0.d0Def_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natClassify_d0Def_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD0.natRule_rhs_ne_d0Def._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroCtorName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleRecName._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD0.probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD1.natRule_rhs_ne_d1MutA._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD1.natRule_rhs_ne_d1MutA._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD1.natRule_rhs_ne_d1MutB._native.native_decide.ax_1_2,
 Lean4Lean.SExpr.ParamsD1.natRule_rhs_ne_d1MutB._native.native_decide.ax_1_3,
 Lean4Lean.SExpr.ParamsD2.d1Classify_tree._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeBranch._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeLeaf._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeList._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeListCons._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeListNil._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeListRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeNode._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d1Classify_treeRec._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.d2Env_isSome._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeBranch_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeLeaf_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeListCons_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeListNil_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeListRec_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeList_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeNode_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.treeRec_fresh._native.native_decide.ax_1_1,
 Lean4Lean.SExpr.ParamsD2.tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2SortEdgeLeaf
