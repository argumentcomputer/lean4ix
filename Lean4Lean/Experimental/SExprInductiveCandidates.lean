import Lean4Lean.Experimental.SExprNormalizationFailure
import Lean4Lean.Experimental.SExprParamsD2

/-!
# L4L-16N′0: mutual-inductive reducibility candidates

The candidate architecture of the L4L-16N′ route, landed from probe Z16
(`plans/probes/probeZ16-indcand.lean`).  The candidate at an inductive type
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
