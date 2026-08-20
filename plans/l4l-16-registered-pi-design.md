# L4L-16 — the registered-endpoint narrowing of the 16C′ leaf, measured

**Date:** 2026-08-15.  **Probe:** `plans/probes/probeU-regpi.lean` (green:
`lake env lean` exit 0, zero sorries, all 19 `#print axioms` checks land on
`[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`).  The probe imports `Lean4Lean.Experimental.ShapeLogRel` **only**,
so non-circularity with respect to adequacy is structural, as in probeS/probeT:
`LR.AdequacyAt`, `LR.ContextualAdequacyAt(Depth)` and every `*.of_adequacy*`
are not in its import closure at all.  No banned input is touched (no
`ParRedSDefeq`/`CRComplete`/`PiStandard`/`PiEdgeInv`/`SubjectRedS`/`PiEdgeObs`,
no `WHRedS.defeq`, no `TypeDefEqPath.collapse`/`RawTypeUniq`, no Theory
`ParRed.defeq`/`StRed.triangle`; the axiom closures certify this).

**Question.**  probeT closed the *stratification* axis of the 16C′ leaf
(`LR.iotaWitnessStep`, ADQ:8553, sorry at :8583) by machine refutation.  Its
recommendation was the remaining unmeasured axis: the leaf's residual
`LRS.PiPathInv` (SLR:11417) inverts Pi along a `TypeDefEqPath` with **both**
endpoints arbitrary, but the leaf's *live* demands may be narrower — one
endpoint pinned to a **registered telescope**, i.e. certificate data
(`SExpr.mkInst ls ci.type` and the `CtorBundle.rhs` telescope
`Ts.foldr .forallE …` it is definitionally equal to, SExpr:1899, 1977-1982).
This is the sanctioned voucher source: "Whatever depth bound a leaf producer
needs must come from its own registered-rule certificates" (ADQ:8514-8515),
and the roadmap flagged this residual's subject as registered — "the first
residual a generation-side argument can attack" (roadmap.md:708-715).

---

## Verdict in one line

**The narrowing is real, non-vacuous, and closes exactly one of the leaf's two
`PiPathInv` sites — the whole *interior* of the constructor chain, which is the
unbounded one — and provably does **not** close the other (`rootRed`, the two
root callbacks), for two independent measured reasons.  The narrowed
proposition itself is *not* easier to prove: the registered class is not closed
under a single path edge, so the decoration dies at the first `trans` of the
path exactly as the depth decoration did (probeT's `transMiddleCertAt_false`).
Net: the registered axis moves the leaf's residual from "Pi inversion at
arbitrary paths, everywhere" to "Pi inversion at arbitrary paths, at two named
root callbacks" — a genuine narrowing of *scope* with no reduction of
*content*.**

---

## (i) The narrowed proposition

```lean
inductive RegTele : Nat → SExpr → Prop where          -- probeU Part 1
  | base : RegTele 0 (args.foldr (fun a f => f.app a) (.const I ls))
  | pi   : RegTele k B → RegTele (k + 1) (.forallE A B)

def LRS.PiPathInvReg : Prop :=                        -- probeU Part 2
  ∀ {Γ k A B A' B' s}, Ctx.WF Γ → RegTele (k + 1) (.forallE A B) →
    TypeDefEqPath Γ (.forallE A B) (.forallE A' B') s →
    ∃ u v, TypeDefEqPath Γ A A' u ∧ TypeDefEqPath (A :: Γ) B B' v
```

`RegTele k T` is *exactly* the syntactic shape of `CtorBundle.rhs` (SExpr:1899)
with the tower length exposed: a `k`-ary Pi tower over a constant-headed
application spine.  `CtorBundle.rhs_regTele` (probeU) certifies the connection
to the real certificate; `LRS.PiPathInvReg.of_piPathInv` certifies that nothing
has been strengthened.  The Prop is `LRS.PiPathInv` plus **one** side condition
— no depth index, no universe alignment, no collapse — so it is exactly the
narrowing the brief asked for and nothing else.

Three facts about the class, all machine-checked, that make it usable:

* **closed under substitution** (`RegTele.subst`), hence under the `inst` a
  spine walk performs at every layer (`RegTele.inst`) — `SExpr.subst` is
  structural on `.forallE`/`.app` and fixes `.const` (SExpr:520-526), so the
  tower length, head constant and levels all survive;
* **invertible** (`RegTele.pi_inv`): a positive member *is* a syntactic Pi
  whose codomain is again in the class one arity lower;
* **the base is load-bearing**: the class excludes Pis whose iterated codomain
  is a sort (`RegTele.not_forallE_sort`), a `.lam`-headed redex
  (`RegTele.zero_not_app_lam`), etc.  Dropping the base condition (a bare
  "k-ary Pi tower") would make the side condition **vacuous at the last
  layer** — `PiTower 1 (.forallE A B)` is `True` — i.e. would silently restate
  the full leaf.  The narrowing is precisely a *data-telescope* restriction.

---

## (ii) The kill-shot check — run first, outcome NEGATIVE (the narrowing survives)

The cheapest way for this axis to be worthless: if the
`LRS.PiPathInv → LRS.ParRedSDefeq` direction of
`LRS.piPathInv_iff_parRedSDefeq` (SLR:16210) needed only the registered class,
then `PiPathInvReg` would inherit the ladder's interderivability with the leaf
and be no cheaper.

It does not.  `ParRed.defeq_of_piPathInv` (SLR:16128) charges `piInv` **exactly
once**, at SLR:16154, on the path returned by `IsDefEqStrong.lam_inv'`, whose
left endpoint is the *abstraction's own declared Pi* — the annotation the term
carries — and whose right endpoint is the application's Pi.  `probeU`'s
`betaSite_outside_regTele` realizes that site verbatim from the banked witness
`betaSort_domain_unconstrained` (SLR:16302), in the **empty context with no
environment assumptions**, and proves **both** endpoints outside the class at
**every** arity (their codomain is a sort; a registered telescope bottoms out in
a constant-headed spine).

So the registered narrowing is a genuinely different question from the one
`piPathInv_iff_parRedSDefeq` closed, and it is not vacuous as an escape.  (It is
also not refutable: `PiPathInvReg` is *implied* by the leaf, so unlike every
Prop probeT closed, the discipline that applies to it is non-vacuity, not
falsity — see the `U-vac` row below.)

---

## (iii) The live sites, measured

The complete inventory of `piInv` *uses* in the tree (grep `piInv hΓ`), split
by whether they are on the leaf path:

| # | site | file:line | on leaf path? | registered? |
|---|------|-----------|---------------|-------------|
| 1 | `SpineWF.result_path`, one per spine layer | SLR:11440 | **yes** (`ctorRetype`) | **YES** — closed, see (iv) |
| 2 | `WHRed.defeq_of_piPathInv`, `beta` case | SLR:11530 | **yes** (`rootRed`) | **no** — measured |
| 3 | `WHRed.defeq_of_piPathInv`, `extra` case (via `constSpineTypeUniqPath`) | SLR:11542 | **yes** (`rootRed`) | **no** — measured |
| 4 | `LRS.PatStep.of_piPathInv` | SLR:16093 | no (CR ladder) | no (same as 3) |
| 5 | `ParRed.defeq_of_piPathInv`, `beta` case | SLR:16154 | no (CR ladder) | no (the kill-shot) |

The leaf path is: leaf `LR.iotaWitnessStep` (ADQ:8553) → `LR.CoherentIotaLeafStep`
(ADQ:7323, whose status note ADQ:7309-7322 names the fold) →
`LRS.CtorDefEq.foldRaw_of_majorChainAnchorStep` (ADQ:1191) →
`LR.MajorChainAnchorStep` (ADQ:1105), whose two fields are `ctorRetype`
(:1106-1111) and `rootRed` (:1112-1115).  Both are live; `of_piPathInv`
(ADQ:1157) discharges them from one general leaf.

**Site (a) — `ctorRetype`, the chain interior.**  `LRS.CtorRetype` ⟸
`LRS.CtorExact.retype_of_ctorSpineTypeUniqPath` (SLR:11564) ⟸
`LRS.CtorSpineTypeUniqPath` (SLR:11196).  Its subject is a *classified
constructor* spine with its head typing and `SpineWF` certificate retained.
**Both** endpoints of the demanded path are types of the *same* constant-headed
spine, so both head types are pinned to the environment's own
`SExpr.mkInst ls ci.type` by `HasTypeStratifiedS.to_core_path` (SLR:11255) —
this is what `LRS.constTypeUniqPath` (SLR:11389) already exploits — and
`Params.Semantic.ctor` (SExpr:1977) turns that into the syntactic telescope
`F.rhs ls` of the constructor's own arity (`CtorBundle.hlen`, SExpr:1895).
So a registered endpoint is available *by construction* at this site.  This is
usage-unbounded: once per native link of the chain (×3 inside
`retype_of_ctorSpineTypeUniqPath`) and once per spine layer inside each.

**Site (b) — `rootRed`, the two root callbacks.**  `LRS.CtorView Γ₀ M X`
(SLR:11009) constrains only the *target* of the weak-head reduction; the root
`M` is the observation's own subject, arbitrary.  Two independent measurements,
both machine-checked:

* **(b-i) the `beta` case is unconstrained.**  `rootRed_meets_beta` (probeU):
  for every classified nullary constructor, `(fun _ : T => c) a` has a
  constructor view through a β step, with **no typing and no environment
  assumptions beyond the classification** — so the β case of
  `WHRed.defeq_of_piPathInv` is live at `rootRed`, at an abstraction domain
  `T` the view says nothing about.  Combined with `betaSite_outside_regTele`
  (§(ii)), the Pi endpoints there are outside the class.  This is the same
  obstruction the *sort* narrowing hit (roadmap.md:799-803), and for the same
  structural reason: sort-typedness constrains the result, registration
  constrains the head — neither constrains an abstraction's domain annotation.
* **(b-ii) the `extra` case has no telescope to anchor on.**
  `extraSite_head_not_isCtor` (probeU): every redex a `Pattern.Action`
  contracts is a spine over a constant that is **provably not a constructor**
  (pattern heads are `symb`-classified at top level: `Pattern.WF` SExpr:20 +
  `Params.pat_wf` SExpr:31, via `Pattern.MatchesS.head_spine` SExpr:899 and the
  new `Arity.head_wf`).  `Params.Semantic.ctor` is the **only** field of the
  semantic bridge that produces a telescope and it is gated on
  `CtorBundle.IsCtor` (`symb_not_isCtor`).

**Semantic-bridge field inventory** (asked for explicitly).  `Params.Semantic`
(SExpr:1964-2050) has exactly six fields: `structureEta`, `ctor`, `defn`,
`iotaRule`, `iotaSite`, `registered`.  **The lemma-(C)-style coherence field
does not exist** — there is no field asserting that the stripped lhs head of a
registered equation classifies as a symbol, and no field giving a telescope
normal form for a `symb`-classified constant.  `defn` covers zero-arity
patterns only, and supplies a *value*, not a type telescope.

---

## (iv) The result: site (a) closes from the narrowed Prop alone

`LRS.CtorSpineTypeUniqPath.of_piPathInvReg` (probeU Part 3), and with it
`LRS.CtorAnchorDisciplineAt.of_piPathInvReg` and
`LRS.CtorChain.foldRaw_of_piPathInvReg` — the whole interior of the
constructor chain — is now discharged from `LRS.PiPathInvReg`, where before it
spent the general leaf (`LRS.CtorSpineTypeUniqPath.of_piPathInv`, SLR:11478).

The proof is a **restructuring**, not a trick, and the restructuring is the
transferable content of this measurement:

* `SpineWF.result_path` (SLR:11430) inducts on *one of the two spine
  derivations*.  Its `conv` case moves that spine's head type off the
  registered telescope at the first opportunity, so the left endpoint of every
  layer inversion is an arbitrary Pi.  That is why the current proof needs the
  general leaf.
* `regSpine_result_uniq` (probeU) never inducts on a spine derivation.  It
  inducts on the **argument list**, keeping the registered telescope as a fixed
  anchor and approaching *both* spines from it with `SpineWF.cons_path`
  (SLR:11322) / `nil_path` (SLR:11305).  Every layer inversion then has the
  telescope's own tail on the left, registered by construction, because the
  class is closed under the `inst` each layer performs.  The arity side
  condition is discharged by the bundle's own `hlen`.

Consequences worth recording:

* the narrowing removes the depth question from this site entirely — neither
  the Prop nor the walk mentions a stratification index, consistent with
  probeT's finding that the depth axis has nothing to offer;
* nothing here consumes a classification of the *other* spine, a universe
  alignment, or a path collapse;
* the leaf's remaining general-`PiPathInv` demand drops from
  "chain length × spine length" uses to **exactly two** — the root callbacks
  (SLR:11755-11758 already names them "the only remaining raw inputs").

---

## (v) The proof attempt for `LRS.PiPathInvReg`, and its obstruction

Two angles were tried (two-strikes discipline), and both fail at the same
place.

**Angle 1 — walk the path from the registered end.**  The only path-walking
argument in the tree is `LRS.PiPathInv.of_piEdgeObs` (SLR:15281): it maintains
the invariant "the current vertex weak-head reduces to a Pi" at *every* vertex,
and consumes `LRS.PiEdgeObs` at each edge.  **`regClass_not_edge_closed`
(probeU) refutes the registered analogue of that invariant**: for *any* type
`T` in *any* context, with no environment assumptions, the identity β-redex
`(fun _ : Sort u => #0) T` is `IsDefEq`-equal to `T` at its own universe and is
outside the class at every arity.  So the walk loses its side condition at the
first edge, and the input it would need at the second is the general
`LRS.PiEdgeObs` again.

**Angle 1′ — induct on the path structure instead.**
`regPath_interior_unregistered` (probeU) sharpens this to the induction that
would have to work: `TypeDefEqPath` is generated by `single` and `trans`, and
`trans`'s middle vertex is existential.  Every registered Pi sits on a path
whose *interior* is outside the class, so a structural induction hands its
inductive hypothesis a non-registered left endpoint at the first `trans` split,
whichever endpoint it starts from.  **This is the registered-axis analogue of
probeT's `LRS.transMiddleCertAt_false`**: both axes decorate the *endpoints* of
a `TypeDefEqPath`, and both are defeated by the same structural fact — the
relation's `trans` retains nothing about the middle.

**Angle 2 — a registered single-edge inversion.**  Blocked upstream, by
inspection of what a single edge costs: the general single-edge Prop
`LRS.PiEdgeInv` has one producer, `LRS.PiEdgeInv.of_crLadder` (SLR:15506),
which spends `LRS.CRComplete` + `LRS.ParRedSDefeq`; registration decorates the
endpoint, not the edge's derivation, so it removes no case from that proof.
The registered analogue of the head-transport factor would be a
`reduce_const`-shaped fact, and SLR:15762-15768 already records that Theory's
`reduce_*` family stops at `reduce_sort`/`reduce_forallE` — `LRS.IndTyHeadNorm`
(SLR:15769) is exactly this missing fact, still open.

**Parked as U-b1** (open sub-question, moot for the verdict): whether a
*neutral-base* generalization of `RegTele` (allowing `bvar`-headed bases, which
is what recursor telescopes like `… → C t` need) plus a new `Params.Semantic`
telescope field for `symb`-classified constants would extend the narrowing to
site (b-ii).  Two observations bound it: the generalization keeps the kill-shot
(a sort base is still excluded), but it does **not** help site (b-i), and it
needs a new generation-side field constructed in every `Params.Semantic`
instance (including `SExprParamsD0/D1/D2`).

---

## Staged obligations (all landed in probeU unless marked)

| # | Statement (one line) | Status |
|---|---|---|
| U0 | `RegTele` is the `CtorBundle.rhs` shape, closed under substitution/`inst`, invertible, and excludes sort/redex-based Pis | probe-proved (`CtorBundle.rhs_regTele`, `RegTele.subst`, `.inst`, `.pi_inv`, `.not_forallE_sort`, `.zero_not_app_lam`) |
| U1 | `LRS.PiPathInvReg` is a weakening of the leaf (nothing strengthened) | probe-proved (`LRS.PiPathInvReg.of_piPathInv`) |
| U2 | **Kill-shot:** the `PiPathInv → ParRedSDefeq` β site is outside the class at every arity, in the empty context | probe-proved (`betaSite_outside_regTele`) — narrowing survives |
| U3 | Two spines reached from one registered telescope have path-equal results, spending only `PiPathInvReg` | probe-proved (`regSpine_result_uniq`) |
| U4 | **Site (a) closes:** `LRS.CtorSpineTypeUniqPath` from `PiPathInvReg` alone | probe-proved (`LRS.CtorSpineTypeUniqPath.of_piPathInvReg`) |
| U4′ | …and with it the leaf-side consumers: the per-leaf anchor discipline and the whole chain-fold interior | probe-proved (`LRS.CtorAnchorDisciplineAt.of_piPathInvReg`, `LRS.CtorChain.foldRaw_of_piPathInvReg`) |
| U5 | **Site (b-i) does not close:** a constructor view is reachable through a β step with no environment assumptions; its Pi endpoints are unregistered | probe-proved (`rootRed_meets_beta` + U2) |
| U6 | **Site (b-ii) does not close:** every `Pattern.Action` redex head is provably not a constructor, so no telescope exists to anchor the walk | probe-proved (`Arity.head_wf`, `symb_not_isCtor`, `extraSite_head_not_isCtor`) |
| U7 | The semantic bridge has no head-classification coherence field and no `symb` telescope field (six fields, enumerated) | measured by inspection (SExpr:1964-2050) |
| U8 | **The narrowed Prop is not easier:** the class is not closed under one path edge, and every registered Pi has unregistered path interiors | probe-proved (`regClass_not_edge_closed`, `regPath_interior_unregistered`) |
| U-vac | Non-vacuity: the class is inhabited, and `PiPathInvReg`'s hypothesis is inhabited **off the diagonal** (environment-conditional, like `LRS.indTyHead_nonvacuous`) | probe-proved (`regTele_nonvacuous`, `LRS.piPathInvReg_nonvacuous`) |
| U-b1 | Neutral-base generalization + a `symb` telescope field for site (b-ii) | **parked** — moot for the verdict (site (b-i) fails regardless) |

---

## (vi) Bottom line, and the single question that remains

**Leaf closable by the registered-endpoint narrowing: NO — but the axis is not
refuted, and it is not empty either.**  Unlike the stratification axis (probeT:
refuted at every depth) and the sort narrowing (banked counterexample), the
registered axis *does* buy something checkable: the entire interior of the
constructor chain — every native link, every layer of every spine — now costs
only `LRS.PiPathInvReg`, whose registered endpoint is supplied by the
constructor's own bundle.  What it does not buy is a cheaper proof: the
decoration is destroyed by the first path edge, for the same structural reason
the depth decoration was destroyed by `trans`.

**What is left of the leaf after both axes are closed** is exactly two root
callbacks, and one question about them:

> **Can `LRS.CtorView` be upgraded to a *typed* view — carrying
> `IsDefEq Γ M X A` alongside the bare `WHRedS Γ M X` — so that `rootRed`
> dissolves the way the chain interior dissolved in the 2026-08-15 repair?**

That is the exact analogue of the repair that killed the interior half: the
interior was not *proved*, it was **retained** (the reconciliation moved into
the `LRS.CtorExact` certificate).  The root views are the last place where a
reduction enters the fold with no typing attached.  The measurement to run is
scoped and additive-or-not-decidable in one probe:

* the views are produced by `LRS.CtorDefEq.toChain` (SLR:11979), whose `whr`
  and `unwhr` cases (SLR:11994-11995) pass through the bare reductions stored
  by the `LogRel` closure law `whr` (SLR:10064), an **iff** — so the upgrade
  must supply typings in *both* directions, which is the real risk;
* the evidence that it may be affordable: at the adequacy producer the
  reduction always arrives typed (e.g. ADQ:8496-8498 builds it from
  `SExpr.WHRed.extra action`, whose `action.sound` is the typing), and
  `WHRed.defeq_of_piPathInv`'s non-β, non-`extra` cases (`app`, `major`) are
  already inversion-free;
* if the upgrade lands, the leaf's **entire** residual becomes
  `LRS.PiPathInvReg` — at which point this document's U8 becomes the only wall
  left, and the honest cost of the leaf is the semantic content the roadmap
  already names (sort/Pi disjointness + standardization) with no structural
  shortcut remaining;
* if it does not, `rootRed` is general weak-head subject reduction
  (`LRS.SubjectRedS` restricted to constructor targets), which
  `LRS.piPathInv_iff_parRedSDefeq` has already shown is interderivable with the
  leaf — i.e. the leaf's cost is unchanged and the map is complete.

**Single next action:** *(executed — 2026-08-20 note)* the
typed-constructor-view probe ran; see `plans/l4l-16-typedview-design.md`
(probeV).  Do **not** re-open the stratification axis (probeT) or
the sort narrowing (banked); and do not re-attempt `LRS.PiPathInvReg` by any
path-structural induction (U8).
