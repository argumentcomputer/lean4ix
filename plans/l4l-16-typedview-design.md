# L4L-16 — the typed constructor view, measured and closed

**Date:** 2026-08-15.  **Probe:** `plans/probes/probeV-typedview.lean` (green:
`lake env lean` exit 0, zero sorries, all 19 `#print axioms` checks land on
`[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`; first-compile green).  The probe imports
`Lean4Lean.Experimental.ShapeLogRel` **only**, so non-circularity with respect
to adequacy is structural, as in probeS/probeT/probeU: `LR.AdequacyAt`,
`LR.ContextualAdequacyAt(Depth)` and every `*.of_adequacy*` are not in the
import closure at all.  No banned input is touched (no `ParRedSDefeq`/
`CRComplete`/`PiStandard`/`PiEdgeInv`/`SubjectRedS`/`PiEdgeObs`, no
`WHRedS.defeq`, no `TypeDefEqPath.collapse`/`RawTypeUniq`, no Theory
`ParRed.defeq`/`StRed.triangle`; the axiom closures certify this).

**Question.**  probeU (l4l-16-registered-pi-design.md) reduced the 16C′
leaf's general-`PiPathInv` uses on the live path to exactly two root
callbacks — `rootRed` (ADQ:1114): `LRS.CtorView Γ₀ M X → IsDefEq Γ₀ M M A →
IsDefEq Γ₀ M X A`, weak-head subject reduction of an arbitrary root to its
classified constructor spine — and recorded one next action: upgrade
`LRS.CtorView` (SLR:11009) to a **typed view** carrying `IsDefEq Γ M X A`,
the exact analogue of the repair that dissolved the chain interior
(`CtorRetype`/`CtorSpineTypeUniqPath`: *retained*, not proved —
roadmap.md:699-712).  Measure whether every producer on the leaf path can
supply the retained typing, and whether the two callbacks then dissolve into
(a) the stored `⤳*` + (b) the retained typing + (c) registered-strength
inversion only.

---

## Verdict in one line

**(ii) — the map is complete.**  The dissolution is a real theorem: with
typed views at the fold's package type, both root callbacks vanish into
projections and the leaf's entire chain residual costs
`LRS.CtorSpineTypeUniqPath` — i.e. `LRS.PiPathInvReg` — only.  But the typed
view is **not producible through the relation**: of its four producers on the
leaf path, the native exact nodes pass, while the three closure-law producers
fail for three independent, machine-checked reasons — the forward weak-head
law is *equivalent to* the subject reduction being dissolved, the backward
law is *refuted outright* (a K-redex typing an ill-typed discarded argument,
against the landed `PiNotFunTyped.of_soundness`), and the `conv` law's
premise at the ctor arm is shape-only, so a conv-closed typed view *provably
collapses all registered inductive head types into one path class*.  The one
retention that survives every closure law (the anchored view) leaves the
callback's demand byte-for-byte where it was.  So `rootRed` cannot be
retained away: it **is** general weak-head subject reduction restricted to
constructor targets, which the banked record
(`LRS.piPathInv_iff_parRedSDefeq`, SLR:16210; probeU U5/U2;
roadmap.md:781-831) places at exactly the leaf's own strength.  No structural
axis remains unmeasured.

---

## (i) The dissolution theorem — the conjecture of the brief, made exact

`LRS.CtorViewT Γ M X A` (probeV Part 1) is `LRS.CtorView` plus one field:
`IsDefEq Γ M X A`, the subject typed against its spine at the observation's
package type.  `LRS.CtorChainT` is `LRS.CtorChain` (SLR:11689) with both
endpoint views typed at the fold's own `D`.  Then, machine-checked:

* `LRS.CtorChainT.foldRaw_of_anchorDiscipline` — the raw fold with **no root
  callbacks at all**.  Where `LRS.CtorChain.foldRaw_of_anchorDiscipline`
  (SLR:11759) takes `left`/`right` subject-reduction callbacks, the typed
  fold takes nothing: `alg.anchor` receives `hleft.defeq`/`hright.defeq` by
  projection, and the path seed is `hleft.defeq.hasType.2`.
* `LRS.CtorChainT.rawDefEqAt_of_anchorDiscipline` — the raw-equality half,
  likewise callback-free.
* `LRS.CtorChainT.foldRaw_of_ctorSpineTypeUniqPath` — the same from the
  environment-level constructor discipline alone, which probeU proved from
  `LRS.PiPathInvReg` (U4: `LRS.CtorSpineTypeUniqPath.of_piPathInvReg`).

So the brief's decomposition "(a) stored `⤳*` + (b) retained typing + (c)
`PiPathInvReg`-strength inversion only" is a **theorem**, conditional on
production: if typed views reach the fold, the leaf's entire residual —
interior *and* roots — is the registered narrowing.  Everything below is the
measurement that they cannot reach it.

What the two callbacks actually need (the brief's determination question):
`foldRaw_of_majorChainAnchorStep` (ADQ:1191-1202) invokes `rootRed` with the
caller's `hM : IsDefEq Γ₀ M M D` and needs `IsDefEq Γ₀ M X D` **at the
fold's `D`** — at the leaf, `D` is `hlastPair.domain` and `hM`/`hN` are
`hlastPair.major.hasType.{1,2}` (SExpr:1433, `LastPair.major`).  So the form
the callbacks need is the root-typed view **at `D` itself** — not a typing
at some other package type (which would re-open raw type uniqueness at `M`
to reconcile), and not an anchored typing (see (iv)).

---

## (ii) The producer inventory — one passes, three fail

The complete set of `LRS.CtorView` introduction sites in the tree (grep):
`toChain`'s `exact` case (SLR:11985-11986), `CtorView.whr` (SLR:11021),
`CtorView.unwhr` (SLR:11028); plus the relation-level laws that feed them —
`LRS.CtorDefEq`'s `whr`/`unwhr` constructors (SLR:10776-10779), demanded by
the `LogRel` interface's **untyped iff** `whr` law (SLR:10064) through
`LRS.IndDefEq.whr` (SLR:12189-12193), and the `conv` law (SLR:10057) at the
ctor arm (`LRS.DefEq`, SLR:12448).  Measured one by one:

**(P1) Exact nodes — PASS** (`LRS.CtorExact.toChainT`, probeV Part 2).
Every native exact leaf yields a typed chain of length one at one common
package type: `LRS.CtorExact.rawDefEq` (SLR:10998) *is* the retained typing,
because a `CtorExact`'s subjects are the spines themselves (SLR:10966-10968).
Both live `LRS.CtorDefEq.exact` production sites — the nullary-constructor
cases of `LR.SelfAdequateConstStep.of_steps` (ADQ:7736) and of the
derivation induction `LR.adequacy_of_iotaWitnessStep` (ADQ:8034) — store
`.rfl` reductions with the head typing `.const hreg hlen` in scope, so the
origin producer supplies the typing with no new obligation.

**(P2) The forward law (`toChain`'s `whr` case) — IS THE RESIDUAL**
(`LRS.ctorViewT_whrClosure_iff`, probeV Part 3).  The transport
`WHRedS Γ M M' → CtorViewT Γ M X A → CtorViewT Γ M' X A` is **equivalent**
to `LRS.CtorTargetSubjectRed`: edge-splitting subject reduction along
constructor chains (`M ≡ X : A` and `M ⤳* M'` give `M' ≡ X : A`).  Its
single-β-step content (`CtorTargetSubjectRed.beta_step`) is verbatim the
per-step obligation `WHRed.defeq_of_piPathInv` (SLR:11507) discharges from
the general leaf at its `beta` case (SLR:11523-11536), where `piInv` is
charged on the abstraction's own declared Pi; and the typed view is
reachable through β at an abstraction domain the view leaves completely free
(`LRS.ctorViewT_beta_view` — the typed sharpening of probeU's
`rootRed_meets_beta`/U5, whose Pi endpoints U2 put outside every measured
narrowing).  So "retain and transport forward" is not a repair; it is the
residual restated.

**(P3) The backward law (`toChain`'s `unwhr` case) — REFUTED**
(`LRS.ctorViewT_unwhrClosure_false`, probeV Part 4).  `LogRel.whr` is an
iff; its right-to-left direction gives the free `unwhr` constructor an
arbitrary new root with a bare `WHRedS` and *no typing in any scope* — this
is the structure field itself, not an accident of a call site.  The typed
transport it imposes is **false**, conditional only on the environment
classifying and typing one constructor (the established non-vacuity
discipline): the K-redex
`(fun _ : T₀ => c) ((Prop → Prop) Prop)` β-reduces to `c`, so the law would
type it at `T₀`; `IsDefEq.strong` (SExpr:2996) plus two applications of the
banked structural inversion `IsDefEqStrong.app_inv'` (SExpr:3688) then type
the discarded argument's function part — `Prop → Prop` — **at a Pi**, and
`LRS.PiNotFunTyped.of_soundness` (SLR:15058, landed from `LE_Interp.sound`
outside the fixpoint) refutes it.  No closedness induction, no new
inversion, no adequacy rung.

**(P4) The `conv` law — COLLAPSING** (probeV Part 5).  The ctor arm lives at
the `.indTy` type shape, and the semantic type equality there is
**shape-only**: `LRS.TyDefEq.indTy_m` (SLR:12476, restated as
`LRS.convPremise_at_indTy`) says the conv premise is two `IndTyHead`
classifications and *nothing else* — no raw equality, no path, no shared
subject.  A conv-closed typed view (`LRS.TypedViewConvClosure`) therefore
transports a spine's typing between package types with no raw connection,
and `LRS.typedViewConvClosure_collapses` shows that together with the
interior discipline the chain repair already retains
(`LRS.CtorSpineTypeUniqPath`) it path-connects the spine's telescope result
type with **every** registered inductive head type simultaneously — with two
registered inductives, `TypeDefEqPath Γ NatTy BoolTy`.  That is the
registered-uniqueness discipline (`LRS.constTypeUniqPath`, SLR:11389 — one
type per registered declaration) in reverse: the obligation is not merely
unsupplied by its premises, it is absurdity-grade in the intended model, so
no producer for it can be built.  (This is a conditional refutation — an
outright `False` would need a separating model, which the abstract `Params`
does not provide; the collapse is the strongest available form and is
sufficient for the verdict.)

**The law/site distinction, recorded for completeness.**  At every *live*
application of the closure laws in the adequacy producer, a typed edge is in
scope — enumerated: ADQ:4090 (iota fire; `hterm` + `action.sound`),
ADQ:7154/7165/7170 and 8243/8251/8254 (β-expansions in the lambda evaluator;
rule premises + argument typings, edge via `IsDefEq.beta`), ADQ:7790
(constant unfold; `Params.Semantic.defn_whRed`'s retained `IsDefEqStrong`
edge, ADQ:7266-7275), ADQ:8481/8488 (defn case; the rule's own `Hdef`
substituted), and the two forward uses ADQ:8439/8498 (β/extra reducts; edges
constructible from premises / `action.sound`).  The typings exist at every
entry and **die at the arm boundary**, because the arm must satisfy the
untyped iff.  That is the precise sense in which the `LogRel` interface —
not any single proof — is what erases root typings; re-typing them
downstream is `rootRed`, and re-founding the interface on a typed `whr` law
is the L1-class relation change probeT already closed ("re-founding, not
repair"), and it would still fail (P4) at `conv`, whose indTy premise is
shape-only by the definition of the relation's type arm (SLR:12240).

**The leaf's own scope (the brief's `htermI`/`hAIType`/`hspineXI/YI`
check).**  At the sorry site (ADQ:8583) those hypotheses type the *recursor*
spines at `AI` and supply `AI`'s sort; the callback inputs at
`D = hlastPair.domain` come from `hlastPair.major.hasType` — sufficient to
*invoke* the callbacks, and sufficient to *build* the typed views at the
roots only given `IsDefEq Γ₀ majorX X D` — which is the callback's own
conclusion.  Manufacturing the typed view at the fold entry from the
caller's inputs is `rootRed` verbatim; the circularity is structural, not an
artifact of missing lemmas.

---

## (iii) The anchored form — the survivor, and why it is worthless

`LRS.CtorViewA` (probeV Part 6) decouples the typing from the root: some
vertex `M₀` with `WHRedS Γ M₀ X` carries `IsDefEq Γ M₀ X A`, while the
subject's own prefix stays bare.  Machine-checked: it is closed under both
transport directions (`CtorViewA.whr` via `WHRedS.determ_l` +
`WHNF.ctorSpine`; `CtorViewA.unwhr` by prefix absorption) and produced at
the origin with the degenerate anchor `M₀ := X`
(`CtorViewA.of_spineTyping`) — so it *is* producible everywhere, including
through the untyped iff.  And it dissolves nothing: the callback's residual
demand (`LRS.CtorViewA.Extraction` — close the untyped prefix at the
caller's `D`) is implied by `rootRed` unchanged
(`Extraction.of_rootRed`), and its demand family still reaches the β site
with a free abstraction domain (`LRS.ctorViewA_beta_premises`: both the
anchored view and the caller-side typing are inhabited at a K-redex whose
domain nothing constrains — probeU's U5 obstruction, untouched by the
anchor).  Anchoring at the pre-reduction root (the brief's suggested
variant) is the special case `M₀ :=` the whr-case's old subject, and the
extraction gap it leaves is the same untyped prefix.

Parked as **V-b1** (moot for the verdict): a "typed shadow" certificate
carried *beside* the relation rather than inside it, produced at the live
sites where typings exist.  Two named walls bound it: it must follow the
relation through `conv` (P4's shape-only premise applies to any carrier
indexed by the package type), and a shadow indexed by the spine's own
telescope type instead re-opens the `A`-vs-`D` reconciliation at the fold,
which is raw type uniqueness at the root.  Threading it through the
relation's function-space quantifiers is the carrier change probeT's L1
analysis classified as a re-founding.

---

## (iv) The crown sub-question, demoted and measured

Under verdict (ii) the leaf's residual is *not* reduced to
`LRS.PiPathInvReg`, so single-edge Pi inversion at a registered endpoint is
no longer "the one hard lemma" — the roots keep their general demand
regardless.  The probe still measures its shape, because probeU left it as
the only unexamined narrowing of U8:

* **U8 recap:** the registered class is not closed under one *path* edge,
  and every registered Pi has unregistered path interiors — path-structural
  induction dies at `TypeDefEqPath.trans`.
* **New (probeV Part 7):** the same wall exists one level down, inside the
  single edge itself.  `IsDefEq.trans` (SExpr:1263) is a constructor of the
  edge relation, its middle is existential, and
  `regEdge_trans_middle_escapes` shows every edge between two Pis — both
  endpoints registered included — factors through a middle
  (`(fun _ : Sort s => #0) (∀A,B)`) that is outside the class at every
  arity **and not syntactically a Pi**, with no environment assumptions.  A
  derivation induction walking the one edge from its registered end hands
  its inductive hypothesis, at the first `trans` constructor, an edge with
  neither a registered nor a Pi left endpoint.

So single-edge inversion at a registered endpoint is **not a different
question**: it is U8's question transposed from the path's `trans` to the
derivation's `trans`, and it falls to the same middle-escape.  What survives
a `trans`-refactoring (walking only the non-`trans` constructors) is exactly
the semantic content — `beta`/`eta`/`proofIrrel`/`extra` — i.e. the
soundness-shape/standardization route the 18A′ map already prices, and
which `LRS.piPathInv_iff_parRedSDefeq` makes interderivable with the leaf.
Crown outcome: **mooted by the verdict, and independently closed as a
structural attack; the residual attack surface on the edge is semantic
only.**

---

## Staged obligations (all landed in probeV unless marked)

| # | Statement (one line) | Status |
|---|---|---|
| V0 | Typed view/chain defined; projections to the live view and typing | probe-proved (`CtorViewT.toView`, `.defeq`) |
| V1 | **Dissolution:** a typed chain folds with NO root callbacks, from the anchor discipline alone | probe-proved (`CtorChainT.foldRaw_of_anchorDiscipline`, `.rawDefEqAt_of_anchorDiscipline`) |
| V1′ | …and hence from `LRS.CtorSpineTypeUniqPath` alone — with probeU U4, from `LRS.PiPathInvReg` | probe-proved (`CtorChainT.foldRaw_of_ctorSpineTypeUniqPath`) + banked U4 |
| V2 | **Producer (exact): PASS** — every native exact leaf yields a typed chain at one common package type | probe-proved (`CtorExact.toChainT`) |
| V3 | **Producer (whr): IS the residual** — forward transport ↔ edge-splitting subject reduction; β content = the leaf's `piInv` site; typed views reachable through β with the domain free | probe-proved (`ctorViewT_whrClosure_iff`, `CtorTargetSubjectRed.beta_step`, `ctorViewT_beta_view`) |
| V4 | **Producer (unwhr): FALSE** — the backward transport the untyped iff imposes is refuted (K-redex + `app_inv'`×2 + landed `PiNotFunTyped.of_soundness`) | probe-proved (`ctorViewT_unwhrClosure_false`) |
| V5 | **Producer (conv): COLLAPSING** — the indTy conv premise is two `IndTyHead`s only; a conv-closed typed view + the retained interior discipline path-connects all registered inductive head types | probe-proved (`convPremise_at_indTy`, `typedViewConvClosure_collapses`) |
| V6 | The anchored view survives all closure laws and production | probe-proved (`CtorViewA.whr`, `.unwhr`, `.of_spineTyping`) |
| V7 | …and buys nothing: its extraction is implied by `rootRed` and still meets the free-domain β site | probe-proved (`Extraction.of_rootRed`, `ctorViewA_beta_premises`) |
| V8 | **Crown (demoted):** single-edge inversion at a registered endpoint inherits U8 at the derivation level — `IsDefEq.trans` middles are unregistered non-Pis between registered endpoints | probe-proved (`regEdge_trans_middle_escapes`, `RegTeleV.not_app_lam`) |
| V-b1 | Typed shadow certificate beside the relation (conv-following + `A`/`D` reconciliation walls; L1-class carrier change) | **parked** — moot for the verdict |

---

## (v) Closure statement for the milestone decision

With probeT (stratification: machine-refuted), probeU (registration: closes
the chain interior, not the roots; the narrowed Prop no easier), and probeV
(retention: dissolution real, production impossible), **every structural
axis on the 16C′ leaf is measured and closed**.  The completed map:

* `rootRed` = weak-head subject reduction to a classified constructor spine.
  Retention cannot remove it (V3/V4/V5); anchoring cannot weaken it (V7);
  registration cannot narrow its β case (probeU U5 + U2); sort-typing
  cannot (banked witness, roadmap.md:799-803); depth vouchers cannot
  (probeT T2/T3/T5).
* Its β content — reconciling an application's domain with the
  abstraction's own annotation — is the exact site where every route into
  the leaf (`WHRed.defeq_of_piPathInv` beta, `ParRed.defeq` beta,
  `StRed.triangle`) charges Pi injectivity, and
  `LRS.piPathInv_iff_parRedSDefeq` (SLR:16210) makes any subject-reduction-
  grade Prop interderivable with the leaf itself.  `rootRed` is therefore
  not an input *to* the leaf; it is the leaf.
* The interior (chain links, spine layers) costs `LRS.PiPathInvReg` only
  (probeU U4/U4′), and with typed views it would be the *whole* cost (V1′)
  — but the views die at the relation's interface, whose untyped `whr` iff
  and shape-only indTy `conv` are load-bearing (V4, V5).

The milestone decision this closes: 16C′ cannot be finished by any further
structural probe.  The remaining options are exactly two, and both are now
priced: **(A)** re-scope 16C′ with `LRS.PiPathInv` as its single named open
input (the tree already threads the entire consumer surface — chain fold,
anchor step, CR ladder, adequacy leaf — through that one Prop), or **(B)**
fund the semantic content itself (sort/Pi disjointness is landed; what
remains is standardization/Church–Rosser-grade normalization for the typing
judgment, which the interderivability results price at the leaf's own
strength, outside the fixpoint).  There is no option (C).

**Single next action:** no further probe on this leaf.  Update roadmap.md's
16C′ section with verdict (ii) and the completed three-axis map
(probeT/probeU/probeV), and take the milestone decision between (A)
parameterizing on `LRS.PiPathInv` and (B) scheduling the semantic
normalization work — recording, either way, that `CtorChainT` (probeV Part
1) is the interface the leaf should consume the moment the leaf's Prop
lands, since it makes the entire residual `LRS.PiPathInvReg`-shaped.  Do
not re-open: stratification (probeT), sort narrowing (banked), registered
path/derivation induction (U8 + V8), or view retention (V4/V5).
