# L4L-16 — the stratified-observation design question, measured and closed

**Date:** 2026-08-15.  **Probe:** `plans/probes/probeT-stratpi.lean` (green:
`lake env lean` exit 0, zero sorries, all 23 `#print axioms` checks land on
`[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`, and the probe imports `Lean4Lean.Experimental.ShapeLogRel` only, so
non-circularity with respect to adequacy is structural, as in probeS).

**Question.** The adequacy iota leaf `LR.iotaWitnessStep`
(ShapeLogRelAdequacy.lean:8553, sorry at :8583; "ADQ") factors through
`LRS.PiPathInv` (ShapeLogRel.lean:11417; "SLR"), and the recorded root cause
is "not `SpineWF` but `LRS.ValTyPi2`/`LogRel` being `WShape`-indexed with no
stratification index" (roadmap.md:844-848).  Three levers were on the table:

* **L3** — the `RectFrame` index upgrade (probeR13-rectframe.lean);
* **L2** — observation-local depth certificates: put depth vouchers on
  `LRS.ValTyPi2`'s two `TypeDefEqPath`s (SLR:10282);
* **L1** — re-index the whole relation, `LogRel Γ n` → `LogRel Γ n d`.

**Verdict in one line.**  L3 closes only the frame-transport layer and
nothing Pi-shaped; **L2 is closed on all three of its possible readings by
machine-checked theorems — one of them refutes the banked
`LRS.ChainAnchorAt` obstruction Prop outright (it is *false* at every
depth, not merely fatal-if-true)** — and L1 inherits the same obstruction
through its `trans` case (`LRS.transMiddleCertAt_false`).  The leaf is not
closable along the stratification axis; the axis itself is now refuted, not
just trap-equivalent.

---

## (i) L3 — exact coverage of the `RectFrame` upgrade

What probeR13-rectframe.lean (green, no `sorryAx`, not landed) proves:

* `LRS.RectFrame` — `LRS.CtorFrame` with the type shape `(a, q)` threaded
  positionally beside the element shape — makes the whole frame-transport
  layer of `LR.CoherentIotaLeafStep` **mechanical**: `LRS.RectFrame.rect`
  is four one-liners (`LogRel.DefEqRect.mono_l` for `mono`,
  `LogRel.LiftEquiv.rect` both ways for `lift`/`unlift`), plus
  `symm_rect` and composition `RectFrame.trans`
  (probeR13-rectframe.lean:54-77, :126-135).
* The failure of the unpaired frame is localized **entirely in the index**:
  `DefEqRect.mono_l` needs `m.HasType a` and `m'.HasType a` at one common
  `a`, which a frame recording only `m ≤ m'` cannot supply, and choosing
  `a` inside the transport is the independent re-selection the N2 decision
  forbids (premortem l4l-16c-buildp-premortem.md:4030-4041).

What L3 **does not** cover:

* The residual after L3 is "produce `RectFrame`, not `CtorFrame`": the
  shape must be threaded from the leaf that owns it through the frame's
  *producers*, which is an index upgrade touching every producer — not an
  additive change (premortem:4036-4041).
* L3 never touches `LRS.PiPathInv`.  Verified two ways: (a) the probe's
  entire content is the `DefEqRect`/`LiftEquiv` algebra — no
  `TypeDefEqPath`, no Pi inversion, no path anywhere in the file; (b) the
  chain-fold discipline that demands `PiPathInv`
  (`LRS.CtorSpineTypeUniqPath.of_piPathInv`, SLR:11478;
  `SpineWF.result_path`, SLR:11430) is a different layer of the leaf from
  the frame transport, and the 16C′ verdict already recorded that the
  chain-wall repair left `PiPathInv` as the *single* residual
  (roadmap.md:708-715, SLR:11404-11416).

**L3 verdict:** worth doing *if and when* the leaf's semantic content
closes, as a mechanical cleanup of the frame layer; it closes nothing on
the `PiPathInv` path and is not a lever on the milestone's open question.

---

## (ii) L2 — the crown question, split into its three readings and closed

L2 proposes: store, with each observation, a voucher that the stored paths'
vertices stratify at depth ≤ D.  The design space splits on what `D` *is*.
Each branch is now settled by a probe theorem.  (All `probeT.*` names below
are in `plans/probes/probeT-stratpi.lean`; `TypeDefEqPathAt` is probeS's
depth-carrying path, restated there.)

### Reading 1 — voucher as existential data (`∃ D` stored per observation)

**Closed: the decoration is information-free.**

* `TypeDefEqPath.restratifyData` (probeT): at any well-formed context,
  every bare path re-decorates itself — `IsDefEq.strong` (SExpr:2996) plus
  `IsDefEqStrong.stratify` (SExpr:2430) hand both endpoints of every edge
  a stratified typing at one common depth, and `max`+`mono`
  (SExpr:2397) joins them across `trans`.
* `typeDefEqPathAt_iff_bare` (probeT): `(∃ D, TypeDefEqPathAt Γ D A B u) ↔
  TypeDefEqPath Γ A B u` given `Ctx.WF Γ`.
* `LRS.valTyPi2D_iff_bare` (probeT): the full certified observation
  `LRS.ValTyPi2D` — the real `ValTyPi2` (SLR:10282) with both paths
  vouchered under one stored `D`, reusing the live `LRS.PiDefEq` — is
  **propositionally equivalent** to the bare observation at every
  well-formed context.  The codomain path's context `B₁::Γ` is well-formed
  from the domain path's own left endpoint typing, so no side condition
  survives.

Every consumer of the observation lives at a well-formed context —
`Ctx.WF Γ₀` is the first argument of `LR.IotaWitnessStep` (ADQ:1945-1950)
and heads every adequacy statement (ADQ:40-48).  So swapping `ValTyPi2D`
for `ValTyPi2` inside `LRS.TyDefEq`'s Pi arm (SLR:12239) changes nothing
about what any consumer, the leaf included, can prove: a voucher the
consumer can manufacture on the spot from what it already holds carries no
information.  And the manufactured `D` is `stratify`'s existential —
nothing relates it to any rung, so the leaf's `∀ d' < d` service
(ADQ:1965-1967) still cannot be invoked on it.

### Reading 2 — voucher bounded by a uniform law

**Closed: the law is FALSE, not merely fatal.**  This upgrades both banked
obstructions.  probeS (Part 7) and SLR:16342-16371 proved the producer- and
consumer-side stratification escapes *equivalent* to a uniform
stratification bound and argued that its truth would make the depth
bootstrap's strong induction vacuous.  probeT settles the question with a
witness family:

* `appHeight`/`HasTypeStratifiedS.appHeight_le` (probeT):
  `HasTypeStratifiedS` (SExpr:2363) pays one level per `app` node along
  every path of the syntax tree, and the induction is total over the
  judgment, so no derivation evades the bound.
* `idredexTower l k` — `k` nested identity β-redexes over `.sort l` — is
  well-typed (definitionally a sort) in the **empty** context with **no**
  environment assumptions (`idredexTower_defeq`), and admits **no**
  stratified typing below depth `k`, at any type, flag, or context
  (`idredexTower_min_depth`).
* Hence, at every `d`:
  * `LRS.uniformStratBound_false d` — the uniform bound (exactly the shape
    of SLR:16351/16359 and probeS's `PathRestratifyAt.uniformDepthBound`)
    is false;
  * `LRS.chainAnchorAt_false d` — **the banked Prop `LRS.ChainAnchorAt d`
    (SLR:16342) is itself false**; composing with probeS's
    `PathRestratifyAt.uniformDepthBound`, `LRS.PathRestratifyAt d` is
    false too;
  * `LRS.voucherServiceAt_false d` — the leaf-side serviceability demand
    ("every incoming path carries a voucher strictly below the rung") is
    false at every rung: the tower appears as a path endpoint below every
    rung.

So any voucher discipline whose *statement* promises a fixed or
rung-bounded depth for the paths the fold hands over is refutable.  Note
the consistency check: SLR's `chainAnchorAt_nonvacuous` (:16371) only shows
the Prop's *hypothesis* inhabited — which is precisely what leaves room for
the Prop's falsity, and is why the equivalence was a real obstruction.

### Reading 3 — voucher compared against the rung inside the observation

**Closed: there is no place to write the comparison, and moving it into
the index is L1 — which inherits the obstruction.**

For the voucher to be *usable* at a rung-`d` leaf, the observation's
proposition must entail `D < d` (destructuring an unconstrained `∃ D`
yields a number the leaf cannot relate to `d`; case analysis on `D < d`
strands the bad branch).  But the observation is defined inside
`LogRel Γ n` (SLR:10045), whose only indices are the context, the shape
level, and the shapes — no depth is in scope.  So the bound is either a
constant/uniform law (Reading 2, false) or the relation gains a depth
index — L1 by definition.

### The production side (sub-question (a)), measured for completeness

The real producer of Pi observations is the `forallEDF` case of the
derivation induction (ADQ:8256-8335): the stored paths are single edges
over the derivation's **own substituted premises** (`.single HAσ`,
`.single (HBody.substCongr S').1`, ADQ:8280-8281, :8328-8330).
`LE_Interp.sound` contributes only shape/level bookkeeping (the `toValTy`
inputs, via `.out`); **it puts nothing in the paths** — the brief's
suspected soundness wall is actually a substitution wall (see T5 below).
probeT's `LRS.piObservation_vouchers_by_construction` measures what a
depth-aware version of the site could voucher, given the two Pi endpoint
certificates such an induction would hold (`HasTypeStratifiedS.forallE_inv`,
SExpr:2577, returns components at `n - 1`):

* the **domain** path vouchers at `max n n' - 1` — strictly below both
  ambient certificates (probeS's favourable arithmetic, reproduced);
* the **codomain left** endpoint certifies at `max n n' - 1` in the right
  context `A :: Γ`;
* the **codomain right** endpoint is certified by `forallE_inv` only in
  `A' :: Γ`; landing it in `A :: Γ` needs context conversion for
  `IsDefEqStrong`/`HasTypeStratifiedS`, and **neither lemma exists in the
  tree** (measured by grep; the weak-judgment `IsDefEq.defeqDF_l'`
  induction at SExpr:3562 has no strong or stratified counterpart).  The
  fallback is `IsDefEqStrong.stratify` — an existential depth with no
  relation to the rung, i.e. Reading 1.

Two further production/closure measurements:

* **`whr` never rebuilds a stored path** — verified twice: on the live
  successor law, whose Pi arm passes `rest` through unchanged
  (SLR:12757-12760; likewise `mono_r_2_ty` SLR:12602-12606, `mono_l`
  SLR:12668-12672, `join_ty` SLR:12716-12724 reuse `hBB', hFF'`
  verbatim), and on the certified observation, where the voucher *value*
  survives verbatim (`LRS.ValTyPi2D.whr`, probeT).  The brief's suspicion
  ("paths live on the Pi components, not the subjects") is confirmed.
* **`trans_ty`/`symm_ty` cannot maintain voucher arithmetic natively.**
  The live laws retype the codomain path along the domain path with
  `TypeDefEqPath.defeqDF_l_path` (SLR:12286, :12269; SExpr:3650); the
  vouchered step needs the two missing conversion lemmas above.  At
  well-formed contexts the law still holds — `LRS.ValTyPi2D.trans`
  (probeT) — but only *through the conservativity equivalence*, which
  re-chooses the voucher; no invariant like "output ≤ max of inputs"
  survives.  A left-endpoint-only voucher variant (production-friendly:
  three of the four certificates above are left-or-domain) loses `symm` —
  `TypeDefEqPathAt.symm` (probeT, mirroring probeS) consumes both endpoint
  certificates, and `symm_ty` is a `LogRel` field (SLR:10053) that flips
  the stored paths (SLR:12261-12275).  **Pincer:** full vouchers fail at
  production (wrong-context codomain-right), left-only vouchers fail at
  closure (`symm`).  Parked as T-b1; moot for the verdict since
  consumption is refuted regardless.
* **The σ-quantifier wall** (`substInstance_min_depth_unbounded`, probeT):
  a fixed subject with a fixed certificate has substitution instances of
  unbounded minimal depth, and `Adequate` (ADQ:9-13) quantifies over
  substitutions *inside* a rung fixed before them
  (`contextualAdequacyAt_of_adequacyAtDepth` picks the rung from
  `H.stratify` at ADQ:8537, before any σ is chosen).  This closes the last
  middle ground — a voucher bounded by a function of the observation's own
  subject — because the leaf receives σ-instances.

### Vacuity control (sub-question (d))

Every new Prop is either refuted outright — which subsumes the
`TShape.bot` instantiation test, there being no instance left to
trivialize — or carries a non-degenerate witness: `TypeDefEqPathAt` at
depth 0 in the empty context, and `LRS.ValTyPi2D` at the bot shapes
(`TShape.bot`-side element/type shapes, the recorded cheap test) with real
weak-head reducts, real strong edges and real depth-0 certificates
(`typeDefEqPathAt_nonvacuous`, `LRS.valTyPi2D_nonvacuous`, probeT).  The
observation does not collapse at bot — its path components survive — so
the definition fails in none of the directions that killed the two
fixed-head-terminal Props (ADQ's `FixedHeadTerminalLink` bot-kill).

---

## L1 — does re-indexing the relation escape, or inherit?

**It inherits, in both of its natural architectures; the only unrefuted
form is a re-founding, not a repair.**

* **(L1-a) Depth-aware derivation induction** (thread the certificates
  through `adequacy_of_iotaWitnessStep`, ADQ:7821 — currently the
  induction is depth-blind: its signature carries no stratification, and
  the depth bootstrap discards the certificate at ADQ:8523, for the
  recorded reason at ADQ:8510-8515).  Refuted:
  `LRS.transMiddleCertAt_false` (probeT) — **for every depth transformer
  `f`, the demand "a `trans` middle certifies at `f` of the root's depth"
  is false**: the tower sits between two endpoints certified at depth 0
  (`HasTypeStratifiedS.sort'` is nullary, SExpr:2365 — the same asymmetry
  that lets `LRS.SortInv` be produced at rung 0, ADQ:560-578).  This is
  the 2026-08-15 G4 audit's "their depth is not a function of the
  endpoints'" (roadmap.md:691-695) upgraded from an audit note to a
  machine-checked refutation.  It applies to *any* induction over
  `IsDefEqStrong` that must certify middles — the re-indexed relation's
  included, since its trans law composes observations about the middle.
* **(L1-a′) The coherent-derivation-certificate variant.**  ADQ:25-30
  already records that "an arbitrary left-endpoint certificate does not by
  itself bound every premise of the accompanying strong equality; a
  coherent derivation certificate is still required" — indexing by a
  *whole-derivation* coherent depth would cross `trans` (the middle's
  premises are inside the certified derivation).  But the certificate
  covers only the root derivation's nodes: the observations the induction
  produces are about **σ-instances** (`Adequate` quantifies substitutions
  after the rung is fixed, ADQ:9-13, :8537), and the iota leaf's own
  obligation quantifies spine arguments with weak typings only
  (`LR.IotaLeafDefEq`, ADQ:1840, weak spine typings at :1882-1888).
  Neither class is covered by the root's certificate,
  and `substInstance_min_depth_unbounded` (T5) shows it cannot be extended
  to cover them at any fixed rung.  So this variant escapes T4 and dies at
  T5.
* **(L1-b) Fixed-index relation with unfiltered quantifiers**
  (`LogRel Γ n d` where all stored data is bounded by `d` but
  `PiDefEq`/`LamDefEq` still quantify over arbitrary weakly-typed
  arguments, SLR:10268-10295): production must bound the stored data of
  argument- and substitution-instances uniformly in the quantifier, which
  is `LRS.UniformStratBound`-shaped — false
  (`LRS.uniformStratBound_false`, `substInstance_min_depth_unbounded`).
* **(L1-c) Depth-filtered quantifiers** (Kripke/product-order: arguments
  quantified per-depth, observations indexed by pairs): this changes the
  relation's meaning — adequacy's consumers apply codomain instances at
  arbitrary well-typed arguments (`LR.adequateApp`, the fold's dependent
  applications), so the theorem being proved changes with it.  probeS
  Part 7 already named this "re-founding the fixpoint on a product order —
  a milestone, not a leaf repair", and any variant that keeps the index
  tied to typing stratification still faces (L1-a) at `trans`.  A depth
  index decoupled from typing stratification altogether (e.g. reduction
  step-indexing) is a different design not covered by the recorded root
  cause (roadmap.md:844-848 names the *stratification* index) and is out
  of scope of this measurement; nothing here refutes it, and nothing here
  supports it.

---

## Staged obligations (all landed in probeT unless marked)

| # | Statement (one line) | Status |
|---|---|---|
| T0 | Voucher-as-data is conservative: `(∃ D, TypeDefEqPathAt Γ D A B u) ↔ TypeDefEqPath Γ A B u` and `ValTyPi2D ↔ ValTyPi2` at WF contexts | probe-proved (`restratifyData`, `typeDefEqPathAt_iff_bare`, `valTyPi2D_iff_bare`) |
| T1 | A well-typed family of unbounded minimal stratification depth exists in the empty context | probe-proved (`appHeight_le`, `idredexTower_defeq`, `idredexTower_min_depth`) |
| T2 | The uniform stratification bound is false at every depth | probe-proved (`uniformStratBound_false`) |
| T2a | `LRS.ChainAnchorAt d` (SLR:16342) is false at every `d`; with probeS's equivalence, so is `PathRestratifyAt d` | probe-proved (`chainAnchorAt_false`) |
| T3 | No rung can promise strictly-below vouchers for incoming paths | probe-proved (`voucherServiceAt_false`) |
| T4 | No depth transformer bounds a `trans` middle's certificate by the root's — L1's induction cannot cross `trans` | probe-proved (`transMiddleCertAt_false`) |
| T5 | σ-instances of a fixed certified subject have unbounded minimal depth — no per-subject voucher bound survives `Adequate`'s quantifier | probe-proved (`substInstance_min_depth_unbounded`) |
| T6 | Production ledger at the Pi site: domain + codomain-left vouchers at `max n n' − 1` by construction; codomain-right only via rung-unrelated `stratify` | probe-proved (`piObservation_vouchers_by_construction`); moot for the verdict |
| T7 | `whr` preserves voucher values; `trans` holds at WF only via T0's equivalence (voucher re-chosen) | probe-proved (`ValTyPi2D.whr`, `ValTyPi2D.trans`) |
| T-b1 | Native voucher arithmetic for `trans_ty`/`symm_ty` needs `IsDefEqStrong.defeqDF_l` + `HasTypeStratifiedS` context conversion (both measured absent) | **parked** — open sub-question, moot for the verdict (T2/T3 close consumption regardless) |

---

## (iii) Bottom line for the milestone decision

**Leaf closable by staged proof work along the stratification axis: NO —
machine-refuted, not merely trap-equivalent.**  Reading 1 of L2 is
provable and adds nothing; Readings 2-3 and both natural forms of L1 are
false; the banked obstruction Props (`ChainAnchorAt`,
`PathRestratifyAt`-shaped) are now known false at every depth, which is
the strongest possible form of "do not open the stratification work"
(roadmap.md:830-831).  The root-cause note (roadmap.md:844-848) should be
read as an *autopsy*, not a work item: adding the missing stratification
index is not a repair that was left undone — it is a repair that cannot
exist in the fixpoint as founded.

**What remains standing** is the adequacy route's semantic content itself
(`PiPathInv.of_adequacy` — roadmap.md:844-846, "the only one standing"),
now with the depth axis closed around it.  The one direction the measured
record marks attackable and this work does not touch: the residual's
subjects at the leaf are **registered declarations** — "the first residual
a generation-side argument can attack" (roadmap.md:708-711;
SLR:11380-11388, `constTypeUniqPath`'s docstring: a registered declaration
has one type).  `LRS.constSpineTypeUniqPath` (SLR:11458) currently spends
general `PiPathInv` once per spine layer; whether the leaf's actual demand
can be narrowed to Pi inversion **with one endpoint pinned to a registered
telescope** (`SExpr.mkInst ls ci.type` and its instantiations) — a class
the environment generates and finite per-declaration induction might
invert without general Π-injectivity — is unmeasured.  The banked
sort-typed narrowing provably did not dodge the hard case
(roadmap.md:799-803), but that β-case obstruction lives in the *ladder*
loop at arbitrary abstraction domains; the *leaf's* chain-fold demands are
constructor/registered-headed, so the registered-endpoint narrowing is a
genuinely different, unrefuted question.

**Single next action:** probe the registered-endpoint narrowing — restate
the leaf's two `PiPathInv` call sites (`SpineWF.result_path`'s layers on
constructor spines, SLR:11430; the `rootRed` residual's type paths,
roadmap.md:712-715) as Pi inversion at registered-telescope endpoints,
measure whether both sites fall inside the class, and attempt the
per-declaration telescope induction for it.  If that class also escapes,
the leaf's remaining cost is the full semantic content
(sort/Pi-disjointness + standardization) with no structural shortcut left
on the map.
