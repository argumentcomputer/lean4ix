# L4L-16 completion plan

Date: 2026-08-13 (audit window 04:50–05:10 EDT)
Author: fresh audit session (Claude), commissioned because L4L-16 "looks
stuck or spinning."
Status: proposal for review. No Experimental/ or roadmap edits were made by
this session. All measurements below were taken against the live working
copy and its freshly rebuilt oleans; the working copy is a **moving
target** (see §1.0), so line numbers are approximate by ±20.

## 0. TL;DR

L4L-16 is much closer to done than the roadmap's tone suggests, and the
spinning has an identifiable root cause. The measured critical path to the
gate theorem is **one file-local sorry** (the adequacy iota leaf, which
decomposes into three named obligations O1–O3, §3) **plus one `SExpr.lean`
lemma** (`WHRedS.defeq`, consumed by the leaf machinery via dot-notation —
the only one of the nine SExpr sorries on the gate path). Of the other
eight, two are false as stated, and one (`CRDefEq.trans`) is a disguised
port of all of L4L-18A. The fix is a milestone re-cut: narrow L4L-16B to
what the gate consumes, resolve the leaf by an explicit interface decision
instead of a sixth transport-infrastructure repair, move the
Church–Rosser-shaped debt into L4L-18A where it belongs, and stage
L4L-16D (the only never-executed segment). Two of L4L-17's four targets
land free when the leaf closes; L4L-17 re-scopes to reflection +
`weakN_iff` + structure-head inversion. The live worker has already begun
the recommended leaf repair (the `PatternLeafSpine.aligned` refactor) —
this plan endorses completing it, with the endpoint pinned in advance.

## 1. Measured state (evidence, not narrative)

### 1.0 Operational context

- Two other AI sessions have this checkout as cwd: a codex session on
  pts/3 (running since Aug 10, ~50 h CPU) and a Claude session on pts/11
  (since Aug 12). One of them was still editing
  `ShapeLogRel.lean`/`ShapeLogRelAdequacy.lean` at 05:02 and rebuilding at
  05:03 during this audit. The Claude peer `navigatrix-1b` explicitly does
  **not** work in this repo (confirmed by direct message).
- The uncommitted working copy is one 18h+ mega-change on top of the
  L4L-18B checkpoint (`oluxtqyk`/`96aeab5c`), mixing: completed L4L-16A,
  partial 16B, near-complete 16C, four file parkings, and ~300 lines of
  roadmap narrative. During the audit window `SExpr.lean` was briefly
  red (a `WithLift.defeq` projection error) and was fixed at 04:56 —
  i.e. the working copy has been oscillating red/green.

### 1.1 The gate path is one sorry wide

Measured with `#print axioms` against the 05:03 oleans:

| Declaration | Closure |
|---|---|
| `VEnv.IsDefEqU.sort_invS` (the L4L-16 endpoint) | `[propext, sorryAx, Classical.choice, Quot.sound]` — **no project axiom** |
| `SExpr.LR.adequacy` | same |
| `SExpr.LE_Interp.sound` | `[propext, Classical.choice, Quot.sound]` — clean |
| `VEnv.IsDefEqStrong.mkS` (judgment translation incl. structEta) | `[propext, Quot.sound]` — clean |
| `SExpr.LRS.CtorDefEq.fold`, `SExpr.LR.DefEq.ctor'_inv` | clean |
| `SExpr.forallE_inv`, `SExpr.sort_forallE_inv` | sorryAx **only via the leaf** |

The `sorryAx` sources on the route are exactly two:

1. the adequacy leaf (`ShapeLogRelAdequacy.lean:~1228`, the body of
   `LR.PatternLeafDefEq.of_iota`'s `by` block inside `LR.adequacy`'s
   const case, downstream of the proved `ctor'_inv`), and
2. `SExpr.WHRedS.defeq` (SExpr.lean:~2920), consumed **via dot-notation**
   (`hredX.defeq`, `hMajorX.defeq`) at ≥6 sites in the adequacy file
   (495/496/507/518 inside the proved `LR.iotaActions_of_exactAt`, plus
   839, 1125). A literal-name grep misses these — which is how one audit
   pass wrongly concluded no SExpr sorry is on the path.

The other eight `SExpr.lean` sorries are not referenced by
`ShapeLogRel.lean` or `ShapeLogRelAdequacy.lean`.

Bonus: `SExpr.forallE_inv` and `SExpr.sort_forallE_inv` already exist and
are sorry-free **except through the leaf** — closing the leaf delivers the
SExpr side of two L4L-17 targets simultaneously.

### 1.2 The L4L-16B list is mis-scoped

Current live `SExpr.lean` sorries (9), triaged:

| # | Decl (≈line) | Verdict |
|---|---|---|
| S1 | `IsDefEqLift.subst` (2655) | **False as stated** — `HasType` is a free section variable, so the premise admits the trivial relation. The sound weak form `substDefEq` (2648) is already proved. Restate with a `:↑`-valued `Ctx.Subst` or **delete** if no consumer needs the lifted conclusion. |
| S2 | `WHRed.weakU_inv` `.extra` (2796) | Real but bounded: needs lowering of `Pattern.Action`'s two `IsDefEq` fields; match-lowering (`matchesS_lift'`) already proved. Route: restate `Action`'s `checked`/`sound` at `:↑`, which also subsumes S1's consumer. (2026-08-15: NOT deletable — `WHRedS.weakU_inv` is live via `InferType.weakU_inv`'s cases and `Experimental/LogRel.lean:210`; consumers now named in its doc comment.) |
| S3 | `WHRedS.defeq` (2919) | **On the gate path now** (2026-08-15 re-measure: 11 live call sites, reduced to 3 — all on the adequacy trunk (`constDefEq`, `SelfAdequateConstStep.of_steps`, `adequacy_of_iotaWitnessStep`) — after the dead-wrapper deletions; original note said 6 dot-notation sites, §1.1). As stated it needs a weak-`IsDefEq` typing-inversion layer (`isType`, `app_inv`, `lam_inv`…) that does not exist SExpr-side and is uniqueness-strength — see §2.3 circularity. Do not prove as stated; close via the narrowed form in §3 (16C′ step 2). |
| S4/S5 | `InferType.hasType`/`InferTypeS.hasType` (3017/3097) | **DELETED 2026-08-15** (zero consumers repo-wide; the adequacy development consumes neither `▷` nor `▷*`). |
| S6 | `CRDefEq.trans` (3239) | **A whole-module port in disguise**: needs `CParRed`, `ParRed.triangle`, `ParRed.church_rosser`, `NormalEq.trans`, `NormalEq.parRed` — the last is itself the open L4L-18A Theory debt. Move out of L4L-16 entirely. |
| S7–S9 | `InferType.whRed` cases (3263–3269) | **Statement wrong** (`▷` is syntactic; no conversion rule; all three cases unprovable as written). Restate (`▷*`/up-to-defeq) or delete; no Theory analogue exists. |

Also stale in the roadmap: `Shape.WF.plift`'s "hidden `stop` admission"
does not exist — lines ~1687–1754 of `ShapeLogRel.lean` are a block
comment with zero consumers, and the file is **live-sorry-free**. The
architectural replacement (`CtorDefEq.lift/unlift` + `LogRel.LiftEquiv`)
is already in place and proved. Delete the commented block and strike the
ledger item. (Also: `Params.Semantic` now has six fields, not five —
`iotaRule` is undocumented.)

### 1.3 L4L-16D is genuinely at zero, with enumerated gaps

No `Params` or `Params.Semantic` instance exists anywhere. Known gaps for
a live instance:

- SExpr `Params`: `classify`, `Pat`, `pat_wf`, and the six combinatorial
  laws must be sourced from block certificates; `AssembledPat` currently
  supplies only `pat_simple` and `ext_covers` — the four uniqueness/
  non-overlap laws exist only block-locally (`IotaPat.*`) and there is no
  cross-term (block-rule vs extension-rule) non-overlap lemma.
- SExpr `Params.Semantic`: six fields (`structureEta`, `ctor`, `defn`,
  `iotaRule`, `iotaSite`, `registered`) to be populated from the L4L-15B
  eta registry, generation certificates, declaration history, and
  D020 beta-collapsed coverage respectively.
- Theory-side `Params`/`Params.Extension.join` (consumed only by
  `IsDefEq.church_rosser`) additionally needs four structEta/forallE
  inversion fields with **no current supplier** — weakN-inversion-strength
  facts, i.e. L4L-17 territory. It is NOT needed for `sort_inv`.

### 1.4 Theory frontier interaction

`IsDefEq.uniq` consumes exactly `sort_inv` (×9) and
`forallE_inv_stratified` (×1); nothing else on the Tier-R list. So the
semantic route, once reflected, unlocks the entire transitional
unique-typing closure — which is what `pat_wf` and the projection
consumers shed `sorryAx` on.

## 2. Root-cause of the spinning

1. **The leaf is a design decision being treated as a lemma.** The
   working-copy roadmap records five successive infrastructure repairs at
   the leaf (`iotaSite` contract, `SpineDefEq`, `LiftEquiv`,
   `PatternLeafSpine`, `CtorDefEq` fold audit), each ending in the same
   discovery: exact constructor observations erase the SExpr type of
   their midpoint/captures, and no amount of transport machinery can
   re-manufacture it. The roadmap itself names the two exits (carry the
   canonical type as data, or promote a limited uniqueness lemma) — and
   the sessions kept building a third thing instead.
2. **A mis-drawn milestone boundary legitimized off-path work.**
   "L4L-16B = close all SExpr admissions" put two false statements, one
   L4L-18A-sized port, and several gate-irrelevant lemmas on the active
   list. Effort flowed to what was listed, not to what the exit consumes.
3. **A latent circularity in the repair machinery.** The already-proved
   leaf machinery (`iotaActions_of_exactAt` and friends) routes typing
   through the sorried `WHRedS.defeq`, whose honest generic proof needs
   weak-judgment typing inversion — the very uniqueness-strength
   frontier this development exists to prove. Theory "solves" this only
   inside its transitional (sorry-bearing) closure. Any repair that
   keeps the generic dependency re-imports the problem. The way out is
   that every call site has stronger evidence in scope than the generic
   lemma assumes (carried `Action.sound` equalities, full `SpineWF`
   certificates), so a certificate-carrying variant suffices — see
   §3 16C′ "S3-narrow".
4. **Process:** 18+ hours of uncommitted mega-change, red↔green
   oscillation, roadmap-as-lab-notebook, and (this morning) two sessions
   plus an auditor in the same working copy. The ladder's own
   one-auditable-claim-per-checkpoint rule has been suspended in practice.

## 3. The re-cut

Principle: **L4L-16's exit is the promotion of `sort_inv` at the accepted
closure. Everything not consumed by that path moves to the milestone that
consumes it.**

### L4L-16B′ — SExpr infrastructure, narrowed

Keep only:
- S2 via the `Pattern.Action`-at-`:↑` restatement (also settles S1's
  consumer question).
- S1: restate-or-delete (decide by grepping consumers; expected: delete).
- S7–S9: restate `InferType.whRed` with a `▷*`/up-to-defeq conclusion or
  delete (no consumer found).
- Delete the commented `Shape.WF.plift` block; correct the roadmap claims
  (§1.2).

Explicitly move out:
- S6 `CRDefEq.trans` → L4L-18A′ (it IS Church–Rosser).
- S3/S4/S5 → deferred until §3's leaf decision determines whether any
  accumulator-typing fact is needed at all, and in what judgment (see
  next).

### L4L-16C′ — close the leaf by decision, not accretion

The leaf (`~1228`) decomposes into three named obligations (per the
2026-08-13 audit; details in the audit agent's map):

- **O1 — a composable fold motive over `LRS.CtorDefEq`.** The blocker.
  `CtorDefEq.exact` hides its head/result types (`CHead, CHead', A, A'`)
  existentially, so the `.trans` handler of any `CtorDefEq.fold` has a
  shared midpoint `N` with **no exportable typing**. Fix (Option A,
  recommended, **already begun by the live worker** — the
  `PatternLeafSpine.recArgs → aligned : LRS.CtorSpineDefEq` refactor):
  restate `.exact` to carry `LRS.CtorSpineDefEq` — which already shares
  **one** result type `A` and one domain `D` per field — and give
  `CtorSpineDefEq` a `trans`. That `trans` does NOT need general
  uniqueness: `SpineWF`/`SpineDefEq` conversion steps each **carry**
  their defeq certificate, and the constructor's head type is pinned
  **syntactically** as a Pi telescope by the live certificate
  (`CtorBundle.rhs` is literally `Ts.foldr .forallE …`, supplied by
  `Params.Semantic.ctor` into `IsDefEqStrong.const`'s `F`/`hF` fields).
  So the midpoint alignment composes from carried conversions plus the
  certificate telescope — nothing is manufactured. Update the two
  construction sites (`constDefEq` ctor case ~961; nullary case ~1264)
  and the `Algebra`/`fold` handlers.
  **Option B (fallback only):** the scoped alignment lemma
  "`SpineWF Γ CHead args.reverse A → SpineWF Γ CHead args.reverse A' →
  ∃ u, Γ ⊢ A ≡ A' : .sort u` for a certificate-pinned head" — L4L-17
  content promoted into 16C. Try it only if A's encoding change
  explodes.
- **O2 — mechanical glue.** With O1's `.exact` handler,
  `LRS.iotaDefEq_of_exactAt` (proved, currently unconsumed) is a direct
  fit; all its remaining inputs are already in scope at the sorry.
- **O3 — `LRS.IotaRHSDefEq`, the one genuinely new proof.** Reduce via
  `of_nonbot` (proved); variable-RHS leaves are discharged by the
  supplied `CaptureDefEqAligned` family (already type-aligned — no
  uniqueness needed). The remaining fixed-tower head case is to be
  proved by **well-founded recursion on the semantic `R`-edges via
  `LE_Interp.recR`** (the design comment at the `IotaRHSDefEq` def says
  exactly this), then the application chain closes by `LRS.DefEq.app`.
  No environment or reduction oracle.

Plus **S3 (revised 2026-08-13 after reading the site contracts —
supersedes "S3-narrow")**: the four live `.defeq` call sites reduce to
two facts about the ROOT pair only — the spine-redex self-typing at the
package `A` (from `htermX` plus major-position congruence) and
`IotaTyping.majorEq` (the typed collapse `majorX ≡ ctorSpine :
majorType`). Neither can be discharged by a certificate-carrying
variant alone: the major's stored reduction is an arbitrary weak-head
sequence, and per-step subject reduction hits beta/extra cases needing
typing inversion. The honest route is the one the `▷` layer was built
for — the **InferType principal-types bootstrap**: syntactic
`InferType.determ` (already proved) substitutes for type uniqueness;
prove inference completeness over `IsDefEq` (each case computes the
principal type and connects it to the derivation's type by the IH, no
uniqueness needed), restate `InferType.whRed` up-to-defeq (the false
exact-form was deleted at 16B′), restore `InferType.subst`/`inst` with
a `:↑`-valued substitution premise, and derive the needed `⤳* → ≡`
conversions from principal-type subject reduction. S4/S5 close en route.
This is a real sub-development (days), and it is confined to the ROOT
pair: intermediate chain links never need it (see the chain addendum).

Note on `hDef`: the "circular constant premise" is a field of
`IsDefEqStrong.const` discharged by `mkS` out of
`Params.Semantic.defn` — it needs **no separate 16C work**; its
live-environment construction is exactly 16D's `defn` field.

Rule: if the chosen option hits a second wall, STOP and re-derive the
mathematical obligation in this file before writing more Lean. No sixth
transport layer.

**O1 design addendum (2026-08-13, recorded before implementation).**
Deriving the fold motive abstractly hit the two-strikes rule: every
variant that runs the typed iota-site construction at *intermediate*
fold nodes (trans midpoints, or exact nodes reached inside the free
closure) terminates at the same irreducible brick — reconciling two weak
typings of one term (midpoint, or reduct spine) without inversion, which
is the uniqueness-strength frontier itself. `Pattern.Action` sites for
intermediate pairs are therefore impossible by design, not by missing
lemmas: the free closure's midpoints are genuinely untyped up to
weak-head expansion (`LogRel.whr` is deliberately an untyped iff).
Decided architecture — **root-anchored capture-chain fold**:

- The fold motive carries NO typing and NO sites: only (i) each
  endpoint's weak-head reduction to its constructor spine, and (ii)
  composable per-field semantic relations (`IH`-level) between the two
  spines' fields, plus the head/level agreement.
- `trans` composes via weak-head determinism (`WHRedS.inferType`
  uniqueness: the shared midpoint's two constructor-spine reducts are
  syntactically equal, so field columns literally coincide) and the
  relation's PER laws; `whr`/`unwhr` via `WHRedS.determ_l`; `mono` via
  `mono_l`; `lift`/`unlift` via the carried `LiftEquiv` fields; `left`/
  `symm` via the PER laws.
- The typed layer (both `Pattern.IotaTyping` sites, the `Action`s, the
  `PathSpineWF` capture spines) is built ONCE, at the root pair, where
  the `PatternLeafSpine` package supplies every typing; the fold's
  output supplies the root-to-root capture relations that
  `IotaRHSDefEq` consumes.

Implementation status (2026-08-13, checkpoint `wolxmups`): the
syntactic midpoint-agreement layer is kernel-checked in `SExpr.lean` —
`Pattern.WF.arity_head`, `spine_inj`, `Params.matchesS_symb_head`,
`WHNF.ctorSpine`, `WHRedS.ctorSpine_eq`, and `WHRedS.ctorSpine_determ`
(two weak-head reductions of one term onto classified constructor
spines land on the same syntactic spine). Remaining chain work, in
order: (1) define `LRS.CtorLink`/`LRS.CtorChain` (links = `.exact`
field bundles between adjacent spines; concatenation via
`ctorSpine_determ`); (2) `CtorDefEq.toChain` by induction on the free
closure — `left`/`symm` need the link mirror (either add the
right-anchored aligned spine to `.exact`, free at both construction
sites since they pass the same head twice, or re-anchor
semantically); `whr`/`unwhr` via `WHRedS.determ_l`; the open
sub-design is `mono`/`lift`/`unlift` bookkeeping — per-field
`HasType` side conditions for `mono_l` must travel in the links
(`CtorSpineDefEq.cons` already stores `hp`), and cross-level moves
compose stored `LiftEquiv`s; if a zigzag resists `trans`/`cancelRight`
reduction, keep links at their native levels and let the consumer
rebase, since links carry their own `HasType`s. Sharpened at the mirror
checkpoint: pointwise lowering of a spine at lifted element-shapes is
NOT derivable — the cons-step's type-shape `a` is existentially bound
and need not be a lift even when the element-shape is, so the
`hliftTy`/`hlift` iffs don't apply; the chain must therefore either
carry per-link native levels with an explicit connection to the root
relation (the LiftEquiv-zigzag question), or the link's semantic
payload must be re-derived from its raw payload at consumption time.
Decide this before writing `toChain`.

**Chain-level design closure (2026-08-13, second autonomous tick).**
The `HasTypeU` inversion characterization settles the lowering
question: for `sort`/`ctor`/`indTy`/`forallE` element-shapes the
type-shape is forced to a lift-stable form (`.type`, `.indTy`,
`.sort r`), so those cons-steps lower through the node iffs after a
`mono_r_2` canonicalization; but a `lam`-shaped field's type-shape is
an arbitrary Pi-shape, no lift-shaped Pi-shape sits below it except
payload-destroying bot-forms, and pointwise lowering is therefore
impossible exactly where the rejected `Shape.WF.plift` said it would
be. Consequently per-link *semantic* payload cannot be transported to
the root level in general, and per-link processing at foreign levels
is out. The forced design: links glue at the RAW layer. Adjacent links
share their middle spine syntactically (`ctorSpine_determ`), so
cross-link field alignment reduces to aligning the two links' raw
telescopes at that shared spine, which descends from one fact —

**Lemma (C), weak constant-type coherence:** any derivation of
`Γ ⊢ .const c ls₀ ≡ .const c ls₀ : T` (more precisely: any
`IsDefEq` derivation whose endpoint is the constant) has
`T` raw-defeq-connected to `mkInst ls₀ ci.type`. Provable by direct
structural induction on the weak judgment — constant-headedness is
preserved or vacuous in every case, `defeqDF` extends the chain,
`proofIrrel` recurses into its typing premise — EXCEPT the `.extra`
case, where a registered equation whose instantiated lhs is the bare
constant would type it at the equation's type. Bare `[Params]` does
not link `env.defeqs` to `classify`, so (C) needs one new coherence
field (natural home: `Params.Semantic`, alongside `registered`):
*the stripped lhs head of every registered equation classifies as a
symbol* — i.e. ctor-classified constants are never definition heads.
The 16D instance discharges it from the same pattern-coherence that
already gives `pat_wf`. With (C), the shared-middle composition gets
its raw domain alignment (`A₁ ≡ A₁'` telescopewise from
`CHead'ᵢ ≡ CHeadᵢ₊₁` by descending both spines' carried `hPi`
conversions), and the root-level field relations compose via the
per-shape semantic argument (sort/indTy/bot free; lam via the aligned
raw premise).

**Composition impossibility map and staged resolution (2026-08-13,
same tick — RECOMMENDED DECISION, flagged for John's review).**
Checking `IsDefEq.trans'` closed the last free route: it is
sort-level-heterogeneous only, not general. The complete map: raw
cross-type composition needs general heterogeneous transitivity (=
weak type uniqueness, L4L-17); semantic composition at `lam`-shaped
fields needs the same rule inside `LamDefEq`'s raw argument premises;
per-link typed sites need it to retype intermediate spines; and (C)'s
telescope descent needs Pi-injectivity (Tier R). Every route
terminates at the same missing rule *for higher-order constructor
fields specifically*; first-order fields (`sort`/`ctor`/`indTy`/`bot`
shapes) compose by per-shape arguments that are all available today
(`LR0` type-obliviousness at the base; `IndTyHead` from target
validity; free `CtorDefEq.trans` one level down for `ctor`-shaped
fields, eliminated recursively).

**Joint-induction design, first pass (2026-08-13, third autonomous
tick).** Two candidate structures examined and one selected as the
working hypothesis:

- *Dead end recorded:* the naive co-proved statement — level-indexed
  raw domain interchange (`U_n`: two Pi-typings of a shared related
  term have raw-defeq domains, derived from adequacy at level `n`) —
  is not derivable from adequacy at any level, because adequacy's
  outputs are semantic relation facts while the lam-field composition
  consumes a *raw* retyping of arguments (`LamDefEq`'s raw premise).
  No relation-level strengthening fixes this without either stripping
  the raw premise (which the fundamental lemma's lam case needs) or
  smuggling in the full uniqueness frontier.
- *Working hypothesis — the principal-type discipline:* InferType
  completeness ("every weak derivation types its subject at a type
  raw-defeq-chain-connected to the syntactic principal type, with the
  chain constructed by the completeness induction itself, not by
  uniqueness") plus the already-proved syntactic `InferType.determ`
  gives shared-term type agreement *by determinism*: two typings of a
  shared term both chain to the SAME principal type, so their
  connection composes through it (`trans'` applies — every chain step
  is sort-typed). The open verification questions, in order: (q1) does
  completeness actually close over this judgment's 15 cases without
  uniqueness — the `extra` case consumes the registered equation's
  type, the `proofIrrel` case recurses into its typing premise, and
  `beta` needs the restored `:↑`-premised `InferType.subst`; (q2) the
  chains' sort-typed steps must convert relation facts along them
  (relation `conv` needs semantic `TyDefEq`, so each chain step's raw
  defeq must pass through adequacy or a direct semantic-validity
  argument — candidate: the chain steps are `defeqDF` side conditions
  that the completeness induction can emit in semantic form too);
  (q3) whether Pi-domain extraction from a chain still needs
  injectivity, or whether anchoring relation facts at principal types
  BEFORE unfolding to Pi-forms avoids the extraction entirely
  (determinism gives one shared Pi-form).

Consequence — dependency inversion: the InferType bootstrap (S3,
task 4) moves AHEAD of the joint-induction finalization; the design
completes against what completeness actually yields. Implementation
order for the bootstrap: (b1) the `:↑`-valued `Ctx.Subst` interface
and restored `InferType.subst`/`inst`; (b2) `InferType.whRed`
up-to-defeq; (b3) completeness; (b4) the derived `⤳* → ≡` conversions
at the root sites; then (q2)/(q3) settle the joint induction's final
statements.

**DECIDED 2026-08-13 (John): the joint L4L-16/17 route** — see the
second resolution in `plans/l4l-16-sort-inversion-decision.md`. The
staging recommendation below is retained for the record but
superseded: instead of restricting to first-order fields, the
milestone co-proves a level-indexed limited uniqueness with adequacy
in one mutual induction (uniqueness at level n from adequacy at level
n, consumed by the lam-field composition at level n+1), and L4L-17's
statements become co-deliverables. Route-independent work (chain
normalization, InferType bootstrap, O3, 16D ladder) proceeds
unchanged.

**Implementation checkpoint (2026-08-13, joint route):** the working
tree now contains the kernel-checked joint interfaces
`LR.AdequacyAt`/`LR.JointStage`/`LR.JointBuilder` and
`LogRel.LimitedUniq`. A subsequent premise audit rejected the first,
same-level builder: `AdequacyAt Γ n` alone cannot imply weak-judgment
uniqueness in an arbitrary context, particularly at bottom shapes. The
replacement records target-context well-formedness and the actual offset
bootstrap: adequacy at 0, specialized adequacy at 1, level-0 uniqueness from
the positive observations, then uniqueness at n consumed by adequacy at
n+2 and used to derive uniqueness at n+1. The SExpr inversions are
parameterized by positive-level `AdequacyAt`. The reflection decision is
also implemented:
`SExpr.mk` is conservative modulo `VEnv.EqUpToLevels`, reflecting
semantic-level equality to `VLevel` equivalence and relating every
well-formed expression to `reify (mk e)`.

The route-independent chain normalization is kernel-checked too.
`CtorExact` stores one finite native leaf; `CtorFrame` retains all
`mono`/`lift`/`unlift` transport back to the root without attempting the
invalid pointwise lowering of high-level fields; `CtorLink` combines
those two pieces; a nonempty `CtorPath` removes free transitivity; and
root `CtorView`s isolate weak-head expansion. `CtorDefEq.toChain`
handles all nine constructors, uses `WHRedS.ctorSpine_determ` at shared
midpoints, and `CtorChain.toCtorDefEq` proves the round trip. Its
`CtorChain.Algebra` elimination boundary has only native exact leaves,
composition, and root anchoring; the original nine-way closure is absent
from consumers. `CtorChain.NativeAlgebra` further pins the crucial order:
finish a native exact leaf, fold the completed result through its
`CtorFrame`, and compose only after reaching the root. This resolves the
lift/unlift uniqueness question without projecting high-level fields or
requiring uniqueness for a foreign native relation. The active joint
dependency is therefore `uniqSucc` plus the deep-`R` iota leaf: the
specialized level-one bootstrap now derives contextual raw uniqueness and
the uniqueness-aware chain consumer through path-valued stratified inversion.
There is no longer an `invZero` field or an unsound generic
`uniqOfAdequacy` obligation.

**InferType q1 resolution (2026-08-13): negative for the generic
proposal.** `InferType.app` can be constructed only after the inferred
function type weak-head reduces to a Pi. An `IsDefEq.defeqDF` conversion
connects that type to a Pi only by definitional equality; turning this into
the required reduction is precisely a Church–Rosser/inversion theorem, not
something inference completeness can emit by structural induction. The
same obstruction remains at the four root reduction conversions even with
the existing `SpineWF` packages, because their weak-head paths may contain
beta and registered steps under an arbitrary converted type. Do not restore
the deleted generic `InferType.subst`/completeness route. Under the combined
L4L-16/17 scope, implement the promised limited uniqueness and consume it
while folding the normalized constructor chain; only then restate the root
subject-reduction lemma at the exact semantic package it needs.

Superseded recommendation (α): stage the claim. Add a first-order-fields
restriction at the observation-consumption boundary (an explicit
`Params.Semantic`-level or shape-level side condition), close the
L4L-16 leaf and `sort_invS` for first-order-constructor environments —
which covers the entire D0–D2 fixture ladder (Nat, List, both tree
blocks; `Acc` is the known exception, entering only at kernel-parity
scope) — and lift the restriction at L4L-17 when
`forallE_inv`/uniqueness arrive, exactly as `pat_wf` sheds its
transitional closure. This matches roadmap §4.5 (staging is monotone
and temporary) and §2.2's "growing subset" posture. The alternative —
promoting general weak uniqueness into L4L-16 — was already rejected
by the route decision (it is Route 2's circularity). Before
implementing: confirm the restriction's exact carrier (a `WShape`
first-order predicate on ctor field shapes is the least invasive) and
record it in the ladder as an explicit stage predicate with a
rejection fixture.

Execution order for `toChain` is therefore: (a) decide/record the
first-order stage predicate; (b) `CtorLink`/`CtorChain` at the root
relation with raw-glued links; (c) `toChain`; (d) the first-order
composition lemma; (e) lemma (C) and the coherence field only if the
first-order composition still needs raw telescope alignment (it may
not: with first-order shapes the semantic layer composes without raw
support). (3) per-link
consumption: each link certifies its own iota contraction pair with
conclusions glued by `(LRS IH).trans` at the package-fixed result type,
with the root endpoints attached by `whr`-expansion.

Verification condition checked before implementation: the per-field
composition step needs `IH.DefEq x y D p a` and `IH.DefEq y z D' p a`
(same syntactic `y`, same shapes, two validity types) to compose.
**Superseded conclusion (rejected by the lambda case):** the
concrete relation is type-independent modulo validity — at `.sort`
type-shapes `DefEq` ignores its type argument entirely, at `.indTy` the
only type-dependence is the `IndTyHead` conjunct (supplied by the target
type's own validity), and at `.forallE` every consumed component
(domain reduction, domain validity, `PiDefEq`, `LamDefEq`) is carried
inside the definition. Therefore a `Retype` law — `R.TyDefEq A' A' a →
R.DefEq M N A m a → R.DefEq M N A' m a` — is provable with no new
assumptions: trivially at `LR0` (its `DefEq` never inspects the type),
by shape-case analysis with recursion into the lower level at `LRS`,
hence at `LR` for every level. With `Retype`, cross-observation field
composition would be `retype` + `IH.trans`.

**Correction (2026-08-13):** `LRS.DefEq` at a lambda observation retains
codomain validity tied to the original Pi typing, so the assumption-free
`Retype` claim is false. The implemented builder boundary is
`RawTypeUniq + LimitedUniq.LamRetype`: raw uniqueness aligns ordinary result
types, and the term-indexed `LamRetype` callback supplies exactly the
successor-level lambda case; all other shapes are structural. `PiTypeAlign`
is retained only as an optional sufficient adapter, because arbitrary valid
Pi observations need not be compatible. This is packaged by
`LRS.limitedUniq_of_typeUniq`; the offset `LR.JointBuilder.succ` now also
receives lower-level adequacy explicitly, matching the actual fixed-head
recursion dependency.

The normalized-chain audit then exposed a separate raw invariant:
constructor leaves previously allowed unrelated universe-level lists on
their two heads. Both producers already use the same semantic list, so
`CtorDefEq.exact`/`CtorExact.intro` now record `ls = ls'`. Consequently each
native leaf has an existential ordinary typed equality. The kernel-checked
`CtorPath.foldRaw` threads one recursor domain across all native links using
`RawTypeUniq`; `CtorChain.foldRaw` and `CtorDefEq.foldRaw` expose the two root
weak-head views as explicit typed callbacks. All these theorems measure at
`[propext, Classical.choice, Quot.sound]`. This proves that intermediate
links need no subject reduction; only the two roots do.

**Native/root consumer correction (2026-08-13).** The normalized
`NativeAlgebra` order remains valid, but it does not by itself close iota.
An exact handler runs at the native relation stored by a link, whereas the
recursor prefix, result functions, and final type relation are available at
the canonical root relation. A lift/unlift zigzag relates arbitrary high
extensions of a common low relation only on shapes lifted from that low
relation; it cannot project the root prefix into an unrelated native
refinement. Constant evaluation now returns `LogRel.DefEqRect` (left endpoint
self-relation, right endpoint self-relation, and cross-relation) so these
three observations remain synchronized through term-indexed retyping. The
remaining iota consumer must therefore prove the generated fixed-head
application chain at the canonical root and use native normalization only for
the raw constructor/capture boundary.

Finally, O3 is not route-independent as previously stated. The current
`IotaRHSDefEq` proposition describes the desired result, but
`PathSpineWF` plus capture alignment does not itself supply logical validity
for the fixed RHS head or the intermediate semantic Pi telescope. Its
constructor must live inside a strengthened `LE_Interp.recR` induction and
receive that head adequacy hypothesis explicitly. The head's syntactic
self-typing is now kernel-checked independently:
`Params.Semantic.closedHasTypeStrong` reifies the semantic levels and
translates the ordered-environment strong typing, and
`Pattern.IotaRule.rhsStrong` packages the registered RHS specialization.

**Heterogeneous-rule correction (2026-08-13).** The earlier principal-chain
notes above still assumed that sort-typed chain edges could be collapsed by
the primitive `IsDefEq.trans'`. That constructor has now been eliminated
from both weak and strong SExpr judgments. Conversion-aware spines use
structural concatenation, while successor Pi type validity stores
`TypeDefEqPath`, a nonempty sequence of ordinary typed equalities. Semantic
transitivity therefore remains assumption-free; collapsing a path to one raw
equality consumes `RawTypeUniq` explicitly. The contextual form is packaged
by `LogRel.ContextualRawTypeUniq` and `LR.ContextualJointBuilder`; the
level-indexed Pi inversion returns paths, and its `_collapsed` adapter uses
context well-formedness to collapse the codomain path under the extended
binder. This supersedes every earlier recommendation that used `trans'` as a
free composition rule.

**Contextual/recursion correction (2026-08-13).** A compiled skeleton of the
promised outer `LE_Interp.recR` / inner strong-derivation induction showed
that shallow `RChildren` evidence is lost in `symm` and the second half of
`trans`: semantic soundness transports the interpretation, not the recursive
provenance attached to its proof. The replacement
`LE_Interp.RDeepChildren`/`recRDeep` traverses ordinary semantic children and
grants the recursive predicate only at abstract constant edges, which is the
well-founded interface needed by an inner stratified self-typing induction.
That induction made the target-context dependency executable rather than
documentary: Pi uniqueness immediately enters `A :: Γ`, so a wrapper that
returns already-built fixed-context `JointBuilder Γ`s is circular.
`JointStage` and `JointBuilder` now quantify over all well-formed target
contexts at each level, and `HasTypeStratifiedS.forallE_inv` preserves the
strictly smaller typing depth at the binder boundary. All three additions
kernel-check and have the standard clean axiom closure.

**Bootstrap/root-closure checkpoint (2026-08-13).**
`JointStratifiedInversion` now states precisely the stratified sort/Pi facts
needed by the syntactic proof, and
`IsDefEq.uniq_of_stratified_inversion` proves contextual weak type uniqueness
by well-founded induction on maximum typing depth. The full application,
lambda, Pi, and conversion cases are kernel-checked at
`[propext, Classical.choice, Quot.sound]`. The initially exposed base boundary
has now been discharged without assuming its result: positive adequacy
propagates non-bottom sort/Pi observations across whole heterogeneous
`TypeDefEqPath`s, proves path-level sort/Pi inversion and stratified path
uniqueness, and only then collapses the paths. Thus
`LogRel.contextualRawTypeUniq_of_adequacy` and
`JointStratifiedInversion.of_adequacy` are kernel-checked, while the redundant
`JointBuilder.invZero` field has been deleted.

The same package now proves `WHRed.defeq_of_stratified_inversion` and
`WHRedS.defeq_of_stratified_inversion`, including beta and registered-rule
steps. `LRS.CtorDefEq.foldRaw_of_jointBuilder` feeds those exact two root
callbacks and the derived raw uniqueness into the normalized constructor
chain. Thus the conditional chain/root part of 16C′ is complete and clean;
the exact lambda-retyping boundary and its lower-adequacy dependency are now
implemented. The remaining proof body is the canonical-root, deep-`R`
fixed-head application chain needed at the iota leaf.

**Proof-relevant semantic-recursion correction (2026-08-13).** The
fixed-head proof does recurse through the interpretations of both the head
term and its registered type, but the first paired implementation exposed a
false interface. `LE_Interp` and its constant payload are propositions, so
proof irrelevance identifies constructor trees that chose different abstract
relations. Consequently `recRDeep₂` is sound only for results independent of
that proof choice; it cannot retain the exact evaluator branch. Focused
conversion and application probes also showed that no ordering of two
homogeneous proof trees supplies both an arbitrary converted type and the
term/type role swap needed by application.

`LE_Interp.Witness` is now the proof-relevant mirror at this internal
boundary. Every public interpretation noncomputably chooses one consistent
witness; `Witness.toInterp`, `witness_toInterp`, `Witness.mono`,
`Witness.recR`/`recRIndex`, and `Lower.realizeWitness` preserve the exact
constant relation and recursive callback while public conclusions remain
proof-independent. The layer builds and audits at
`[propext, Classical.choice, Quot.sound]`. `recRDeep₂` remains available for
proof-independent consumers, but is no longer the planned evaluator
recursor. The live adequacy constant case now destructs `hM.witness`, so its
`R` callback returns exact witnesses rather than reconstructed propositions.
`Witness.recDeep` now supplies exact ordinary and registered children for the
inner stratified induction, and proof-relevant `recDeep₂` supports term/type
role swaps without erasing either callback tree. `RHS.fixedWitness`/`fixedLowerWitness`,
`Witness.mono_l`/`closed`, and
`IotaRHSDefEq.of_nonbotWitness` carry that callback through the reached fixed
RHS head and expose it to the generated-chain consumer. The retained-tree
finite merge is complete too: `RDeepChildren.JoinLaws` states the four exact
closure laws, and proof-relevant `compat_join` constructs one synchronized
joined witness/tree through applications, binders, and constant evaluators.
`RDeepChildren.Laws`, `TypedRDeep.lam`, and `TypedRDeep.forallE` now close the
same retained package under weakening and both binders.  The conversion probe
then fixed the recursion order: `recNatRDeep`/`recNatRDeep₂` make stratified
depth the primary decrease, so a smaller conversion premise can restart on
an arbitrary exact target witness without assuming its retained tree.
`FitsRDeep`, `SoundRDeepAt`, `soundRDeepRestart`, and
`recNatRDeepSound` kernel-check the complete syntax-directed induction,
including application, lambda, Pi, and conversion.  All audit at the same
clean baseline. The remaining work is now the consumer-specific `buildP`
algebra. Its dependent-application core is isolated in the clean
`LR.adequateApp` lemma: three lower callbacks (function, argument, and
instantiated result) discharge the complete application shape join at the
standard axiom baseline. The retained self-typing probe instantiates that
interface directly. What remains is the conversion/type-relation handoff
and constant case, then consuming the rectangle along the generated
`ShapeSpine` and folding the sole adequacy leaf.

Exit measurement: `sort_invS` reaches
`[propext, Classical.choice, Quot.sound]`. Record that
`SExpr.forallE_inv` and `SExpr.sort_forallE_inv` went clean at the same
moment; their VExpr reflection is a joint L4L-16 co-deliverable at 16E.

### L4L-16D — live-environment instance, staged (the real risk)

The only segment never executed end-to-end. De-risk with a thin vertical
slice before full coverage:

- **D0 (slice) — complete 2026-08-14 in the active working tree:** the
  generated Nat block's zero/successor iota rules plus the checked
  `d0def : Nat := Nat.zero` declaration run through complete
  `Params` + `Params.Semantic` values, with `d0SortInvS` instantiated.
  `SExprParamsD0.lean` has no local admission, its 122-job Lake target is
  green, and the exact inherited endpoint closure is pinned in-source.
- **D1 — delivered 2026-08-15 (working tree), except the quot semantic
  instance:** `SExprParamsD1.lean` (187 decls, no local admission).
  Mutual-definitions half complete end to end: first live
  `VDecl.WF.mutualDef` (genuine forward reference inside the block; a
  three-layer unfolding chain through `d0def` exercises
  `IsDefEqStrong.defn` in sequence), D0→D1 transport functor with the
  previously-vacuous `const`/`defn` cases now live, full
  `Params.Semantic` with the Nat iota sites replayed against `d1Env`,
  endpoint `d1SortInvS` pinned (closure = D0's set + named D1-local
  `native_decide` observations; `sorryAx` inherited from 16C′ only).
  Quotient half: environment layer delivered and pinned sorryAx-free
  (`d1qEnv_wf` with a checked `VDecl.WF.quot` step,
  `d1qEnv_defeq_quot`), plus the kernel-checked forcing lemma
  `quotPattern_forces_ctor_classification`; the quot
  `Params`/`Params.Semantic` instance is blocked on a 16C′-owner
  interface decision (guardrail #3): any WF classifier forces
  `Quot.mk = .ctor 3`, and `Semantic.ctor`'s unrestricted level
  quantifier then violates `CtorBundle.hu0` at Prop instantiations —
  the punit disqualification biting a live constructor. Candidate
  repairs recorded at `SExprParamsD1.lean:2703–2755`
  (typing-conditional `hu0`, or well-sorted-instantiation restriction
  of `Semantic.ctor`); independently the quot site-check needs
  stuck-`Quot` injectivity (L4L-18A′ strength). Take the interface
  decision before any further quot attempt.
- **D2:** ordinary/block inductive rules via `AssembledPat`. **The new
  mathematics is done (probe-proved 2026-08-15, kernel `decide` only —
  no `native_decide`):** `plans/probes/probeD2-nonoverlap.lean` proves
  the four union-level laws in exact `Params`-field shape under a
  single `ExtSeparation` hypothesis (self/block/uniqueness/pairwise
  separation — each field a fixture obligation, `decide`-dischargeable
  for literal-name fixtures), the cross-term engine
  (`SimplePattern.HeadSep.inter_subpattern_none`), and a falsity
  witness showing the hypothesis-free `pat_uniq` is unprovable. The
  real cross-term case is block-rule vs extension-rule; cross-inductive
  pairs inside one block were already covered by `IotaPat.pat_uniq`.
  The demo instantiates the whole family on the mutual
  PatTree/PatForest block + quot extension. **Landed 2026-08-15**:
  Parts 1–3 in `Theory/Typing/InductivePatternEnv.lean` and the demo
  in `InductivePatternFixtures.lean`, strictly additive, all
  `#guard_msgs`-pinned (engine laws at `[propext, Quot.sound]`);
  `Lean4Lean.Theory` gate green; D0/D1 rebuilt downstream with pins
  re-verified. **D2 fixture delivered 2026-08-15 through the
  structural layer:** `SExprParamsD2.lean` (1033 lines, 75 decls, no
  admission, 9 pins) — `d2Env` extends d1Env with a *checked* mutual
  block step (`VDecl.WF.inductBlock`), and `d2Params` is the first
  complete structural `Params` over a live block-inductive
  environment. It uses the Tree/TreeList block, not PatTree/PatForest,
  because only `treeGeneration` carries a proved `gen.WF` certificate.
  All four non-overlap laws discharged through the freshly landed
  Theory lemmas by kernel `decide` (no `native_decide` anywhere in the
  pattern layer) — the union machinery worked as designed on first
  live contact. Remaining D2: `Params.Semantic`'s
  `iotaSite`/`registered` for the 5 block rules plus `ctor`/`defn` via
  the D1→D2 transport clone. **CORRECTED 2026-08-15: not pure volume.**
  Tree's parameter makes each rule's iota `checked` discharge (one
  `.defeq` of the ctor-side vs rec-side parameter capture per rule) a
  stuck-inductive-application-injectivity obligation — L4L-18A′
  strength (probeG `iotaCheck_param`), so D2's semantic layer closes
  only conditionally on one named per-rule premise. The measured
  volume figure was also an undercount: ~640 lines was `iotaSite` for
  TWO rules; a new rule's full cost including the 6-theorem
  `registered` tower is ~1400–1700 lines (D0's Nat towers measure
  1166/1433), i.e. ~7000–8500 for five rules by hand — hence the
  generic replay lemma below is mandatory, not optional. Original
  record: ~640 lines/rule of evidence-rich replay over an
  8-argument major at `uvars = 2` (large elimination adds the motive
  universe; D0/D1 only ever saw `uvars = 1`). Forcing lemmas
  `d2Pat_block_rule`/`d2Registered_obligation` pin both fields as
  obliged. **Cost-control decision to take before D3:** the per-rule,
  per-fixture replay is what makes D2–D4 expensive; a generic replay
  lemma parameterized over the generation certificate would retire all
  five at once and pay off again on D3/D4 (the generic-instance design
  doc reaches the same conclusion from the other side, and warns that
  iota *check* discharge — one check per parameter and per index —
  needs stuck inductive-application injectivity, never exercised
  because Nat has neither parameters nor indices; Tree has a
  parameter, so this bites exactly at D2's `iotaSite`).
- **D3:** nested rules as registered equations only (per roadmap).
- **D4:** registered structure eta from the L4L-15B registry.

Explicitly OUT of L4L-16: constructing Theory's `Params`/
`Params.Extension.join` live instance (consumed only by
`IsDefEq.church_rosser`; needs L4L-17-strength inversion fields). It
moves to L4L-18A′. The roadmap's §2.1 "Not claimed" paragraph should be
amended accordingly.

### L4L-16E — promotion (recon executed 2026-08-15)

Executable checklist with full citations: `plans/l4l-16e-promotion-map.md`
(move-map, allowlist edits, gate table with the expected re-pin sets,
type-checked draft statements in `plans/probes/CoDeliverableDrafts.lean`
and `plans/probes/SExprCounterpartDrafts.lean`).

Move the consumed modules out of `Experimental/`, close public
`IsDefEqU.sort_inv` from the instances, shrink the allowlist 22 → 21 at
the promotion checkpoint (execution step 6; step 7's co-deliverables
then take it to 17), add the missing `#guard_msgs`/`#print axioms` pins
for the promoted roots (none exist today because Experimental is
ungated), and take the digama reconcile-or-defer decision (prepared
analysis with defer recommendation:
`plans/l4l-16-boundary-digama-drift.md`). The recon surfaced items the
plan had not assigned; they are 16E work items now:

- Both co-deliverables already exist as sorried statements in the
  trusted tree — `IsDefEqU.weakN_iff`
  (`Theory/Typing/UniqueTyping.lean:171`, backward direction proved,
  forward/strengthening open) and `WF.registeredStructureHeadInversion`
  (`Theory/Projection.lean:3518`). Nothing needs drafting; 16E proves
  them and re-pins the ~10 downstream guards that flip.
- **`weakN_iff` forward — design pass executed 2026-08-15; verdict:
  research-grade, not closable inside 16E** (route decision + staged
  obligations: `plans/l4l-16-weakn-design.md`; W0–W8 type-checked in
  `plans/probes/probeE-weakn.lean`). Chosen route: SST —
  de-circularized stratified standardization on the Theory side; the
  forward direction assembles in ~15 lines from three staged lemmas,
  but their cores (`NormalEq.weakN_inv` mutual with `trans` on a
  (depth, meas, derivation) measure; per-depth CR re-founding) are 3–6
  focused weeks, after the 16C′ endpoints and the 18A `.extra` holes.
  Rejected routes carry machine-checked obstructions (W0
  trans-midpoint re-lift gluing witness, proved; semantic descent
  impossible by relation design — bot shape relates all terms;
  Theory-CR circular definitionally and at the `Params` oracle
  fields). Banked now at `[propext, Quot.sound]`: W0 and W1
  (`strengthen_of_witness`, forward under inhabited insertion).
  **Ladder attacked the same day — W2 and W3 are PROVED**
  (`plans/probes/probeE2-weakn-w2w3.lean`, exit 0, no sorries in the
  probe; closures `[propext, sorryAx, Classical.choice, Quot.sound]`
  with every `sorryAx` traced to four named upstream stubs). Headline
  correction: W2/W3 are not "real work" — they are *consumers*, and
  the design doc's dependency arrow was inverted (W3 uses W2, not the
  reverse; W2's only non-elementary input is `InferType.exists`, i.e.
  the W6 CR core). Both statements were *strengthened*: probe E's
  `hA : IsType` / `hF` hypotheses are redundant — which matters,
  because the SST assembly's caller does not have base-context typing
  before strengthening. Blocking delta discovered: the bare-`VEnv.WF`
  forms are not provable today — the engine is `[Params]`-generic and
  needs `[Params.Extension]`, so W2/W3 ride on the same
  generic-instance debt as W8 and `sort_inv` (see below). Bonus
  de-circularization: `OnCtx.weakN_inv` (UniqueTyping.lean:198), a
  direct consumer of the target sorry, is re-proved from
  `IsType.weakN_inv_ex` alone. Revised remainder: 2.5–5 weeks serial,
  or **8–11 staged agent sessions**, with W5+W6 (the coupled
  `NormalEq`/CR cores) carrying essentially all residual risk. W4's
  route is settled as option (a) `Pattern.Action` packaging (`meas` is
  lift-invariant and a rule RHS may exceed the redex, so neither
  `meas` nor size bounds the payloads). One newly-scoped ~1-session
  piece de-circularizes W2 alone: re-prove `InferType.weakU_inv` by
  size induction with a type-level strengthening premise.
  **DECISION REQUIRED:** re-scope `weakN_iff` (and the dependent
  `registeredStructureHeadInversion` fields that consume it) off the
  16E gate into an L4L-18A′-coupled slice — both design passes
  recommend yes; 16E's allowlist exit count then lands at 19, not 17.
- **`registeredStructureHeadInversion.constructor_name_inv` /
  `constructor_inv` are false as stated** (axiom-headed major and
  defn-alias counterexamples; `TrProj` constrains only the major's
  type, and the safe Verify consumer's `whnf`+`ctorInfo` facts never
  reach the Theory statement). Repair with a head-classification
  premise before proof work; budget the consumer-side change.
- **Pre-promotion sorry closure step (new):** the four off-path
  `SExpr.lean` sorries (:3810 `WHRed.weakU_inv` `.extra`; :4033
  `WHRedS.defeq` — superseded by `defeq_of_stratified_inversion`,
  delete/restate and migrate its two consumers; :4136/:4202
  `InferType(S).hasType`) do NOT close with the leaf and block the
  module move; they get their own step before promotion.
- **Instance generalization — design pass executed 2026-08-15;
  recommendation: neither D4's endpoint nor a 16E step, but a named
  successor milestone (L4L-16F)** (`plans/l4l-16-generic-instance-design.md`,
  staged obligations R0–R9 type-checked in
  `plans/probes/probeG-generic-instance.lean`). `sort_invS` holds at
  `[Params.Semantic]`; public `sort_inv` quantifies over arbitrary
  `VEnv.WF env`. A *conditional* instance was checked and refuted as a
  route: `adequacyAt` quantifies over all derivations and `mkS`
  demands `Semantic.ctor` at every `constDF` node of the arbitrary
  input derivation, so the restriction cannot be moved onto the goal —
  a conditional instance just restates the fixture ladder. Banked
  results: promotion is one instance wide (R0); the syntax transport
  functor is generic in `univs`-equality (R1 — deletes ~1200 lines of
  D0/D1 boilerplate and pays off again on D2–D4, so land it BEFORE
  more fixture work). Attackable now without any interface decision:
  R2 (per-step extension theorem — the D-ladder's transport pattern
  literally IS the induction step, with only five new-content fields
  varying per rung), R3 (classify/`pat_wf` packaging), R4
  (`ExtSeparation` from history freshness — 6 new lemmas; provably not
  droppable per `separation_is_necessary`), R5 (`defn` at `uvars > 0`).
  Note `structureEta` is vacuous in all three existing instances —
  never once exercised. **Circularity trap recorded:** the generic
  construction must NOT consume Theory's `BlockGenerationChecked.pat_wf`
  — it carries `sorryAx` through `IsDefEqU.trans` → `uniq` → the
  sorried `sort_inv`.
  **New hard constraint on the entry point (proved 2026-08-15,
  `plans/probes/probeK-deltarank.lean`): `VEnv.WF` admits δ-cycles.**
  `VDecl.WF.mutualDef` (`Theory/Typing/Env.lean:28-32`) adds every block
  constant BEFORE checking any block value, so
  `mutual def a : Prop := b; def b : Prop := a end` is a well-formed
  history — the probe constructs it, proves both `VEnv.Ordered` and
  `VEnv.WF` for it, then proves no δ-rank function can exist for it.
  Consequences: (i) the δ-rank the 16C′ leaf needs cannot be derived
  from `Params.henv` and must be `Params` fields; (ii) a generic
  `VEnv.WF → Params` construction therefore CANNOT discharge those
  fields in general — 16F must either exclude cyclic definitions from
  `Pat` (handling them through `Semantic.registered` as opaque
  constants) or carry δ-acyclicity as an explicit environment
  hypothesis. Decide that at 16F's design, not at implementation.
  Independently worth noting: a δ-cyclic definition makes δ-reduction
  non-terminating, so this is a point where the VEnv model is more
  permissive than the kernel it models.
- **`CtorBundle.hu0` — recommendation: delete the field outright**
  (supersedes both candidate repairs recorded in the D1 quot record).
  Banked evidence: `hu0_impossible_at_prop` (under type uniqueness no
  `CtorBundle` can satisfy it for a Prop-typed constructor — the wall
  is intrinsic, not a fixture artifact) and `propWitness_of_ctor_zero`
  (the Prop typing is free from the bundle's own equality, so no
  replacement field or premise is needed). The wall is far wider than
  D1 recorded: not just `Quot.mk` at `[.zero]` but every constructor
  of a Prop-sorted inductive (`Eq.refl`, `And.intro`, `Acc.intro`) at
  *every* instantiation, since a constructor's type ends in its
  inductive type and `imax _ 0 = 0`. **SUPERSEDED 2026-08-15: the
  deletion is REFUTED by the executed discriminating experiment**
  (`plans/probes/probeA1-hu0.lean`, run at both consumption sites).
  The ADQ site is free (`u ≠ .zero` is derivable there from the
  ambient `.indTy`-shaped interpretation — probe P4), but
  `build_spine`'s post-deletion statement is FALSE for Prop-sorted
  ctor-classified pattern-argument heads: `Matches.app` hard-codes the
  `.ctor'` spine entry, whose realization forces
  `.indTy.HasType .type`, provably impossible at Prop (probe P2). Root
  cause: the shape algebra's proof-irrelevance law
  (`WShape.HasType.proofIrrel`) requires `.indTy` non-Prop-sortedness,
  and `hu0` is that law's syntactic mirror — relaxing the `hasType`
  indTy row makes `proofIrrel` false. Landing any resolution therefore
  needs a DESIGN, not a deletion: either a Prop-branch at the
  Matches/classification level (not expressible in `Pattern.WF`'s
  classify-only signature) or exclusion of Prop-recursor iota patterns
  from `Pat` with a matching nonzero-sort law. Consequently D1's
  quotient half remains blocked on that design (obstruction 1 stands),
  in addition to obstruction 3's stuck-`Quot` injectivity (L4L-18A′);
  only obstruction 2 would dissolve under any resolution that keeps
  the pattern in `Pat`. The dead `Params.ctor_ty` re-export was
  deleted independently (zero consumers).
- Mechanical but previously unlisted: regenerate
  `Audit/SorryFrontier.lean`'s import block at promotion (else the
  moved modules silently leave the audited surface); resolve the
  `Experimental/UniqueTyping.lean` filename collision (fold into the
  adequacy module or rename); consider the `SExpr.Params` rename for
  the `Lean4Lean.Params` vs `VEnv.Params` near-collision during API
  stabilization.

### L4L-17′ — re-scoped

1. **Reflection first** (already the roadmap's position, now sharper):
   decide conservativity-lemma vs adequacy-restated-on-VEnv. Note `mk`
   is a proved retraction (surjective), so naive injectivity is
   unavailable; any faithfulness statement is modulo `≈`.
2. Reflect `forallE_inv_stratified` and `sort_forallE_inv` (SExpr halves
   already delivered by 16C′).
3. `weakN_iff` (forward direction) and
   `registeredStructureHeadInversion` — no SExpr counterparts yet; and
   whatever Option B promoted, generalize here.
4. Re-run `uniq`/`uniqU` and downstream guards (unlocks the transitional
   closure: `pat_wf`, projection consumers).

### L4L-18A′ — grows, honestly

Theory `NormalEq.parRed` holes (as before) **plus** the work moved here:
Theory-side live `Params`/`Params.Extension.join` instance (its four
structEta/forallE fields now supplied by L4L-17 outputs), and only then —
if any promoted statement still needs it — the SExpr Church–Rosser mirror
(S6). Expected outcome: S6 is simply deleted along with `CRDefEq` if no
promoted API consumes it.

## 4. Execution order and checkpoints

Each numbered item is one committed checkpoint (jj makes this cheap);
Experimental stays buildable at every pause point.

1. **Stabilize & checkpoint L4L-16A(+)**: single writer designated
   (§5.1); commit the current working copy as the L4L-16A checkpoint with
   the roadmap corrections from §1.2 (plift, six fields, S1/S7–9
   verdicts, S6 move). Gated surface is untouched by the diff, so §6
   gates pass as-is; run them anyway.
2. **16B′ cleanup** (delete/restate items — small, mechanical).
3. **16C′ joint interface + O1 normalization** (**kernel-checked in
   the current working tree**: limited uniqueness contract,
   level-indexed adequacy/inversions, `mk` reflection boundary, and
   `CtorLink`/`CtorChain`/`toChain`).
4. **16C′ O3 + O2 leaf closure.** The path/direct stratified inversion
   bootstrap, generic uniqueness theorem, chain consumer, and root subject
   reduction are kernel-checked; the exact successor lambda-retyping and
   synchronized endpoint rectangle are implemented. Complete the canonical
   deep-`R` fixed-head application chain and fold the leaf → measured clean
   `sort_invS`; SExpr `forallE_inv`/`sort_forallE_inv` recorded clean.
5. **16D0 slice**, then **16D1–D4** as separate checkpoints.
6. **16E promotion** + allowlist 21 + digama decision.
7. Land the former L4L-17 statements as the joint 16E co-deliverables.

Rough effort guess (calibrate against how fast 16A went): 1–2 days for
1–2; the 16C′ spike+closure is the genuine unknown — timebox the spike,
expect days not hours for closure; 16D is 1–2 weeks of mostly
certificate plumbing; 16E days.

## 5. Anti-spin guardrails (process)

1. **One writer.** Exactly one session edits `Experimental/` at a time.
   Right now at least two AI sessions plus an auditor share this working
   copy; pick one (the pts/3 codex session and pts/11 Claude session
   cannot both continue).
2. **Checkpoint every kernel-checked sub-result.** No more 18-hour
   uncommitted mega-changes; the ladder's one-claim-per-checkpoint rule
   applies to Experimental work too.
3. **Two-strikes rule.** Two failed repair attempts on the same
   obligation → stop, write the obligation as a Lean statement in the
   plan file, and make an interface decision before more proof text.
4. **Roadmap is status, not lab notebook.** Move the L4L-16C attempt
   narrative (~100 lines) into `plans/l4l-16c-adequacy-log.md`; the
   roadmap keeps a 5-line status per slice. (The narrative was valuable —
   it is how this audit found the root cause — it just belongs in a log.)
5. **Measure, don't assert, closures.** The roadmap carried three stale
   claims about this work (plift `stop`, five fields, `WHRed.subst`
   `.extra` open). Add a tiny uncommitted probe file with
   `#print axioms` for the route waypoints and re-run it at every
   checkpoint until 16E's real guards exist.
