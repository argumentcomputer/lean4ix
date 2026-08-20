# L4L-16E promotion map — executable checklist

*(The 2026-08-15 same-day addendum was folded into the body on 2026-08-20;
sorry counts below re-measured 2026-08-20.  Line references drift — always
re-locate by declaration name.)*

Produced 2026-08-15 by a read-only recon session over the working tree
(all citations verified against the live sources; draft statements
type-checked against the current oleans). Companion to the 16E section
of `plans/l4l-16-completion-plan.md`. Durable probe copies of the draft
statements: `plans/probes/CoDeliverableDrafts.lean`,
`plans/probes/SExprCounterpartDrafts.lean`.

Headline correction to the plans: **both joint co-deliverables already
exist verbatim in the trusted tree with `sorry` bodies.** 16E does not
draft them; it proves them (and re-pins their guards).

## (a) Co-deliverable dossiers

### A1. `IsDefEqU.weakN_iff` — forward direction. Verdict: see `plans/l4l-16-weakn-design.md` (research-grade; re-scope decision pending).

- Statement exists at `Lean4Lean/Theory/Typing/UniqueTyping.lean:171-174`;
  the backward direction is proved (`h.weakN henv W`); the sole
  obligation is the forward implication (strengthening).
- Promised at roadmap.md 16E co-deliverable list;
  l4l-16-completion-plan.md ("no SExpr counterparts yet");
  l4l-16-sort-inversion-decision.md; allowlist entry
  `Lean4Lean/Audit/SorryFrontier.lean:173`.
- What hangs on it (already written, proved modulo this one sorry): the
  inversion suite UniqueTyping.lean:176-368 (`VExpr.WF.weakN_iff`,
  `IsDefEq.skips`, `weakN_iff'`, `OnCtx.weakN_inv`,
  `HasType/IsType.weakN_iff`, the `weak'_iff` family,
  `SpineWF.weakN_inv/weak'_inv`); `VLocalDecl.weakN_iff`
  (Theory/LocalContext.lean:98); ~20 sites in
  Theory/Typing/ChurchRosser.lean (:609-1701); Verify
  (Typing/ConditionallyTyped.lean:72,126; Typing/Lemmas.lean:377). CR's
  `VEnv.Params.structEta_weakN_inv` field is documented as the
  structure-family specialization, supplied from this co-deliverable at
  L4L-18A.
- Route analysis:
  - Semantic route: adequacy endpoints return judgment-level facts only
    at observation heads (sort/Pi/ctor); strengthening of an arbitrary
    pair is not an observation extraction. Interpretation-level descent
    exists (`LE_Interp.weak'_iff`/`weak_iff` ShapeLogRel.lean:5893/5929;
    `LogRel.LiftEquiv` + `lift/unlift` :10745-10885) but no bridge back
    to arbitrary judgments.
  - Derivation-induction route: SExpr weak `IsDefEq` has primitive
    homogeneous `trans` (SExpr.lean:1263) and `defeqDF` (:1273) — the
    trans midpoint is an arbitrary non-lift term (the documented
    "genuinely untyped midpoints" wall). Chain normalization
    (`WHRedS.ctorSpine_determ`) covers classified constructor heads
    only; generalizing is standardization ≈ L4L-18A. Note
    `WHRed.weakU_inv`'s `.extra` case is itself sorried
    (SExpr.lean:3810) and is a prerequisite of any derivation-induction
    attempt.
  - Theory-CR route: circular (ChurchRosser.lean consumes `weakN_iff`).
- No proof sketch exists anywhere in plans/. Recommendation: schedule a
  dedicated design pass (two-strikes rule) BEFORE the 16C′ leaf closes;
  do not treat as post-leaf cleanup.
- POSTSCRIPT (later 2026-08-15): the design pass ran —
  `plans/l4l-16-weakn-design.md` supersedes this dossier's route
  analysis. Verdict: research-grade, 3–6 focused weeks via the SST
  route; W0 wall witness machine-checked; W0/W1 proved at
  `[propext, Quot.sound]`; re-scope recommendation on file.
  Corrections to this dossier: `Theory/Typing/HeadReduction.lean` was
  missing from this map (sorry-free-but-tainted `WHRed(S).weakU_inv`,
  standardization `StRed`/`ParRedS.standard`, `reduce_sort/forallE`,
  syntax-directed `InferType` with strengthening); the sorried
  `.extra` case is the SExpr mirror only — Theory's is
  proved-but-tainted; the `HasType.skips` repair idea above is
  circular (it is a corollary of the target, UniqueTyping.lean:180-187
  / 225-228); the pre-171 suite additionally rides on Injectivity's
  three sorried endpoints.

### A2. `VEnv.WF.registeredStructureHeadInversion`. Verdict: real work, shallower than A1 — AFTER a statement repair.

- Statement exists at `Lean4Lean/Theory/Projection.lean:3518-3520` over
  the four-field record at :3465-3512 (`weak'_inv`, `unique`,
  `constructor_name_inv`, `constructor_inv`). Design docstring
  :3449-3464: proof uses `IsDefEqU.weakN_iff` + injectivity of
  registered inductive heads. Allowlist entry SorryFrontier.lean:174.
- Per-field:
  - `weak'_inv`: mostly consumption once `weakN_iff` closes
    (`IsDefEqU.weak'_iff` UniqueTyping.lean:231, `SpineWF.weak'_inv`
    :327, `HasType.skips` :226). Residual real step: registered
    inductive-head injectivity below a lift (reflected indTy-observation
    inversion) — implied machinery, not separately listed anywhere.
  - `unique`: consumption + plumbing given `uniq`/`uniqU` + head
    injectivity + `projectionCodes` congruence. `TrProj` fields
    :3183-3199.
  - `constructor_name_inv` / `constructor_inv`: **FALSE AS STATED.**
    `TrProj` constrains its major only via `majorType`
    (Projection.lean:3193) and `VEnv.WF` admits any declaration history
    (axioms, defs). Counterexamples: `axiom ax : S` with
    `major := .const ax ls`, `constructorArgs := []`, reflexive defeq
    forces `ax = view.constructorName`; a `def mkAlias := S.mk` applied
    to a full spine refutes `constructor_inv` (:3212 demands
    `constructor_name_eq`). The Verify consumer is safe only because
    its head survived `whnf` AND a `ctorInfo` lookup
    (Verify/TypeChecker/WHNF.lean:59-83) — facts the Theory statement
    never receives. REPAIR FIRST: add a head-classification premise
    ("runtime head is the constructor of some registered view") and
    budget the consumer-side change that supplies it. Same failure
    class as the 2026-08-13 S1/S7-S9 audit.
- Consumers: `TrProj.weak'_inv`/`defeqDFC`/`uniq`
  (Verify/Typing/Lemmas.lean:679-686, 987-995), `Inner.whnf` projection
  path (Verify/TypeChecker/WHNF.lean:63, 81).

## (b) Promotion move-map

The plans never pin target paths; targets below are derived from the
constraints (audit surface = prefixes `Lean4Lean.Theory`/`.Verify`,
SorryFrontier.lean:129; Theory must not import Verify; promotion
requires zero sorries + stable API).

| Module (current, Experimental/) | Suggested target | Notes |
|---|---|---|
| `SExpr.lean` | `Theory/Typing/SExpr.lean` | 2 live sorries (measured 2026-08-20) must close/delete first: :4206 `WHRed.weakU_inv` `.extra` (documented off-path, in-source); :4429 `WHRedS.defeq` (the gate-path admission — live sites all adequacy-trunk, they shed with the 16C′ leaf) |
| `ShapeLogRel.lean` | `Theory/Typing/ShapeLogRel.lean` | zero live sorries (re-measured 2026-08-20) |
| `ShapeLogRelAdequacy.lean` | `Theory/Typing/ShapeLogRelAdequacy.lean` | 1 sorry (`LR.iotaWitnessStep`, :8680 — the 16C′ leaf; re-measured 2026-08-20) |
| `UniqueTyping.lean` | fold into the adequacy module, or rename (e.g. `SExprUniqueTyping.lean`) | FILENAME COLLISION with `Theory/Typing/UniqueTyping.lean`; holds one compat theorem `IsDefEqStrong.uniq_sort` |
| `SExprParamsD0.lean` (and D1+) | `Verify/Environment/SExprParamsD0.lean` (or Tests) | imports Verify fixtures — cannot go to Theory/ (Theory-imports-Verify gate) |

Stays parked in Experimental/: NormalEq, ParallelReduction (L4L-18A),
Stratified, StratifiedUntyped, Stronger, CoinductiveLogRel,
DomainTheory, LogRel, StepIndexed, MoreStepIndexed, Thierry, Thierry2.

Consumers to touch (verified: NOTHING in Lean4Lean/, Main.lean, or
Tests imports `Lean4Lean.Experimental` today):

1. The moved files' own `import Lean4Lean.Experimental.*` lines.
2. `plans/probes/*.lean` import headers — or retire the probes: 16E
   replaces the probe practice with in-source `#guard_msgs` pins.
3. `Lean4Lean/Audit/SorryFrontier.lean:1-75` import block — REGENERATE
   per the in-file recipe (:97-101) so the new Theory/Verify modules
   enter the audited surface (the audit only sees imported modules —
   without this the moved modules silently leave the surface); update
   the ":103-104 Experimental is intentionally not imported" comment.
4. Optionally `Lean4Lean/Theory.lean` root import list.
5. No lakefile edit needed (globs cover the targets; the Experimental
   lib entry stays for the residue; CI's
   `lake build Lean4Lean.Experimental` still works).

Collision risks (checked): no hard full-name clashes. SExpr's
`Lean4Lean.Params` (SExpr.lean:5,:24) vs ChurchRosser's
`Lean4Lean.VEnv.Params` first co-import inside the regenerated
SorryFrontier — co-importable but confusing; consider renaming SExpr's
to `SExpr.Params` during API stabilization. `Pattern.WF` is a new def
on Theory's `Pattern` (no existing `WF` — verified). `Classification`,
`WShape`, `SLevel`, `TShape`, `Valuation`, `LogRel`, `LE_Interp` have
no Theory/Verify counterparts. The only hard collision is the
`UniqueTyping.lean` FILE name.

## (c) Allowlist artifact + exact edits

Artifact: `Lean4Lean/Audit/SorryFrontier.lean` — compiled `run_cmd`
audit (:201-218) comparing `sorryAx`-referencing declarations in the
`Lean4Lean.Theory`/`Verify` surface against `allowlist : Array
Lean.Name` (:134-188), currently exactly 22 entries (10 Tier V + 6
Tier R + 6 Tier F). Enforced by `lake build
Lean4Lean.Audit.SorryFrontier` (roadmap §6 gate; CI).

- 22 → 21 (execution step 6, promotion): delete line 170,
  `` `Lean4Lean.VEnv.IsDefEqU.sort_inv, `` — forced and safe once the
  real proof lands (the audit fails in both directions).
- Full 16E exit (execution step 7, co-deliverables): additionally
  delete lines 171-174 (`forallE_inv_stratified`, `sort_forallE_inv`,
  `weakN_iff`, `registeredStructureHeadInversion`) → **17 entries**
  (Tier R residue: `NormalEq.parRed` only). The roadmap's "22 → 21"
  describes step 6 only. Update the Tier R comment block (:169) and the
  roadmap frontier row alongside.

## (d) Gates

"§6" lives in roadmap.md §6 "Gates and process" (:863-932), not the
completion plan. Verbatim command block:

```
lake build Lean4Lean.Theory Lean4Lean.Verify
lake build Lean4Lean.Audit.SorryFrontier
lake build
nix build --accept-flake-config .#lean4lean .#lake-dependency
nix flake check --accept-flake-config --print-build-logs
nix fmt --accept-flake-config -- --check flake.nix
git diff --check
```

| Gate | Today | 16E action |
|---|---|---|
| Theory+Verify build | expected green (working-tree delta is Experimental/+plans/ only) | every `#guard_msgs` sorryAx pin that flips FAILS this build until re-pinned. Expected re-pin set: Theory/LocalContext.lean:137-141; Theory/Projection.lean:3522-3526; Verify/Typing/Lemmas.lean:1703-1741 (4 pins: `TrProj.weak'_inv`/`defeqDFC`/`uniq`/`structuralLaws`); Verify/TypeChecker/InferType.lean:1057-1060 (`inferProj.WF`); InductivePatternWF.lean:942-947 (`pat_wf`, sheds at the uniq/uniqU re-run) |
| Sorry frontier | green at 22 | re-run after each allowlist edit (21, then 17) and after the import-block regeneration |
| Default `lake build` | expected green | promoted modules join automatically |
| Nix builds / flake check / fmt | last verified at the L4L-15R checkpoint | rerun at the promotion checkpoint (flake gate builds for real) |
| `git diff --check` | measured green today (exit 0) | keep green |

Roadmap §6 "Additionally" items binding 16E: new theorem roots need
checked `#print axioms` output — none exist today because Experimental
is ungated; candidates = `sort_invS`, `LR.adequacy`, `LE_Interp.sound`,
`IsDefEqStrong.mkS`, `SExpr.forallE_inv`, `sort_forallE_inv`, the
D-ladder endpoints (the AxiomProbe list is the ready-made inventory).
`rg '^import Lean4Lean.Verify' Lean4Lean/Theory` must stay empty.
Theory API changes additive-only. Non-command gate due at this
boundary: the digama reconcile-or-defer decision — prepared analysis
with defer recommendation already in
`plans/l4l-16-boundary-digama-drift.md` (sign-off, not new work).

## (e) Items the plans missed (now assigned in the completion plan)

1. `constructor_name_inv`/`constructor_inv` statement repair (see A2)
   — repair BEFORE proof work, plus consumer-side premise supply.
2. `weakN_iff` forward has no recorded proof design — schedule the
   design pass early; `WHRed.weakU_inv` `.extra` (SExpr.lean:3810) is a
   prerequisite of any derivation-induction attempt and is currently an
   off-path deferral.
3. Promotion-blocker recount (2026-08-20): `SExpr.lean` now carries
   exactly TWO sorries — `WHRed.weakU_inv` `.extra` (:4206, documented
   off-path; needs its own pre-promotion step) and `WHRedS.defeq`
   (:4429, the gate-path admission; its live sites are all
   adequacy-trunk and shed with the 16C′ leaf).  The former four-sorry
   list (:3810/:4033/:4136/:4202) is stale: `InferType.hasType`/
   `InferTypeS.hasType` were deleted (zero consumers), as were
   `InferTypeS.weakU_inv`, `LRS.iotaDefEq_of_exactAt`,
   `LR.iotaActions_of_exact`.  `ShapeLogRel.lean` has zero live sorries;
   `ShapeLogRelAdequacy.lean` has one (`LR.iotaWitnessStep`, :8680).
4. SorryFrontier import-block regeneration at promotion (else silent
   audit-surface loss).
5. `UniqueTyping.lean` filename collision; `Lean4Lean.Params` vs
   `VEnv.Params` near-collision first co-imports in the regenerated
   frontier.
6. The instance-generalization step: resolved by the design pass
   `plans/l4l-16-generic-instance-design.md` — named successor milestone
   L4L-16F ("live instance"); note its `hu0`-deletion recommendation has
   since been refuted by probeA1 (`plans/probes/probeA1-hu0.lean`).
7. Doc rot: "22→21" vs 17-at-full-exit (see (c)); completion-plan
   execution item 6 should point at the prepared digama note.
