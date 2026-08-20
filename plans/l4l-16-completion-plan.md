# L4L-16 completion plan

Date: 2026-08-13 (audit window 04:50–05:10 EDT)
Author: fresh audit session (Claude), commissioned because L4L-16 "looks
stuck or spinning."

Trimmed 2026-08-20: executed/superseded sections removed (measured-state
audit, root-cause analysis, the completed 16B′ block, executed execution-order
items); full text in git history.

## 3. The re-cut

Principle: **L4L-16's exit is the promotion of `sort_inv` at the accepted
closure. Everything not consumed by that path moves to the milestone that
consumes it.**

### L4L-16C′ — close the leaf by decision, not accretion

Superseded 2026-08-20: the live 16C′ record — program status and the
machine-checked refutations that ended 16C′-as-scoped — is `plans/roadmap.md`
§5. The surviving session residue (the binding N2 decision, the
vacuity-discipline rule, the banked consumers) is
`plans/l4l-16c-buildp-premortem.md`.

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
  research-grade, not closable inside 16E.** Route decision (SST),
  staged obligations W0–W8, the rejected routes' machine-checked
  obstructions, and the W0/W1 banking: `plans/l4l-16-weakn-design.md`
  (probes `plans/probes/probeE-weakn.lean`).
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
  successor milestone (L4L-16F).** Staged obligations R0–R9, the banked
  results, the conditional-instance refutation, the vacuous-`structureEta`
  finding, and the `BlockGenerationChecked.pat_wf` circularity trap:
  `plans/l4l-16-generic-instance-design.md`
  (probes `plans/probes/probeG-generic-instance.lean`).
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
- **`CtorBundle.hu0`** — the recommendation to delete the field outright
  (which superseded both candidate repairs recorded in the D1 quot
  record) is itself **REFUTED by the executed discriminating experiment
  (2026-08-15, `plans/probes/probeA1-hu0.lean`, run at both consumption
  sites)**: the ADQ site is free (`u ≠ .zero` is derivable there from
  the ambient `.indTy`-shaped interpretation — probe P4), but
  `build_spine`'s post-deletion statement is FALSE for Prop-sorted
  ctor-classified pattern-argument heads (probe P2). Root cause: the
  shape algebra's proof-irrelevance law (`WShape.HasType.proofIrrel`)
  requires `.indTy` non-Prop-sortedness, and `hu0` is that law's
  syntactic mirror — relaxing the `hasType` indTy row makes
  `proofIrrel` false. Landing any resolution therefore needs a DESIGN,
  not a deletion: either a Prop-branch at the Matches/classification
  level (not expressible in `Pattern.WF`'s classify-only signature) or
  exclusion of Prop-recursor iota patterns from `Pat` with a matching
  nonzero-sort law. Consequently D1's quotient half remains blocked on
  that design (obstruction 1 stands), in addition to obstruction 3's
  stuck-`Quot` injectivity (L4L-18A′); only obstruction 2 would
  dissolve under any resolution that keeps the pattern in `Pat`. The
  dead `Params.ctor_ty` re-export was deleted independently (zero
  consumers).
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
Experimental stays buildable at every pause point. Items 1–4 are executed
(see git history); the live remainder:

5. **16D0 slice**, then **16D1–D4** as separate checkpoints.
6. **16E promotion** + allowlist 21 + digama decision.
7. Land the former L4L-17 statements as the joint 16E co-deliverables.

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
