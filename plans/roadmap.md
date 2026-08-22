# Lean4Lean completion roadmap

**Status:** authoritative local roadmap, audited 2026-08-12 against the
committed fork, the current `jcb/formalization2` development bookmark, and
the uncommitted L4L-16 working copy; publication (moving
`origin/jcb/formalization2`) is a separate boundary and currently matches
the local bookmark at the L4L-18B checkpoint.

**Versioning.** `plans/roadmap.md` is intentionally tracked so the
status-bearing milestone ladder travels with each checkpoint, as are the
design/decision notes the ladder references
(`l4l-15-structure-eta-design.md`, `l4l-16-sort-inversion-decision.md`,
`l4l-18b-extension-interface-design.md`, `l4l-16-completion-plan.md`,
`l4l-16c-adequacy-log.md`, `l4l-16c-buildp-premortem.md`,
`l4l-16d0-slice-map.md`); every other file under `/plans` remains
ignored, and the tracked set is mirrored as explicit `.gitignore`
negations. The root-level `upstream-divergence.md` is the
tracked per-delta ledger and complements this roadmap. This document is
forward-looking only: completed milestones are deleted from the ladder when
they close, and their full narratives, hashes, and gate evidence live in this
file's git history and the checkpoint commit messages.

## 1. Mission and exact meaning of “complete”

Lean4Lean has two products:

1. `Lean4Lean/Theory/`: an implementation-independent model of Lean's kernel
   language, typing, definitional equality, environment growth, and the
   metatheory needed to use that model safely.
2. `Lean4Lean/Verify/`: a proof that the executable checker over `Lean.Expr`
   refines Theory.

External checkers translate their own expression representations into the
same Theory and prove their checkers sound there; lean4lean's job is to make
that possible from published Theory APIs alone. Success therefore means more
than deleting the original three inductive sorries.

The supported formalization is complete when all of the following hold:

- **Theory coverage:** every safe inductive declaration accepted by
  `Lean4Lean/Inductive/Add.lean` has a faithful Theory description, generated
  recursors and iota rules, and an `Ordered`/`WF` preservation proof. Temporary
  `stageN` predicates are gone from the public contract or have become proved
  implementation lemmas rather than permanent restrictions.
- **Live proof closure:** there are zero real `sorry` tokens in
  `Lean4Lean/Theory/` and `Lean4Lean/Verify/`. `Experimental/` is explicitly
  not part of the supported product; parked experiments must not be imported
  by a supported root.
- **No semantic placeholders:** `Verify.Environment.AddInduct` is inhabited
  and useful, `TrProj` has a justified semantics, and every currently empty or
  impossible verification path corresponds to a real checker execution.
- **Checker refinement:** the remaining Level/TypeChecker proof roots are
  proved, including recursor reduction, projection inference/reduction,
  structure eta, and unit-like comparison.
- **Trust is explicit:** all final roots have an audited `#print axioms`
  closure. No bridge axiom known to be false for the pinned Lean toolchain is
  reachable. Any unavoidable runtime contracts (for example pointer equality
  or opaque C++ implementations) are narrowly stated, tested, documented, and
  separated from the mathematical Theory.
- **Consumers are enabled:** a downstream checker can, from published
  `Lean4Lean.Theory.*` APIs alone, construct inductive block certificates with
  their lookup/pattern consequences, obtain a concrete projection-laws
  package, and derive literal well-formedness from a prelude contract.
  Consumer-side trusted oracles remain consumer trust boundaries by design,
  not lean4lean proof holes.
- **Upstreamability:** the fork delta is split into reviewable PRs, every
  deliberate divergence is tracked, and both the fork and upstream build at
  each release boundary.

This definition deliberately separates **proof-complete** (no sorries or
fake relations) from **trust-minimal** (no unnecessary custom axioms). Both are
required for the final release; they can be reached in separate milestones.

## 2. Current state

| Fact | Value |
|---|---|
| Ladder position | **L4L-16 active** (semantic environment bridge and sort inversion). L4L-18B completed first on 2026-08-12: proof-carrying pattern contractions, an explicit registered-equation join contract, beta-collapsed generated-iota/`quotDefEq` coverage, and `VEnv.LE` transport now form the fork-owned interface (design note `plans/l4l-18b-extension-interface-design.md`, ledger D020). The former L4L-17 merged in on 2026-08-13 (joint route; second resolution in the sort-inversion decision note). Slices 16A and 16B′ are complete at checkpoints `quyyrlks`/`pxluxmvm`; the WHNF/determinism layer and mirror-spine refactor landed at `wolxmups`/`mvmrxuus`; 16D0 is complete in the active working tree (`SExprParamsD0.lean`, D0a + definition-extended D0b, `d0SortInvS`); 16C′ joint leaf closure remains active (§5), with publication held until it measures clean |
| Current formalization source | the L4L-18B checkpoint (jj change `oluxtqyk`) descends from the L4L-15B checkpoint `7c1e89fc` (jj change `xuzusmnl`) and is published at `jcb/formalization2` after the complete gate passed |
| Parent lineage | the L4L-15B implementation descends from the v4.33 reconciliation merge `99a7f8ae7b89` (second parent: digama `upstream/master` `b292275c`); Lean on v4.33.1, lean4-nix on `argumentcomputer/lean4-nix` (upstream pins v4.33.0-rc2 — ledger D018; v4.33.1 kernel changes mirrored per D021) |
| Fixed `master` baseline | `1a16b72d2e35932a82aa501beb29ef2c3d072580` — local `master` bookmark (corrected 2026-08-12; the row previously carried a fork formalization hash that no `master` ref ever pointed at). The v4.33 reconciliation merged the later digama `upstream/master` `b292275c` as its second parent without moving `master`; `origin/master` has since moved (see remote drift) |
| Remote drift (re-verified 2026-08-14 via GitHub API; local `upstream/master` was never fetched past `b292275c`, so any reconcile begins with a fetch) | digama master is now **four** commits past the merged `b292275c`, tip `4b60e53d` (2026-08-14): stage-2 replay perf (clean-apply), the normalize-backed level-algorithm enable (half-absorbed — the fork independently made the `isEquivList` change in `99a7f8ae`; residue is the `geq'` flip inside `checkConstructors`), a proj-reduction restructure that conflicts with the fork's sorry-free `reduceProj.WF` (upstream's own version rests on a new sorry), and a neutral K-target reorder — checker-side work landing in L4L-19A/B territory; per-commit analysis and a defer-recommendation (reconcile as L4L-19's first action) in the local untracked note `plans/l4l-16-boundary-digama-drift.md`; the reconcile-or-defer decision remains due at the L4L-16 boundary (§7). `origin/master` moved one commit to `715bfaff` ("verify: prove soundness of the standard library normalize") — already an ancestor of the fork's formalization line (the `eval_normalize`/`eval_normalize_total` proofs are in-tree), so content is absorbed and only the ref recording changed |
| Trust frontier | exactly 16 sorried proof declarations (10 Tier V, 6 Tier R; `NormalEq.parRed` carries two tokens) plus six kernel-rejection recovery declarations — 22 compiled allowlist entries — and 34 custom-axiom declarations; all are pinned by exact audits. L4L-15B removed the two structure-eta checker roots from the direct frontier; their inherited L4L-16--19 dependencies remain explicit in exact axiom guards |
| Gates | the full §6 gate is green on this checkpoint: the 212-job default Lake build, the Nix flake checks, the 22-entry exact sorry frontier, the Theory-only import/axiom audit, downstream-consumer and CLI checks, and whitespace hygiene |

### 2.1 What is green

Completed-milestone narratives, hashes, and gate evidence live in this
file's git history and the checkpoint commit messages; this section keeps
only the current claim surface and where each piece lives.

**Inductive Theory: analysis, generation, transactions.** One artifact
path runs from the raw/view `Normalization` boundary (computed shape plus
semantic `Normalization.WF env`) through dependent `Checked`/`CheckedBlock`
analysis — arbitrary nonempty non-nested mutual blocks, block-wide
target-family ordinals, generated-name uniqueness, the impredicative-Prop
exception — into mixed generation and the four-phase block transaction:
the public raw `addInduct` selects the block descriptor, its exact trace
supplies atomicity, freshness, lookups, monotonicity, and `Ordered`/WF
preservation, and the proof-carrying `GenerationCertificate`/
`addInductCertified` and `ValidationCertificate` boundaries remain
available (`addInductSingleton` survives only as a deprecated migration
wrapper). The accepted slice covers parameters, per-family indices,
direct and sibling recursion, recursive targets below Pi telescopes,
small and subsingleton-large elimination, exact K-target metadata, and
zero-/one-constructor generation. The consumer-neutral local-context
core lives in `Theory/LocalContext.lean`; `Theory/Literals.lean` owns
literal encodings, containment, primitive descriptors, and
`VEnv.PreludeReady` — an ordered exact Bool/Nat/Char/List/String
contract (generated recursors and iota rules for Bool/Nat/List;
`Char`/`String` opaque behind `Char.ofNat`/`String.ofList`) that derives
direct literal WF, is stable under ordered extension and fresh
constants, and stays independent of `Lean.Expr`; Verify retains only
traversal and proves its constructor result equal to the direct Theory
encoding.

**Mutual blocks.** `Normalization.BlockWF`, `CheckedBlock.WF`,
`ValidatedBlock.WF`, and `ValidationCertificate` give arbitrary blocks an
exact environment-indexed semantic package: shared-parameter agreement,
one semantic result universe, staged family constants, and a complete
source-order constructor trace including sibling recursion and recursion
beneath Pi binders. The real Tree/TreeList and IndexedTree/IndexedTreeList
fixtures run the ordinary kernel validators, inhabit every WF certificate,
compare all generated metadata with the kernel field by field, and replay
the four phase boundaries through `AddInductBlockTrace`,
`TrEnv'.inductBlock`, and `Aligned.addInductBlock` to actual
implementation `ConstMap`s; exact negatives pin the parameter-mismatch,
result-universe-mismatch, and reordered-family validation phases.

**Kernel parity and differential fixtures.** One integrated 14-row
positive matrix (Nat, Bool, List, Option, Prod, Unit — honestly
represented by the kernel's `PUnit` — Empty, Or, And, Eq, HEq, Fin,
Vector, Acc) reruns the ordinary producer and definitionally compares
every represented metadata field, recursor type, rule count, and iota
RHS; the consolidated 32-row rejection matrix covers the closure,
collision, universe/result-shape, raw/view-incoherence, normalization,
negativity/recursive-target, field-universe, and elimination/K failure
space. `AliasFormer`, `AliasRec`, and `NormalizationMatrix` prove
normalization is necessary and exactly aligned across alias positions,
with fuel-boundary, opaque, and non-defeq rejections. Elimination and
K-target decisions retain exact operational traces differentially
aligned with Theory generation, pinned by the
`Eq`/`And`/`Or`/`Nat`/source-universe fixtures and the `PUnit`/`Empty`
one-/zero-constructor boundary; Verify's `RecursorKMatches` makes a
type-correct recursor with wrong K metadata fail alignment.

**Verify refinement layer.** Checker-run certificates (`WhnfRun`,
`CheckTypeRun`, `IsDefEqRun`, `DefEqEvidence`, `TelDefEqEvidence`,
`NormalizedCtorRun`, `GenerationRun`) turn exact ordinary-checker
executions into Theory typing and definitional equality. The level
normalizer, subsumption, and equivalence layer is proved sound through
the verified project comparator (`NormLevel.le_eval`, `geq'_wf`,
`isEquiv_wf`) at standard-only closures with all-pairs core/project
differentials; the constructor-universe audit's non-Prop branch keeps
Lean's core `Level.geq` decision inside the ordinary validator's
existing acceptance boundary. The executable candidate producer
(`buildNormalizationCandidate`) retains recursively indexed traces,
structurally certified annotation consumption (runtime producer
validation, never a semantic proof field), and arbitrary-length
dependent `Produced` witnesses. Semantic-hierarchy assembly is automatic
under `Nonempty`: the staged owners — generation readiness, post-family
alignment independent of fresh-FVar identities, and the executable
pre-family replay with omitted recursive locals — close structurally on
real metadata (`ConstructorValidityMatrix`, `PropRecursiveBoundary`)
with nearest-kernel negatives, at the guarded transitional closure plus
the single exact L4L-01E producer-execution witness.

**End-to-end producer regressions.** AliasFormer, AnnotatedPi, and
`IndexedVec` each prove the exact successful whole
`buildNormalizationCandidate` call, inhabit the exact produced package
through the generic closure, and route both the certified Theory
transaction and the checked replay through it; `AnnotatedParam` closes
constructor-parameter parity against real kernel metadata, with a
well-typed but genuinely non-defeq prefix rejected at the exact
kernel-facing error. The operational L4L-01E package authority remains
the exact AnnotatedPi producer case. Negatives stay sharp: opaque
annotations, truncated/reordered views, missing/extra constructors,
recursive-local dependency, and the environment-free
closure/universe/name/result/collision matrix.

**Replay and the consumer certificate API.** The supported replay matrix
executes 25 actual-metadata transactions: the 19-row L4L-07 singleton
inventory (the 14 fixed rows plus the alias/normalization/annotation
fixtures, with Fin and Vector replaying over their real dependency
slices) plus the two-parameter `BiBox` dependency, both mutual tree
blocks, and three nested blocks. Every row retains its exact
input/output `ConstMap` and `VEnv`, input-map WF and dependency
ordering, data-bearing transaction trace, final roles, and recursor
lookup uniqueness. The consumer-neutral Theory API
`VInductDecl.BlockCertificate`/`NestedBlockCertificate` reconstructs the
raw `addInduct` result, `addInduct_le`, `addInduct_WF`, exact lookups,
freshness, uniqueness, registered rule membership/WF, rule closure, and
the L4L-10 recursor-pattern facts from one checked transaction; it
imports no Verify state, `Lean.Expr`, normalization oracle, or kernel
object, its WF root closes at the standard baseline (the rule/pattern
root adds `Classical.choice`), and neither reaches `sorryAx`. Verify's
unified matrix keeps one exact guarded `sorryAx`, solely through the
separately tracked projection/refinement frontier. A separate fresh
replay loads the 296-declaration compiled dependency closure of the
notation-heavy fixture into an empty kernel environment and checks every
declaration, so numerals, notation, lists, arrays, products,
conditionals, and strings exercise real compiled prelude dependencies.

**Nested inductives.** The stored Theory payload is the source
`VInductDecl` unchanged; nested support is additive.
`VInductDecl.nestedElimination?` (`Theory/NestedInductive.lean`) mirrors
`ElimNestedInductive` phase for phase against caller-supplied
environment-free target metadata, and `nestedStage3` gates acceptance by
flattening success plus generation readiness of the flattened block
through the unchanged block analyzers. The restoration σ (`restoreExpr`)
rebuilds the flattened block's generation artifacts onto the
`appendIndexAfter` inventory (`NestedBlockChecked`),
`VEnv.addInductNested` inserts source families/constructors plus
restored recursors/rules through the four block phases, and
`AddInductNestedTrace`, `NestedBlockChecked.WF`, and
`addInductNested_WF` mirror the block transaction's lemma suite through
`Ordered` preservation. Verify proves the Theory flattening equal to the
port's on the rose-tree, nested-indexed, and `DeepBi`/`BiBox` fixtures,
matches kernel accept/reject on four nearest negatives, and round-trips
the port's complete `Environment.addInductive` output against the Theory
artifacts (payload constants, recursors, K flags, rule RHSs,
`numNested`).

All three nested fixtures also replay from real stored metadata through
`TrEnv'.inductNested` (`Verify/Environment/NestedReplay.lean`), with
exact freshness chains, K-flag agreement, the literal rule fold, and
complete `NestedBlockChecked.WF` packages proved by direct concrete
typing derivations; the package closures are the standard baseline plus
the persistent-map container axioms and named `native_decide`
observations — no `sorryAx` — while the full `TrEnv'` roots carry the
usual guarded transitional checker closure. The generic σ̂ typed
transport (`Theory/Typing/NestedTransport.lean`: the `ConstInterp`
environment morphism and `IsDefEq.substConst` with its
`HasType`/`IsType`/`VConstant.WF`/`VDefEq.WF` corollaries) is proved as
the justification layer; its β-collapse bridge to the spine-collapsed
artifact substitution on generated artifacts remains available future
work, not a nested-coverage gap. Source nested declarations remain
rejected by the non-nested raw analyzer; the dedicated nested analyzer
and transaction own their flattened/restored recursors, rules, and
replay.

**Patterns.** Every certified block's iota rules are exact
`SimplePattern.iota` patterns with RHS templates, check lists, and
`RuleClosure` payload closedness (`Theory/Typing/InductivePattern.lean`;
implementation-independent shape layer in `Theory/Typing/Pattern.lean`).
The complete generic pattern-combinatorics obligations — `pat_simple`, match
inversion with rule-index/constructor recovery, rule distinctness, and the
`pat_uniq`/`pat_app_l`/`pat_app_l_uniq`/`pat_app_uniq` non-intersection
laws — are proved for one certified block from the certified inventories
at guarded `propext`/`Quot.sound`-level closures. The typed β-collapse
layer (`Theory/Typing/InductivePatternWF.lean`: `IsDefEq.appN_lamN`,
`varN_matches_paths`) is sorry-free, and `pat_wf` composes it into
pattern soundness: a successful match whose parameter and index checks
hold is definitionally equal to the instantiated RHS template, derived
from the exact rule defeq registered by `addInduct`, with the redex
arriving decomposed into recursor and constructor spines — precisely
what a verified reduction site holds — at exactly the Church–Rosser
development's transitional unique-typing closure, shedding `sorryAx`
automatically when the joint L4L-16 closure lands. The block-local assembler
(`Theory/Typing/InductivePatternEnv.lean`) builds environments whose
defeq set is exactly one certified block's generated rules plus
separately certified extension rules over a constant base
(`assembleEnv_defeqs`, `assembleEnv_WF`), and the union pattern set
`AssembledPat` couples the block's facts with each
`CertifiedExtension`'s payload and beta-collapsed coverage. L4L-18B removes
semantic soundness and raw-registration coverage from `Params`: each
`ParRed`/`CParRed`/`WHRed.extra` step carries the exact local `IsDefEqU`
certificate, while `Params.Extension.join` separately requires a typed
`CRDefEq` witness for every registered raw equation. Generated iota rules and
`quotDefEq` have kernel-checked `VExpr.stripLams` coverage, and named
`VEnv.LE.extra`/`extra_appN` transports preserve registered tower equality
under environment growth. No open-environment extension instance is
installed; both fixture blocks assemble over the empty base with their defeq
sets pinned to their generated rules.

**Projections.** `Theory/Projection.lean` is the consumer-neutral
projection boundary decided at L4L-13A/B. `VStructureView` restricts the
same one-family `GenerationChecked` artifact used by inductive
generation to the kernel structure class — exactly one constructor, no
indices, no recursive fields — and retains per-field sort levels.
Projections are recursor-encoded: `projectionCodes` computes, per field,
a dependent motive (`typeFn`, with earlier projections substituted into
later field types), the selecting minor, and the projector program,
with `projectionType?`/`project?` derived. `Registered`/`WF` tie a view
to exact environment lookups and generated iota rules, and
`VEnv.TrProj env U Γ view levels params idx major result` demands level
WF and arities, a well-formed parameter spine, the exact instantiated
major type, and the computed program; syntactic determinism
(`result_eq`) and environment extension (`mono`) are proved at
`propext`/`Quot.sound`. Verify's `TrProj` is now a fully constrained
compatibility wrapper (existential view/levels/params with
`view.name = structName`; no invented metadata), so the former Tier S
specification sorry is gone and roots that merely mention `TrExprS` no
longer inherit `sorryAx` through the projection branch. The
`DependentRecord` fixture — simultaneously parameterized,
universe-polymorphic, and dependent — pins the complete encoding
(`Tests/ProjectionExpressibility.lean`).

The L4L-14 structural package is proved: weakening, inverse weakening,
context-defeq transport, WF, uniqueness, term substitution, and universe
instantiation retain their compatibility names and are bundled by
`TrProj.structuralLaws`. L4L-15A proves `inferProj.WF`, both constructor and
string branches of `reduceProj.WF`, and the enclosing WHNF/translation
projection paths. Their exact guards distinguish the remaining inherited
Tier-R inversion dependency from projection-specific proof debt.

**Structure eta.** L4L-15B adds the registered lower-layer `VStructEta`
descriptor, monotone `VEnv.structEtas` registry, ordered subject-reduction
certificate, and the exact `VEnv.IsDefEq.structEta` contraction for complete
parameter spines. The checked-view bridge fixes reconstruction to the
deterministic recursor-encoded projector programs; `StructureEtaArtifact`
retains the exact host family/constructor alignment and registry membership.
Weakening, substitution, strong typing, inversion/discrimination,
standardization, nested transport, and every environment-schema consumer
carry the new case. `StructEq` retains oriented reconstruction
seeds and complete typed constructor-spine congruence; its named parallel
join records the constructor/iota, nesting, internal reduction, dependent
field, proof/Prop, and registered-`.extra` interactions. The unconditional
`tryEtaStructCore.WF` and `isDefEqUnitLike.WF` roots are now proved from the
registered artifact, removing both direct Tier V sorries. Exact axiom guards
pin registration, subject reduction, the primitive rule, Church--Rosser, and
both roots; the executable/kernel fixture matrix covers dependent
parameterized, zero-field, proof-field, Prop-valued, recursive,
multi-constructor, and indexed declarations.

**Theory-only consumer surface.** The L4L-15C audit moved the generic
`SpineWF` weakening/inversion laws to `Theory/Typing/UniqueTyping.lean`,
primitive-environment extension and Bool-literal typing to
`Theory/Literals.lean`, constant-absence and containment facts to their
Theory owners, and the Bool-to-elimination-mode conversion to
`Theory/Inductive.lean`. Verify keeps only deprecated compatibility shims
where a public name existed. `Tests/TheoryConsumerSurface.lean` imports no
Verify module and pins the availability and exact axiom closure of every
migrated API.

**Not claimed.** The remaining metatheory/checker roots. The beta-collapsed
certificates do not constitute the whole-live-environment
`Params.Extension` instance; constructing it (consumed only by
`IsDefEq.church_rosser`, and needing weakN-inversion-strength fields that
arrive with the joint L4L-16 co-deliverables) is L4L-18A work under the 2026-08-13 re-cut, while
L4L-16D builds the SExpr-side instances that `sort_invS` consumes. Pattern coverage,
checks, and registry membership never imply an operational rewrite without
the local equality certificate. The nested fixtures prove the current
single-target, indexed, and queued deep two-parameter boundaries; nesting
classes beyond the accepted flattened-block analyzer remain rejected. The
296-declaration notation replay is a real fresh prelude prefix, not a claim
that an arbitrary whole kernel environment replays. Bare producer success is
never generation-shape authority or Theory semantics.

### 2.2 Live debt

The sorry audit (`Lean4Lean/Audit/SorryFrontier.lean`, a declaration-level
`sorryAx` allowlist over the compiled Theory/Verify surface) currently
accepts exactly 16 sorried proof declarations (`NormalEq.parRed` carries two
tokens), plus six deliberately kernel-rejected fixture recoveries that are
not proof debt. The compiled allowlist therefore contains 22 declarations:

| Area | Live debt |
|---|---|
| Core metatheory (Tier R) | `Injectivity.lean` x3; `UniqueTyping.lean` x1; `Projection.lean` x1; `ChurchRosser.lean` x2 |
| Checker verification (Tier V) | `Verify/Environment.lean` x2 (`addDecl.WF` — now only its `inductDecl` case — and the re-sorried `addQuot.WF`); `Boundaries.lean` x1 (upstream's `checkPrimitiveDef.WF`); `Extension.lean` x5 (the D017 checker-readiness transports); `WHNF.lean` x1; `InductiveFixtures.lean` x1 (`aliasFormerAlignmentRun` repair debt) |

All Tier V entries are L4L-19A/19B territory; the eight added at the v4.33
reconciliation are classified in ledger row D017. Non-sorry debt:

- The public inductive spec has complete one-family, non-nested mutual,
  and nested generation, preservation, metadata parity, environment
  replay, generic iota-pattern facts, pattern soundness (`pat_wf`), and
  the block-local pattern environment assembler. The complete supported
  replay matrix and consumer certificate API are now closed, but the accepted
  inductive language remains a growing subset rather than kernel-complete;
  projection semantics landed at L4L-13A/B and projection structural/checker
  verification closed at L4L-14/L4L-15A; structure eta and unit-like
  comparison closed at L4L-15B as a documented divergence (ledger D019) on
  the reconciled v4.33 base. `pat_wf` carries the Church–Rosser
  development's transitional unique-typing closure until the joint L4L-16 closure lands.
- The L4L-15C consumer-neutral audit is complete. Generic spine laws,
  primitive-environment extension, literal typing, containment/absence, and
  elimination-mode conversion now have Theory-only homes, with a dedicated
  import-boundary/axiom audit and deprecated Verify shims only where needed.
- 34 project-specific `axiom` declarations outside `Experimental/`: 32 in
  `Verify/Axioms.lean` and two pointer-equality contracts in `PtrEq.lean`.
  The v4.33 reconciliation added five upstream reference equations for core
  level operations (`Level.normalize_eq`, `Level.mkMaxAux_eq`,
  `Level.skipExplicit_eq`, `Level.isExplicitSubsumedAux_eq`,
  `TreeMap.any_eq_any_toList`) consumed by upstream's `LevelStd`
  verification. Three cached-field equations from the group once false on
  older pins (`lean4#8554`) remain unproved and therefore forbidden
  contracts. The 2026-08-10 dead-axiom finding shrank: upstream's merged
  proofs use `TreeMap.all_eq_all_toList` again, so only
  `Level.mkLevelIMaxCore_eq`, `Expr.liftLooseBVars_eq`, and `Expr.equal_eq`
  remain deletion candidates, and their reachability must be re-run on the
  v4.33 tree at L4L-20A before deleting. 28 of the 32 carry `@[simp]`, so
  §3's simp ban is containment work not yet done. The L4L-13A/B `sorryAx`
  shed moved a large population of candidate/fixture roots into the
  sorry-free set with the cached-field trio (and other reference equations)
  still in their closures, so enforcing the "no forbidden axiom in a
  sorry-free supported root" CI rule waits on the actual L4L-20A retirement
  (prove the equations for the pinned implementation or take them off the
  trace-proof simp path).
- `addInductSingleton` (deprecated 2026-08-07) has zero callers outside
  its own shim block and is deletable as one self-contained block; the
  deprecation has not yet appeared in any published checkpoint, so time
  the removal against the consumer window.
- `NestedBlockCertificate` exposes the full lookup/freshness/WF/rule
  surface but no `ruleClosure`/`IotaPat` pattern facts; pattern facts are
  block-certificate-only until the σ̂ β-collapse bridge lands (L4L-19A).
- The semantic route to injectivity/unique typing runs through the
  in-tree `Experimental/` `SExpr`/`ShapeLogRel` development; the route
  and joint-route decisions live in
  `plans/l4l-16-sort-inversion-decision.md`, the design state in
  `plans/l4l-16-completion-plan.md`, and the measured gate path in the
  L4L-16 ladder entry (§5). Current admission surface: the adequacy
  iota leaf and `SExpr.WHRedS.defeq` are the two `sorryAx` sources on
  the gate path; three further `SExpr.lean` admissions are documented
  off-path deferrals; `ShapeLogRel.lean` is live-sorry-free. Nothing
  there merges as a completed proof, and no experimental assumption
  substitutes for a supported root's accepted closure.
- `Lean4Lean.Experimental` is not among Lake's `defaultTargets`, so no §6
  gate ever builds it. L4L-16A explicitly parked the four pre-broken,
  unreferenced prototypes — `Stratified`, `StratifiedUntyped`, `Stronger`,
  and `ParallelReduction` — as import-compatible stubs. Their stale source
  targeted the pre-structure-eta/non-mutual judgment, and `Stronger` and
  `ParallelReduction` also carried admissions; none belongs on the L4L-16
  trust path. `Experimental/UniqueTyping.lean` was separately migrated to
  a strong-judgment compatibility endpoint: it no longer attempts the
  invalid recovery of lost strong evidence from weak `IsDefEq`.
- The dev-branch flake rework scoped `leanSrc` to a fileset, retiring the
  earlier `inputs.self.outPath` source-invalidation debt; remaining flake
  debt is cosmetic. The `system` deprecation warning comes from the
  pinned Nix stack and is non-fatal.
- The generated transitive axiom-closure report for all supported roots does
  not exist yet (L4L-20A); the reachability audit is partially established,
  not release-clean.

## 3. Trust policy

**Decision.** The axiom set of the current inductive **Theory** roots is
reasonable: only the standard logical baseline `propext`,
`Classical.choice`, `Quot.sound` (often a strict subset) and no axiom about
Lean's implementation behavior or representation. The axiom set of the
end-to-end **Verify** roots is not release-acceptable: their `sorryAx` and
collection/opaque implementation contracts are diagnostics while proofs
migrate, not foundations. Returning assembled hierarchies under `Nonempty` is
deliberate: it states semantic existence without using choice to extract a
data-bearing checker-selected view.

Current custom-axiom inventory (34 declarations; classification records
intended release treatment, not evidence the equations are true):

| Class | Count | Declarations | Release treatment |
|---|---:|---|---|
| Unproved cached-field equations, once false on older pins | 3 | `Level.hasParam_eq`, `Level.hasMVar_eq`, `Expr.looseBVarRange_eq` | Forbidden from every supported theorem root until proved for the pinned implementation |
| Reference equations documented as `@[implemented_by]` candidates | 17 | `Expr.replace_eq`, lift/lower, instantiate/range/reverse, abstract/range, `hasLooseBVar_eq`, `eqv_eq`, `equal_eq`; the v4.33 core level-operation equations `Level.normalize_eq`, `Level.mkMaxAux_eq`, `Level.skipExplicit_eq`, `Level.isExplicitSubsumedAux_eq` | Replace axioms with logical reference definitions and separately justified implementations |
| Persistent collection semantics | 6 | `TreeMap.all_eq_all_toList`, `TreeMap.any_eq_any_toList`; `PersistentArray.toList'_push`; hash-map insert, find, and contains/find agreement | Prove upstream or narrow to the actual WF/reachable-state invariant |
| Other opaque or representation-layout bridges | 5 | `Syntax.structEq_eq`; Level and Expr data-layout equations; `Level.mkLevelIMaxCore_eq` | Expose/prove upstream, narrow to the properties actually needed, or reject |
| Candidate platform contracts | 3 | `ptrEqExpr_eq`, `ptrEqConstantInfo_eq`, `Level.instLawfulBEqLevel` | May remain only in a named, version-pinned platform manifest with differential tests |

**Per-root closures.** Exact `#guard_msgs`/`#print axioms` guards in the
source are the authoritative per-root record; this roadmap does not mirror
them. Two standing facts frame that record: generic Theory transaction and
inductive roots close over the standard baseline only, while concrete Verify
packages, candidate/semantic runs, and replay fixtures inherit the
transitional closure (`sorryAx` via `TrProj`, pointer/reflection, layout, and
container contracts) — exactly guarded, release-blocking, and kept out of
Theory. The separation to preserve: once a checked generation value is
supplied, Theory-level consequences (for example iota-rule membership in the
final environment) close at `propext`/`Quot.sound` without inheriting the
Verify closure. Do not summarize any of this as “four acceptable axioms”: a
theorem's axiom set includes dependencies through its statement and inductive
types, so a proof can be locally sorry-free while its exported roots remain
transitively sorry-bearing. Only the generated transitive closure of each
named root is authoritative for release (L4L-20A).

| Boundary | Allowed during development | Required at its release gate |
|---|---|---|
| Computational `Checked` analysis, normalization shape, and generation | No axiom declaration; evaluation and equality fixtures must compute | Same; no oracle or opaque semantic bridge in acceptance/generation |
| Theory normalization validity, preservation, patterns, projection semantics, and consumer-facing Theory API | Any subset of `propext`, `Classical.choice`, `Quot.sound`; exact closure guarded per exported root | Same subset policy; zero `sorryAx`, zero project-specific axiom, and no import path to `Verify/Axioms` or `PtrEq` |
| Verify's mathematical refinement roots | Transitional bridges may remain only when named, classified, and exposed by an exact guard | Standard logical baseline only, unless the theorem is explicitly a platform-refinement theorem |
| Version-pinned platform adapter | A narrowly stated candidate contract with an owner, pinned Lean revision, removal issue, and tests | Only reviewed manifest entries; expected upper bound is the two pointer-equality implications and possibly lawful level `BEq`; never reachable from Theory or a consumer-facing semantic root |
| Fixtures and differential tests | May expose transitional dependencies to diagnose their path | They do not justify an axiom; release fixtures must have the closure required by the root they certify |

Apply these rules mechanically:

1. Treat the accepted baseline as a **set upper bound**. Keep exact
   `#guard_msgs` checks for named roots so growth or unexpected shrinkage
   receives review; audit computation and proof closure separately.
2. Reject `sorryAx` from every release root; a statement reaching a sorried
   relation is not release-clean merely because its proof body has no sorry.
3. Reject every known-false or unproved cache equation from supported roots
   and ban project-specific axioms from the global simp set; removing `[simp]`
   is containment, not discharge.
4. Expanding the logical baseline or platform manifest requires an explicit
   design decision; difficulty, convenience, or prior existence in
   `Verify/Axioms.lean` is not justification.
5. A consumer's trusted oracle stays in the consumer; it authorizes no
   lean4lean Theory axiom, assumed inductive oracle, or opaque projection
   relation.
6. A normalization view is untrusted data until it has both computed shape
   coherence and an environment-indexed `Normalization.WF` proof derived from
   checker/defeq evidence; neither Verify nor any consumer may assume a
   normalization oracle or add a reduction axiom.
7. Before closing a milestone checkbox, run both the exact guards and a
   generated transitive-closure check of the public roots; the same audit
   applies to every exported consumer-facing theorem.

## 4. Architecture and trust contract

These are invariants at every milestone.

1. **Theory points downward only.** `Lean4Lean/Theory/` imports no
   `Lean4Lean/Verify/`. Mathematical declarations mention `VExpr`, `VLevel`,
   `VEnv`, and proof objects, not `Lean.Expr`, `FVarId`, `ConstMap`, or any
   consumer's expression/address/catalog types.
2. **Consumer-neutral semantics.** No consumer-specific namespace, hash,
   address, cache, or checker-state type enters lean4lean; consumer-specific
   transport stays downstream.
3. **Theory-shaped APIs live in Theory.** Move literal encodings, the
   VExpr-only local-declaration core, primitive readiness, projection
   semantics, and generally useful pattern lemmas down. Leave `Lean.Expr`
   translation and `ConstMap` alignment in Verify. Old Verify paths re-export
   compatibility names while consumers migrate.
4. **Kernel parity is the adequacy test.** `Inductive/Add.lean` determines
   which safe declarations and metadata must be modeled. The Theory generator
   must compute its own output; proofs may compare it with the kernel but may
   not assume translated recursor shapes as hypotheses.
5. **Staging is monotone and temporary.** Every Stage-N predicate is an
   executable, proved subset with rejection fixtures. The final public
   contract covers the full safe implementation. Extend the shared
   `Checked`/`Normalization`/`GenerationChecked` contracts monotonically; do
   not reintroduce parallel Boolean analyses or downstream de Bruijn
   reconstruction, and never replace a missing case with `sorry`, an oracle,
   or an overstrong premise that real kernel output cannot satisfy.
6. **Checked analysis and normalization have explicit roles.** The raw
   `VInductDecl` is the stored constant payload. `Normalization` supplies a
   shape-compatible analysis view, and `Normalization.WF env` justifies that
   view by Theory defeq at the kernel's declaration stages. `Checked` is the
   environment-independent result computed from the view; `Checked.WF env`
   supplies its semantic typing evidence. Do not fold `VEnv`, `Lean.Expr`, or
   consumer-specific evidence into the computational analyzer, and do not
   treat a shape-compatible view as semantically valid without its WF proof.
7. **One accepted source/view pair, one artifact path.** A normalized block
   accepted by the public transaction must preserve the raw metadata payload,
   use the same checked view for every WHNF-sensitive decision, generate and
   preserve one artifact set, expose it through `AddInductSuccess`, and replay
   it in Verify. Parallel raw/view or direct/generalized generators are
   permitted only as short-lived proof migrations; no checkpoint may accept a
   case for which the public accessor returns a weaker or different
   recursor/rule set. The consumer-facing erasure is `GenerationCertificate`:
   it must couple the exact generation with its WF proof, and
   `addInductCertified` must remain definitionally the same computation as
   `addInductGeneration`. The proof may authorize preservation but may not
   affect generated artifacts or transaction control flow.
8. **Additive migrations first.** Before changing an existing exported Theory
   signature, add the new API and a compatibility theorem or re-export first;
   remove the old path only after a deprecation window for downstream
   consumers.
9. **Classic-module compatibility.** Do not introduce `module` headers in
   reachable files without a coordinated migration; downstream consumers use
   classic imports because lean4lean does.
10. **Axiom budget is checked per root.** New Theory roots may depend only on
   the accepted logical baseline (usually a subset). Verify bridge contracts
   need a separate, named manifest. “It was already in `Verify/Axioms.lean`”
   is not acceptance.
11. **Every fork divergence is tracked.** `upstream-divergence.md` carries one
   entry per semantic/API delta, its downstream impact, test, upstream
   issue/PR, and removal condition. Empty means fully upstreamed.

## 5. Milestone ladder

This is the sole status-bearing execution ladder and the only milestone
naming scheme. Exactly one milestone may be active; every later milestone is
queued, and no later milestone begins until the active one is complete. A
milestone completes only when its entire deliverable and every applicable §6
gate pass on one committed checkpoint; completed milestones are then removed
from this ladder, with their record kept in git history. Earlier partial
implementation counts as a prerequisite, never as partial credit. A suffixed
identifier such as L4L-01D2 is a full checkpoint with its own commit and
gates. Read-only design reconnaissance for a later milestone is allowed when
it changes the active design. Implementation and publication normally stay
serial; an explicitly independent later milestone may close as its own
audited checkpoint while the active milestone waits at a mandatory external
approval gate, provided this exception is recorded here and does not change
the blocked semantics. L4L-15C closed under this exception while L4L-15B
stood at the former structure-eta approval gate. This keeps one auditable
claim per checkpoint and
prevents several half-migrated public artifact paths from being live
simultaneously.

If upstream advances at a milestone boundary, insert an explicit
integration-only reconciliation checkpoint (as was done for v4.31) rather
than hiding merge work inside a semantic milestone.

### Metatheory closure (L4L-16–L4L-18A)

L4L-18B completed the prerequisite interface split on 2026-08-12 (design
note `plans/l4l-18b-extension-interface-design.md`, ledger D020).
Identifiers are stable names carried by their deliverables; execution
order is this list's order. This work proceeds independently of
upstream: no milestone blocks on upstream review or interface approval,
every interface departure is decided here and recorded, and upstream
engagement consolidates in the L4L-20C series.

**L4L-16 — semantic environment bridge, sort inversion, and joint
inversion/uniqueness closure.** Execute the semantic route on the
L4L-18B interface per `plans/l4l-16-sort-inversion-decision.md` (both
resolutions). The former L4L-17 is merged in (joint route, 2026-08-13):
the composition impossibility map showed that eliminating the
constructor-observation closure for higher-order constructor fields
needs a level-indexed limited uniqueness, so the inversion/uniqueness
statements are co-proved with adequacy in one mutually founded
development — the shape-level stratification supplies the well-founded
structure the originally declined joint route lacked. Execution detail
and design state live in `plans/l4l-16-completion-plan.md`; the attempt
history is in `plans/l4l-16c-adequacy-log.md`.

Measured gate path (probed against built oleans, 2026-08-13):
`VEnv.IsDefEqU.sort_invS` closes at
`[propext, sorryAx, Classical.choice, Quot.sound]` with no project
axiom; the `sorryAx` sources are exactly the adequacy iota leaf and
`SExpr.WHRedS.defeq` (consumed by the leaf machinery by dot-notation).
`LE_Interp.sound`, `VEnv.IsDefEqStrong.mkS`, `LRS.CtorDefEq.fold`, and
`LR.DefEq.ctor'_inv` are measured clean, and the SExpr-side
`forallE_inv`/`sort_forallE_inv` carry `sorryAx` only through the leaf,
so they go clean with it.

- *L4L-16A — bridge interface and judgment translation.* **Complete**,
  checkpoint `quyyrlks` (2026-08-13). *L4L-16B′ — SExpr infrastructure
  narrowed to the gate.* **Complete**, checkpoint `pxluxmvm`
  (2026-08-13); four Experimental admissions remain, documented
  in-source, with `WHRedS.defeq` the only gate-path item. Narratives
  live in the checkpoint messages and the adequacy log.
- *L4L-16C′ — joint leaf closure (active).* In dependency order:
  (1) the joint-induction design — state the level-indexed limited
  uniqueness that higher-level lam-field composition consumes from its
  predecessor, use the specialized level-one adequacy bootstrap to derive
  the first weak-judgment alignment in a well-formed target context, restate the
  SExpr-side inversion lemmas level-indexed (they are currently
  top-level only), verify well-foundedness of the combined recursion,
  and take the mk-faithfulness/reflection decision here (a VEnv-side
  adequacy restatement must be known before the leaf closes, not
  after); (2) chain-normalize constructor observations
  (`CtorLink`/`CtorChain`/`toChain`) over the landed WHNF/determinism
  layer (`WHNF.ctorSpine`, `WHRedS.ctorSpine_determ`, the mirror-spine
  `exact` fields — checkpoints `wolxmups`, `mvmrxuus`); (3) the
  joint weak inversion/uniqueness result at the two root constructor
  views, closing only those `WHRedS.defeq` call sites; (4) strengthen the
  `LRS.IotaRHSDefEq` fixed-tower contract with the head adequacy supplied
  by well-founded recursion on semantic `R`-edges via `LE_Interp.recR`;
  (5) fold the chain at the leaf and measure
  `sort_invS` at `[propext, Classical.choice, Quot.sound]`, with the
  SExpr-side inversion lemmas recorded clean simultaneously. The
  `hDef` premise needs no 16C work (it is `IsDefEqStrong.const`'s
  field, discharged by `mkS` from `Params.Semantic.defn`; its live
  construction is 16D's `defn`).
  **Status (2026-08-14):** steps (1)–(3) are kernel-checked at the
  standard clean closure — the joint interfaces (level-indexed
  `AdequacyAt`, contextual `JointStage`/offset `JointBuilder`, `mk`
  reflection at `VEnv.EqUpToLevels`), the normalized constructor chain
  (`CtorLink`/`CtorChain`/`toChain`/`foldRaw`), and the stratified
  inversion/uniqueness bootstrap (`JointStratifiedInversion`,
  `IsDefEq.uniq_of_stratified_inversion`,
  `WHRed(S).defeq_of_stratified_inversion`, with contextual raw
  uniqueness derived from level-one adequacy). Step (4) settled at the
  proof-relevant `LE_Interp.Witness` recursion boundary after proof
  irrelevance invalidated the paired proof-indexed recursors; the full
  retained-typing induction (`FitsRDeep`/`SoundRDeepAt`/
  `recNatRDeepSound`) and the admission-free dependent-application
  core `LR.adequateApp` are kernel-checked. The D0 review then closed two
  concrete interface gaps ahead of the live instance: weak constant-endpoint
  universe-arity inversion and a finite proof-carrying
  `IsDefEqStrong.defn` rule, both threaded through adequacy and building.
  The buildP pre-mortem also found that the retained fixed-head result had
  erased its Nat index; it is now represented by `FixedHeadResultAt`, paired
  with same-depth `SelfAdequateAt`, and promoted to the old polymorphic result
  only after construction at every depth. The replayable conversion-path
  certificate and the ρ-decoupled closed-valuation leaf consumer are
  kernel-checked (2026-08-15); the fallback legs no longer erase the
  focused seed. The depth bootstrap landed 2026-08-15
  (`contextualAdequacyAtDepth_of_iotaSteps`: strong Nat induction,
  G4-clean, the level tower now a facade over the depth fixpoint),
  conditional on one named family — the per-rung depth-indexed leaf
  `∀ d, ContextualIotaWitnessStepAtDepth d`; the N1 peel core is
  ported in-file. `SelfAdequateConstStep` landed the same day,
  conditional on two named Props (`CoherentIotaLeafStep` — the chain
  wall and home of the G4 rung audit — and `ConstDefnLocalStep`),
  with the seed interface decided at the ambient valuation (the
  nil-witness form proved underivable; argument journaled). Remaining
  for step (5): **the rung audit ran on 2026-08-15 and fired the G4
  tripwire — a structural repair is required, not another proof
  cycle.** The chain fold's interior-vertex retyping and root subject
  reduction demand type uniqueness at a depth no premise in scope
  names: interior vertices are the middle terms of `CtorDefEq.trans`,
  which retains nothing about them, so their depth is not a function
  of the endpoints'. Neither the rung index (withheld by design — the
  derivation induction is depth-blind) nor the rule certificates
  (they bound the contractum, not the major) supply the bound. The
  whole residual is now the single named, produced-and-consumed Prop
  `LR.MajorChainFoldStep`. **The repair landed the same day**
  (additive, zero ripple: no constructor gained a premise, no
  structure gained a field). Its pivot was a restatement — the fold's
  per-link uniqueness never types a `trans` middle term; after the
  first link the anchor travels with the term, so the call reconciles
  the link's own `SpineWF` result type against the inherited anchor.
  Retaining that reconciliation at the constructor observation
  (`CtorRetype`/`CtorSpineTypeUniqPath`, path-valued, SLR:11112-11147)
  discharges the interior half outright and re-lands the whole raw
  consumer surface without `RawTypeUniq`. **The residual has left the
  depth-indexed fixpoint** — `CtorSpineTypeUniqPath` carries no depth
  index and its subject is a registered declaration, so it is the
  first residual a generation-side argument can attack. Both fields of
  `MajorChainAnchorStep` then landed, and `rootRed` needed no
  re-certifying subject-reduction lemma at all: retaining the
  conversions `HasTypeStratifiedS.to_core` was discarding collapses the
  whole discipline to Pi injectivity for type paths, `LRS.PiPathInv`.
  `CoherentFixedHeadStep` also landed (its application fold spends
  adequacy at `depth` — an instance the step already holds — and at
  `depth - 1` via `isType`, so no same-rung demand), leaving three
  named Props; the N2 premise change and the ordered telescope producer
  are in the file, and `hcap` is now provably dead weight.

  **2026-08-15 verdict — the leaf cannot close inside 16C′ as scoped.**
  `PiPathInv` is not provable by any path-, spine-, or depth-level
  argument: `JointPathInv.iff` shows the chain-wall repair removed
  exactly one field (`sortPathInv`) and nothing more;
  `PiPathInv.of_three` decomposes it into `SubjectRedS` + `PiEdgeInv` +
  `PiHeadNorm`, the first two recoverable from it (so an equivalence
  modulo the third); and the depth-indexed escape route is closed by
  two independent machine-checked obstructions (the layer transport
  needs bounded output where a rung gives bare output — the gap Prop is
  equivalent to a *uniform* stratification bound that would make the
  depth induction vacuous; and the chain leaf cannot supply the bounds,
  since the anchor is manufactured from the previous link's output and
  grows per conversion edge while chain length is unbounded; yield:
  spines of length ≤ 1). The irreducible factor is `PiHeadNorm` =
  `TypeWHNFEx` (a well-typed type HAS a weak-head normal form) +
  `PiHeadStable`. **The 18A′ scoping pass then relocated the wall
  again, and this is the current position:** `TypeWHNFEx` is NOT needed
  — that decomposition is sufficient, not necessary, and is the
  expensive branch. `PiHeadNorm` follows from Church–Rosser plus
  **standardization**, transporting a Pi that already exists
  (`PiHeadNorm.of_crLadder`); Theory already proves the analogue,
  `VEnv.IsDefEq.reduce_forallE` (HeadReduction.lean:512) via
  `ParRedS.standard` (:489) — a connection no plan doc had made. The
  real wall is **sort/Pi shape disjointness**: `NormalEqPiInvL` is
  structural in six of `NormalEq`'s eight constructors, and the
  survivors `etaL`/`proofIrrel` cost exactly the facts Theory spends
  the sorried `sort_forallE_inv`/`sort_inv` on. Confluence cannot
  supply them (`proofIrrel` is a congruence with no operational
  content), and they are unavoidable: `SortForallEDisj.of_piHeadNorm`
  shows the leaf ENTAILS sort/Pi disjointness in four lines. **So
  L4L-18A′ can never close the leaf on its own, however scoped**, and
  `TypeWHNFEx` alone unblocks nothing. Scoping pass:
  `plans/l4l-18a-prime-scope.md` (12-rung ladder, 8 of 12 already
  machine-checked; implement by transport via `reify`, not by porting,
  saving ~1600 lines; `Experimental/NormalEq.lean` and
  `ParallelReduction.lean` are dead stubs recommended for deletion).
  **That question is now answered, favourably, and the leaf has a
  mapped non-circular closure path.** Three of the four disjointness
  facts need NO adequacy rung: they follow from `LE_Interp.sound`,
  which lives outside the depth fixpoint (disjointness is about head
  shapes, which the interpretation already records; injectivity is
  about the level, which the shape records only as a nonzero bit —
  that is the asymmetry). The fourth, `sortInv`, is produced at rung 0,
  because its subject is a syntactic sort and `HasTypeStratifiedS.sort'`
  is nullary with a free depth index. All of this is landed in
  ShapeLogRel (:14996-:15501) and the depth-0 producers in ADQ, 48
  results, none carrying `sorryAx`, with a negative control
  (`sortInv_bit_only`) proving soundness recovers the bit and NOT the
  level — a sharp boundary, not a leaky one. Consequently the suspected
  16C′ ⇄ 18A′ cycle does not exist: `PiPathInv.of_crLadder_noAdequacy`
  closes the residual from the CR ladder alone, and rung R11
  (`PiEdgeInv`) is proved, removing itself as an input.

  **The leaf's remaining inputs, exactly:** from 18A′ —
  `LRS.CRComplete` (Church–Rosser modulo its two `.extra` holes and the
  live `Params.Extension` join), `ParRedSDefeq`, `PiStandard`, plus
  `SortHeadNorm` (transport of Theory's proved `reduce_sort`); from the
  fixpoint — `SortInv` at rung 0 only; genuinely new —
  `LR.PiComponentTransport`, the component half of the Pi observation.
  **CORRECTION (measured with a dependency-closure walker, superseding
  an earlier `weakN_iff` claim recorded here): the CR-ladder route is
  CIRCULAR and cannot close 16C′.** `ParRedS.defeq`/`.standard` do not
  touch `weakN_iff` at all; their sorry roots are `IsDefEqU.sort_inv`
  and `IsDefEqU.forallE_inv_stratified` — the 16C′ deliverables
  themselves. The identification is literal, not moral:
  `PiPathInv.of_adequacy` is definitionally `SExpr.forallE_inv`, which
  is what `forallE_inv_stratified` promotes. So the loop closes:
  `PiPathInv` = `SExpr.forallE_inv` ⇒ `forallE_inv_stratified` ⇒
  `IsDefEqU.forallE_inv` ⇒ `ParRed.defeq` ⇒ `ParRedS.defeq` ⇒
  (transport) `ParRedSDefeq` ⇒ (R11) `PiPathInv`. `PiEdgeInv.of_piPathInv`
  is one line, making the loop sharp: R11 is a re-presentation of the
  leaf, not a reduction to anything cheaper. The essential uses are the
  β cases of `ParRed.defeq` (ChurchRosser:1149) and `StRed.triangle`
  (HeadReduction:438), each reconciling an application's domain with
  its abstraction's own domain before β can fire — textbook "subject
  reduction for β needs Π-injectivity". The native SExpr route is NOT
  blocked by weakening (that machinery measures clean) but hits the
  same β case. Genuine narrowing banked: all three CR-ladder inputs are
  used only at SORT-typed subjects (`ParRedSDefeqSort`/`CRCompleteSort`/
  `PiStandardSort`, with `PiPathInv.of_crLadder_R12`), and the
  narrowing provably does not dodge the hard case (an explicit
  sort-typed β-redex witness). Note `weakN_iff` remains a real but
  DIFFERENT obligation: it gates `church_rosser`, not these two Props.
  **The loop is now PROVED, and the stratification escape is closed
  too.** `LRS.piPathInv_iff_parRedSDefeq` establishes the ladder and
  the leaf are interderivable: the native derivation
  `PiPathInv → PatStep → ParRedSDefeq` goes through with no
  Church–Rosser, no standardization and no adequacy (verified by a
  dependency walker, and structurally — ShapeLogRel's 17-module import
  closure contains none of ChurchRosser/HeadReduction/UniqueTyping/
  Injectivity). Any proof of the rung is a proof of the leaf.
  Three corrections came with it: the β case holds a *path* between
  Pis, not a single edge, so the `PiEdgeInv` framing trades the leaf
  for the L4L-17 co-deliverable via `TypeDefEqPath.collapse` rather
  than avoiding it; there is a second, independent uniqueness site
  (`LRS.PatStep`, from `Pattern.Action.sound` holding at the type the
  action chose) which is NOT Π-injectivity and follows from raw type
  uniqueness alone; and the leaf is charged at the *contraction*, not
  the congruence — the β congruence needs no Π-inversion at all, while
  `IsDefEq.beta` demands the argument at the abstraction's OWN domain.
  The sort restriction does not help (sort-typedness constrains the
  result type, never the domain — machine-checked witness in the empty
  context). Stratification: probeS's producer-side obstruction does NOT
  apply here (both IHs fire at the types the inversion suite returns,
  before any path is traversed), but the consumer-side one applies
  verbatim — the ladder must be handed an anchor manufactured from the
  accumulated path, and that demand (`LRS.ChainAnchorAt`) is provably
  equivalent to a uniform stratification bound. So a perfectly
  stratified rung still could not be consumed. **Do not open the
  stratification work.**

  **Consolation, and it is substantial:** the same interderivability
  makes the CR ladder a free downstream CONSUMER of the leaf. Landing
  `ParRed(S).defeq_of_piPathInv` banks the whole ladder
  (`SubjectRedS`, `PiEdgeInv`, `PiEdgeObs`, …) as a native consequence
  that fires the moment the leaf lands — and retires the `sorryAx`
  Theory's `ParRed.defeq`/`StRed.triangle` currently carry. The
  inversion suite it needed (`IsDefEqStrong.app_inv'`/`.lam_inv'`/
  `.forallE_inv_path`, ~145 lines, structural, first-try) is worth
  landing on its own: each returns the `TypeDefEqPath` from the
  subject's own type to the declared type, eliminating the
  type-uniqueness fixups wherever the SExpr side inverts a typing at a
  converted type. **Remaining route for the leaf: the joint/adequacy
  route (`PiPathInv.of_adequacy`) — after this measurement it is the
  only one standing.** Root cause is not `SpineWF` but
  `LRS.ValTyPi2`/`LogRel` being `WShape`-indexed with no stratification
  index. Closure records: `plans/probes/probeP-pipathinv.lean`,
  `probeS-spinedepth.lean`. N2 is decided (capture-domain link on the
  consumer's premise at the telescope's own `headTy` index).
  Narrative:
  `plans/l4l-16c-adequacy-log.md`; gap audit:
  `plans/l4l-16c-buildp-premortem.md`.

  **2026-08-15 (second session): the stratification lever is REFUTED
  and the residual is renarrowed to the two root callbacks.** The
  "missing stratification index" root-cause note is now an autopsy,
  not a work item: `plans/l4l-16-stratified-observation-design.md` +
  `probeT-stratpi.lean` machine-check that voucher-as-data is
  conservative (`valTyPi2D_iff_bare`), the uniform bound is false
  (`uniformStratBound_false` via an unbounded-minimal-depth β-redex
  tower — and `chainAnchorAt_false`: the banked `ChainAnchorAt` Prop
  is itself false at every depth), and a full `LogRel` re-indexing
  inherits the wall at `trans` middles (`transMiddleCertAt_false`,
  σ-instances unbounded). Do-not-open is now a theorem. The
  **registered-endpoint narrowing** then landed
  (`plans/l4l-16-registered-pi-design.md` + `probeU-regpi.lean`):
  `PiPathInvReg` — Pi-path inversion with one endpoint a certificate
  telescope — survives the vacuity kill-shot (the CR ladder's β site
  has BOTH endpoints outside the registered class at every arity), and
  `regSpine_result_uniq` (argument-list induction anchored at the
  constructor's own telescope, replacing `SpineWF.result_path`'s
  spine-derivation induction whose `conv` edges lose the anchor)
  closes the entire chain-fold interior from `PiPathInvReg` alone.
  General-`PiPathInv` demands on the leaf path drop from
  chain-length × spine-length to exactly two — the root callbacks —
  and both provably escape the registered class (`rootRed_meets_beta`;
  `Pattern.Action` redex heads are never constructors). `PiPathInvReg`
  itself is not provable by path induction (U8: the class is not
  closed under one edge). Bankables landed the same session:
  `IndTyHeadNorm` reclassified as banked-consumer plumbing (all five
  consumers CR-conditional; soundness core `indTyShapeTransport`
  landed), the RectFrame index-upgrade residual dissolved additively
  (`CtorFrame.toRectFrame` at the recoverable `.indTy` type shape;
  probeR13 superseded; remaining follow-up is a RectFrame at the
  rec-app observation), and the δ-rank component has a
  consumer-shaped design probe (`probeD-deltarank2.lean`:
  `DeltaRankFields` + D0/D1 inhabitation with literal ranks;
  `ConstDefnDeepInstStep` produced outright; wiring plan = a new
  `Params.DeltaRank` class). **The typed-constructor-view probe then
  returned verdict (ii): the map is COMPLETE**
  (`plans/l4l-16-typedview-design.md` + `probeV-typedview.lean`, green
  first compile, no sorryAx). Retention dissolves the root callbacks
  as a theorem (`CtorChainT.foldRaw_of_anchorDiscipline` — `rootRed`
  becomes projection; the residual prices at `CtorSpineTypeUniqPath` =
  `PiPathInvReg`), but PRODUCTION of the typed view is impossible at
  the closure laws, each failure machine-checked independently:
  forward `whr` transport is equivalent to edge-splitting subject
  reduction whose β instance is verbatim the leaf's `piInv` charge
  site; backward `unwhr` transport is refuted outright
  (`ctorViewT_unwhrClosure_false`, K-redex + `PiNotFunTyped`); and a
  conv-closed typed view collapses all registered inductive head
  types into one path class. The anchored variant survives every law
  and dissolves nothing. The crown sub-question is independently
  closed: single-EDGE inversion at a registered endpoint inherits U8
  one level down (`regEdge_trans_middle_escapes` — a `trans` middle
  between two registered Pis is provably unregistered and non-Pi).
  **Consequently, with probeT (stratification), probeU (registration:
  interior only), and probeV (retention) all machine-refuted, no
  structural axis to the leaf remains.** The milestone choice is
  binary: (A) re-cut 16C′ to close conditionally, parameterized on the
  named Prop `LRS.PiPathInv` — the option `l4l-18a-prime-scope.md:448`
  already recommends, with `CtorChainT` recorded as the consumption
  interface the moment the Prop lands — or (B) fund the semantic
  normalization content (a new logical-relation development for
  subject reduction at classified spines) as its own research
  milestone. There is no option (C).

  **Decision (2026-08-15): take (A).** L4L-16C′ is re-cut as a
  conditional closure whose semantic boundary is the already named
  `LRS.PiPathInv`; the independent subject-reduction/normalization research
  moves out of milestone 16/17. This is not yet permission to wrap the
  existing leaf in that one premise: the buildP pre-mortem identified two
  mechanical obligations still visible after the constructor-chain roots
  consume `PiPathInv` — transport of the synchronized `RectFrame` from the
  native constructor observation to the recursor-application result, and
  the terminal fixed-head dominance comparison. Those remain 16C′ work and
  stay named separately until they have real producers. The δ side of the
  cut is now implemented: `HasTypeStratifiedR` and `Params.DeltaRank` expose
  a strictly decreasing definition certificate; the clean
  `ConstDefnDeepInstStep.of_deltaRank`/
  `ConstDefnDeepStepR.of_deltaRankStage` restart bridge is axiom-pinned; and
  D0, D1, and D2 instantiate literal ranks for every registered definition.
  No `VEnv.WF` cycle or opaque normalization premise is hidden in that
  interface.
- *L4L-16D — live-environment instance.* The only route segment never
  executed end to end — therefore staged, thin vertical slice first:
  **D0 complete (2026-08-14, active working tree):** the generated Nat
  fixture (both constructor iota rules) plus `d0def : Nat := Nat.zero`
  now runs through complete SExpr `Params`/`Params.Semantic` instances
  with `d0SortInvS` instantiated.  The D0 module is admission-free,
  its 122-job Lake target is green, and its exact endpoint axiom closure
  is pinned in-source; the remaining `sorryAx` is inherited from 16C′.
  **D1 delivered 2026-08-15 except the quot semantic
  instance:** `SExprParamsD1.lean` is admission-free — first live
  `VDecl.WF.mutualDef`, D0→D1 transport, full `Params.Semantic`,
  pinned `d1SortInvS`; the quot environment layer is in and pinned
  sorryAx-free, while the quot `Params`/`Semantic` instance is blocked
  on the Prop-wall design (the `hu0` deletion is refuted — see the
  16E entry and `probeA1-hu0.lean`) plus
  stuck-`Quot` injectivity of L4L-18A′ strength. **D2** ordinary/block
  inductive rules via `AssembledPat` — the union non-overlap
  mathematics is proved and landed in Theory 2026-08-15 (four laws +
  cross-term engine + exact `ExtSeparation` side conditions with a
  falsity witness; kernel `decide` only, `#guard_msgs`-pinned),
  leaving registry consumption. **Second 2026-08-15 session:** the
  rule-independent replay is now generic — `SExprTransport.lean` (R1:
  syntax transport generic in `univs` agreement, proof-complete) and
  `SExprGenericReplay.lean` (R2: the `Replay` certificate, generic
  type-uniqueness/spine-view tower, and the sorryAx-free
  `ruleCollapse` reify/`appN_lamN`/`mkS` chain proved once, plus the
  `iotaSiteOf` assembler); D2 consumes them through `d1StrongToD2`
  with unconditional `Semantic.ctor` (all five block bundles) and
  `Semantic.defn`.  The replay boundary has since been tightened and is
  exposed by `d2SortInvSExact` under `D2BlockStepExact`: the complete
  ten-rule RHS registry proves descriptor subsingletonhood, and
  `d2IotaRule_entry_elim` reduces every descriptor to the two literal Nat
  or five literal Tree entries.  The earlier checked contract was repaired
  to retain the actual capture typing, valid context, typed spines and
  successful match; both Nat checks are discharged outright, so its only
  remaining `D2TreeCheckedStep` premise is the five-rule
  L4L-18A′-gated stuck-inductive-application injectivity.  Recursor
  level-arity is also proved for all seven entries.  The other three exact
  fields are the seven capture spines, seven β-collapses, and five block
  registered towers—the per-rule volume the engine takes as input, exactly
  as Theory's generic block-rule theorem does. The D2 environment now also carries the same
  checked δ-rank certificate as D0/D1; block heads are irreducible at rank
  zero and the inherited definition dependency chain is ranked literally.
  Reduction sites do not transport downward, so the capture/collapse fields
  still re-cover the two inherited Nat rules;
  **D3** nested rules as registered equations only (nested pattern
  facts stay L4L-19A); **D4** registered structure eta from the
  L4L-15B registry certificate. Sources:
  `classify` from block certificates, `Pat` through the D020
  beta-collapsed coverage, non-overlap from the L4L-10B match-inversion
  library, and the `Semantic` fields from the eta registry, generation
  certificates, declaration history, and `IsDefEq.strong` plus beta
  collapse. Scope: the **SExpr** instances only; the Theory-side
  `Params`/`Params.Extension.join` live instance is consumed only by
  `IsDefEq.church_rosser` and moves to L4L-18A.
- *L4L-16E — promotion and joint co-deliverables.* Supported roots
  never import experiments: the consumed modules leave `Experimental/`
  with a stable API and a sorry-free path, the public
  `IsDefEqU.sort_inv` closes from the instances, and the audit
  allowlist shrinks 22 → 21. The joint co-deliverables land here from
  the same development: `IsDefEqU.forallE_inv_stratified`,
  `IsDefEqU.sort_forallE_inv`, `IsDefEqU.weakN_iff`,
  `VEnv.WF.registeredStructureHeadInversion` (whose projection
  consumers shed `sorryAx` automatically), general type uniqueness over
  weak SExpr defeq with admissibility/elimination of the heterogeneous
  `trans'` rule, and the re-run `IsDefEq.uniq`/`uniqU`, context
  inversion, and downstream `#print axioms` checks. The digama
  reconcile-or-defer decision (§7) is taken at this boundary.
  2026-08-15 recon (checklist: `plans/l4l-16e-promotion-map.md`): both
  co-deliverable statements already exist sorried in the trusted tree;
  `registeredStructureHeadInversion`'s two constructor fields are
  false as stated and need a head-classification premise before proof;
  the `weakN_iff` forward design pass (2026-08-15,
  `plans/l4l-16-weakn-design.md`) returned research-grade — now 2.5–5
  weeks serial / 8–11 staged agent sessions via de-circularized
  stratified standardization, with machine-checked obstructions
  killing every shortcut route, the W2/W3 rungs already proved (and
  strengthened) the same day, and the coupled `NormalEq`/CR cores
  (W5+W6) carrying the residual risk — and recommends re-scoping it
  plus the dependent
  `registeredStructureHeadInversion` fields to an L4L-18A′-coupled
  slice, decision pending; promotion is additionally gated on the four
  off-path `SExpr.lean` sorries and the frontier-audit import
  regeneration. The generic-instance construction behind "closes from
  the instances" got its own design pass the same day
  (`plans/l4l-16-generic-instance-design.md`): a conditional instance
  is refuted as a route, the D-ladder's transport pattern *is* the
  induction step, and the recommendation is a named successor
  milestone **L4L-16F** rather than a 16E step or a D4 endpoint —
  with `CtorBundle.hu0` recommended for outright deletion — **a
  recommendation REFUTED 2026-08-15 by the executed discriminating
  experiment** (`plans/probes/probeA1-hu0.lean`): the ADQ consumption
  site is free, but `build_spine`'s post-deletion statement is false
  for Prop-sorted ctor-classified pattern-argument heads, because the
  shape algebra's proof-irrelevance law (`WShape.HasType.proofIrrel`)
  requires `.indTy` non-Prop-sortedness and `hu0` is that law's
  syntactic mirror. Resolving the Prop wall needs a
  Matches/classification-level design (Prop-branch, or excluding
  Prop-recursor iota patterns from `Pat`), so D1's quotient half stays
  blocked on that design plus stuck-`Quot` injectivity.

*Exit:* the public `sort_inv` sorry and the merged inversion/uniqueness
statements are removed with exact accepted axiom closures — no
`sorryAx`, no `extra_pat`-style axiom, and no environment oracle on any
path — and the route record carries any residual semantic-route debt.

**L4L-18A — Church–Rosser `.extra` cases.**
*Promoted 2026-08-15: L4L-18A′ is a HARD DEPENDENCY of the 16C′ leaf,
not a later cleanup — but it is not sufficient for it either.* The
leaf's residual `LRS.PiPathInv` factors as `SubjectRedS` + `PiEdgeInv`
+ `PiHeadNorm`; the CR ladder supplies all three (`PiPathInv.of_crLadder`,
machine-checked), with `PiHeadNorm` coming from CR + **standardization**
rather than from any normalization theorem — `TypeWHNFEx` is not
needed. What CR cannot supply is **sort/Pi shape disjointness**, which
the leaf provably entails; scope that separately (see the 16C″
recommendation in `plans/l4l-18a-prime-scope.md`, whose ladder has 12
rungs with R1–R4 parallel-attackable and 8 of 12 already
machine-checked). Implement by transport via `reify` rather than
porting. Correction to `SExpr.lean:4371`: its comment claims nothing on
the L4L-16 gate path consumes `CRDefEq.trans` — that clause is now
false (recorded as the type-checked `LRS.crDefEq_is_on_the_gate_path`).
Also: `SExpr.WHRedS.defeq` (:4033) is not separate work — it follows
from `ParRedS.defeq`; and `HeadReduction.lean` is sorry-free but
tainted three ways, one of them (via `sort_inv`/`sort_forallE_inv`)
previously unrecorded.

**2026-08-15: one hole closed, the other is FALSE as stated.** The
`constDF` × `.extra` case is discharged (additively, `:939-1041`),
which needed only two of the four predicted lemmas — level congruence
for `RHS.apply` and `Check.OK` transport. The key was
`EqUpToLevels.instL_equiv`, a purely SYNTACTIC congruence: the existing
`EqUpToLevels.instL` demands an `IsDefEqStrong` derivation, which a
closed `Pattern.RHS.fixed` template does not have. `EqUpToLevels` was
also missing symmetry. The `appDF` × `.extra` case is refuted under
`[Params]` alone by an explicit counterexample: with a `Prop`-typed
argument position, `.app rec (.bvar 0)` is reduction-normal while
`.app rec ctor` contracts, and NO `NormalEq` constructor relates the
results (`structural` is uninhabited without structure-eta,
`proofIrrel` would need the result type in `Prop`). This is not
adversarial — Lean's own large-eliminating `Prop` inductives realize
it (`Acc.rec`/`Eq.rec` at a `Type`-valued motive; for `Eq` the kernel
recovers by K-style reduction, which the pattern language cannot
express). Weakest known fix: a new semantic side condition — if a
registered contraction's argument position is `Prop`-typed, its result
is `Prop`-typed — i.e. a NEW `Params` field, machine-checked in
`plans/probes/probeCR2-extra.lean` to close the whole sub-case. That
fires §7.1 of the scope doc ("if R3 needs a new field, the estimate is
the wrong shape"). Note the predicted blocker was wrong: proof
irrelevance at a pattern-spine HEAD is already handled; the problem is
at a pattern ARGUMENT.

The holes in `NormalEq.parRed`
are the constant/application cases where a parallel step meets a
proof-carrying user-defeq pattern step. Use the generic `Params` pattern
combinatorics, L4L-10B's match
inversion/non-overlap library, and rule RHS congruence to prove the
commuting diagrams, keeping the theorem generic in `[Params]`. Neither hole
requires `[Params.Extension]`: each operational step already carries its
local equality certificate, while the global join instance is consumed only
by `IsDefEq.church_rosser`;
`ParRed.triangle`'s `.extra` case is the working template. The concrete
missing lemmas: (1) `NormalEq` match inversion/spine descent — the `≡ₚ`
analogue of the existing `ParRed` inversion, with proof irrelevance at a
pattern-spine head the genuinely open sub-case; (2) `Check.OK` transport
along `≡ₚ` and `≈`-equivalent level lists, extending `Check.OK.map`;
(3) level-congruence for `RHS.apply` on closed templates under
`Forall₂ (· ≈ ·)` — bridge `EqUpToLevels.instL` into a
`NormalEq`/`IsDefEq` congruence; (4) routine typing side conditions at
the transported match. The SExpr-side `CRDefEq.trans` mirror was deleted
at the L4L-16B′ checkpoint precisely because it subsumed this milestone
(it needed `CParRed`, `ParRed.triangle`/`church_rosser`, and
`NormalEq.trans`, none of which exist SExpr-side): land the argument once
against the finished Theory script here, and re-add an SExpr mirror only
if a promoted API turns out to consume it. This milestone also owns, per
the 2026-08-13 re-cut, constructing the Theory-side live
`Params`/`Params.Extension.join` instance that `IsDefEq.church_rosser`
consumes — its four structEta/forallE inversion fields are supplied by
the joint L4L-16 co-deliverables, which is why it sits here and not in L4L-16D.
*Exit:* `ParRed.church_rosser`, normal-form uniqueness, and the live
standardization/head-reduction endpoints contain no hidden placeholder
assumptions.

### Checker closure (L4L-19A–L4L-19C)

Digama upstream carries two unabsorbed checker-side commits past the
reconciled `b292275c` (stage-2 environment replay; enabling the new level
algorithm — see the §2 remote-drift row) that land in exactly this
territory. The reconcile-or-defer decision made at the L4L-16 boundary
precedes detailed L4L-19 scoping; if deferred, repeat the check here.

**L4L-19A — recursor reduction verification.** Prove `reduceRecursor.WF` for
Quot and certified inductive rules, obtaining the selected rule, match,
checks, RHS translation, and result typing from the generated/translated
metadata — not from a global oracle. For nested blocks this requires the
σ̂ β-collapse bridge left open in `NestedTransport` — transporting the
flattened block's rule defeqs and pattern facts onto the restored
`appendIndexAfter` artifacts — and extending the certificate pattern
surface accordingly (`NestedBlockCertificate` currently exposes no
`ruleClosure`/`IotaPat` facts).
*Exit:* Quot, singleton, mutual, and nested recursor reductions pass;
enclosing WHNF roots have exact guards.

**L4L-19B — environment-to-checker closure.** Prove the remaining
nonprojection checker refinements (the v4.33 front-end `addDecl.WF` — now
only its `inductDecl` case — plus the D017 `checkPrimitiveDef.WF` and
extension-transport entries and the re-sorried `addQuot.WF`) and full
`TrEnv` over fixture environments containing ordinary
declarations, Quot, single/mutual/nested inductives, literals, structures,
and extension defeqs; state and audit the final executable-checker soundness
theorem over this full environment class.
*Exit:* the complete environment corpus and final checker root build with
exact closures; only the mechanical zero-sorry policy switch remains.

**L4L-19C — zero-sorry gate.** Remove every remaining supported Theory/Verify
sorry. Keep the audit allowlist exact throughout: every proof PR deletes
entries, and no PR may rename/move a sorry and merely update the allowlist.
At zero, reduce the allowlist to the deliberately kernel-rejected fixture
recoveries so any sorried declaration fails outright.
*Exit:* the proof-debt frontier is zero, only fixture-recovery entries
remain, and full gates pass.

### Trust closure and release (L4L-20A–L4L-20C)

**L4L-20A — axiom reachability and retirement.** Generate the actual
transitive closure for every supported root rather than hand-maintaining §3.
The root set contains at minimum the exported
checked-inductive/transaction/preservation roots and the consumer-facing
checked-inductive/projection API; the unique-typing, Church-Rosser,
standardization, and head-reduction endpoints; and the public checker
operations with the final executable-checker soundness theorem. Each row
records the root, layer, standard axioms, project axioms, §3 classification,
pinned Lean revision, and disposition; keep normalized output under version
control or as a deterministic CI artifact so a dependency change produces a
reviewable diff, generalizing the existing local `#guard_msgs` mechanism.

Acceptance states: (1) logical baseline; (2) platform contract — narrowly
stated, manifested, version-pinned, tested, absent from Theory roots;
(3) transitional bridge — named, classified, with a removal issue, never a
silent release assumption; (4) forbidden — known false on a supported
toolchain or unproved after the implementation changed.

Immediate pre-work is already scoped by the 2026-08-10 audit, as amended
2026-08-12: delete the three dead axioms (`Level.mkLevelIMaxCore_eq`,
`Expr.liftLooseBVars_eq`, `Expr.equal_eq`); upstream's merged v4.33 proofs
consume `TreeMap.all_eq_all_toList` again, and the unmerged
`origin/ap/prove-treemap-all` branch would turn that axiom into a theorem
at a future reconciliation. After the L4L-13A/B `sorryAx`
shed the forbidden cached-field trio sits in many sorry-free closures, so
the forbidden-axiom CI rule waits on their actual retirement rather than
a two-root cleanup. Then retire in risk order: the three remaining
cached-field equations; the
remaining reference equations (convert to logical definitions with
`@[implemented_by]` only when extensionally correct); the collection and
opaque/layout equations (replace with upstream theorems or narrowly bounded
WF lemmas); then decide the final platform budget explicitly (expected: the
two pointer-equality implications, possibly lawful level `BEq`). CI must
reject a new unclassified project axiom, any project axiom in a Theory root,
any forbidden axiom in a supported root, a retained platform contract without
manifest entry and tests, and `[simp]` on any project-specific axiom.
*Exit:* the report regenerates from a green build with every dependency in
an accepted state; no project axiom reaches Theory.

**L4L-20B — complete differential corpus.** Automate a harness that
elaborates fixture declarations with Lean, translates the resulting raw
environment metadata, constructs the justified analysis view, and compares it
with Theory generation, across the fixed inductive, projection, prelude, and
extension corpus. Compare failures as data: accepted/rejected, raw/view
normalization stage, generated constants, universe lists, field counts,
recursive positions, K flag, rule count, and every RHS.
*Exit:* CI compares acceptance phase, metadata, generated constants,
universes, recursive positions, flags, rules, and every RHS; all supported
cases pass.

**L4L-20C — upstream series and release.** Submit dependency-ordered semantic
PRs: (1) level-normalizer proofs and small generic lemmas; (2) Theory API
extraction with compatibility re-exports; (3) the staged inductive vertical
slice and fixtures; (4) indexed/normalization/small-elimination/
recursive-argument support; (5) mutual and nested support; (6) the pattern
package and Verify `AddInduct` alignment; (7) the projection structure view,
laws, and checker proofs; (8) injectivity/Church-Rosser completion; (9) the
remaining checker and axiom-minimization work. Do not rewrite published
`jcb/formalization2` checkpoints: each PR series is extracted onto a fresh
review branch rebased on its current upstream target. Do not mix the large
Nix/fork-infrastructure delta into proof PRs unless upstream asks. Record
every PR in the divergence ledger.
*Exit:* the final release revision is green; every fork delta is upstreamed
or has an owner, issue, and removal condition; release artifacts and
manifests are reproducible.

## 6. Gates and process

Every milestone must pass all applicable gates:

```text
lake build Lean4Lean.Theory Lean4Lean.Verify
lake build Lean4Lean.Audit.SorryFrontier
lake build
nix build --accept-flake-config .#lean4lean .#lake-dependency
nix flake check --accept-flake-config --print-build-logs
nix fmt --accept-flake-config -- --check flake.nix
git diff --check
```

The dev-branch fileset flake does not support eval-only checking
(`nix flake check --no-build` fails with "path '…-source' is not valid", as
documented at the `leanSrc` definition), so the flake gate builds for real;
non-Linux systems stay declared but ungated, matching dev CI.

Plain `lake build` covers Lake's `defaultTargets` (`Lean4Lean`,
`lean4lean`, `Lean4Lean.Theory`, `Lean4Lean.Verify`, `Lean4Lean.Tests`);
`Lean4Lean.Experimental` is a separate lib outside every gate and builds
only via `lake build Lean4Lean.Experimental`. A red experiment therefore
never blocks a checkpoint, and conversely a green gate claims nothing
about `Experimental/` — promotion at L4L-16E is what moves the semantic
development into the gated surface.

The flake is authoritative: milestone evidence must use the pinned Nix
toolchain and dependencies. The Lake commands above run directly from the
already active `nix develop` shell; from outside that shell,
`nix develop --command lake ...` is equivalent. Elan or another host `lake`
never substitutes for the pinned-shell Lake builds, `nix build`, or the flake
checks above.

Additionally:

- all new fixtures build in a default proof target;
- new theorem roots have checked `#print axioms` output;
- every named root satisfies the boundary-specific axiom threshold in §3,
  with no `sorryAx` or project-specific dependency in a Theory root;
- `rg '^import Lean4Lean.Verify' Lean4Lean/Theory` is empty;
- every source/view pair accepted by the public checked transaction is
  generated and preserved by the same artifact path; temporary
  direct/generalized or raw/normalized migration functions are not both
  semantically live at a checkpoint;
- exported Theory names change only additively, through compatibility
  re-exports and a deprecation window;
- the kernel differential matrix is green for inductive/projection changes.

**Publication.** Publish only after the complete gate passes on one committed
checkpoint; never publish a red or semantically split state (for example
midway through an artifact or transaction switch). Only
`origin/jcb/formalization2` moves; local/remote `master` and every
digama/upstream ref move only at explicit reconciliation checkpoints, and
remote-ref verification is part of each publication. Keep published
checkpoints recoverable, and refresh the divergence ledger and sorry-frontier
wording with each checkpoint.

**Downstream consumers.** Lean4Lean is an independent upstream. Downstream
projects pin published green checkpoints and are responsible for their own
migrations, audits, and pin cadence; their demand analyses, oracle
constructions, and migration protocols live in their own repositories and do
not gate this ladder. Consumer worktrees, lockfiles, and branches stay out of
lean4lean commits. What this repository guarantees to consumers: published
checkpoints pass the complete gate; exported Theory APIs are consumer-neutral
and change additively with compatibility re-exports; the trust story (exact
per-root guards, the tracked sorry frontier, the divergence ledger) travels
with every checkpoint; and consumer-facing semantic obligations are met by
strengthening the checked-block API here, never by asking a consumer to
assume an oracle or axiom.

## 7. Principal risks and decision points

- **Checkpoint drift.** The `jcb/formalization2` line is ahead of `master`,
  and the local head runs ahead of `origin/jcb/formalization2` between
  publications. Keep published checkpoints recoverable, require
  Linux/Darwin CI builds at release boundaries, and record any replacement
  hash here.
- **A subset masquerading as the spec.** A sorry-free `stageN` definition can
  still be incomplete. Final acceptance is kernel coverage plus negative
  agreement, not the absence of sorries.
- **Analyzer/artifact drift.** Guarded for the current subset: analysis,
  public accessors, preservation, transaction output, and Verify metadata all
  consume the same generalized artifacts. Keep the kernel-equality and alias
  fixtures as regressions; older direct/raw-only definitions remain
  compatibility specifications only.
- **Normalization as an accidental oracle.** Shape equality alone does not
  justify a rewritten declaration, and whole-type defeq alone does not
  identify raw binder positions. Require `Normalization.WF`, structural
  raw/view pairing, and derivation from checker or consumer defeq evidence.
  Runtime agreement with opaque `consumeTypeAnnotations` is a producer
  consistency check, never semantic authority. Never accept an arbitrary
  supplied view; never repair a missing reduction theorem with a custom
  axiom.
- **Raw de Bruijn scaling.** Indexed, mutual, and recursive-Pi rules multiply
  lift/inst arithmetic. Keep moving normalized evidence into the descriptor
  and telescope lemmas rather than duplicating index calculations.
- **Structure eta changes Theory as a tracked divergence.** The new defeq
  constructor affects injectivity, confluence, standardization, and
  downstream consumers. The design note and ledger entry come first
  (decision 2026-08-11); upstream review moves to the L4L-20C PR series,
  and every reconciliation checkpoint revisits the divergence.
- **Pattern-interface divergence.** The upstream `Params` fields
  (`extra_pat`'s syntactic match, `pat_wf`'s bare-`HasType` premise)
  cannot be satisfied by tower-registered environments, including
  `quotDefEq`. L4L-18B resolves this with proof-carrying contractions,
  beta-collapsed coverage, and `Params.Extension.join` (ledger D020).
  The residual risks are a larger upstream-review surface at L4L-20C and
  reconciliation conflicts wherever upstream's own `Params` and
  experimental work move — keep the redesign minimal, ledgered, and behind
  compatibility shims where feasible.
- **Research-branch optimism.** The in-tree `SExpr`/`ShapeLogRel`
  development is evidence of a viable path, not a drop-in solution. The
  two remaining optimism hazards: the joint level-indexed
  uniqueness-with-adequacy induction is a novel structure whose
  well-foundedness must be verified at design time — the recorded
  fallback is the first-order staging option in the completion plan,
  which restores a closable milestone at reduced scope — and L4L-16D's
  live-environment instance is the one segment of the route that has
  never been executed end to end.
- **Unsound bridge axioms.** Some cache equations were documented false on
  older pins and remain unproved. Zero sorries is not a soundness claim until
  final-root axiom reachability is clean.
- **Upstream collision.** Repeat the ancestry and overlap check at every
  milestone boundary; if upstream advances again, insert another explicit
  integration checkpoint rather than hiding merge work inside a semantic
  milestone. The 2026-08-12 check found digama `upstream/master` two
  checker-side commits past the merged `b292275c` (§2 remote-drift row);
  the reconcile-or-defer decision is due at the L4L-16 boundary.
  `origin/master`'s one-commit advance is already in the fork's ancestry
  and needs no action.
- **Scope leakage from Experimental.** No supported root may import
  experiments. Promote a proof only after removing its experimental sorries
  and giving it a stable API.
