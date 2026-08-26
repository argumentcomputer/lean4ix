# Lean4Lean upstream divergence ledger

This file tracks every deliberate semantic, API, build, or verification delta
from `upstream/master` that must either be upstreamed or explicitly retained.
It is the tracked counterpart to `plans/roadmap.md`.

Audit baseline after the complete L4L-12B literal-readiness checkpoint
(2026-08-10):

- current upstream reconciliation parent: digama `upstream/master`
  `ef849dfbd94a`
- historical generation-readiness comparison upstream: `0c38ab8`; the
  ahead-of-upstream counts below use this older baseline
- published semantic checkpoint:
  `cf3d5a47d35867e0e6ebe023c0803982e3e36cd1` (33 commits ahead of upstream)
- first published documentation child:
  `d35a2f6c94212faae20d5a03341b138bb0e22d36`
  (`docs: record IndexedVec semantic checkpoint`; 34 commits ahead of
  upstream). It changes only this ledger relative to `cf3d5a47`.
- source-indexed list checkpoint:
  `c9e4ae2d26f28e0adb0c21ffde0e11b42bb691c2`
  (`feat: generalize candidate list production`; 35 commits ahead of upstream;
  32 files changed, 38,205 insertions, and 59 deletions)
- generic produced-package checkpoint:
  `a7d101b5e16f1258c6f5c2a7ea08e55f45eb17f1`
  (`feat: generalize produced candidate packaging`; 37 commits ahead of
  upstream; 3 files changed, 49 insertions, and 30 deletions)
- retained semantic-hierarchy checkpoint:
  `f0caf16c5788d094fdbf1e990884c0c061d6fc75`
  (`feat: retain candidate semantic hierarchy`; 39 commits ahead of upstream;
  3 files changed, 432 insertions, and 111 deletions)
- produced semantic-hierarchy checkpoint:
  `e3cf22d293b081ba11be63e910d0d1e1510a042f`
  (`feat: assemble produced semantic hierarchy`; 41 commits ahead of upstream;
  3 files changed, 608 insertions, and 39 deletions)
- semantic-hierarchy ownership checkpoint:
  `7e5f4f7715cf71be8d09a583f0ec0d8f7aa02e72`
  (`feat: harden semantic hierarchy ownership`; 42 commits ahead of upstream;
  3 files changed, 670 insertions, and 25 deletions)
- structural generation-evidence checkpoint:
  `2b1d802fc6796e7317ec1d24708a3ebdda416655`
  (`feat: derive structural generation evidence`; 44 commits ahead of upstream;
  4 files changed, 445 insertions, and 100 deletions)
- generation analyzer-provenance checkpoint:
  `a64fe982bc2a7f1c6c34ec82565ec5fe1c26350b`
  (`feat: derive generation analyzer provenance`; 46 commits ahead of upstream;
  4 files changed, 138 insertions, and 22 deletions)
- generation shape-alignment checkpoint:
  `5aa9ab69fce1c7dab3f4ca357f6ed8f349fd9397`
  (`feat: derive generation shape alignment`; 48 commits ahead of upstream;
  3 files changed, 458 insertions, and 180 deletions)
- consolidated generation-readiness checkpoint:
  `bbb45e0e950724cdbbd405d75e304e2020cecf82`
  (`feat: consolidate generation readiness`; 50 commits ahead of upstream;
  3 files changed, 701 insertions, and 98 deletions)
- upstream v4.31 reconciliation checkpoint:
  `7f864b459e4a6062b468d6e5416688feac0f9f99`
  (`merge: reconcile upstream v4.31`; second parent digama
  `upstream/master` `ef849dfbd94a`)
- retained constructor-validation checkpoint:
  `097efb45018136df32c2f6e0dbbbbf7c7106c149`
  (`feat: retain constructor validation traces`)
- local-committed constructor-universe semantic checkpoint:
  `a246c048390c7f3c3a06f87fdb94b23ef671681f`
  (`proof: establish constructor universe foundation`; 5 files changed,
  1,686 insertions, and 3,608 deletions, including the roadmap rewrite).
  Publication to the fork's `jcb/formalization2` branch is pending.
- local-committed post-family constructor semantic checkpoint:
  `37d2dd998e626e25cda8874d9f6a32f85288bb91`
  (`proof: establish post-family constructor semantics`; 5 files changed,
  3,963 insertions, and 1 deletion). Publication to the fork's `jcb/formalization2`
  branch is pending.
- local-committed pre-family constructor safety checkpoint:
  `9e40cbe00e9c6fe808ebb0720c912bba21aa1b06`
  (`proof: establish pre-family constructor safety`; 5 files changed,
  3,482 insertions, and 1 deletion; 67 commits ahead of the reconciled
  upstream). Publication to the fork's `jcb/formalization2` branch is pending.
- local-committed analyzer-owned constructor view-WF checkpoint:
  `98921daf15aa` (`proof: establish analyzer-owned constructor view WF`)
- local-committed generic singleton package checkpoint:
  `ae6726cef1e1` (`proof: establish generic singleton package closure`)
- local-committed project level-normalization checkpoints:
  `70c02b0e89d8` (`proof: establish level subsumption evaluation`) and
  `a72979db8cd3` (`proof: establish level equivalence soundness`)
- local-committed constructor level-comparison checkpoint:
  `de3d98c9fc5fd066b2ab88ec450e01402ed38357`
  (`proof: verify constructor level comparison`). Publication to the fork's
  `jcb/formalization2` branch is pending.
- remote development checkpoints for L4L-03 at `jcb/formalization`:
  `3e6efcce` (`proof: widen D3 constructor replay`), `53d5f923`
  (`fix: emit recursors over checked parameters`), `bb883178`
  (`test: cover definitionally equal constructor parameters`), and
  `04a1a4f29de4` (`proof: certify definitionally equal parameter replay`).
  Publication to the fork's `jcb/formalization2` branch is pending.
- remote development elimination/K checkpoints at `jcb/formalization`:
  `37e2ada60b04` (`proof: certify elimination mode and recursor levels`) and
  `41e1126bb587` (`proof: certify recursor K-target metadata`), followed by
  `0c6b178cc1bd` (`proof: cover empty and singleton generation edges`) and
  `df58a3a00087` (`proof: close empty and singleton edge parity`).
- remote development L4L-07 checkpoints at `jcb/formalization`:
  `bb39cb2ace0c` (`verify: add singleton parity matrix`),
  `cc132cddb874` (`verify: add singleton rejection and replay inventories`),
  and `fefb93fe15e9` (`verify: replay all fixed singleton families`), followed
  by `9910e14e8cdf` (`verify: close L4L-07 singleton parity`) with the exact
  trust manifests and ledger closure.
  Publication to the fork's `jcb/formalization2` branch is pending.
- remote development mutual-block checkpoints at `jcb/formalization`:
  `79e1ae4f697c` adds the L4L-08A source-indexed dependent family spine,
  shared block parameters, per-family indices/results/constructors, and
  block-wide recursive-target ordinals. The L4L-08B closure adds
  executable block validation/normalization, all-family staging, exact mutual
  semantic certificates, phase-local negatives, and recursive-Pi target
  traces. L4L-08C then lands block generation and its typing chain in
  `12040b3e`, `3d97ac16`, `6311fa69`, `48882b9c`, and `67d65928`; complete
  metadata comparison in `1d280960`; Theory/Verify environment replay in
  `eeae5282`; the block-wide public raw transaction in `1159c655`; and the
  metadata/trust audit in `aa10005d`; this closure checkpoint adds the
  deprecated singleton migration shim and completion records.
- local-committed nested-inductive checkpoints at `jcb/formalization2`:
  representation and flattening from `e0ee54e` through `b8899c7`, restored
  generation/real-output alignment from `4b3d449` through `3475370`, typed
  constant-interpretation transport in `b71ab5c`, and the two real replay
  closures `a77e358` and `e297560`.
- local-committed generated-pattern checkpoints at `jcb/formalization2`:
  the certified-block iota-pattern core `3689b11` and typed pattern soundness
  plus the block-local environment assembler `bc51f98`.
- L4L-11 closure checkpoint: the consumer-neutral block/nested
  certificates, complete 25-row actual-metadata replay matrix, real queued
  two-parameter nested replay, and 296-declaration notation-prelude replay
  described in D013. Publication is pending.
- L4L-12A extraction checkpoint `958d03b7`: the Theory-only local-context and
  literal encoding APIs plus Verify compatibility re-exports described in
  D014, based on `0587b91a`.
- L4L-12B readiness checkpoint: the exact prelude contract, derived literal
  WF, and Verify/direct translation agreement described in D014, layered on
  `958d03b7`. Publication of both checkpoints is pending.
- fixed fork master: `1fb7d6ef9042c5a80b2de9320c88ac0f3ce404cb`
  on local and `origin/master`
- audited L4L-08C semantic base: the L4L-08C closure extends the
  `jcb/formalization` L4L-07 base, which integrates Nat, Bool, List, Option,
  Prod, Unit/`PUnit`,
  Empty, Or, And, Eq, HEq, Fin, Vector, and Acc into one executable kernel
  parity matrix, alongside five normalization cases and a consolidated
  32-case rejection matrix. The fixed rows compare ordinary-producer
  acceptance and all stored family/constructor/recursor/rule metadata,
  including exact translated universe order and every iota RHS. All 14 fixed
  families and the five normalization cases then replay actual `ConstantInfo`
  through proof-carrying environment transactions to final `Aligned` and
  `Ordered` outputs. Fin and Vector carry their exact aligned dependency
  slices. The umbrella exposes `SingletonParityReplay` as the sole L4L-07
  artifact path. On top, `CheckedBlock` analyzes arbitrary nonempty family
  lists through `CheckedFamilies source params ordinal types`, so exact source
  order and target-family numbering are indices of the representation rather
  than unchecked parallel data. `ValidatedBlock.WF` and
  `ValidationCertificate` pair that structure with arbitrary-block
  normalization, one shared semantic result universe, all-family staging, and
  constructor semantics. `BlockGenerationChecked` then constructs one motive
  and recursor per family, one globally flattened minor/rule inventory, and
  target-family-directed recursive calls. The transaction exposes exact
  all-family/all-constructor/all-recursor/rule phase boundaries and preserves
  ordering, lookup, freshness, and rule membership. Tree/TreeList and
  IndexedTree/IndexedTreeList execute the exact ordinary validator phases,
  compute recursive targets including Pi-hidden sibling recursion, compare
  every family/constructor/recursor/rule metadata field represented by Theory,
  and replay the actual metadata maps through `TrEnv'.inductBlock` to final
  aligned environments. The raw public `addInduct` consumes the same block
  artifact; `addInductSingleton` retains the former one-family raw wrapper for
  a deprecation window. Mismatch/reordering negatives still pin the nearest
  kernel phases. Exact closure guards and the full completion gate are recorded
  in the roadmap.
- generation-readiness source checkpoint: `bbb45e0e` builds on the exact
  arbitrary-length
  producer witnesses and source-indexed semantic inputs that return a
  `Nonempty ProducedNormalizationCandidateSemanticRun`. The retained checker
  selects every Theory view; callers provide verified contexts and strict
  source translations, never a view. Semantic generation wrappers project
  family and constructor spines from that same hierarchy, so normalization,
  generation, packaging, and produced packaging cannot substitute parallel
  roots. AliasFormer, AnnotatedPi, and `IndexedVec` all use this ownership path.
  `IndexedVec` additionally proves that automatic assembly preserves its exact
  `nil`/`cons` order and rejects a swapped view at the computational shape
  gate. Exact compile-time guards cover the generic constructors, projections,
  and fixture roots. Exact checked family/constructor shape now recovers every
  candidate view telescope; the checked family result level supplies family
  terminal typing; and one typed post-family family constant plus each checked
  constructor-result spine supplies every constructor target judgment.
  AliasFormer, AnnotatedPi, and `IndexedVec` no longer provide `viewTel` or
  `rightType`; the former circular `IndexedVec` terminal-typing helpers are
  deleted. `GenerationCandidateRun` now retains the exact successful dependent
  `generation?` equation instead of a fixture-provided normalization equality.
  Theory proves that successful `check?` and `generation?` results retain their
  analyzed normalization, so the candidate/analyzer normalization equality is
  derived generically. Verify also reconstructs post-family `VEnv.WF` from the
  verified pre-family context, candidate raw/view definitional equality,
  checked family typing, and exact raw-family insertion. AliasFormer,
  AnnotatedPi, and `IndexedVec` therefore provide neither `normalization_eq` nor
  `typeEnv_wf`; each supplies only its exact analyzer-success equation. The new
  reduced generation-shape boundary also prevents fixtures from choosing
  normalized constructor pairs or supplying raw/view component equations.
  Exact analysis determines the raw family, checked family view, complete
  normalized constructor list, and every positional raw/view pairing. A total
  stored-spine count then determines each raw telescope and result, while
  checked shape determines each view terminal. The source-indexed recursive
  assembler preserves the analyzer's full constructor order without `zip`,
  lookup defaults, truncation, or reordering. AliasFormer, AnnotatedPi, and
  `IndexedVec` no longer supply checked WF or any per-family/per-constructor
  shape records. A strengthened executable producer retains the exact ordinary
  producer equation together with one complete generation-spine check over
  the family and constructors. Exact dependent analysis plus WF of the
  analyzer-owned view declaration derives checked WF, and the one Boolean gate
  derives every
  positional stored-spine/count record without `zip` or truncation. Bare
  producer success is deliberately not treated as semantic or spine-shape
  authority. The exact 20-sorry frontier, focused direct compiles, 157-job
  default Lake build, 124-job Theory/Verify and Nix proof builds, default Nix
  build, all six current-host flake checks, all-system no-build evaluation,
  formatter, Theory import-boundary, and whitespace checks pass at that
  checkpoint. Use the branch ref, not a detached Git `HEAD`, for published-fork
  comparisons.

- upstream v4.33 reconciliation checkpoint (L4L-15R, 2026-08-11): the
  working-copy merge on `jcb/formalization2` whose second parent is digama
  `upstream/master` `b292275c` ("perf: skip the NormLevel for levels with no
  essential imax"; upstream advanced past the planned `1a16b72d` before the
  merge executed, so the reconciliation took the actual head). Toolchain
  v4.33.0 final (upstream pins v4.33.0-rc2 — see D018); lean4-nix input
  repointed to `argumentcomputer/lean4-nix` (`fromToolchainFile` API).
  Upstream absorbed since `ef849dfb`: verified standard-library level
  operations (`Verify/LevelStd.lean`) plus sound-and-complete primed
  comparators; front-end declaration checking #28 (`addDecl.WF` proved for
  every kind except `inductDecl`, `VEnvAt`, `Environment/Checker.lean`,
  `Extension.lean`, `Boundaries.lean`); unsafe/mutual definition blocks
  (`TrEnv'.ignore`/`mutualDef`/`thm`); dead `cheapRec` removal; the new do
  elaborator; and `isZero → isAlwaysZero` in inductive universe checks.

- upstream v4.33-drift reconciliation checkpoint (L4L-16R, 2026-08-20): the
  working-copy merge on `jcb/formalization3` whose second parent is digama
  `upstream/master` `e0e3f6bc` (five commits past `b292275c`). Absorbed:
  stage-2 fresh-replay environments (`Environment.empty (stage₁ := false)`),
  the level-algorithm enable (`isEquivList := all2 isEquiv'` converged;
  `geq → geq'` in constructor universe checks, propagated through
  `ValidationTrace` and the fixture replays), the `lazyDeltaProjReduction`
  restructure (`ReductionStatus.true`/`.false tn sn`, `reduceProjCore`
  split — the fork's proof now discharges upstream's `reduceProjCore.WF`
  sorry, see D022), the `isKTarget`-before-`mkRecInfos` phase alignment,
  upstream's three new `divergences.md` entries, and the self-contained
  `Theory/LevelSat.lean` coNP-hardness reduction. Kept fork-side: toolchain
  v4.33.0 (D018), `Tests` in `defaultTargets` plus the fork's CI structure
  (D021), the D012 sort-routing residue, and the 16C′w Experimental
  deletions (upstream's `def → theorem` hunks in files the fork removed
  resolve as deletions; the five remaining zero-token parked stubs —
  `StepIndexed`, `CoinductiveLogRel`, `Stratified`, `StratifiedUntyped`,
  `Stronger` — were deleted as import-leaves per the 16R plan). The sorry
  frontier is unchanged at exactly 22 entries; V6
  (`aliasFormerAlignmentRun`) was attempted and remains the allowlisted
  sorry, with the v4.33 kabstract-transparency findings recorded at the
  declaration.

Status vocabulary: `worktree`, `local-committed`, `published-fork`, `submitted`,
`upstreamed`, or `intentional-fork`. `published-fork` means pushed to an
Argument Computer fork branch but not yet submitted upstream. An entry is
removed only after its removal condition is met and every consumer has moved
to the replacement.

## D001 — Nix packaging and downstream artifacts

- **Status:** published-fork
- **Commits:** `e4c46ec`, `29d017f`, `5ad48f9`, `ae43b7b`, plus the
  all-system evaluation repair in `5e5bb76`
- **Delta:** flake packaging, full Lake dependency artifacts, downstream
  consumer/CLI checks, lock deduplication, and Linux/Darwin CI. The current
  flake reuses `inputs.self.outPath` for the Lake source so evaluation never
  depends on an unrealized nested `fileset.toSource` store path.
- **Ix impact:** supplies the proof-bearing artifact needed by `IxTcVerify`
  and makes a pinned fork reproducible in Nix.
- **Tests:**
  `nix flake check --all-systems --no-build --accept-flake-config`;
  `nix flake check --accept-flake-config --print-build-logs`;
  `downstream-consumer`, `cli-smoke`, `cli-smoke-external`, and `cli-noarg`.
- **Remaining local debt:** restore narrow source invalidation without
  reintroducing an evaluation-time unrealized path. This is a build-efficiency
  optimization, not a correctness or ix-pin blocker.
- **Upstream issue/PR:** TBD; split packaging and CI into independently
  reviewable PRs.
- **Removal condition:** upstream publishes equivalent full dependency and
  consumer-test outputs and ix pins that upstream revision.

## D002 — replay teardown safety

- **Status:** published-fork
- **Commit:** `4a55f8d`
- **Delta:** avoid the `replayFromImports` teardown segfault.
- **Ix impact:** makes executable environment replay reliable when ix or its
  fixtures invoke the Lean4Lean CLI.
- **Tests:** `cli-smoke`, `cli-smoke-external`, and `cli-noarg` in the flake.
- **Upstream issue/PR:** TBD.
- **Removal condition:** equivalent fix lands upstream and all CLI regression
  checks pass against it.

## D003 — multi-part olean replay deduplication

- **Status:** published-fork
- **Commit:** `7c9ed2c`
- **Delta:** skip constants already imported while replaying multi-part oleans.
- **Ix impact:** prevents false duplicate-name failures when constructing an
  environment from compiled dependencies.
- **Tests:** external-environment CLI smoke test and full flake check.
- **Upstream issue/PR:** TBD.
- **Removal condition:** upstream replay is idempotent for the same fixture and
  the local special case can be deleted.

## D004 — case-insensitive current-module inference

- **Status:** published-fork
- **Commit:** `d81fd04`
- **Delta:** infer the current module without a case-sensitive path/name
  assumption.
- **Ix impact:** avoids host/filesystem-dependent replay failures in downstream
  builds.
- **Tests:** external-environment and no-argument CLI checks.
- **Upstream issue/PR:** TBD.
- **Removal condition:** upstream implements an equivalent portable inference
  rule and the cross-platform checks pass.

## D005 — exact sorry-frontier enforcement

- **Status:** published-fork
- **Commits:** `c8a9ef8` (Perl token audit), replaced by the Lean
  environment audit in dev's `0d541a4` and reconciled with the
  formalization line at this checkpoint
- **Delta:** declaration-level `sorryAx` allowlist over the compiled
  `Theory`/`Verify` surface (`Lean4Lean/Audit/SorryFrontier.lean`),
  excluding `Experimental/`, wired into Nix and CI.
- **Ix impact:** guarantees that upstream proof debt can only shrink at pin
  boundaries; the current exact allowlist records 19 sorried declarations
  (20 `sorry` tokens) plus six deliberately kernel-rejected fixture
  recoveries.
- **Tests:** `lake build Lean4Lean.Audit.SorryFrontier` and the `proofs`
  flake check.
- **Upstream issue/PR:** TBD.
- **Removal condition:** upstream adopts an equal or stricter shrink-only gate;
  at zero debt, replace the allowlist with an unconditional rejection rule.

## D006 — staged computational inductive semantics

- **Status:** remote-development (the earlier checkpoints are published-fork
  or pushed to `jcb/formalization`; the L4L-09 through L4L-11 extensions are
  checkpointed at `jcb/formalization2`, while publication to `jcb/formalization2`
  remains pending)
- **Commits:** `71f2eae`, `06e904d`, `201c12f`, `efb2a2b`, the generalized
  single-family integration in `472a6f0`, the L4L-06A/B checkpoints
  `37e2ada6` and `41e1126b`, the L4L-06C edge checkpoints `0c6b178c` and
  `df58a3a0`, and the L4L-07 checkpoints `bb39cb2a`, `cc132cdd`,
  `fefb93fe`, `9910e14e`, the L4L-08A checked representation `79e1ae4f`, the
  L4L-08B validation/normalization closure, the L4L-08C implementation chain
  through `aa10005d`, and this closure/audit follow-up
- **Delta:** replace the three placeholder inductive declarations with real
  `VInductDecl.WF`, computational generation, generated recursor/iota rules,
  and sorry-free preservation for the accepted class. The published
  single-family path supports parameters, indices, index-changing recursion,
  recursive targets below positive Pi telescopes, raw/view normalization,
  mixed raw-syntax-preserving artifacts, exact ordinary small/large elimination
  modes, independently computed K-target metadata, and a traced normalized
  transaction. Zero- and one-constructor blocks use the same checked
  family/constructor/recursor/rule component chain, including ordinary empty
  constructor and rule folds. Acceptance is the dependent descriptor from
  D009. The complete one-family checkpoint now has a 14-row fixed kernel
  matrix, five focused normalization rows, and a 32-row rejection matrix.
  L4L-08A additionally computes a pure checked representation for arbitrary
  nonempty mutual family lists, including shared parameters, per-family
  index/result/constructor data, and cross-family target ordinals. L4L-08B
  adds executable block family/constructor validation, all-family staging,
  arbitrary-block normalization semantics, and exact environment-indexed
  checked/validated certificates. L4L-08C adds block-wide motive, minor,
  recursor, and rule generation; proves every artifact well formed and the
  exact four-phase transaction ordered; and replays both real mutual fixtures
  through the implementation environment. L4L-09 adds flattening/restoration,
  generation, preservation, and real-metadata replay for the accepted nested
  class; L4L-10 adds generated iota patterns, typed pattern soundness, and the
  block-local assembler; L4L-11 adds the consumer certificates and complete
  supported replay matrix recorded in D013. This remains an underapproximation
  of the full kernel: unsupported nesting classes, projections, and the
  remaining metatheory/checker roots are still open.
- **Ix impact:** discharges ix gap A1's three upstream `sorryAx` origins and is
  the semantic basis for constructing `InductiveOracle`; current breadth is
  not yet enough for all ix blocks.
- **Tests:** the integrated Nat, Bool, List, Option, Prod, Unit/`PUnit`, Empty,
  Or, And, Eq, HEq, Fin, Vector, and Acc matrix; five normalization rows;
  all 32 named rejection branches; exact acceptance, translated stored types
  and universe order, names/counts/flags, recursor types, rule metadata, and
  every iota RHS; supporting `IndexedVec`, elimination/K, and edge
  differentials; exact Tree/TreeList and indexed-mutual representation,
  validator execution, recursive-target matrices, semantic/generation
  certificates, complete family/constructor/recursor/rule metadata, global
  minor/rule order, and Theory/Verify environment replay; exact
  parameter/result-universe mismatch and reordering failures at their
  validation phases; Theory/Verify and default Lake builds; full Nix/flake
  gate; exact axiom guards for the matrix, singleton inventories, mutual
  generation/preservation roots, and replay outputs.
- **Upstream issue/PR:** TBD; submit in the staged PR sequence described in the
  roadmap rather than as one proof mega-diff.
- **Removal condition:** upstream exposes kernel-complete checked inductive
  semantics and preservation with the same fixture coverage, then ix pins it.

## D007 — consumer-facing inductive transaction API

- **Status:** remote-development (the one-family base is published-fork, the
  L4L-08C block transaction is pushed at `jcb/formalization`, and the nested
  transaction plus L4L-11 certificate façade are checkpointed at
  `jcb/formalization2`)
- **Commits:** the normalized core in `472a6f0`, the proof-carrying
  non-identity API in `6a77882`, and the block transaction/public migration
  through `12040b3e`, `48882b9c`, `67d65928`, `1159c655`, and `aa10005d`
- **Delta:** `VEnv.AddInductSuccess`, `AddInductGenerationTrace`,
  `addInductGeneration`, `GenerationCertificate`, and
  `addInductCertified`, with generated type/constructor/recursor lookups,
  rule membership, freshness, monotonicity, atomic success/failure, and
  `Ordered` preservation. L4L-08C adds `BlockGenerationCertificate`,
  `AddInductBlockGenerationTrace`, `addInductBlockGeneration`, and
  `addInductBlockCertified`, with list-wide phase invariants and consequences.
  The raw `VEnv.addInduct` now selects the same block artifact and no longer
  performs singleton projection. The former one-family raw computation remains
  available as deprecated `addInductSingleton`; the normalized
  `addInductGeneration`/`addInductCertified` APIs remain unchanged. The
  L4L-09 nested transaction and L4L-11 `BlockCertificate`/
  `NestedBlockCertificate` consumer façade are tracked in D013.
- **Ix impact:** lets `InductiveOracle` consume checked block results without
  unfolding `Option` binds or `foldlM`, and gives ix a Theory-only
  non-identity certificate boundary without importing Verify.
- **Tests:** identity and non-identity transaction fixtures, consumer-style
  `IndexedVec`, `Acc`, AliasFormer, AnnotatedPi, `PUnit`, and `Empty`
  transactions; raw/certified Tree/TreeList and indexed-mutual transactions;
  collision and atomicity fixtures; Theory/Verify and flake gates; and exact
  axiom guards for the public singleton/block trace and WF roots.
- **Upstream issue/PR:** TBD; submit after or with the Stage-3 preservation PR.
- **Removal condition:** equivalent stable postconditions are upstream and ix
  no longer imports the fork-only names.

## D008 — Verify inductive-environment alignment

- **Status:** remote-development (the earlier checkpoints are published-fork
  or pushed at `jcb/formalization`, and the L4L-09 nested replays plus complete
  L4L-11 matrix are checkpointed at `jcb/formalization2`)
- **Commits:** initial alignment in `472a6f0`, extended through `a1d8943`,
  `6a77882`, `bc37d43`, `37e2ada6`, `41e1126b`, `0c6b178c`, `df58a3a0`,
  `bb39cb2a`, `cc132cdd`, `fefb93fe`, the L4L-07 closure, and the L4L-08C
  replay/audit checkpoints `eeae5282` and `aa10005d`
- **Delta:** replace the empty `AddInduct` relation with a data-bearing trace
  for `inductInfo`, ordered `ctorInfo` insertion, `recInfo`, and the generated
  defeq fold. Fold realization, lookup, freshness, monotonicity,
  map-WF/value-preservation, `Aligned.addInduct`, and the formerly impossible
  `TrEnv'.of_value` inductive case are live. `RecursorKMatches` additionally
  requires `recInfo.k` to equal the shared Theory generation decision, so a
  type-correct recursor carrying the wrong reduction flag cannot align. The
  sole L4L-07 replay inventory now carries actual Lean metadata transactions
  for all 14 fixed families and five normalization cases through final WF,
  alignment, ordering, and every rule insertion. Fin and Vector use exact
  aligned dependency slices, rather than pretending to start from the empty
  environment. Translation now handles stored `.mdata` type annotations by
  the same semantic erasure already used by `TrExprS`, which is required by
  the real `Array.size` metadata in Vector's dependency slice. The normalized
  trace owns the exact generation and its semantic certificate instead of
  restating artifacts; the legacy phase fixtures remain implementation inputs,
  not competing public inventories. L4L-08C adds `AddInductBlockTrace` and
  list-wide constant phases, proves fold realization and monotonicity, and
  extends `TrEnv'`/`Aligned` with an atomic mutual-block case. Both real mutual
  maps replay every family, constructor, and recursor in kernel order before
  installing the globally flattened rules. L4L-09 adds the corresponding
  restored nested trace/alignment path and two actual-metadata replays; L4L-11
  adds final-map translated role/uniqueness lemmas, the third deep replay, and
  the unified matrix in D013. The V3 primitive transaction now derives exact
  canonical Bool/Nat source preservation and zero nested auxiliaries from the
  executable recognizer shape plus the retained public nested-elimination run;
  the transaction record no longer accepts either equality as a
  producer-supplied field. The same closed recognizer shape now selects the
  complete canonical Theory declaration directly. Primitive transaction
  producers therefore choose neither a parallel raw declaration nor a
  source-indexed semantic normalization run. A dedicated primitive replay now
  consumes only family, constructor, and recursor insertion folds indexed by the
  retained execution, retargets their exact maps to the public outer endpoints,
  and constructs the coherent safety-indexed `AddInductBlockTrace` family using
  an internally selected canonical generation. The public primitive transaction
  package contains this exact replay rather than accepting arbitrary traces.
  This fold-level surface also avoids imposing the generic staging records'
  final `TrEnv' .safe` postcondition on valid partial and unsafe input models
  that contain additional visible constants. This separate path is necessary
  because the family-only intermediate environment for `Bool` or `Nat` cannot
  satisfy `HasPrimitives` before its constructors have been inserted. Verify now
  provides lightweight interpreters that construct each exact insertion fold
  from the retained declaration equation, semantic list translations, and
  `Aligned`; the primitive replay assembler consumes those results directly.
  The retained family validator now exports preservation of its universe
  parameters, and the primitive execution uses that invariant plus the closed
  recognizer shape to derive the canonical family translations.  Its resulting
  family insertion supplies the exact Theory lookup used to derive both Bool
  or Nat constructor translations and the constructor insertion fold; neither
  phase remains a primitive replay input. That same singleton family-add
  equation now derives the complete canonical Bool/Nat
  `BlockGenerationChecked.WF`, including the successor recursive-field
  certificate. `CanonicalPrimitiveReplay.ofInsertions` therefore constructs
  `generation_wf` internally instead of accepting it from a producer.
- **Ix impact:** establishes the implementation-to-Theory environment bridge
  needed to translate checked inductive blocks and eventually construct
  `InductiveOracle`. The supported singleton, mutual, and nested replay matrix
  and generated-pattern consequences are now closed; projection semantics and
  unsupported inductive forms still prevent construction for the full kernel
  surface.
- **Tests:** `lake build Lean4Lean.Verify.Environment.SingletonParityReplay`;
  executable 14/5/19 inventory equalities; every actual-metadata transaction,
  final alignment, and derived output ordering; exact Fin/Vector dependency
  maps; the pre-Nat value-preservation regression; full Theory/Verify, default
  Lake, Nix, and flake gates; primitive nested no-op, canonical-source, and
  retained-execution replay consumer checks, canonical family/constructor
  evidence, insertion, and canonical Bool/Nat generation-WF checks; and
  compile-time trust manifests for the fixed, normalization, combined replay,
  output-ordering, and both mutual-block roots.
- **Axiom note:** the guarded roots currently inherit `sorryAx` through
  `TrConstVal → TrExprS → TrProj`, plus the standard logical baseline. E1
  declares no new axiom. The fixed replay inventory additionally reaches the
  three existing persistent-map contracts while proving its `SMap` insertion
  freshness. The normalization and combined inventories expose the already
  classified pointer, expression/level, persistent-array/map, and syntax
  contracts inherited from their ordinary producer evidence. The mutual replay
  roots use only the already classified `TrProj` and persistent-map frontier;
  fixture-local native-decision axioms have been removed from their semantic
  closures. Every public root has an exact compile-time manifest; Track P/T2
  must remove or narrowly justify these inherited dependencies before release.
  The canonical declaration and generation selectors use only the logical
  baseline. The
  primitive nested no-op proof introduces no axiom or admission; its exact
  equality uses the existing classified `Expr.abstract_eq` bridge, which is
  pinned on the proof and every affected transaction root. Retargeting the
  staged primitive replay to the public outer endpoints has the same exact
  closure; constructing the trace at the retained flattened endpoints uses only
  the standard logical baseline. The two canonical generation-WF lemmas, their
  retained-family-fold consumer, and the updated replay assembler likewise use
  only that logical baseline.
- **Upstream issue/PR:** TBD; submit with or immediately after the staged
  inductive-semantics series.
- **Removal condition:** upstream has a non-vacuous inductive alignment with
  concrete replay fixtures, ix uses it, and the guarded closure contains no
  `sorryAx`.

## D009 — shared checked inductive descriptor

- **Status:** remote-development (the base descriptor is published-fork; its
  K-target, empty/singleton, complete singleton-parity, and mutual-generation
  extensions are pushed at `jcb/formalization`)
- **Commit:** introduced and integrated in `472a6f0`; K-target retention is
  extended through `41e1126b`, with zero-/one-constructor coverage through
  `0c6b178c`, `df58a3a0`, singleton closure through `9910e14e`, and the
  L4L-08A checked representation `79e1ae4f`, the L4L-08B
  validation/normalization closure, the L4L-08C implementation chain through
  `aa10005d`, and this closure/audit follow-up
- **Delta:** add dependent `VInductDecl.Checked`, normalized constructor and
  recursive-argument records, and the computational `checked?` analyzer.
  Define public Stage-3 acceptance as descriptor existence. Route recursor/rule
  access, `VEnv.addInduct`, its success/WF proof anatomy, Theory fixtures, and
  Verify's `AddInductTrace` through the descriptor. Add exact closed-metadata,
  all-annotation universe-range, family-telescope self-reference, direct
  result-shape, and generated-name `Nodup` checks plus a centralized proof API.
  Add `Checked.WF env` for normalized telescope/field/result-spine semantics,
  prove both compatibility directions and an iff with `VInductDecl.WF`, and
  make preservation consume it. `NormalizedChecked`, `GenerationChecked`, and
  their WF contracts retain the raw singleton block, checked view, mixed
  generation layout, ordered constructor pairing, exact K-target decision
  independently of elimination mode, and exact analyzer result.
  `PUnit` and `Empty` compute through this same descriptor: the former retains
  one zero-field, nonrecursive constructor and one minor/rule, while the latter
  retains empty constructor/minor/rule lists without a proof-only premise.
  Stable constructor/recursor collision rejection and identity compatibility
  remain part of the public proof API. L4L-08A adds `CheckedFamily`, the
  ordinal- and source-list-indexed `CheckedFamilies`, `CheckedBlock`, and
  `checkedBlock?`. Shared parameters occur once at block scope; each family
  retains exact indices, result level, and constructor order; block-wide
  recursive analysis records sibling targets in `RecArg.targetType`. L4L-08B
  adds `NormalizedCheckedBlock`, `ValidatedBlock`, their computational
  analyzers, block-wide WF relations, and the Theory-only
  `ValidationCertificate`. L4L-08C adds `BlockGenerationChecked` and its
  family/constructor semantic WF package, block-wide generated artifacts, and
  `BlockGenerationCertificate`. The old `Checked`/`checked?`,
  `GenerationChecked`, and certified one-family path remain available; raw
  compatibility is exposed by deprecated `addInductSingleton`, while public
  `stage3`/`addInduct` consume the non-singleton block descriptor.
- **Ix impact:** creates the stable, consumer-neutral analysis object that E2
  can use to assemble `InductiveOracle` without duplicating raw declaration or
  de Bruijn analysis. The semantic certificate gives ix an environment-indexed
  proof boundary without importing Verify, while the transaction certificate
  lets it reuse the exact checked value. Reserved recursive binder telescope
  and target-family fields provide the extension point for Acc-like and mutual
  recursion.
- **Tests:** computed descriptor-shape checks for Nat, Eq, `IndexedVec`,
  `PUnit`, and `Empty`, plus exact K-target shapes for Eq, And, Or, Nat,
  `PUnit`, and `Empty`; exact Tree/TreeList and indexed-mutual source order,
  shared parameters, per-family indices/results, constructor order,
  recursive field positions/indices, and target ordinals; exact mutual
  normalization/checked/generation WF certificates and
  parameter/result-universe/reordering phase checks; computed mutual
  motive/minor/recursor/rule inventories and public raw transaction success;
  semantic bridge fixtures for `IndexedVec`; negative fixtures for loose data,
  internal/pre-existing name collisions, self-referential parameters, invalid
  levels, malformed results/spines, parameter counts, and universe-count
  mismatches; exact Theory/Verify build; 20-sorry audit; Theory import boundary;
  formatter; all six current-host flake checks; and all-system no-build
  evaluation.
- **Axiom note:** the analyzer and descriptor are computational and declare no
  axiom. The new block analyzer, dependent source-order theorem, and both
  mutual fixture roots have exact `propext`/`Quot.sound` manifests.
  Compile-time guards pin every exported singleton structural fact, the three
  `Checked.WF` compatibility roots, transaction success/exact-analysis facts,
  and collision theorems to exactly `propext` and `Quot.sound`, a subset of the
  accepted Theory baseline. `addInduct_WF` retains the accepted
  `propext`/`Classical.choice`/`Quot.sound` closure.
- **Upstream issue/PR:** TBD; include as the architecture-first mutual-block
  patch after the I2 one-family-parity series.
- **Removal condition:** upstream generation, preservation, Verify alignment,
  and downstream consumers share an equivalent checked block result, and ix
  no longer imports the fork-only descriptor API.

## D010 — executable normalization and certified producer boundary

- **Status:** remote-development (the earlier checkpoints are published-fork;
  L4L-03 is pushed at `jcb/formalization`, while publication to `jcb/formalization2`
  remains pending)
- **Commits:** `1fb7d6e`, `9fde4c6`, `b283912`, `a84aa19`, `c2b1c4f`,
  `a1d8943`, `6a77882`, `bc37d43`, `5e5bb76`, `33b99f4`, `a3ff992`,
  `9a865ea`, `a627362`, `6732659`, `c40a471`, `c739d41`, `82f4a54`,
  `d553930`, `cf3d5a4`, `c9e4ae2`, `a7d101b`, `f0caf16`, `e3cf22d`,
  `7e5f4f7`, `2b1d802`, `a64fe98`, `5aa9ab6`, `bbb45e0`, `7c79220`,
  `da45b53`, `097efb4`, `a246c04`, `37d2dd9`, `9e40cbe`, `98921da`,
  `ae6726c`, `3e6efcc`, `53d5f92`, `bb88317`, and `04a1a4f`
- **Delta:** retain exact ordinary-checker full-check, WHNF, and `isDefEq`
  executions in source- and context-indexed candidate traces; interpret them
  into Theory normalization and generation certificates; assemble dependent
  family/constructor lists without truncation; and package the exact generation
  with its semantic WF proof. `ProducedGenerationCandidatePackage` adds the
  stronger equation that the executable whole metadata call produced that
  same candidate. AliasFormer and AnnotatedPi are complete positive instances
  and each supplies its Theory transaction and Verify replay from its produced
  package. AnnotatedPi's outer operational proof now covers exact family and
  constructor validation, freshness, transparent recursion and positivity
  traversals, raw-family declaration, annotation consumption, nested-Π
  candidate traversal, dependent family/constructor list assembly, and the
  complete successful `buildNormalizationCandidate` equation. The executable
  boundary now also covers Lean's real universe-polymorphic `IndexedVec`:
  exact parameter/index family validation, post-family `nil` and dependent
  recursive `cons` candidates, ordered constructor-list assembly, and the
  complete successful outer producer equation. Generic recursive identity
  replay retains caller-selected Theory endpoints for identity-normalizing
  traces. The executable list layer now exposes arbitrary-length dependent
  `CandidateFamilyTypeListProduced`, `CandidateConstructorListProduced`, and
  `CandidateFamilyListProduced` witnesses whose `.normalize` theorems recover
  the exact list results without erasure, truncation, reordering, or unchecked
  positional lookup. AliasFormer and AnnotatedPi use singleton instances;
  `IndexedVec` exercises the ordered two-constructor instance.
  `GenerationCandidateRun.producedPackage` now supplies the generic outer
  singleton step: given an already verified semantic run and the exact
  successful whole-call equation indexed by its same source and candidate, it
  constructs `ProducedGenerationCandidatePackage`. All three fixtures use this
  constructor instead of fixture-specific record assembly.
  `CandidateExprSemanticRootRun` now retains the exact recursive semantic run
  behind each root, derives the normalization-facing root and generation-facing
  spine from that one value, and can existentially select the view from a
  verified context plus strict source translation. Dependent semantic
  constructor-list, family, and singleton-normalization structures preserve the
  same source order through the complete hierarchy. AliasFormer, AnnotatedPi,
  and `IndexedVec` have been migrated to that ownership model.
  `CandidateExprSemanticRootInput`, dependent constructor/family inputs, and
  `NormalizationCandidateSemanticInput.exists_ofProduced` now combine those
  verified inputs with the exact operational family-type and family-list
  witnesses and return the complete produced semantic hierarchy under
  `Nonempty`. `CandidateFamilySemanticGenerationRun`,
  `CandidateSemanticNormalizedCtorRun` and its dependent list, and
  `GenerationCandidateSemanticRun` make that hierarchy the sole owner of the
  recursive runs and spines consumed by generation. Their compatibility,
  package, and produced-package projections preserve the existing public API.
  The structural generation layer no longer accepts fixture-supplied view
  telescopes or terminal typing judgments. `Checked.type_eq` and
  `GenerationChecked.viewCtorType_eq` expose exact accepted family/constructor
  decomposition. `GenerationCandidateRun.familyView_eq` fixes the singleton
  candidate view; family terminal typing follows from the checked result level;
  the inserted raw family constant is typed once at the checked family type;
  and `GenerationChecked.checkedResultTarget_hasType` applies the checked
  parameter/index spines to derive each constructor result target.
  `CandidateNormalizedCtorRun.viewTel_eq` and `rightType_ofChecked` transport
  these facts through the exact candidate telescope. AliasFormer, AnnotatedPi,
  and `IndexedVec` now omit both record fields, and the circular `IndexedVec`
  right-typing theorems formerly obtained from a complete identity-generation
  WF proof are deleted.
  `GenerationCandidateRun` and its semantic owner now store the exact equation
  that candidate normalization's dependent `generation?` analysis returned the
  retained `GenerationChecked`. Theory's
  `Normalization.check?_normalization` and
  `Normalization.generation?_normalization` derive normalization identity from
  successful analysis. `GenerationCandidateRun.normalization_eq` projects that
  result, and `GenerationCandidateRun.typeEnv_wf` reconstructs the post-family
  environment from the verified pre-family context, checked family typing,
  candidate raw/view equality, and exact raw-family insertion. The three live
  fixtures now provide `analysis := rfl` and no independent
  `normalization_eq` or `typeEnv_wf` field.
  `GenerationCandidateSemanticShapeRun` is the next reduced boundary. Its
  source-indexed family and constructor shapes retain only `storedSpine` and
  the total traversed-binder count. Exact dependent analysis derives the raw
  family identity, complete checked family view, every normalized constructor
  pair, and the full ordered pair list; total spine length derives every raw
  telescope/result equation, and exact checked shape derives every view
  terminal equation. Its `.run` reconstructs the established semantic
  generation owner. AliasFormer, AnnotatedPi, and the two-constructor
  `IndexedVec` fixture now use this path and no longer hand-assemble normalized
  pairs or any raw/view telescope/result equations.
  `normalizationCandidateGenerationShape` now performs one executable check
  over the complete singleton family and its source-indexed constructor list.
  It requires each retained trace to preserve the emitted Pi spine, checks the
  full raw telescope length, and rejects constructor-list mismatches in either
  direction. `ProducedGenerationShapeCandidate` couples that check to the exact
  successful ordinary producer equation, while
  `produceGenerationShapeCandidate` rejects a produced candidate that cannot
  support mixed raw/view generation. This is intentionally a strengthened
  operational boundary: success of `buildNormalizationCandidate` alone does
  not imply stored-spine preservation and does not acquire Theory meaning.
  `GenerationCandidateSemanticRun.ofGenerationShape` combines the retained
  semantic hierarchy, exact dependent analysis, WF of the analyzer-owned view
  declaration, and the one complete shape result. It derives the analyzed
  checked block's WF and every dependent family/constructor shape record
  generically. `ProducedGenerationShapeCandidate.producedPackage` then returns
  the existing complete produced package for that same candidate. AliasFormer,
  AnnotatedPi, and `IndexedVec` all use this consolidated path; fixtures no
  longer provide checked WF or per-position generation-shape structures.
  Constructor validation now has a parallel strengthened semantic boundary.
  `checkConstructorUniverseListSemantics` replays every source-ordered
  constructor telescope and accepts an ordinary field through structural
  universe order, the impredicative-Prop result exception, or the normalized
  comparison intersection documented in D012. Strict kernel level translation
  turns that executable decision into exactly the Theory disjunction needed
  later by `fieldsWF`. The additive
  `StagedNormalizationCandidateUniverseInput` retains the successful audit
  alongside the established semantic owner without changing
  `buildNormalizationCandidate` or treating its success as semantic evidence.
  AliasFormer, AnnotatedPi, and `IndexedVec` use that owner. The ordinary
  validator remains unchanged, while the former normalized max/parameter gap
  is now accepted only when core and verified project comparison agree.
  `ConstructorViewAlignmentTrace` then aligns each validation-owned telescope
  with its candidate-owned telescope at the corresponding Theory de Bruijn
  positions, rather than equating their fresh-FVar identifiers. The complete
  post-family semantic list run interprets the retained root type check,
  parameter definitional equalities, ordinary and recursive field type checks,
  positivity targets, and terminal family applications in the actual verified
  post-family context. `StagedNormalizationCandidatePostFamilyInput` couples
  that source-ordered result to the same produced candidate and universe audit.
  AliasFormer, AnnotatedPi, and `IndexedVec` inhabit the staged owner, and the
  two-constructor regression pins both source order and genuinely distinct
  validator/candidate field identifiers.
  `buildConstructorPreFamilySafety` and
  `checkConstructorPreFamilySafety` add the strengthened D3 boundary without
  changing ordinary candidate production. Their dependent traces instantiate
  the analyzer-owned family parameters, retain exact ordinary-field
  `checkType`/`ensureType`/annotation equality observations, omit recursive
  outer-field locals, and replay family-free nested Pi binders and
  recursive/result index spines in the pre-family context. Recursive fields no
  longer have to form a suffix: an independent ordinary field may follow an
  omitted recursive local and is reconstructed through the common D3 context.
  Every later domain/result must still be syntactically independent of each
  omitted FVar. The semantic trace interpretation and proved prefix-weakening
  projections derive the pre-family field, binder, and spine judgments from
  those exact executions. The additive
  `StagedNormalizationCandidatePreFamilyInput` retains the safety trace beside
  D2's owner and reconstructs its semantic result under `Nonempty` from the
  exact family terminal context. AliasFormer, AnnotatedPi, and `IndexedVec`
  inhabit the new produced owner; executable initial-state fixtures accept an
  independent ordinary field after recursion and reject a later field that
  actually depends on the omitted local.
- **Ix impact:** prevents ix from receiving an unrelated hand-selected
  normalization or generation witness while keeping checker state out of the
  Theory API. This is the proof boundary needed before executable metadata can
  be treated as certified inductive generation.
- **Latest checkpoint:** the L4L-03 semantic source at `04a1a4f2` builds on the
  generic L4L-01E package closure at `ae6726c`. Pre-declaration full checks,
  WHNF Pi/result and recursive-target traversal, and the exact AnnotatedPi
  producer package remain the operational authority. D3 now carries
  independent ordinary fields past omitted recursive locals. `AnnotatedParam`
  separately pins the ordinary constructor-parameter `isDefEq` outcome, emits
  the checked parameter in the recursor, and replays the resulting kernel
  metadata through the certified Theory transaction and Verify environment.
  This split is deliberate: no second hand-assembled produced package is
  claimed for `AnnotatedParam`.
- **Current gap:** the singleton normalization differential, omitted-local
  dependency boundary, mutual result-universe equality/block staging, mutual
  generation, and environment replay are closed through L4L-08C. Nested
  transformation and producer packaging remain assigned to L4L-09.
- **Tests:** exact positive AliasFormer, AnnotatedPi, and `IndexedVec`
  whole-call equations; positive semantic/transaction/replay fixtures for the
  first two plus the complete checkpoint semantic/transaction/E1 replay for
  `IndexedVec`; exact `IndexedVec` family/`nil`/`cons` candidate traces;
  opaque-`outParam` whole-candidate rejection; exact positive and genuinely
  non-defeq negative `AnnotatedParam` whole-call guards; checked-parameter
  recursor/iota parity plus certified transaction, metadata lookup, WF,
  alignment, uniqueness, and rule replay; exact axiom guards for the
  semantic-input constructors, produced hierarchy, semantic-generation and
  reduced-shape projections, the three operational list theorems, and both
  outer package constructors; singleton and two-constructor list regressions;
  exact `IndexedVec` source-order preservation plus swapped-view rejection;
  retained-hierarchy and semantic-generation migrations for all three
  fixtures; absence of fixture `viewTel`, `rightType`, `normalization_eq`,
  `typeEnv_wf`, checked-WF, per-position generation-shape, normalized-pair,
  `rawTel`, `rawResult`, and `viewResult` inputs; exact strengthened-producer
  success for all three fixtures; missing-raw and extra-raw constructor-list
  rejection; exact analyzer-success replay in all three fixtures; structural
  and impredicative-Prop universe positives; normalized max/parameter
  acceptance through core/project agreement; exact universe-bridge and
  staged-owner axiom guards; exact post-family alignment of all AliasFormer,
  AnnotatedPi, and ordered `IndexedVec` fields/results; distinct
  validator/candidate
  `IndexedVec` field-FVar regression; exact successful pre-family replay and
  produced semantic ownership for all three fixtures; executable independent
  ordinary-after-recursive acceptance and recursive-local-dependency
  rejection guards;
  exact generic and fixture post-family/pre-family axiom guards; focused direct
  compiles, 156-job default Lake build, and
  119-job Theory/Verify and Nix proof builds; 20-sorry frontier check; default
  Nix build; all six current-host flake checks; all-system no-build evaluation;
  formatter; Theory import-boundary; and whitespace checks.
- **Axiom note:** no normalization oracle, native evaluator, or new axiom was
  added. `Checked.type_eq`, `GenerationChecked.viewCtorType_eq`, and
  `GenerationChecked.checkedResultTarget_hasType` are exactly guarded at
  `propext`/`Quot.sound`. `GenerationCandidateRun.familyView_eq` and
  `CandidateNormalizedCtorRun.viewTel_eq` have exactly the small transitional
  `propext`/`sorryAx`/`Classical.choice`/`Quot.sound` closure inherited from
  their Verify evidence. Family-constant and constructor-target typing inherit
  the already recorded full checked-semantic closure and are exactly guarded.
  The three operational list theorems are guarded at exactly the
  accepted `propext`/`Classical.choice`/`Quot.sound` baseline. The generic outer
  constructor has the exactly guarded
  `propext`/`sorryAx`/`Classical.choice`/`Quot.sound` closure inherited through
  its dependent Verify evidence types; it declares no axiom and does not widen
  the producer equation into semantic authority. Concrete Verify producer
  roots expose existing checker-refinement, pointer/cache, and projection
  dependencies; generic Theory transaction roots retain their narrower
  guarded closure. The semantic `spine` projection has exactly the
  `propext`/`sorryAx`/`Classical.choice`/`Quot.sound` closure. Semantic input
  construction, produced hierarchy assembly, and semantic-generation
  projections inherit the already documented checked semantic closure,
  including the existing pointer, expression, level, persistent-array/map, and
  syntax implementation contracts. They are now exact compile-time guarded;
  the AliasFormer and `IndexedVec` roots match that set, while AnnotatedPi adds
  only the already documented `Expr.hasFVar_eq` dependency reached by its
  annotated free-variable checker trace. Returning semantic existence under
  `Nonempty` avoids a choice-based data extractor. No root declares a new
  axiom, assumes a normalization oracle, or gives operational production
  independent semantic authority.
  The new Theory normalization-retention lemmas are exactly guarded at
  `propext`/`Quot.sound`. The Verify normalization projection has exactly the
  small inherited `propext`/`sorryAx`/`Classical.choice`/`Quot.sound` closure;
  reconstructed post-family WF has exactly the already recorded checked
  semantic closure. These are derivations from retained analysis/context
  evidence, not new axioms or an expansion of the accepted trust budget.
  `NormalizationCandidateRun.sourceType_eq` and `familyViewType_eq` are guarded
  at exactly `propext`/`sorryAx`/`Classical.choice`/`Quot.sound`, inherited from
  their dependent Verify evidence. `GenerationCandidateSemanticShapeRun.run`
  has exactly the previously recorded checked semantic set. The structural
  list recursion and telescope decomposition introduce no new axiom, and the
  public projection does not enlarge the semantic owner's closure.
  The complete executable generation-shape functions, strengthened producer,
  and its exact-success theorem are guarded at exactly
  `propext`/`Classical.choice`/`Quot.sound`; they declare no axiom and contain no
  semantic claim. Expanding a successful shape result into the dependent
  semantic generation owner, deriving checked WF, and constructing the final
  package inherit exactly the already recorded checked semantic closure. Exact
  fixture guards expose only their pre-existing checker/pointer/cache and
  projection dependencies. The kernel-level structural equality/order roots
  remain at exactly `propext`/`Quot.sound`; the normalized project comparison
  and resulting Theory universe-disjunction root use only the standard
  `propext`/`Classical.choice`/`Quot.sound` basis documented in D012. No oracle,
  custom axiom, or new sorry is reachable. The additive staged projections
  explicitly guard their inherited Verify closure instead of presenting it as
  a smaller mathematical trust claim. The D2 staged owner and all three
  fixture roots are each compile-time guarded at the same established post-family checker
  closure: `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, and the
  existing expression, level, pointer-equality, persistent-collection, and
  syntax implementation contracts. The positional alignment and semantic-run
  structures declare no axiom; no `native_decide`, new sorry, or additional
  custom trust contract is reachable from these roots.
  D3's independent-after-recursive acceptance and dependency rejection guards
  compute without an axiom or proof premise. The trace interpretation,
  weakening lemmas, staged generic
  owner, and all three fixture roots are compile-time guarded at exactly the
  same established Verify closure as D2: `propext`, `sorryAx`,
  `Classical.choice`, `Quot.sound`, and the existing expression, level,
  pointer-equality, persistent-collection, and syntax implementation
  contracts. No constant-removal axiom/theorem, native evaluator, new sorry,
  or new project-specific trust contract is reachable.
  `AnnotatedParam`'s Theory definitional equality, complete generation WF,
  certified transaction, and final iota membership are guarded exactly at
  `propext`/`Quot.sound`. Its real-metadata replay trace and `TrEnv'` root add
  only the existing `sorryAx`/`Classical.choice` and persistent-map contracts;
  they reach no pointer, expression, level, native-evaluation, or new custom
  axiom.
- **Upstream issue/PR:** TBD; submit after the singleton producer interface is
  stable enough that the first PR does not freeze fixture-specific APIs.
- **Removal condition:** upstream executable inductive ingestion returns or
  derives an equivalently source-indexed certified package, all supported
  metadata paths use it, and ix no longer relies on the fork-only producer API.

## D011 — verified syntactic definitional-equality fast path

- **Status:** published-fork
- **Commit:** `f0d80f8`
- **Delta:** `TypeChecker.Inner.isDefEq` accepts `Expr.eqv` inputs before
  entering `isDefEqCore`. The verified refinement transports the strict source
  translation across expression equivalence and proves the ordinary Theory
  definitional equality result. The successful fast path leaves checker state
  unchanged; non-equivalent inputs retain the existing core behavior.
- **Ix impact:** removes an operational state-mutation obstruction in exact
  constructor-candidate replay and makes reflexive executable equality checks
  cheaper without changing the Theory API.
- **Tests:** exact-state AliasRec, AnnotatedPi, and `IndexedVec` fixtures;
  `TypeChecker.Inner.isDefEq.WF`; focused and full Theory/Verify builds; exact
  20-sorry audit; default Nix build; all-system no-build evaluation; and the
  current-host flake check.
- **Axiom note:** no new axiom was declared. The Verify proof reaches the
  existing `Expr.eqv_eq` implementation contract; it grants no new Theory
  authority and remains part of Track T's platform-contract audit.
- **Upstream issue/PR:** TBD; submit as an isolated checker optimization plus
  its refinement theorem and exact-state regressions.
- **Removal condition:** an equivalent verified fast path lands upstream, or
  the fork removes this behavior and all candidate-replay fixtures pass against
  the upstream state transition instead.
- **v4.33 note:** upstream's new `Tests/KernelHardening.lean` fuel probe
  assumed `checkType (deepNat 100)` consumes recursion fuel through the
  per-argument `isDefEq` dispatch; this fast path answers those identical
  comparisons without dispatch, so the fork's copy of the probe reduces the
  term (`whnf`) instead of type-checking it. Same lean4#13956 property, a
  fast-path-immune trigger.

## D012 — verified project universe-level comparison

- **Status:** local-committed; publication is pending
- **Commits:** `70c02b0`, `a72979d`, and `de3d98c`
- **Delta:** prove evaluation preservation for project level normalization and
  comparison without assigning a logical contract to Lean's opaque v4.31
  normalizer. `NormLevel.subsumption_eval` covers every raw normalized map by
  retaining active-path membership witnesses when constants are removed.
  Canonical ordered-entry equality gives `NormLevel.eval_congr`,
  `isEquiv_wf`, and dependent level-list equivalence. `NormLevel.le_eval`
  proves the transparent project order sound for every raw `NormLevel`, and
  `geq'_wf` transports that result back through normalization. Constructor
  semantic validation admits a normalized non-Prop field only when the
  unchanged ordinary core `Level.geq` decision and verified project `geq'`
  decision both succeed. The core half preserves the ordinary acceptance
  boundary; only the proved project half supplies Theory meaning.
- **Ix impact:** removes the structural/Prop-only universe under-approximation
  from the certified singleton producer while retaining the same kernel-facing
  validation result and a consumer-neutral Theory inequality.
- **Tests:** generated old/new normalization differentials and exact evaluator
  regressions over zero, successor, max, imax, parameters, and nested forms;
  an all-pairs mvar-free core/project comparison matrix; the formerly excluded
  max/parameter constructor comparison as a positive semantic-gate regression;
  exact axiom guards for `NormLevel.le_eval`, `geq'_wf`, and the constructor
  bridge; focused builds; 119-job Theory/Verify and 156-job default Lake
  builds; exact 20-sorry audit; default Nix build; all-system no-build
  evaluation; all six current-host flake checks; formatter, Theory import
  boundary, and whitespace checks.
- **Axiom note:** no oracle, native evaluator, custom axiom, or new sorry was
  introduced. The new comparison roots close exactly over `propext`,
  `Classical.choice`, and `Quot.sound`. Lean's core `Level.geq` remains an
  executable acceptance condition only and is never used as a semantic proof
  premise.
- **Upstream issue/PR:** TBD; submit the generic level-normalizer proofs and
  comparison bridge before the constructor-validation integration.
- **Removal condition:** upstream provides an equivalent standard-only
  mvar-free level-order theorem and constructor semantic validation consumes it
  without a fork-only comparator.
- **v4.33 note (partially absorbed):** upstream now verifies the standard
  library level operations (`Verify/LevelStd.lean`) and proves the primed
  comparators sound *and* complete with core `isEquiv`/`geq` as verified fast
  paths, superseding this row's fork-local normalizer proofs — the merge took
  upstream's `Level.lean`/`Verify/Level.lean` machinery wholesale. What
  remains fork-only: routing the typechecker's sort comparison through
  `isEquiv'` and constant-level lists through `isEquivList := all2 isEquiv'`
  (upstream keeps core `isEquiv` on both paths); the transparent
  `Level.isStructEq` test plus `isStructEq_eq`/`isStructEq_iff_eq` (fixture
  consumers); and the constructor-validation bridge, which now consumes
  upstream's `geq'_wf`/`isEquiv'_wf` instead of the retired fork lemmas.
  Upstream's reference equations for core ops (`Level.normalize_eq`,
  `Level.mkMaxAux_eq`, `Level.skipExplicit_eq`,
  `Level.isExplicitSubsumedAux_eq`, `TreeMap.any_eq_any_toList`) joined
  `Verify/Axioms.lean`, and `TreeMap.all_eq_all_toList` is live again in
  upstream's proofs (no longer a deletable dead axiom).
- **L4L-16R note (narrowed further, 2026-08-20):** upstream `3f6e8f92`
  ("enable the new level algorithm") flipped its own
  `isEquivList := List.all2 isEquiv'` and switched `checkConstructors` to
  `geq'` — both halves converged with the fork, so the constant-level-list
  routing and the constructor universe check are no longer divergences at
  all (the fork absorbed the `geq → geq'` flip into
  `checkConstructorType.loop`, `ValidationTrace`'s
  `ConstructorUniverseTrace`, and the semantic-gate replay). The residue of
  this row is now exactly: the `quickIsDefEq` sort comparison routed through
  `isEquiv'` (upstream still compares sorts with core `isEquiv`), plus the
  fork-only `isStructEq` family and the `levelStructGe` structural fast path
  in `checkConstructorType` (accepts a subset of `geq'`, so kernel-facing
  behavior matches upstream exactly). The Verify-side
  `constructorUniverseSemanticGe` audit still requires `geq && geq'` in its
  fallback; since the executable check now accepts via `geq'` alone, the
  audit is strictly narrower than the checker — a proof-surface choice, not
  a checker divergence.

## D013 — complete inductive replay and consumer certificates

- **Status:** remote-development at `jcb/formalization2`; publication to
  `jcb/formalization2` is pending.
- **Commit:** this L4L-11 closure checkpoint, based on `bc51f980`.
- **Delta:** add the Theory-only `VInductDecl.BlockCertificate` and
  `NestedBlockCertificate` façades over successful proof-carrying
  transactions. They export raw transaction recovery, environment growth/WF,
  exact family/constructor/recursor lookups and freshness, lookup uniqueness,
  registered rule membership/WF, derived rule closure, and generated-recursion
  pattern facts without carrying Verify state or implementation metadata.
  Verify now preserves old implementation-map lookups across inductive folds
  and exports exact final-map translated roles. A single 25-row inventory
  combines 20 ordinary singleton candidate executions, both real mutual
  blocks, and three analyzer-produced nested blocks with explicit dependency
  maps/environments, data-bearing traces, every constructor role, and recursor
  uniqueness. The new `DeepBi` row replays actual stored metadata over the
  two-parameter `BiBox` dependency and exercises a queued second nested
  occurrence, three restored recursors, and all three kernel rule RHSs. A
  separate executable test freshly replays the real compiled dependency
  closure of a notation-heavy fixture (296 declarations) instead of using a
  hand-built Theory prelude.
- **Ix impact:** downstream checkers can consume one implementation-independent
  block certificate for growth, preservation, metadata lookup, registered
  rules, and L4L-10 pattern consequences. The matrix demonstrates that the
  supported singleton/mutual/nested class is constructible from actual kernel
  metadata with dependencies kept explicit.
- **Tests:** focused deep-nested and unified-matrix builds; aggregate
  Theory/Verify/Tests/sorry-frontier and default Lake builds; exact 20/2/3/25
  inventory counts and the 296-declaration fresh replay; default Nix proof and
  dependency builds; clean-source `nix flake check`; formatter, whitespace,
  and Theory import-boundary checks; exact compile-time axiom manifests.
- **Axiom note:** the Theory certificate WF roots close over only `propext` and
  `Quot.sound`; rule closure/pattern facts additionally use
  `Classical.choice`, never `sorryAx` or a project-specific axiom. Verify's
  translated matrix retains the already classified projection `sorryAx`,
  pointer/expression/persistent-container contracts, existing mutual/nested
  observations, and six narrowly named native observations for selecting the
  singleton matrix and pinning the new deep fixture. No new `axiom`
  declaration or source `sorry` was added, and the compiled frontier remains
  exactly 25 allowlisted entries.
- **Upstream issue/PR:** TBD; submit the Theory façade independently of the
  implementation replay corpus where practical.
- **Removal condition:** upstream exposes equivalent consumer-neutral block
  consequences and actual-metadata replay breadth, all downstream users move
  to it, and the fork-only certificate/matrix can be deleted.

## D014 — Theory local-context and literal readiness API

- **Status:** local-committed at `jcb/formalization2`; publication to
  `jcb/formalization2` is pending.
- **Commit:** L4L-12A extraction is `958d03b7`, based on `0587b91a`; this
  L4L-12B readiness checkpoint is its independently gated child.
- **Delta:** move the consumer-neutral `VLocalDecl` core and its VExpr-only
  structural, WF, and defeq laws to `Theory/LocalContext.lean`. Move literal
  encodings, containment, primitive descriptors, and lift/substitution laws
  to `Theory/Literals.lean`, while keeping `Lean.Expr` traversal in Verify as
  a compatibility surface. Add exact Bool/Nat/Char/List/String descriptors,
  including generated recursors and iota rules, and package them with
  `Ordered` as `VEnv.PreludeReady`. Derive typed literal expressions from
  readiness plus the actual containment witness, preserve readiness across
  ordered environment growth and successful fresh constant/defeq additions,
  and connect Verify's `Literal.toConstructor` traversal to the direct Theory
  encoding and WF result.
- **Ix impact:** Theory-only consumers can use local declarations and typed
  literals without importing implementation expressions or relying on name
  containment as a type oracle. Existing Verify import paths continue to
  re-export the moved declarations.
- **Tests:** L4L-12A independently passed focused local-context/literal and
  complete Verify builds plus the full release gate. L4L-12B independently
  passes focused literal, Verify-bridge, and readiness fixture builds; exact
  descriptor equality against kernel-checked Bool, Nat, List, Char, and String
  metadata (including every required recursor and iota rule); large-nat and
  Unicode-string notation fixtures; aggregate and default Lake builds;
  unchanged 25-entry compiled sorry frontier; Nix proof and dependency builds;
  clean-source `nix flake check`; formatter, whitespace, and Theory
  import-boundary checks.
- **Axiom note:** no project axiom or source `sorry` was added. New Theory
  readiness preservation closes over only `propext` and `Quot.sound`; direct
  literal WF additionally uses `Classical.choice`. The Verify traversal bridge
  retains the already classified `sorryAx` inherited from its expression
  translation frontier and is guarded separately.
- **Upstream issue/PR:** TBD; submit the Theory extraction and exact readiness
  contract independently from consumer-specific traversal where practical.
- **Removal condition:** upstream provides equivalent Theory-only local-context
  and exact typed-literal readiness APIs, Verify consumers migrate to them,
  and the compatibility-only fork delta can be deleted.

## D015 — consumer-neutral projection semantics

- **Status:** local-committed (L4L-13A/B through L4L-15A checkpoints);
  publication is pending
- **Delta:** `Theory/Projection.lean` is a new consumer-neutral projection
  boundary: `VStructureView` restricts the one-family `GenerationChecked`
  artifact to the kernel structure class, `projectionCodes` encodes projections
  as recursor programs with dependent motives, and
  `VEnv.TrProj env U Γ view levels params idx major result` is the registered
  projection judgment with syntactic determinism, environment monotonicity, the
  L4L-14 structural-law bundle (`TrProj.structuralLaws`), and the staged
  structure-eta typing infrastructure (`etaRebuild`,
  `etaRebuild_hasType_of_constructorPrefix`). Verify's `TrProj` became a fully
  constrained existential wrapper over the Theory judgment (no invented
  metadata), and `inferProj.WF`/`reduceProj.WF` are proved against it.
  The registered-head inversion statement now requires an explicit
  completed-inductive `VEnv.ConstructorHead` certificate at both constructor
  conclusions. `ProjectionReady` derives that certificate from every host
  `ctorInfo` lookup, excluding axiom heads and definition aliases before the
  still-open injectivity proof is attempted.
  Upstream has no counterpart; its projection handling is unverified executable
  code only.
- **Ix impact:** downstream checkers obtain a concrete projection-laws package
  from published Theory APIs alone.
- **Tests:** `Tests/ProjectionExpressibility.lean` (`DependentRecord`),
  `Tests/StructureEtaCapability.lean`, `Tests/TheoryConsumerSurface.lean`, and
  the projection-reduction paths of the L4L-15A WHNF proofs.
- **Axiom note:** Theory roots close at `propext`/`Quot.sound`
  (`Classical.choice` where staged); no new axiom.
- **Upstream issue/PR:** TBD — PR 7 of the planned L4L-20C series.
- **Removal condition:** upstream adopts the projection structure view, laws,
  and checker proofs (or an agreed equivalent) and consumers migrate.

## D016 — executable checker refactors for verification

- **Status:** local-committed; publication is pending
- **Delta:** behavior-preserving reshapes of executable checker code so exact
  proofs can name its intermediate steps: `inferProj` uses extracted
  `invalidProj`/`inferProjParams`/`inferProjFields` helpers and adds the
  `isProjectionReadyStructure` and `idx < ctorInfo.numFields` guards (error
  path only); `tryEtaStructCore`'s field loop is the named
  `tryEtaStructFieldStep` callback; `whnfCore`/`reduceNative`/`reduceNat` use
  the transparent `Expr.structuralEq` where upstream uses the `BEq` `==`; and
  `checkConstructors` iterates families through the named
  `checkConstructorsLoop` recursion instead of `for`-notation (the v4.33 do
  elaborator synthesizes membership proofs that block exact-run rewriting).
- **Ix impact:** none directly; keeps checker-run certificates replayable.
- **Tests:** the executable-mirror fixtures in `Inductive/ValidationTrace.lean`
  and `Verify/Environment/*Replay*.lean`; kernel differential matrices.
- **Axiom note:** no new axiom; the guards reject strictly more, never accept
  more.
- **Upstream issue/PR:** TBD; mostly mechanical, submit alongside the proofs
  that need each reshape.
- **Removal condition:** upstream adopts the reshapes or the proofs stop
  needing named intermediate steps.

## D017 — checker readiness meets the v4.33 front-end chains

- **Status:** intentional-fork; extension and quotient transports proved at
  the 2026-08-24 STAB checkpoint
- **Delta:** this fork's `VContext`/`VEnvs.WF` carry `ProjectionReady` and,
  since L4L-15B, registered `StructureEtaReady` obligations that upstream's
  newly proved front-end declaration chains (#28) do not establish. The merge
  added the projection field to upstream's `VEnvAt`; L4L-15B paired the exact
  same five transitional declarations with structure-eta readiness, without
  adding or renaming a frontier entry. Both fields are supplied honestly by
  `VEnvs.WF.toVEnvAt`; the shared `Verify/Environment/Readiness.lean`
  transport now proves all five former declaration-extension obligations.
  `ProjectionReady` additionally maps every successful host `ctorInfo` lookup
  to a completed Theory inductive transaction and transports that evidence
  monotonically. Upstream's vacuous quotient-initialization proof
  (`checkEqType.WF` via `TrEnv'.no_inductInfo`) is refutable on this fork — the
  inductive boundary is implemented, so a translated environment can contain
  the real `Eq` — and has been replaced by a constructive `addQuot.WF` proof.
  `TrEnv'.sf_mono` was deleted (upstream's `ignore` constructor makes blanket
  safety-lowering unsound); the fixture `TrEnv'` derivations are now stated
  parametrically in `safety` instead.
- **Ix impact:** none; `addDecl`-chain roots were transitional premerge and
  remain transitional, now at finer grain.
- **Tests:** readiness staging, quotient replay, default Theory/Verify builds,
  and the exact sorry-frontier/trust audit.
- **Axiom note:** no new axiom or admission; the five extension entries and
  quotient entry have left the frontier. Upstream's
  `checkPrimitiveDef.WF` boundary remains.
- **Upstream issue/PR:** not applicable upstream (the obligation is
  fork-only); resolved by the L4L-19B transport proofs.
- **Removal condition:** upstream adopts equivalent projection,
  constructor-classification, structure-eta, and constructive quotient
  readiness contracts, or the fork's checker no longer requires them.

## D018 — v4.33.0 final toolchain (upstream pins v4.33.0-rc2)

- **Status:** intentional-fork (temporary)
- **Delta:** `lean-toolchain` pins `leanprover/lean4:v4.33.0` and batteries
  `v4.33.0` because `argumentcomputer/lean4-nix` vendors released toolchains
  only; upstream pins `v4.33.0-rc2`.
- **Removal condition:** upstream bumps to the final release (expected
  imminently); no code delta is attached to this row.

## D019 — registered structure eta in Theory

- **Status:** implemented intentional fork divergence; L4L-15B completed on
  the reconciled v4.33 base (2026-08-11).
- **Owner:** John C. Burnham; semantic review is part of the L4L-20C PR
  series.
- **Delta:** extend Theory with an explicit environment-registered
  structure-eta descriptor and a typed `VEnv.IsDefEq.structEta` rule for the
  same nonrecursive, single-constructor, zero-index structures accepted by
  Lean's kernel. The descriptor fixes the family and constructor heads and
  the deterministic recursor-encoded projector list, and carries syntactic
  lift/substitution laws. Registration is monotone and ordered; the equality
  constructor retains an exact family parameter spine and both endpoint
  typings. The durable design summary and removal condition are consolidated
  in `plans/roadmap.md` under TRUST/DIFF/RELEASE; the full original design and
  case inventory remain in git history.
- **Downstream impact:** every exhaustive `IsDefEq` consumer gains a case,
  including strong typing/inversion, weakening and substitution, environment
  monotonicity, Church--Rosser/parallel reduction, head standardization,
  nested transport, and the Verify structure-artifact bridge. Downstream
  Theory consumers see an additive descriptor/registry API and one additional
  definitional-equality constructor.
- **Tests:** executable metadata and kernel-conversion fixtures cover
  dependent parameterized neutral majors, parameterized zero-field,
  proof-field, and Prop-valued positives plus recursive, multi-constructor,
  and indexed negatives. Exact axiom guards cover registration, subject
  reduction, the primitive rule, Church--Rosser, `tryEtaStructCore.WF`, and
  `isDefEqUnitLike.WF`; the latter two left the direct sorry frontier, reducing
  it from 24 to 22 entries. The full release gate is green.
- **Axiom note:** no new project axiom or source `sorry` is permitted. Existing
  L4L-16--L4L-18 frontier dependencies remain explicit in per-root manifests.
- **Parallel upstream conversation:** implementation is intentionally allowed
  to proceed in the fork as of 2026-08-11; upstream review is deferred to the
  L4L-20C proof-PR sequence. Record the issue/PR URL here when opened.
- **Removal condition:** upstream adopts the registered rule or an agreed
  equivalent and the fork migrates. If upstream rejects a Theory eta rule,
  disable the two executable structure-eta heuristics and remove this
  divergence rather than retaining an unsound verifier claim.

## D020 — proof-carrying extension reductions and beta-collapsed coverage

- **Status:** implemented intentional fork divergence; L4L-18B completed on
  the reconciled v4.33 base (2026-08-12).
- **Owner:** John C. Burnham; semantic review is part of the L4L-20C PR
  series.
- **Delta:** split upstream's combined `Params.pat_wf`/`extra_pat` contract
  into three explicit layers. `Params` retains only pattern combinatorics;
  every `ParRed`/`CParRed`/`WHRed.extra` contraction carries an exact
  `IsDefEqU` certificate for its concrete redex and instantiated payload;
  `PatternArgumentNonFunction` excludes eta-sensitive under-saturated
  constructor majors; `StructurePatternCompatibility` names only the local
  registered-iota/structure-eta critical pair; and `Params.Extension.join`
  adds a consumer-supplied `CRDefEq` obligation for every raw registered
  equation in every well-formed context while inheriting both admissibility
  contracts.
  `CertifiedExtension.covers` records only a match after `VExpr.stripLams`,
  where generated iota and quotient tower bodies actually expose a
  first-order pattern. The durable rationale, trust boundary, and removal
  condition are consolidated in `plans/roadmap.md` under
  TRUST/DIFF/RELEASE; the full original trust matrix remains in git history.
- **Downstream impact:** Church--Rosser and head standardization transport the
  local equality certificate through weakening, substitution, context
  conversion, match inversion, and triangle proofs. Only results that invoke
  the repaired `NormalEq.parRed` require the two explicit admissibility
  classes; raw registered-equation Church--Rosser requires
  `[Params.Extension]`, which supplies both.
  `VEnv.LE.extra`, `extra_appN`, and `extra_appN_symm` publish the environment
  growth boundary. L4L-16 must construct the whole-live-environment join
  instance through the semantic bridge; the block assembler intentionally
  does not synthesize one.
- **Tests:** exact guards cover the two public admissibility interfaces,
  universe-instantiation of matches, the
  generated-iota and `quotDefEq` beta-collapsed certificates, and all three
  `VEnv.LE` transport helpers. Concrete mutual-block and quotient fixtures
  compile the tower obligations. Focused Church--Rosser, head-reduction, and
  pattern-environment builds plus the full release gate cover migrated
  consumers.
- **Axiom note:** no new project axiom or source `sorry` is permitted. The
  concrete tower witnesses have only the standard logical baseline and no
  `sorryAx`; existing L4L-16--L4L-18 proof-frontier dependencies are unchanged
  and remain visible in their existing guards.
- **Parallel upstream conversation:** implementation proceeds in the fork as
  decided on 2026-08-12; upstream review is deferred to the L4L-20C proof-PR
  sequence. Record the issue/PR URL here when opened.
- **Removal condition:** upstream adopts the proof-carrying contraction plus
  explicit registered-equation join split, or an equivalent interface that
  represents beta-collapsed tower rules without a trusted shape or soundness
  oracle, and the fork migrates.

## D021 — Tests stay in the default build surface

- **Status:** intentional-fork, created by the L4L-16R reconciliation
  (2026-08-20)
- **Delta:** upstream `3f6e8f92` moved `Lean4Lean.Tests` out of
  `defaultTargets` and compensated with an explicit "Build Lean4Lean.Tests"
  CI step; the fork keeps `Lean4Lean.Tests` in `defaultTargets`
  (`lakefile.toml`) because the §6 release gate and the Nix `proofs` check
  build the default surface with `--wfail` and rely on Tests riding along.
  Upstream's CI intent (Tests must compile) is therefore satisfied by the
  fork's default `lake build` step, and the fork's `ci.yml` keeps its own
  structure (frontier check, `--wfail`, Experimental job) without the extra
  step. The fork also retains its batteries pin `v4.33.0` (upstream:
  `v4.33.0-rc2`; see D018).
- **Ix impact:** none; build-surface only.
- **Tests:** `lake build` (default targets) is the §6 gate's first line.
- **Removal condition:** the gate stops depending on default-target Tests
  coverage (e.g. it names `Lean4Lean.Tests` explicitly), after which the
  lakefile can converge with upstream's.

## D022 — `reduceProjCore.WF` proved (upstream carries it as a sorry)

- **Status:** local-committed; upstream-contribution candidate — submit
  while `62441418` is fresh
- **Delta:** upstream `62441418` ("perf: add lazyDeltaProjReduction") split
  `reduceProj` into `reduceProjCore` + a `>>=` wrapper and moved
  `reduceProj.WF` to `Verify/TypeChecker/Reduce.lean`, proved atop a *new
  sorry* `reduceProjCore.WF`. The fork had already proved the unsplit
  `reduceProj.WF` sorry-free via its TrProj semantics
  (`registeredStructureHeadInversion`, projector/constructor alignment); the
  L4L-16R merge reshaped that proof onto the split, so
  `Verify/TypeChecker/Reduce.lean` now proves `reduceProjCore.WF` outright
  (the string-literal branch and the `withApp` constructor-field selection)
  and keeps upstream's wrapper derivation for `reduceProj.WF` verbatim. Both
  measure `[propext, sorryAx, Classical.choice, Quot.sound]` plus only the
  three persistent-collection contracts — a subset of the file's
  pre-existing `reduceNat.WF` closure; the `sorryAx` is inherited from the
  unchanged 22-entry frontier (whnf/whnfCore method chains and the TrProj
  transport lemmas), not from any new admission.
- **Ix impact:** none directly; keeps the fork's proj-reduction closure
  intact across upstream's defeq-path change (`isDefEqCore'` proj case now
  runs `lazyDeltaProjReduction`, fully verified upstream given
  `reduceProjCore.WF`).
- **Tests:** `lake build Lean4Lean.Verify`; the frontier audit stays at
  exactly 22 known sorries.
- **Upstream issue/PR:** TBD — the discharge depends on the fork's TrProj
  machinery, so it travels with the projection-semantics series (D015), but
  the statement-level fact that the sorry is dischargeable is worth
  signalling upstream immediately.
- **Removal condition:** upstream proves `reduceProjCore.WF` (theirs or a
  ported version of this proof) and the fork rebases onto it.

## D023 — honest opaque-runtime domains and cache-independent fallbacks

- **Status:** implemented in the 2026-08-25 trust-repair checkpoint;
  upstream-contribution and reconciliation candidate.
- **Source:** manually adapted from lean4lean PRs #44 (`1eb66c6`), #45
  (`3bcfe75`), and #46 (`d666dd6`); no wholesale PR merge and no unrelated
  co-author trailers.
- **Delta:** narrow the level/expression `mkData` equations to the runtime bit
  ranges, range-instantiation equations to checked slices, simultaneous
  instantiation to the source-closed/all-substituends-closed domain,
  abstraction equality to closed/no-duplicate inputs, persistent-array push
  to generated `WF` arrays, and loose-bvar cache equality to hereditary
  `BVarBounded` expressions. A weaker `AbstractFVarShape` bridge serves callers
  that need only abstraction skeleton preservation. Cached `false` bits imply
  structural absence where needed; unsupported structural-to-cache converses
  are not retained.
- **Executable delta:** `cheapBetaReduce` performs its no-op instantiation;
  lambda/forall comparison always introduces a real fresh fvar; and a reached
  loose bvar is rejected explicitly. These differ from Lean only on malformed
  or cache-corrupt expressions and preserve ordinary valid-input results.
- **Ix impact:** this is release-blocking trust hardening. Ix may later regain
  the cache fast paths only behind a certificate preserved by every expression
  ingress and a proof of observational equivalence with the simple path.
- **Tests:** `Lean4Lean.Tests.TrustRepair`, the full Verify environment replay
  surface, exact repaired-signature guards, and the four-root axiom policy.
- **Axiom note:** the formerly inconsistent unconditional
  `Expr.looseBVarRange_eq` no longer exists. The manifest now has 28 honest
  custom contracts (including the shape-only replacement), none reachable
  from Theory; exact rationale is in `docs/axiom-audit.md`.
- **Removal condition:** upstream adopts equivalent truthful domains and
  checker behavior, or Lean/Ix supplies verified implementations that allow
  the corresponding bridges to be deleted. Do not remove this row by
  reinstating unconditional cache equations.

## D024 — C++-compatible raw universe-level construction

- **Status:** implemented by UP5 from the reviewed `differential` topic;
  upstream-contribution candidate.
- **Owner:** Argument Computer Corporation; review on each Lean toolchain
  update.
- **Source:** manually adapted from upstream topic commit
  `26f9838a876079204ad41a5faa174680cc49a3bf` rather than merged wholesale.
- **Delta:** Lean v4.33.0's public level helpers and its C++ kernel apply
  different local simplifications while constructing raw levels: the Lean
  helper collapses
  `max (succ u) 1`, while C++ preserves it, and only C++ collapses
  `imax 1 u` to `u`. The fork has separately named `*Cpp` level, expression,
  and declaration-instantiation functions and uses them in kernel-facing
  constant inference, forall inference, projection inference, delta
  unfolding, and recursor reduction. These functions are not canonicalizers.
  Semantic equivalence and ordering still use the Géran-based `NormLevel`
  model through `isEquiv'` and `geq'`; Verify proves the C++-compatible raw
  constructors preserve those existing `VLevel` semantics. See
  `docs/universe-levels.md` for the layer boundary.
- **Ix impact:** exact expression structure determines expression hashes and
  the type checker's unfold/WHNF cache keys and values. Out-of-circuit and
  circuit transports therefore need the C++ kernel's result, not merely a
  semantically equivalent universe. Canonical equality alone cannot recover
  the raw representation after it has been erased.
- **Tests:** `Lean4Lean.Tests.DifferentialParity` builds deliberately raw
  unchecked local declarations, compares both discriminating cases against
  `Lean.Kernel.check` on Lean v4.33.0
  (`d8b18978322de05a8f3dba51ef03cf5461676c17`), and pins exact expression,
  hash, unfolded-value, unfold-cache, and WHNF-cache parity. The fixture also
  fails explicitly once the public helpers converge, prompting removal of
  the compatibility layer.
- **Axiom note:** no new axiom or admission. The adapted structural proofs
  reduce the printed closure of
  `primitiveCandidateObserversOfNestedRun` by `Expr.mkAppData_eq` and
  `Expr.replace_eq`.
- **Removal condition:** Lean's public level constructors and substitution
  chain match the C++ kernel on the discriminating fixtures, after which the
  `*Cpp` copies can be deleted and callers/proofs moved back to the standard
  APIs. Upstream can satisfy this by promoting `26f9838` or an equivalent
  stdlib/kernel convergence fix.

## D025 — safe definition bodies precede primitive recognition

- **Status:** implemented as the UP6 foundation; upstream-contribution
  candidate already represented by lean4lean PR #32.
- **Owner:** Argument Computer Corporation; remove or revise with the primitive
  certificate pipeline.
- **Source:** manually extracted from upstream PR #32 commit
  `19a18e5dd143386cd9485728878b9944850bc9c1`; its unrelated unsafe and mutual
  definition refactors were not imported.
- **Delta:** a checked safe definition now validates and translates its header
  and body before running `checkPrimitiveDef`, then calls `checkName` with the
  recognizer result. Accepted declarations are unchanged, but a declaration
  that would fail in more than one phase can report a body error before a
  primitive-shape, reserved-name, or duplicate-name error. The named
  `checkConstantValBody` and `checkDefinitionBody` helpers expose the exact
  successful prefix needed by per-primitive `isDefEq` certificates.
- **Ix impact:** this is verification infrastructure for proving primitive
  declarations preserve `VEnv.HasPrimitives`. Ix consumers should not depend
  on the old ordering of errors for invalid declarations.
- **Tests:** `Lean4Lean.Tests.Environment` pins the phase order with a malformed
  duplicate `Nat.add` whose header references a missing constant; the full
  Verify environment proves that the new successful prefix supplies the
  translated, well-typed `VDefVal` consumed by primitive checking.
- **Axiom note:** no admission was added. The existing
  `checkPrimitiveDef.WF` boundary remains one allowlisted sorry, but its domain
  is narrower: callers must now supply translations and a typing derivation
  for the candidate body, and it accepts the post-body checker state.
- **Removal condition:** upstream lands PR #32 or an equivalent body-first
  certificate architecture and this fork reconciles to that implementation;
  the named helpers may remain if they are part of the shared API.

## D026 — direct Nat.add primitive certificate and lambda-closed equations

- **Status:** implemented as the first semantic UP6 slice; upstream-derived
  specialization with remaining primitive families still open.
- **Owner:** Argument Computer Corporation; extend by one independently green
  primitive family at a time.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its executable
  certificate, checker infrastructure, conservation, and dispatch commits;
  no whole-PR merge and no `PSigma`-specialized mod/div or bitwise material.
- **Executable delta:** the isolated Nat.add equation helpers close their open
  equations with `Expr.lam0`, as PR #32 does, rather than wrapping their
  bodies in `Expr.arrow`. This checks equality of the intended pointwise
  functions. Other primitive branches retain their old helpers until their
  own certificate slices land. `checkNatAddPrimitive` is otherwise a
  definitional extraction of the Nat.add branch into a bounded executable
  surface.
- **Verification delta:** `Verify/Primitive.lean` proves Nat.add's exact typed
  recognizer trace, converts its zero/successor equations into literal
  reflection, and transports all other local `HasPrimitives` fields through
  the definition extension. `checkSafeNatAddDefinition.WF` and
  `addDefinition.WF_safe_natAdd` connect those proofs to the retained
  readiness-aware `AddDef` transaction. The live `addDefinition.WF` selects
  this theorem for safe Nat.add before falling back to the generic primitive
  boundary for other names.
- **Ix impact:** Nat.add is the first primitive definition whose supported
  declaration path has a concrete end-to-end certificate rather than relying
  on the opaque generic recognizer assumption. The structure is intentionally
  family-specific so Ix can transport only the primitives it supports.
- **Tests:** `Lean4Lean.Tests.Primitive` checks that the live dispatch directly
  names the Nat.add certificate and that the certificate's transitive closure
  excludes `checkPrimitiveDef.WF`. It also pins the exact six inherited
  sorry-carrying metatheory/type-checker dependencies; the global frontier
  remains 15 and no new source admission is added.
- **Removal condition:** upstream lands the corresponding PR #32 slice (or a
  stronger generic proof) and this fork can reconcile without losing its
  readiness transaction, dependency pin, or more precise accepted-domain
  requirements.

## D027 — retained Nat.pred reflection and direct primitive certificate

- **Status:** implemented as the second semantic UP6 slice; upstream-derived
  specialization with the remaining primitive families still open.
- **Owner:** Argument Computer Corporation; retain through the Nat.sub slice
  and review when reconciling the complete primitive contract upstream.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its unary
  reflection, Nat.pred recognizer certificate, conservation theorem, and live
  dispatch; no whole-PR merge.
- **Executable delta:** `checkNatPredPrimitive` extracts the Nat.pred branch
  and closes its open successor equation with `Expr.lam0`, so the executable
  check states the intended pointwise equation. Other unported primitive
  branches retain their existing helpers until their own slices land.
- **Verification delta:** the retained Theory contract now includes
  `ReflectsNatNat` and a `natPred` field carrying both the unary constant type
  and literal computation. This is the minimum persistent evidence required
  to certify Nat.sub's successor recurrence; the previous local contract
  intentionally omitted Nat.pred and would have forgotten that evidence
  after declaration installation. The direct typed recognizer, safe checker,
  and readiness-aware `AddDef` path establish and preserve the new field.
- **Ix impact:** Nat.pred now has a concrete end-to-end declaration
  certificate, and later transports can rely on its exact unary literal
  behavior rather than merely its presence. Adding Nat.pred to
  `reflectedPrimitiveNames` also prevents unrelated declaration transactions
  from silently replacing it.
- **Tests:** `Lean4Lean.Tests.Primitive` checks that the live dispatch names
  both direct elementary-Nat roots, that neither reaches
  `checkPrimitiveDef.WF`, and that each reaches exactly the same six inherited
  sorry-carrying dependencies. The complete sorry-frontier and release-root
  audits remain unchanged.
- **Removal condition:** upstream lands the corresponding PR #32 slice (or a
  stronger generic proof) and reconciliation preserves the unary reflection
  needed by Nat.sub together with the fork's readiness transaction and trust
  pins.

## D028 — direct Nat.sub certificate consumes retained Nat.pred reflection

- **Status:** implemented as the third semantic UP6 slice; upstream-derived
  specialization with the remaining primitive families still open.
- **Owner:** Argument Computer Corporation; extend next through Nat.mul and
  Nat.pow, then review with the complete primitive dispatch.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its Nat.sub
  recognizer certificate, recurrence conservation, and live dispatch; no
  whole-PR merge or unrelated mod/div infrastructure.
- **Executable delta:** `checkNatSubPrimitive` extracts the Nat.sub branch and
  closes both binary equations with `Expr.lam0`. Its successor recurrence
  explicitly calls the already-installed `Nat.pred`; unported branches retain
  their existing helpers until their own bounded slices land.
- **Verification delta:** the typed recognizer translates the exact binary
  checker trace and obtains the successor right-hand side from the retained
  unary Nat.pred reflection. `ReflectsNatNatNat.of_sub_equations` converts
  those equations into Nat.sub literal reflection, `addNatSubDef` preserves
  the full readiness-aware primitive contract, and the safe checker plus live
  `AddDef` path install that evidence without the generic recognizer theorem.
- **Ix impact:** Nat.sub now has a concrete end-to-end declaration certificate
  whose dependency on Nat.pred is semantic, not merely a name-presence check.
  Ix transports can select this narrow arithmetic chain without importing the
  later mod/div or well-founded-recursion certificate machinery.
- **Tests:** `Lean4Lean.Tests.Primitive` checks that all three direct
  elementary-Nat roots are named by live dispatch, exclude
  `checkPrimitiveDef.WF`, and each reach exactly the same six inherited
  sorry-carrying dependencies. The global source frontier remains unchanged.
- **Removal condition:** upstream lands the corresponding PR #32 slice (or a
  stronger generic proof) and reconciliation preserves the retained Nat.pred
  dependency, readiness transaction, and exact trust pins.

## D029 — typed binary reflection and direct Nat.mul certificate

- **Status:** implemented as the fourth semantic UP6 slice; upstream-derived
  specialization with the remaining primitive families still open.
- **Owner:** Argument Computer Corporation; retain through Nat.pow and review
  with the complete primitive dispatch.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its typed binary
  reflection, shared binary-step recurrence proof, Nat.mul recognizer and
  conservation certificate, and live dispatch; no whole-PR merge.
- **Contract delta:** `ReflectsNatNatNat` now retains the reflected constant's
  `Nat → Nat → Nat` typing in addition to literal computation. Literal
  evaluation alone was enough for reduction but could not justify applying
  Nat.add to Nat.mul's arbitrary typed recursive result. All model-extension,
  primitive-family, definition-equation, and structure-eta transports now
  preserve both components.
- **Executable delta:** `checkNatMulPrimitive` extracts the Nat.mul branch and
  closes both equations with `Expr.lam0`; unported branches retain their old
  helper shape until their own slices land.
- **Verification delta:** the typed recognizer translates the recursive Nat.add
  application, `of_binop_step_equations` proves the general binary recurrence,
  and `addNatMulDef` installs the resulting reflection through the existing
  readiness-aware `AddDef` transaction. Live safe dispatch no longer reaches
  the generic recognizer theorem for Nat.mul.
- **Ix impact:** the stronger reflection is the evidence shape needed for
  compositional arithmetic transports: an Ix consumer can both reduce a
  certified binary primitive on literals and type its use inside the next
  primitive certificate.
- **Tests:** `Lean4Lean.Tests.Primitive` checks that all four direct
  elementary-Nat roots are named by live dispatch, exclude
  `checkPrimitiveDef.WF`, and each reach exactly the same six inherited
  sorry-carrying dependencies. The source frontier remains unchanged.
- **Removal condition:** upstream lands the corresponding PR #32 slice (or a
  stronger generic proof) and reconciliation preserves the typed binary
  contract, readiness transaction, and exact trust pins.

## D030 — direct Nat.pow certificate completes the elementary recurrence spine

- **Status:** implemented as the fifth semantic UP6 slice; upstream-derived
  specialization with comparison, bitwise, mod/div, and wrapper families
  still open.
- **Owner:** Argument Computer Corporation; retain through final primitive
  dispatch and review with the complete V4 disposition.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its Nat.pow
  recognizer, binary-step conservation specialization, and live dispatch; no
  whole-PR merge.
- **Executable delta:** `checkNatPowPrimitive` extracts the Nat.pow branch and
  closes its base-one and successor equations with `Expr.lam0`; later
  primitive branches retain their existing helper shape until their bounded
  slices land.
- **Verification delta:** the typed recognizer translates one as
  `Nat.succ Nat.zero` and types the recursive multiplication with the retained
  Nat.mul reflection. `of_pow_equations` reuses the generic binary recurrence
  at base value one, and `addNatPowDef` installs the result through the fork's
  readiness-aware `AddDef` transaction. Live safe dispatch no longer reaches
  the generic recognizer theorem for Nat.pow.
- **Ix impact:** the complete elementary arithmetic chain now has narrow,
  compositional declaration certificates through exponentiation. An Ix
  transport can select these roots without importing the later condition or
  well-founded-recursion certificate machinery.
- **Tests:** `Lean4Lean.Tests.Primitive` checks that all five direct elementary
  Nat roots are named by live dispatch, exclude `checkPrimitiveDef.WF`, and
  each reach exactly the same six inherited sorry-carrying dependencies. The
  source frontier remains unchanged.
- **Removal condition:** upstream lands the corresponding PR #32 slice (or a
  stronger generic proof) and reconciliation preserves the retained Nat.mul
  dependency, readiness transaction, and exact trust pins.

## D031 — typed Nat-to-Bool reflection and direct Nat.beq certificate

- **Status:** implemented as the sixth semantic UP6 slice; Nat.ble is tracked
  separately by D032, while shift, bitwise, and mod/div families remain open.
- **Owner:** Argument Computer Corporation; review alongside D032 when the
  condition-reflection consumers land.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its typed
  Nat-to-Bool reflection, shared four-equation checker, constructor-recursion
  conservation theorem, Nat.beq certificate, and live dispatch; no whole-PR
  merge.
- **Contract delta:** `ReflectsNatNatBool` now retains the reflected
  constant's `Nat → Nat → Bool` typing in addition to literal computation.
  The previous evaluation-only contract sufficed for literal reduction but
  could not type the reflected predicate for later condition consumers. All
  constant, definition-equation, structure-eta, and primitive-family
  transports preserve both components.
- **Executable delta:** `checkNatBEqPrimitive` extracts the Nat.beq branch and
  closes the three open constructor equations with `Expr.lam0`; no
  condition-reflection or mod/div code enters this slice.
- **Verification delta:** `checkNatBinaryBoolTyped.WF` certifies the common
  four-equation trace, `of_rec_equations` proves the resulting literal
  reflection, and `addNatBEqDef` installs it through the readiness-aware
  `AddDef` transaction. Live safe dispatch no longer reaches the generic
  recognizer theorem for Nat.beq.
- **Ix impact:** equality on Nat literals is now both computable and typed in
  the verified model, providing the narrow predicate evidence required by
  later Ix condition and arithmetic transports.
- **Tests:** `Lean4Lean.Tests.Primitive` checks that all six direct roots are
  named by live dispatch, exclude `checkPrimitiveDef.WF`, and each reach
  exactly the same six inherited sorry-carrying dependencies. The source
  frontier remains unchanged.
- **Removal condition:** upstream lands the corresponding PR #32 slice (or a
  stronger generic proof) and reconciliation preserves the typed predicate
  contract, readiness transaction, and exact trust pins.

## D032 — direct Nat.ble certificate

- **Status:** implemented as the seventh semantic UP6 slice; the elementary
  comparison pair is complete. Nat.shiftLeft is tracked separately by D033;
  Nat.shiftRight, bitwise, and mod/div remain open.
- **Owner:** Argument Computer Corporation; review with D031 when the shared
  condition-reflection consumers land.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its Nat.ble
  recognizer certificate, constructor-equation conservation, and final
  dispatch pattern; no whole-PR merge.
- **Executable delta:** `checkNatBLEPrimitive` extracts the Nat.ble branch and
  checks its exact `(true, true, false)` constructor table plus successor-pair
  recurrence under lambdas.
- **Verification delta:** `checkPrimitiveDef.natBLE.WF_typed` reuses the
  shared typed binary-Boolean checker introduced by D031;
  `ReflectsNatNatBool.of_rec_equations` is instantiated at `Nat.ble`, and
  `addNatBLEDef` installs the result through the fork's readiness-aware
  `AddDef` transaction. Live safe dispatch no longer reaches the generic
  recognizer theorem for Nat.ble.
- **Ix impact:** both primitive Nat equality and ordering now have typed
  literal computation certificates, completing the elementary predicate
  basis needed by later verified condition handling.
- **Tests:** `Lean4Lean.Tests.Primitive` checks that all seven direct roots are
  named by live dispatch, exclude `checkPrimitiveDef.WF`, and each reach
  exactly the same six inherited sorry-carrying dependencies. The source
  frontier remains unchanged.
- **Removal condition:** upstream lands the corresponding PR #32 slice (or a
  stronger generic proof) and reconciliation preserves the shared typed
  predicate contract, readiness transaction, and exact trust pins.

## D033 — direct Nat.shiftLeft certificate

- **Status:** implemented as the eighth semantic UP6 slice; Nat.shiftRight
  remains ordered after Nat.div, while bitwise and its wrappers remain open.
- **Owner:** Argument Computer Corporation; review when the remaining shift or
  bitwise families are extracted.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its shift checker,
  recursive-input conservation theorem, and dispatch pattern; no whole-PR
  merge.
- **Executable delta:** `checkNatShiftLeftPrimitive` extracts the exact closed
  type, zero-shift equation, and successor equation from the monolithic
  recognizer. It depends only on the already certified Nat.mul constant.
- **Verification delta:** `checkNatShiftTyped.WF` certifies the shared shift
  trace and literal two, while `of_shiftLeft_equations` proves literal
  reflection by induction on the shift amount with the first argument
  generalized. `addNatShiftLeftDef` installs that reflection through the
  fork's readiness-aware `AddDef` transaction, and live safe dispatch no
  longer reaches the generic recognizer theorem for Nat.shiftLeft.
- **Accepted-domain decision:** Nat.shiftLeft is extracted before the bitwise
  family because its checker is finite and compositional. Nat.shiftRight
  still requires the unported Nat.div certificate; Nat.land, Nat.lor, and
  Nat.xor are syntactic wrappers over Nat.bitwise and cannot yet receive
  honest literal reflection without that larger well-founded certificate.
- **Ix impact:** verified literal left shifts can now be transported using a
  narrow root whose only arithmetic dependency is Nat.mul, without importing
  division, conditions, or bitwise well-founded recursion.
- **Tests:** `Lean4Lean.Tests.Primitive` checks that all eight direct roots are
  named by live dispatch, exclude `checkPrimitiveDef.WF`, and each reach
  exactly the same six inherited sorry-carrying dependencies. The source
  frontier remains unchanged.
- **Removal condition:** upstream lands the corresponding PR #32 slice (or a
  stronger generic proof) and reconciliation preserves the retained Nat.mul
  dependency, readiness transaction, and exact trust pins.

## D034 — shared reflected-condition certificate foundation

- **Status:** implemented as the ninth UP6 foundation slice; this certifies
  selector behavior but does not yet claim a direct Nat.mod or Nat.div
  declaration certificate.
- **Owner:** Argument Computer Corporation; review with the first mod/div or
  bitwise consumer.
- **Source:** manually extracted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally
  `ConditionReflect.lean` plus the small generic support declarations that
  its upstream import obtained indirectly from the bitwise and monolithic
  primitive modules. No mod/div recursion or bitwise certificate was imported.
- **Dependency decision:** the fork exposes `ConditionSupport` explicitly.
  It contains constructor fragments, lambda-equation instantiation, and the
  raw checked-selector evidence types. `ConditionReflect` depends on that
  neutral module rather than a misleading bitwise support import.
- **Verification delta:** checked nondependent and dependent selector
  equations can be canonicalized to chosen closed translations, and typed
  calls select the branch determined by an evaluated Boolean condition. Seven
  proof sites were adapted to Lean v4.33's current explicit lift/instantiation
  normal forms; no checker domain was changed.
- **Ix impact:** later Nat.mod/div and bitwise transports can share one typed
  condition-elimination boundary instead of duplicating proof-argument and
  branch-selection reasoning.
- **Tests:** `Lean4Lean.Tests.ConditionReflect` pins four representative
  theorem closures. The two equation-canonicalization endpoints use only
  `propext`, `Classical.choice`, and `Quot.sound`; the two typed
  branch-selection endpoints transparently retain the existing upstream
  `sorryAx` dependency.
- **Removal condition:** upstream exposes an equivalently neutral module
  boundary, or reconciliation can import the same proof layer without the
  fork-owned split and Lean-v4.33 normalization adaptations.

## D035 — retained Nat-≤ selector evidence

- **Status:** implemented as the tenth bounded UP6 slice; the checker now
  exports the selector evidence needed by Nat.mod/div, but this entry does not
  claim either recursive primitive certificate.
- **Owner:** Argument Computer Corporation; review with the Nat.mod and Nat.div
  declaration slices.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally the generic
  reflection-checker WF segment and `ModDivCondition.lean`; no bitwise support,
  Nat.mod/div recursion, or admitted generic primitive boundary was imported.
- **Executable delta:** `Reflection.checkITE` and
  `Reflection.checkNatDITE` check closed-lambda equations rather than equations
  in temporary local contexts. `Condition.check` also checks the synthesized
  Boolean decision function's type. The Nat-≤ primitive wrapper first checks a
  finite list of evidence expressions so their translations are available to
  the conservation proof.
- **Accepted-domain decision:** the closed equations and explicit decision
  function check are intentional evidence-retaining guards inherited from the
  upstream certificate design. They strengthen the observable checker contract
  needed by the proof instead of reconstructing unrecorded facts after the
  check succeeds.
- **Verification delta:** `ConditionChecker` proves the executable reflection
  and Nat-≤ checker path. `ModDivCondition` packages successful checks as a
  `NatLESelectorCertificate`, canonicalizes both ITE and DITE equations, and
  selects their true or false branches from the already certified direct
  `Nat.ble` semantics.
- **Ix impact:** the direct Nat.mod transport now consumes, and the forthcoming
  Nat.div transport can consume, one
  explicit, monotone selector capability rather than depending on the generic
  primitive theorem or on an opaque Boolean-elimination assumption.
- **Tests:** `Lean4Lean.Tests.ModDivCondition` pins the exact checker-WF and
  evidence-wrapper axiom closures, including the existing executable-model
  bridge axioms, and separately pins representative ITE and constructor-DITE
  selector endpoints to the four expected logical/admitted dependencies.
- **Removal condition:** upstream exposes the same retained-evidence boundary,
  or reconciliation can import its checker and selector modules directly while
  preserving this fork's explicit trust pins and readiness-aware Nat.ble
  dependency.

## D036 — direct Nat.mod certificate without a new expression axiom

- **Status:** implemented as the eleventh bounded UP6 slice; the live safe
  definition path has a direct Nat.mod certificate, and Nat.div is next.
- **Owner:** Argument Computer Corporation; review with the Nat.div declaration
  slice and any later consolidation of the shared fuel-recursion layer.
- **Source:** manually adapted from lean4lean PR #32, principally commit
  `27304be` as retained at head
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`; no whole-PR merge, bitwise
  certificate, or admitted generic primitive dispatch was imported.
- **Executable delta:** `natModTopEquation`, `natModGoEquation`, and
  `checkNatModPrimitive` name the exact closed type, zero equation,
  less-than-or-equal helper type, recursive helper type, selector checks, and
  top/recursive equations that the existing monolithic recognizer accepts.
  The live `checkPrimitiveDefCore` Nat.mod branch now calls that named checker.
- **Verification delta:** `checkPrimitiveDef.natMod.WF_typed` retains the
  checker trace; `FuelStep` and `VExpr.natModGo` prove the fuel-indexed literal
  semantics; the recursive branch consumes the retained Nat-≤ selector and
  direct Nat.sub reflection; and `NatModPrimitiveEvidence` installs the result
  through every readiness safety model and `addDefinition.WF`.
- **Trust decision:** PR #32's proof route adds the opaque expression equality
  `Lean.Expr.liftLooseBVars_eq`. This fork instead defines the proof-side
  sources structurally with `liftLooseBVars'` and pins the resulting theorem
  closures. The slice adds no custom axiom, `native_decide` proof, or source
  `sorry`.
- **Accepted-domain decision:** the checker retains the closed primitive type,
  zero equation, Nat-≤ and recursive-helper types, selector evidence,
  top-level equation, and recursive equation. These are evidence-preserving
  guards matching the executable upstream certificate, not a narrower
  hard-coded semantic model.
- **Ix impact:** the model now certifies actual natural-number remainder on
  literals through a narrow live root suitable for later Ix kernel transport;
  it does not yet certify Nat.div, shiftRight, gcd, or bitwise operations.
- **Tests:** `Lean4Lean.Tests.NatMod` enforces an explicit axiom allowlist for
  the checker, fuel, semantics, conservation, wrapper, and safe-definition
  roots, including exclusion of `Lean.Expr.liftLooseBVars_eq`.
  `Lean4Lean.Tests.Primitive` checks that all nine direct live roots avoid
  `checkPrimitiveDef.WF` and reach exactly the six existing inherited sorry
  carriers. The global source frontier remains 15.
- **Removal condition:** upstream lands an equivalent Nat.mod certificate
  without requiring a stronger opaque expression axiom, or reconciliation can
  reuse its result while preserving the fork's readiness transport,
  accepted-domain checks, and exact trust pins.

## D037 — direct Nat.div certificate with a proved structural lift bridge

- **Status:** implemented as the twelfth bounded UP6 slice; the live safe
  definition path has a direct Nat.div certificate, and Nat.shiftRight is
  next.
- **Owner:** Argument Computer Corporation; review with Nat.shiftRight and any
  later consolidation of the shared mod/div fuel-recursion layer.
- **Source:** manually adapted from lean4lean PR #32, principally commit
  `27304be` as retained at head
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`; no whole-PR merge, bitwise
  certificate, or admitted generic primitive dispatch was imported.
- **Executable delta:** `natDivTopEquation`, `natDivGoEquation`, and
  `checkNatDivPrimitive` name the exact closed type, top-level quotient
  equation, less-than-or-equal helper type, recursive helper type, selector
  checks, and recursive equation. The live `checkPrimitiveDefCore` Nat.div
  branch now calls that evidence-retaining checker. A reducible
  `primitiveLiftLooseBVars` constructs the one-binder shifts used by those
  equations instead of relying on an opaque runtime equality theorem.
- **Verification delta:** `checkPrimitiveDef.natDiv.WF_typed` retains the
  checker trace; the shared fuel-recursion layer proves literal quotient
  evaluation from the checked top and recursive branches; those branches
  consume the retained Nat-≤ selector and Nat.sub reflection;
  and `NatDivPrimitiveEvidence` installs the result through every readiness
  safety model and `addDefinition.WF`.
- **Trust decision:** PR #32 assumes the opaque implementation equality
  `Lean.Expr.liftLooseBVars_eq`. This fork proves
  `primitiveLiftLooseBVars_eq` by structural recursion against the proof-side
  `Expr.liftLooseBVars'`. The Nat.div trust test explicitly rejects any
  dependency on the opaque equality. The slice adds no custom axiom,
  `native_decide` proof, or source `sorry`.
- **Accepted-domain decision:** the checker retains the closed primitive type,
  helper types, selector evidence, and both defining equations. These are the
  same evidence-preserving guards used by the executable certificate, not an
  assumed semantic quotient model.
- **Ix impact:** the model now certifies actual natural-number quotient on
  literals through a narrow live root suitable for later Ix kernel transport.
  It supplies the semantic dependency needed by Nat.shiftRight; gcd and
  bitwise operations remain outside this slice.
- **Tests:** `Lean4Lean.Tests.NatDiv` pins the structural lift theorem and the
  checker, fuel, semantics, conservation, wrapper, and safe-definition roots
  to an explicit axiom allowlist while forbidding
  `Lean.Expr.liftLooseBVars_eq`. `Lean4Lean.Tests.Primitive` checks that all ten
  direct live roots avoid `checkPrimitiveDef.WF` and reach exactly the six
  existing inherited sorry carriers. The global source frontier remains 15.
- **Removal condition:** upstream lands an equivalent Nat.div certificate
  without requiring the opaque lift equality, or reconciliation can reuse its
  result while preserving the fork's readiness transport, accepted-domain
  checks, and exact trust pins.

## D038 — direct Nat.shiftRight certificate over verified division

- **Status:** implemented as the thirteenth bounded UP6 slice; both shift
  primitives now have direct live certificates.
- **Owner:** Argument Computer Corporation; review with later arithmetic
  wrappers and any consolidation of the shared shift checker.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its shared shift
  checker, quotient recurrence proof, and conservation theorem; no whole-PR
  merge, bitwise certificate, or admitted generic dispatch was imported.
- **Executable delta:** `checkNatShiftRightPrimitive` extracts the exact
  closed binary-Nat type, zero-shift equation, and successor equation from the
  monolithic recognizer. Its sole arithmetic dependency is the now-certified
  `Nat.div` constant.
- **Verification delta:** `checkPrimitiveDef.natShiftRight.WF_typed` reuses
  `checkNatShiftTyped.WF` and translates the recursive quotient by literal
  two. `ReflectsNatNatNat.of_shiftRight_equations` proves literal reflection
  by induction on the shift amount, rewriting the recursive result through
  retained Nat.div reflection. `addNatShiftRightDef` then installs the result
  through every readiness model and the live `addDefinition.WF` dispatch.
- **Accepted-domain decision:** this remains the upstream finite,
  equation-based certificate. It neither identifies the implementation with
  bitwise recursion nor narrows the accepted body beyond the two equations
  already checked by the executable recognizer.
- **Ix impact:** literal right shifts now have a narrow verified transport
  root, completing the pair of performance-relevant natural-number shifts
  without importing the larger gcd/bitwise well-founded-recursion machinery.
- **Tests:** `Lean4Lean.Tests.Primitive` checks that all eleven direct live
  roots are named by dispatch, avoid `checkPrimitiveDef.WF`, and reach exactly
  the six existing inherited sorry carriers. The global source frontier
  remains 15, with no new custom axiom or native decision.
- **Removal condition:** upstream lands the corresponding certificate (or a
  stronger generic proof) and reconciliation preserves the readiness
  transaction, exact accepted equations, and trust pins.

## D039 — checked Char.ofNat boundary and semantic declaration contract

- **Status:** implemented as the fourteenth bounded UP6 slice; the live safe
  definition path has a direct `Char.ofNat` certificate, leaving
  `String.ofList` as the next finite literal primitive.
- **Owner:** Argument Computer Corporation; review with the `String.ofList`
  slice and any upstream revision of primitive type-boundary checking.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its typed
  `Char.ofNat` branch and semantic `HasPrimitives` field; no whole-PR merge or
  admitted generic dispatch was imported.
- **Executable delta:** the upstream branch calls inference-only
  `ensureType q(Char)`. Lean4Ix instead composes `checkType q(Char)` with
  `ensureSort`, so successful safe checking establishes the source `Char`
  declaration's safety and typing before comparing `Nat → Char`. This agrees
  on valid safe preludes and intentionally rejects a malformed prelude whose
  `Char` declaration is unsafe or otherwise not checkable.
- **Verification delta:** `checkTypeEnsuresType.WF` derives strict translation
  and canonical type evidence without assuming `Char` was already verified;
  `checkPrimitiveDef.charOfNat.WF_typed`,
  `checkSafeCharOfNatDefinition.WF`, `addCharOfNat`, and
  `addDefinition.WF_safe_charOfNat` carry that evidence through every
  readiness safety model and the live dispatch.
- **Contract repair:** the retained local `HasPrimitives.charOfNat` field used
  to require syntactic equality of the stored type with `Nat → Char`, while
  the executable checker accepts definitional equality. That implication is
  false in general. The field now records zero universe parameters and
  canonical typing in every context, matching the upstream semantic repair;
  every environment transport was updated monotonically.
- **Trust decision:** no equation from definitional equality to syntax was
  introduced. The slice adds no custom axiom, `native_decide` proof, or source
  `sorry`; its direct root reaches exactly the same six inherited sorry
  carriers as the other finite primitive roots.
- **Ix impact:** the verified kernel can now install the character conversion
  constant needed by direct string-literal elaboration while retaining an
  explicit safe-prelude boundary.
- **Tests:** `Lean4Lean.Tests.Primitive` checks all twelve direct live roots,
  including `Char.ofNat`, for dispatch reachability, exclusion of
  `checkPrimitiveDef.WF`, and the exact inherited sorry closure. The global
  source frontier remains 15.
- **Removal condition:** upstream adopts an equivalent checked `Char` boundary
  and semantic declaration contract, or reconciliation preserves this fork's
  stronger malformed-prelude rejection, readiness transaction, and trust
  pins.

## D040 — checked String.ofList prelude boundary and semantic contract

- **Status:** implemented as the fifteenth bounded UP6 slice; the live safe
  definition path has a direct `String.ofList` certificate, completing the
  finite literal-primitive pair before the Nat.gcd/bitwise track.
- **Owner:** Argument Computer Corporation; review with the well-founded
  primitive slices and any upstream revision of literal-prelude checking.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally its finite
  `checkStringOfListPrimitive` boundary, typed certificate, and semantic
  `HasPrimitives` repair; no whole-PR merge or admitted generic dispatch was
  imported.
- **Executable delta:** the old inline branch used inference-only type checks
  for part of the prelude. The extracted recognizer now requires `Char`,
  `List`, `List.nil`, `List.cons`, and `String`; pins their universe arities;
  rejects unsafe or partial dependencies on the safe path; and checks the
  canonical types of both unspecialized and `Char`-specialized list
  constructors before comparing the candidate declaration type.
- **Verification delta:** source lookups and guards produce strict Theory
  translations for the five checked constants. Closed-Pi helpers construct
  the exact `List.nil`, `List.cons`, and `List Char → String` target shapes;
  `checkPrimitiveDef.stringOfList.WF_typed`,
  `checkSafeStringOfListDefinition.WF`, `addStringOfList`, and
  `addDefinition.WF_safe_stringOfList` carry their typing evidence through
  every readiness safety model and the live dispatch.
- **Contract repair:** the retained local `HasPrimitives.stringOfList` field
  used to require syntactic equality of the stored declaration type even
  though the executable checker accepts definitional equality. It now records
  zero universe parameters, canonical typing in every context, and the two
  specialized constructor typings. Every environment transport and literal
  translation consumer was updated monotonically.
- **Trust decision:** no definitional-equality-to-syntax principle was added.
  The slice adds no custom axiom, `native_decide` proof, or source `sorry`;
  its direct root reaches exactly the same six inherited sorry carriers as
  the other finite primitive roots.
- **Ix impact:** the verified kernel now installs the complete checked
  character-list boundary used to translate Lean string literals, with the
  dependency safety and arity assumptions explicit in the executable model.
- **Tests:** `Lean4Lean.Tests.Primitive` checks all thirteen direct live roots,
  including `String.ofList`, for dispatch reachability, exclusion of
  `checkPrimitiveDef.WF`, and the exact inherited sorry closure. The global
  source frontier remains 15.
- **Removal condition:** reconciliation with upstream preserves the explicit
  five-constant safety/arity boundary, semantic declaration contract,
  readiness transaction, and trust pins.

## D041 — generic-state Nat.gcd well-founded certificate

- **Status:** implemented as the sixteenth bounded UP6 slice; the live safe
  definition path now has a direct `Nat.gcd` certificate. `Nat.bitwise`, the
  final finite dispatch, and the generic V4 disposition remain open.
- **Owner:** Argument Computer Corporation; review with the remaining
  well-founded primitive work and any upstream revision of PR #32.
- **Source:** manually adapted from lean4lean PR #32 at
  `6cfd43a48d17be85c76414638655c12ef9a7ee23`, principally executable
  certificate commit `2fc4f84` and reflection commit `27304be`; no whole-PR
  merge, generic-dispatch admission, or concrete-state contract was imported.
- **Executable delta:** `checkNatGcdPrimitive` returns a proof-relevant
  `NatGcdFixCertificate`. Fixpoint discovery runs transactionally, closes and
  rechecks the retained call, entry, fuel, Boolean selector, generic step, and
  GCD zero/successor equations, and still enforces the legacy public-equation
  and direct-zero checks. The generic certificate retains the discovered
  `stateFn` and constructs every state through it instead of matching a
  particular pair constructor.
- **Acceptance repair:** PR #32 specializes the recursive state to the
  compiler's current `PSigma` encoding. This fork deliberately accepts any
  definitionally valid packing function exposed by the same checked
  well-founded fixpoint. Both the shipped `PSigma`-based `Nat.gcd` and an
  independently compiled `Prod (Nat × Nat)` implementation pass the checker.
- **Verification delta:** transparent expression-shape evidence and the
  generic checker certificate feed Euclidean zero/successor semantics,
  literal GCD reflection, preservation of the readiness-aware
  `VEnv.HasPrimitives` contract, typed safe checking, and the direct
  `addDefinition.WF_safe_natGcd` transaction for every safety model receiving
  the definition.
- **Trust decision:** auxiliary closure is checked by a structural
  loose-binder traversal whose equality with the proof-side model is proved by
  recursion. Packed `Expr.hasLooseBVars` metadata is not semantic authority.
  The slice adds no custom axiom, `native_decide` proof, or source `sorry`;
  its direct root reaches exactly the same six inherited sorry carriers as
  the previous thirteen roots.
- **Ix impact:** Ix may choose a performance-oriented recursive-state layout
  without changing the verified primitive contract, while the certificate
  still exposes the exact equations needed to transport `Nat.gcd` semantics
  into the specialized kernel and circuit models.
- **Tests:** `Lean4Lean.Tests.NatGcd` pins the semantic and checker axiom
  closures; `Lean4Lean.Tests.NatGcdProdState` pins alternate-state executable
  acceptance; and `Lean4Lean.Tests.Primitive` checks all fourteen direct live
  roots for dispatch reachability, exclusion of `checkPrimitiveDef.WF`, and
  the exact inherited sorry closure. The global source frontier remains 15.
- **Removal condition:** upstream adopts a proof-relevant certificate generic
  in the discovered state packer, structural rather than cache-authoritative
  closure checks, and an equivalent direct safe-definition transaction; or
  reconciliation explicitly retains this Ix acceptance boundary.

## Review checklist

At each publish or ix pin boundary:

1. Refresh both baseline hashes and
   `git log upstream/master..jcb/formalization2`; do not use a detached `HEAD` as the
   published-fork baseline.
2. Add an entry before landing any new semantic/API delta.
3. Record the upstream issue or PR as soon as one exists.
4. Run the tests named by every touched entry.
5. Delete an entry only when its removal condition is demonstrably satisfied.
