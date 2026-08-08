# Lean4Lean upstream divergence ledger

This file tracks every deliberate semantic, API, build, or verification delta
from `upstream/master` that must either be upstreamed or explicitly retained.
It is the tracked counterpart to `plans/roadmap.md`.

Audit baseline after the complete L4L-08C mutual generation/preservation/replay
checkpoint (2026-08-07):

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
  Publication to the fork's `jcb/induct` branch is pending.
- local-committed post-family constructor semantic checkpoint:
  `37d2dd998e626e25cda8874d9f6a32f85288bb91`
  (`proof: establish post-family constructor semantics`; 5 files changed,
  3,963 insertions, and 1 deletion). Publication to the fork's `jcb/induct`
  branch is pending.
- local-committed pre-family constructor safety checkpoint:
  `9e40cbe00e9c6fe808ebb0720c912bba21aa1b06`
  (`proof: establish pre-family constructor safety`; 5 files changed,
  3,482 insertions, and 1 deletion; 67 commits ahead of the reconciled
  upstream). Publication to the fork's `jcb/induct` branch is pending.
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
  `jcb/induct` branch is pending.
- remote development checkpoints for L4L-03 at `jcb/formalization`:
  `3e6efcce` (`proof: widen D3 constructor replay`), `53d5f923`
  (`fix: emit recursors over checked parameters`), `bb883178`
  (`test: cover definitionally equal constructor parameters`), and
  `04a1a4f29de4` (`proof: certify definitionally equal parameter replay`).
  Publication to the fork's `jcb/induct` branch is pending.
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
  Publication to the fork's `jcb/induct` branch is pending.
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
- fixed fork master: `1fb7d6ef9042c5a80b2de9320c88ac0f3ce404cb`
  on local and `origin/master`
- current audited semantic checkpoint: the L4L-08C closure extends the
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

- **Status:** remote-development (the earlier checkpoints are published-fork;
  the elimination/K/edge, complete L4L-07 singleton-parity, and L4L-08C
  mutual-generation extensions are pushed at `jcb/formalization`, while
  publication to `jcb/induct` remains pending)
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
  through the implementation environment. This remains an underapproximation
  of the full kernel: nested inductives and the later
  generated-pattern/projection corpus are not implemented.
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

- **Status:** remote-development (the one-family base is published-fork; the
  L4L-08C block transaction is pushed at `jcb/formalization`)
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
  `addInductGeneration`/`addInductCertified` APIs remain unchanged.
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

- **Status:** remote-development (the earlier checkpoints are published-fork;
  complete L4L-07 actual-metadata execution alignment and L4L-08C mutual
  replay are pushed at `jcb/formalization`)
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
  installing the globally flattened rules.
- **Ix impact:** establishes the implementation-to-Theory environment bridge
  needed to translate checked inductive blocks and eventually construct
  `InductiveOracle`; non-nested mutual replay is now closed, while nested and
  generated-pattern/projection work is still required before that oracle is
  constructible for the full kernel surface.
- **Tests:** `lake build Lean4Lean.Verify.Environment.SingletonParityReplay`;
  executable 14/5/19 inventory equalities; every actual-metadata transaction,
  final alignment, and derived output ordering; exact Fin/Vector dependency
  maps; the pre-Nat value-preservation regression; full Theory/Verify, default
  Lake, Nix, and flake gates; compile-time trust manifests for the fixed,
  normalization, combined replay, output-ordering, and both mutual-block roots.
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
  L4L-03 is pushed at `jcb/formalization`, while publication to `jcb/induct`
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

## Review checklist

At each publish or ix pin boundary:

1. Refresh both baseline hashes and
   `git log upstream/master..jcb/induct`; do not use a detached `HEAD` as the
   published-fork baseline.
2. Add an entry before landing any new semantic/API delta.
3. Record the upstream issue or PR as soon as one exists.
4. Run the tests named by every touched entry.
5. Delete an entry only when its removal condition is demonstrably satisfied.
