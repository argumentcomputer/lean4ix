# Lean4Lean upstream divergence ledger

This file tracks every deliberate semantic, API, build, or verification delta
from `upstream/master` that must either be upstreamed or explicitly retained.
It is the tracked counterpart to `plans/roadmap.md`.

Audit baseline after the `IndexedVec` semantic checkpoint (2026-08-02):

- upstream: `0c38ab8`
- published semantic checkpoint:
  `cf3d5a47d35867e0e6ebe023c0803982e3e36cd1` (33 commits ahead of upstream)
- first published documentation child:
  `d35a2f6c94212faae20d5a03341b138bb0e22d36`
  (`docs: record IndexedVec semantic checkpoint`; 34 commits ahead of
  upstream). Local Git and `origin/jcb/induct` agreed there at audit time. It
  changes only this ledger relative to `cf3d5a47`; the accumulated fork delta
  remains 32 files changed, 38,037 insertions, and 59 deletions.
- fixed fork master: `1fb7d6ef9042c5a80b2de9320c88ac0f3ce404cb`
  on local and `origin/master`
- audited source checkpoint: `cf3d5a47` with concrete `IndexedVec`
  identity witnesses, generation-ready spine runs, the complete
  producer-selected semantic package, certified Theory transaction, and
  checked E1 replay. The exact sorry audit, focused and 124-job full
  Theory/Verify builds, default Nix build, all-system no-build evaluation, and
  current-host flake check pass at that checkpoint. The documentation child
  has the identical source tree. Use the branch ref, not a detached Git `HEAD`,
  for published-fork comparisons.

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
- **Commits:** `c8a9ef8`, with the current Stage-3 wording in `472a6f0`
- **Delta:** token-aware, declaration-attributed allowlist excluding
  `Experimental/`, wired into Nix and CI.
- **Ix impact:** guarantees that upstream proof debt can only shrink at pin
  boundaries; currently records exactly 20 supported-tree sorries.
- **Tests:** `perl .github/scripts/check_sorry_frontier.pl` and the
  `sorry-frontier` flake check.
- **Upstream issue/PR:** TBD.
- **Removal condition:** upstream adopts an equal or stricter shrink-only gate;
  at zero debt, replace the allowlist with an unconditional rejection rule.

## D006 — staged computational inductive semantics

- **Status:** published-fork
- **Commits:** `71f2eae`, `06e904d`, `201c12f`, `efb2a2b`, and the generalized
  single-family integration in `472a6f0`
- **Delta:** replace the three placeholder inductive declarations with real
  `VInductDecl.WF`, computational generation, generated recursor/iota rules,
  and sorry-free preservation for the accepted class. The published
  single-family path supports parameters, indices, index-changing recursion,
  recursive targets below positive Pi telescopes, raw/view normalization,
  mixed raw-syntax-preserving artifacts, and a traced normalized transaction.
  Acceptance is the dependent descriptor from D009. This remains an
  underapproximation: full positivity, small elimination, K, mutual blocks,
  nested inductives, and the complete differential matrix are not implemented.
- **Ix impact:** discharges ix gap A1's three upstream `sorryAx` origins and is
  the semantic basis for constructing `InductiveOracle`; current breadth is
  not yet enough for all ix blocks.
- **Tests:** exact Nat, Bool, List, Prod, Option, Eq, HEq, index-changing
  `IndexedVec`, and recursive-Pi `Acc` recursor/iota fixtures; the structured
  rejection matrix; Theory/Verify build; full flake check; exact axiom guards
  for `VEnv.addInduct_WF` and the normalized preservation roots.
- **Upstream issue/PR:** TBD; submit in the staged PR sequence described in the
  roadmap rather than as one proof mega-diff.
- **Removal condition:** upstream exposes kernel-complete checked inductive
  semantics and preservation with the same fixture coverage, then ix pins it.

## D007 — consumer-facing inductive transaction API

- **Status:** published-fork
- **Commits:** the normalized core in `472a6f0` and the proof-carrying
  non-identity API in `6a77882`
- **Delta:** `VEnv.AddInductSuccess`, `AddInductGenerationTrace`,
  `addInductGeneration`, `GenerationCertificate`, and
  `addInductCertified`, with generated type/constructor/recursor lookups,
  rule membership, freshness, monotonicity, atomic success/failure, and
  `Ordered` preservation. The legacy `VEnv.addInduct` is an exact identity-view
  compatibility wrapper; the certified API erases its proof and computes
  through the same normalized transaction.
- **Ix impact:** lets `InductiveOracle` consume checked block results without
  unfolding `Option` binds or `foldlM`, and gives ix a Theory-only
  non-identity certificate boundary without importing Verify.
- **Tests:** identity and non-identity transaction fixtures, consumer-style
  `IndexedVec`, `Acc`, AliasFormer, and AnnotatedPi transactions, collision and
  atomicity fixtures, Theory/Verify and flake gates, and exact axiom guards for
  the public trace/WF roots.
- **Upstream issue/PR:** TBD; submit after or with the Stage-3 preservation PR.
- **Removal condition:** equivalent stable postconditions are upstream and ix
  no longer imports the fork-only names.

## D008 — Verify inductive-environment alignment

- **Status:** published-fork
- **Commits:** initial alignment in `472a6f0`, extended through `a1d8943`,
  `6a77882`, and `bc37d43`
- **Delta:** replace the empty `AddInduct` relation with a data-bearing trace
  for `inductInfo`, ordered `ctorInfo` insertion, `recInfo`, and the generated
  defeq fold. Fold realization, lookup, freshness, monotonicity,
  map-WF/value-preservation, `Aligned.addInduct`, and the formerly impossible
  `TrEnv'.of_value` inductive case are live. Actual Lean metadata for Nat, Eq,
  index-changing `IndexedVec`, recursive-Pi `Acc`, AliasFormer, and AliasRec is
  replayed through final equality, WF, alignment, and lookup uniqueness.
  AnnotatedPi adds a seventh focused replay whose raw constructor retains
  `outParam Prop` beneath a recursive Pi and whose generated recursor/iota rule
  is pinned. The normalized trace owns the exact generation and its semantic
  certificate instead of restating artifacts.
- **Ix impact:** establishes the implementation-to-Theory environment bridge
  needed to translate checked inductive blocks and eventually construct
  `InductiveOracle`; later I2-I4 replay fixtures plus the I5 pattern package
  are still required before that oracle is constructible.
- **Tests:** `lake build Lean4Lean.Verify.Environment.InductiveFixtures`;
  all actual-metadata replay roots and rule-RHS equalities; the pre-Nat value
  preservation regression; full Theory/Verify and flake gates; compile-time
  axiom guards for generic alignment and every concrete checked replay.
- **Axiom note:** the guarded roots currently inherit `sorryAx` through
  `TrConstVal → TrExprS → TrProj`, plus the standard logical baseline. E1
  declares no new axiom. The concrete fixture additionally reaches the three
  existing persistent-map contracts while proving its `SMap` insertion
  freshness; Track P/T2 must remove or narrowly justify these inherited
  dependencies before release.
- **Upstream issue/PR:** TBD; submit with or immediately after the staged
  inductive-semantics series.
- **Removal condition:** upstream has a non-vacuous inductive alignment with
  concrete replay fixtures, ix uses it, and the guarded closure contains no
  `sorryAx`.

## D009 — shared checked inductive descriptor

- **Status:** published-fork
- **Commit:** introduced and integrated in `472a6f0`
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
  generation layout, ordered constructor pairing, and exact analyzer result.
  Stable constructor/recursor collision rejection and identity compatibility
  remain part of the public proof API.
- **Ix impact:** creates the stable, consumer-neutral analysis object that E2
  can use to assemble `InductiveOracle` without duplicating raw declaration or
  de Bruijn analysis. The semantic certificate gives ix an environment-indexed
  proof boundary without importing Verify, while the transaction certificate
  lets it reuse the exact checked value. Reserved recursive binder telescope
  and target-family fields provide the extension point for Acc-like and mutual
  recursion.
- **Tests:** computed descriptor-shape checks for Nat, Eq, and `IndexedVec`;
  semantic bridge fixtures for `IndexedVec`; negative fixtures for loose data,
  internal/pre-existing name collisions, self-referential parameters, invalid
  levels, malformed results/spines, parameter counts, and universe-count
  mismatches; exact Theory/Verify build; 20-sorry audit; Theory import boundary;
  formatter; all six current-host flake checks; and all-system no-build
  evaluation.
- **Axiom note:** the analyzer and descriptor are computational and declare no
  axiom. Compile-time guards pin every exported structural fact, the three
  `Checked.WF` compatibility roots, transaction success/exact-analysis facts,
  and collision theorems to exactly `propext` and `Quot.sound`, a subset of the
  accepted Theory baseline. `addInduct_WF` retains the accepted
  `propext`/`Classical.choice`/`Quot.sound` closure.
- **Upstream issue/PR:** TBD; include as the architecture-first patch in the I2
  one-family-parity series.
- **Removal condition:** upstream generation, preservation, Verify alignment,
  and downstream consumers share an equivalent checked block result, and ix
  no longer imports the fork-only descriptor API.

## D010 — executable normalization and certified producer boundary

- **Status:** published-fork
- **Commits:** `1fb7d6e`, `9fde4c6`, `b283912`, `a84aa19`, `c2b1c4f`,
  `a1d8943`, `6a77882`, `bc37d43`, `5e5bb76`, `33b99f4`, `a3ff992`,
  `9a865ea`, `a627362`, `6732659`, `c40a471`, `c739d41`, `82f4a54`,
  `d553930`, and `cf3d5a4`
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
- **Ix impact:** prevents ix from receiving an unrelated hand-selected
  normalization or generation witness while keeping checker state out of the
  Theory API. This is the proof boundary needed before executable metadata can
  be treated as certified inductive generation.
- **Latest checkpoint:** the concrete recursive identity witnesses feed
  generation-ready family/`nil`/`cons` spine runs and a complete
  `GenerationCandidatePackage`. `indexedVecSemanticProducedGenerationCandidatePackage`
  projects the certificate selected by the exact outer call; the corresponding
  certified Theory transaction and checked E1 `TrEnv'` replay are complete and
  exactly guarded.
- **Current gap:** combine the generic operational list witnesses with generic
  construction of retained semantic family/constructor runs and the outer
  produced singleton package. Then complete the normalization differential
  matrix and eventually extend the same indexed shape to mutual and nested
  blocks.
- **Tests:** exact positive AliasFormer, AnnotatedPi, and `IndexedVec`
  whole-call equations; positive semantic/transaction/replay fixtures for the
  first two plus the complete checkpoint semantic/transaction/E1 replay for
  `IndexedVec`; exact `IndexedVec` family/`nil`/`cons` candidate traces;
  opaque-`outParam` whole-candidate rejection; exact axiom guards for the two
  public semantic roots and the three operational list theorems; singleton and
  two-constructor list regressions; focused and full 124-job Lake builds;
  20-sorry audit;
  default Nix build; all-system no-build evaluation; current-host flake check;
  formatter check; and diff/import-boundary gates.
- **Axiom note:** no normalization oracle, native evaluator, or new axiom was
  added. The three operational list theorems are guarded at exactly the
  accepted `propext`/`Classical.choice`/`Quot.sound` baseline. Concrete Verify
  producer roots expose existing checker-refinement, pointer/cache, and
  projection dependencies; generic Theory transaction roots retain their
  narrower guarded closure.
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

## Review checklist

At each publish or ix pin boundary:

1. Refresh both baseline hashes and
   `git log upstream/master..jcb/induct`; do not use a detached `HEAD` as the
   published-fork baseline.
2. Add an entry before landing any new semantic/API delta.
3. Record the upstream issue or PR as soon as one exists.
4. Run the tests named by every touched entry.
5. Delete an entry only when its removal condition is demonstrably satisfied.
