# Lean4Lean completion roadmap

**Status:** authoritative local roadmap, audited and refreshed 2026-08-20
against the committed fork at `06f13e02` (clean working copy), a full
compiled-frontier sorry audit, a fresh digama-upstream scan, and the
2026-08-20 plans garbage collection; publication (moving
`origin/jcb/formalization2`) is a separate boundary and currently matches
the local bookmark at `06f13e02`.

**Versioning.** `plans/roadmap.md` is intentionally tracked so the
status-bearing milestone ladder travels with each checkpoint, as are the
design/decision notes the ladder references — the tracked set is exactly
the `.gitignore` negation list: `roadmap.md`,
`l4l-15-structure-eta-design.md`, `l4l-16-sort-inversion-decision.md`,
`l4l-18b-extension-interface-design.md`, `l4l-16-completion-plan.md`,
`l4l-16c-buildp-premortem.md`, `l4l-16d0-slice-map.md`,
`l4l-16e-promotion-map.md`, `l4l-16-weakn-design.md`,
`l4l-16-generic-instance-design.md`, `l4l-18a-prime-scope.md`,
`l4l-16-stratified-observation-design.md`,
`l4l-16-registered-pi-design.md`, `l4l-16-typedview-design.md`, and
`l4l-16-boundary-digama-drift.md`, and
`l4l-16n-failure-report.md`. Every other file under `/plans` remains
ignored. The 2026-08-20 GC deleted the retired notes (adequacy log, port
queue, segfault plan, nix plan — surviving content re-homed here) and
trimmed the rest to live detail; full text lives in git history. The
root-level `upstream-divergence.md` is the tracked per-delta ledger and
complements this roadmap. This document is forward-looking only: completed
milestones are deleted from the ladder when they close, and their full
narratives, hashes, and gate evidence live in this file's git history and
the checkpoint commit messages.

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
| Ladder position | **Lane R halted at L4L-16N/N2 on 2026-08-20** (§5): both authorized termination measures fail on the checked Tree/TreeList block (`L4L16NFailure.treeBranch_primaryMeasure_fails`, `tree_familyOrdinalFallback_false`), activating the recorded "halt and report; no third fallback" rule. N0/N1 are banked; N3–N5 did not run. The L4L-16C′w conditional regime therefore persists: `LRS.PiPathInv` and `LR.MajorLinkRect` remain explicit inputs. **The successor is approved and probe-validated (2026-08-20, same day): L4L-16N′** — normalization by mutual-inductive membership candidates, whose rung-0 evidence `plans/probes/probeZ16-indcand.lean` proves the exact killed `Tree.branch` transition by membership-derivation induction (no measure, no rank) with positivity settled on the kernel-accepted class; Lane R re-opens there, and L4L-16X queues behind N′4. Full halt record: `plans/l4l-16n-failure-report.md`. **L4L-16C′w completed 2026-08-20** (checkpoint `e73d29fd` pre-rebase; full §6 gate + Experimental green), and **L4L-16R completed 2026-08-20** (merge `29d67a7c`). L4L-18B (D020) stands; 16D0/D1 complete and D2 remains conditional |
| Current formalization source | **`jcb/formalization3`** — the former `jcb/formalization2` line was squash-merged into `dev` as PR #4 (`3d1390a`, tree-equal to `06f13e02` modulo repo housekeeping), PR #5 ("chore: Fix warnings", 34 Theory/Verify files + `warn.sorry` frontier annotations + flake churn) landed on top (`4844eda4`), and the branch was deleted on origin (2026-08-18). The five 16C′w-era commits were segment-rebased onto `origin/dev` `4844eda4` on 2026-08-20 (one trivial `result-1` conflict; Lake gates + 22-entry frontier re-verified green on the rebased line); pre-squash history remains recoverable locally |
| Parent lineage | the squash flattened git ancestry: all content through digama `upstream/master` `b292275c` (the v4.33 reconciliation `99a7f8ae`) is absorbed in the squash, but the published line no longer carries the merge commits, so the L4L-16R merge will see an old git merge-base — the same situation the post-PR#3 line was in when `99a7f8ae` landed green, so precedent stands. Lean on v4.33.0 final, lean4-nix on `argumentcomputer/lean4-nix` (upstream still pins v4.33.0-rc2 — ledger D018, re-verified 2026-08-20) |
| Fixed `master` baseline | historical baseline `1a16b72d2e35932a82aa501beb29ef2c3d072580`; the tracked local `master` bookmark auto-advanced to `origin/master` `715bfaff` at the 2026-08-20 fetch (content already absorbed in-tree) |
| Remote drift | **reconciled at L4L-16R** (2026-08-20, merge `29d67a7c`): local and merged upstream tip = `e0e3f6bc`; nothing unabsorbed. Standing watch items, re-checked at every checkpoint boundary (§7): **PR #43** (third-party iota-reduction formalization — 16 of 20 files collide with fork-modified files; unreviewed by Mario; the fork's appDF×`.extra` refutation applies to its CR `.pat` TODO and the design comparison lives in the drift note + ledger D022 context), **PR #32** (+24k-line HasPrimitives verification overlapping D017 Tier-V debt — the V4 absorb-don't-duplicate tripwire), **#27** (would prove two of the three forbidden cached-field axioms — absorb at the next reconcile). History: `plans/l4l-16-boundary-digama-drift.md` |
| Trust frontier | exactly 16 sorried proof declarations, one token each (10 Tier V, 6 Tier R; the `NormalEq.parRed` `constDF` half closed 2026-08-15, its remaining token is the `appDF`×`.extra` case) plus six kernel-rejection recovery declarations — 22 compiled allowlist entries — and 34 custom-axiom declarations; all pinned by exact audits. `Experimental/` carries **zero** sorry tokens and zero `stop`-hidden admissions since the 16C′w wrap (2026-08-20): the former three tokens closed by conditionalization on the named leaf inputs (`LRS.PiPathInv`, `LR.MajorLinkRect`) and by the E3 chain deletion, and the token-carrying scratch prototypes were deleted (jj-recoverable). Every mainline sorry has a named closure route in §5.0 |
| Gates | the L4L-16N halt checkpoint re-ran every §6 gate on 2026-08-20: Theory/Verify (165 jobs), 22-entry frontier OK (160 jobs), default build (213 jobs), Experimental including the failure record (134 jobs), `nix build` both targets, `nix flake check` all-passed, `nix fmt --check`, and whitespace/import-boundary checks. Earlier full evidence remains at the pre-rebase `e73d29fd` checkpoint and the rebased `jcb/formalization3` line |

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
automatically only when a future replacement for the halted
L4L-16N′/L4L-16X route lands. The block-local assembler
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
were intended to arrive with the L4L-16N′/L4L-16X co-deliverables) is
gated on their future replacement, while
the D-ladder builds the SExpr-side instances that `sort_invS` consumes. Pattern coverage,
checks, and registry membership never imply an operational rewrite without
the local equality certificate. The nested fixtures prove the current
single-target, indexed, and queued deep two-parameter boundaries; nesting
classes beyond the accepted flattened-block analyzer remain rejected. The
296-declaration notation replay is a real fresh prelude prefix, not a claim
that an arbitrary whole kernel environment replays. Bare producer success is
never generation-shape authority or Theory semantics.

### 2.2 Live debt

The sorry audit (`Lean4Lean/Audit/SorryFrontier.lean`, a declaration-level
`sorryAx` allowlist over the compiled Theory/Verify surface) accepts exactly
16 sorried proof declarations — one source token each, verified 2026-08-20 —
plus six deliberately kernel-rejected fixture recoveries that are not proof
debt. The compiled allowlist therefore contains 22 declarations. Every row
below has a named closure route and milestone in §5.0.

| Area | Live debt |
|---|---|
| Core metatheory (Tier R, 6) | `Injectivity.lean`: `IsDefEqU.sort_inv` (:12), `IsDefEqU.forallE_inv_stratified` (:21), `IsDefEqU.sort_forallE_inv` (:34); `UniqueTyping.lean`: `IsDefEqU.weakN_iff` (:174, forward direction; gates `church_rosser` only); `ChurchRosser.lean`: `NormalEq.parRed` (:1893, the `appDF`×`.extra` case; `constDF` closed 2026-08-15); `Projection.lean`: `VEnv.WF.registeredStructureHeadInversion` (:3520; two constructor fields are false as stated and need a head-classification premise before proof) |
| Checker verification (Tier V, 10) | `Verify/Environment.lean` x2 (`addDecl.WF` — only its `inductDecl` case — and `addQuot.WF`, whose upstream v4.33 proof was vacuous); `Boundaries.lean` x1 (`checkPrimitiveDef.WF`); `Extension.lean` x5 (the D017 readiness transports at :274/:355/:439/:522/:587 — verified to share one `ProjectionReady ∧ StructureEtaReady` transport argument across declaration kinds); `Verify/TypeChecker/WHNF.lean` x1 (`reduceRecursor.WF`); `InductiveFixtures.lean` x1 (`aliasFormerAlignmentRun` — pure v4.33 elaborator-shape repair, statement true) |

All Tier V entries are lane/L4L-19 territory; the eight added at the v4.33
reconciliation are classified in ledger row D017. `Experimental/` has
carried zero sorry tokens and zero `stop`-hidden admissions since the
16C′w wrap (2026-08-20): the gate-path admissions closed by
conditionalization on the named leaf inputs (`LRS.PiPathInv`,
`LR.MajorLinkRect`), the off-path `weakU_inv` chain and the
token-carrying scratch prototypes were deleted (all jj-recoverable; the
W4 `Pattern.Action` content re-enters at 18S). Standing mitigation from
the old `stop`-blindspot record: the frontier audit's `surfacePrefixes`
must be extended before any Experimental module is promoted (owned by
L4L-16E), so hidden admissions can never enter the audited surface
unseen.

Non-sorry debt:

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
  development's transitional unique-typing closure until a replacement for
  the L4L-16N′/L4L-16X route lands.
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
  in-tree `Experimental/` `SExpr`/`ShapeLogRel` development
  (`ShapeLogRel.lean` is live-sorry-free; the admission surface is the
  three tokens listed above). The route decisions live in
  `plans/l4l-16-sort-inversion-decision.md`, and the closure program is
  §5's L4L-16C′w conditional regime plus the halted 16N record; 16X is
  blocked pending a new route. Nothing there merges as a completed
  proof, and no experimental assumption substitutes for a supported
  root's accepted closure. `Experimental/UniqueTyping.lean` remains a
  strong-judgment compatibility endpoint only.
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
naming scheme. A suffixed identifier such as L4L-16C′w is a full checkpoint
with its own commit and gates. A milestone completes only when its entire
deliverable and every applicable §6 gate pass on one committed checkpoint;
completed milestones are then removed from this ladder, with their record
kept in git history. Earlier partial implementation counts as a
prerequisite, never as partial credit. Read-only design reconnaissance for
a later milestone is allowed when it changes the active design.

Concurrency rule (revised 2026-08-20, superseding the strict
one-active-milestone rule): after the L4L-16R checkpoint, up to three named
lanes may run simultaneously. Lane R is now closed by the L4L-16N halt;
Lane V (checker pre-closure) and Lane D (D-ladder volume) remain live, with
L4L-16E promotion mechanics in
whichever lane has slack — because their file surfaces are disjoint and
each lane is serial within itself. Every landing remains one audited
checkpoint passing its applicable gates; no lane touches another lane's
files, and a cross-lane interface change forces a joint checkpoint. Outside
the lane phase exactly one milestone is active. If upstream advances at a
milestone boundary, insert an explicit integration-only reconciliation
checkpoint (L4L-15R and L4L-16R are the precedents) rather than hiding
merge work inside a semantic milestone.

### 5.0 Sorry-closure route map

The refined ladder's claim: **every remaining sorry has a named closure
route.** Confidence classes: *certain* (mechanical repair), *engineering*
(no design risk, only volume), *engineering-after-inputs* (mechanical once
a named input lands), *research* (open content, with named kill criteria
and fallbacks in the owning milestone entry).

| # | Sorried declaration | Closes at | Route | Class |
|---|---|---|---|---|
| R1 | `IsDefEqU.sort_inv` (`Injectivity.lean:12`) | L4L-16X (instances, after 16N′-N′4), L4L-16F (public form) | `sort_invS` fires once 16N′-N′4 discharges `LRS.PiPathInv` and `LR.MajorLinkRect`; the conditional wiring (`d0SortInvS` … `d2SortInvSExact`) remains in place from 16C′w; rung-0 evidence for the discharging route is probe Z16 | engineering after 16N′ |
| R2 | `IsDefEqU.forallE_inv_stratified` (`Injectivity.lean:21`) | L4L-16X (after 16N′-N′4) | literally the open leaf — `piPathInv_iff_parRedSDefeq` identifies it with `LRS.PiPathInv`; the halted measure route is recorded in `l4l-16n-failure-report.md`, the successor route in the L4L-16N′ entry | engineering after 16N′ |
| R3 | `IsDefEqU.sort_forallE_inv` (`Injectivity.lean:34`) | after R2's replacement input | the SExpr disjointness block is already proved sorry-free (`ShapeLogRel.lean:14996-15501`, 48 results); reflection remains mechanical once the open leaf is supplied | engineering after research input |
| R4 | `IsDefEqU.weakN_iff` (`UniqueTyping.lean:174`, forward) | L4L-18S | SST route per `plans/l4l-16-weakn-design.md`: W0–W3 proved (probeE2, corrected dependency direction); W4 is the `Pattern.Action`-at-`:↑` repackaging decision; residual risk concentrated in W5+W6 (coupled `NormalEq`/per-depth-CR cores) | research, contained |
| R5 | `NormalEq.parRed` appDF×`.extra` (`ChurchRosser.lean:1893`) | L4L-18A′ | new `Params` field `PatArgProp` — "a registered contraction with a Prop-typed argument position has a Prop-typed result" (`probeCR2-extra.lean:208` closed the math; `normalEq_parRed_appDF_propArg` :219); every live instance satisfies it vacuously, and its falsity for `Acc.rec`/`Eq.rec`-class large elimination is the true boundary of this CR presentation (see 16N stretch tiers), not a route defect | engineering |
| R6 | `VEnv.WF.registeredStructureHeadInversion` (`Projection.lean:3520`) | L4L-18S | statement repair first — the `constructor_name_inv`/`constructor_inv` fields are false as stated (axiom-headed-major / defn-alias counterexamples) and take a head-classification premise; then `weak'_inv` from R4, `unique` from `TrProj.result_eq` + uniqueness, constructor fields from a future replacement for 16N's intended `IndTyAppInj` corollary | engineering after inputs |
| V1 | `Extension.lean` x5 readiness transports (:274/:355/:439/:522/:587) | Lane V | verified to share one argument: a `ProjectionReady.add`/`StructureEtaReady.add` lemma pair (stability of old lookups under fresh non-`inductInfo`/`ctorInfo` `Environment.add`; `VEnv.LE`-monotonicity of `ProjectionArtifact` and the `structEtas` registry) in a new `Verify/Environment/Readiness.lean`, then five one-line applications — kept separate so a PR #32 merge re-applies trivially | engineering, 1–2 sessions |
| V2 | `addQuot.WF` (`Verify/Environment.lean:126`) | Lane V | constructive link replacing upstream's vacuous proof: `checkEqType` postcondition → `VEnv.addQuot` + `Theory/Typing/QuotLemmas.lean` `addQuot_WF` + the `addQuot_objs` lookup suite through a `TrEnv'` quot step, plus the V1 transport for the result | engineering, 1–2 sessions |
| V3 | `addDecl.WF` `inductDecl` case (`Verify/Environment.lean:222`) | L4L-19B | the generic front-end of what all 25 replay rows do concretely: checker inductive path → `buildNormalizationCandidate` → `GenerationCertificate`/`addInductCertified` → `TrEnv'.inductBlock`/`inductNested`, mirroring `addMutual.WF`'s structure, plus V1's transport; this is the "no semantic placeholders" criterion's `Verify.Environment.AddInduct` model | engineering, multi-session |
| V4 | `checkPrimitiveDef.WF` (`Boundaries.lean:35`) | Lane V, #32-gated | upstream PR #32 (+24k lines) verifies exactly this recognizer; absorb and adapt if Mario merges it, prove in-fork (M.WF-style run proof producing `PrimitiveResult`) if it stalls past the 18A′ checkpoint | engineering |
| V5 | `reduceRecursor.WF` (`Verify/TypeChecker/WHNF.lean:8`) | L4L-19A | selected rule/match/checks/RHS translation/result typing from certified generated metadata via `pat_wf` (sheds its transitional closure at 16X) and the block-certificate pattern surface; quot branch against the quot lemmas; nested branch needs the σ̂ β-collapse bridge plus `NestedBlockCertificate` pattern facts | engineering, multi-session |
| V6 | `aliasFormerAlignmentRun` (`InductiveFixtures.lean`, the file's one sorry) | Lane V | attempted at L4L-16R (2026-08-20), recipe banked in the declaration comment: `simp only [aliasFormerKernelType]` first re-enables `rw [build.eq_def]`, and `simp only [context_eq] at closed rootCheck` aligns the record-update trace hypotheses; the residual is firing the dependent match — trace-slot metavars type-check at reducible transparency against fuel/name-indexed binder types, so the fixture defs need pre-normalization across goal and hypothesis types (then the same for `ConstructorViewAlignmentTrace.build` and the recursive nil case) | certain, one focused session |

The six remaining allowlist entries are deliberate kernel-rejection fixture
recoveries, not debt; L4L-19C reduces the allowlist to exactly those.

### Metatheory closure (lane phase–L4L-18S)

The former 16C′ experimental admissions are closed as of the 16C′w
checkpoint `e73d29fd` (2026-08-20): `Experimental/` carries zero sorry
tokens, and the gate endpoints are conditional on the two named leaf
inputs `LRS.PiPathInv` and `LR.MajorLinkRect`. L4L-16N halted before
discharging either input; the conditional endpoints remain the supported
state. The remaining sorries are exactly the 16 mainline rows above.

**Lane phase after the L4L-16N halt.** Lane R re-opens at **L4L-16N′**
(below) — the approved third route, whose rung-0 truth-status evidence is
probe Z16. Lane V runs the V1 → V2 rows of §5.0, starts the V3 skeleton
(statement-level decomposition with named holes), holds V4 on the #32
watch, and takes R6's independent statement repair in its first
Theory-touching session. Lane D runs the D-ladder volume: the three
mechanical D2 steps (`D2CaptureSpineCoreStep`, `D2CollapseStep`,
`D2RegisteredTowerStep`) via the generic replay engine
(`SExprTransport.lean`/`SExprGenericReplay.lean`), then D3 (nested rules
as registered equations only; migration recipe in
`plans/l4l-16d0-slice-map.md`) and D4 (registered structure eta from the
L4L-15B registry certificate). `D2TreeCheckedStep` (stuck-inductive-
application injectivity) and D1's quot instance stay conditional; they
are gated on 16N′-N′4 and on 16F-P1 respectively.
L4L-16E promotion mechanics run in
whichever lane has slack.

**L4L-16N — semantic normalization for the classified class (Lane R;
HALTED at N2 on 2026-08-20).** This was the milestone intended to discharge
`LRS.PiPathInv`. Two
machine-checked facts frame it: restriction alone cannot break the
circularity (`piPathInv_iff_parRedSDefeq` is `[Params]`-generic — the β
*contraction* charges the leaf in every environment class, so a third
node with genuine normalization content is required), and unrestricted the
semantic argument is blocked by published mathematics (the appDF×`.extra`
counterexample is the in-tree face of the Abel–Coquand
failure-of-normalization for impredicative proof-irrelevant systems with
large elimination; the Gilbert–Cockx–Sozeau–Tabareau sProp criterion
rejects exactly those patterns). The restriction is what makes the third
node possible.

*Execution result:* N0 and N1 landed as the sorry-free
`SExprClassified.lean` and `SExprReducibility.lean` infrastructure. N2 then
reached its named Tree kill criterion. The production under-Pi iota rule
grows from 123 LHS nodes to 127 RHS nodes under the primary
`(rank, size, depth)` order, and no leading family-rank
assignment can repair it while remaining non-increasing on the reverse
`TreeList -> Tree` edge. Both failures are kernel-checked in
`SExprNormalizationFailure.lean`; the detailed record is
`plans/l4l-16n-failure-report.md`. Per the precommitted rule, the milestone
halts here and does not invent a third fallback. The target and route below
remain historical specification, not a claim of completion.

*Target, precisely:* `LRS.PiPathInv` proved for every
`[Params] [Params.Semantic] [Params.DeltaRank]` instance satisfying a
newly named class `Params.Classified`, together with two corollaries of
the same development: stuck-application injectivity at `.indTy`-classified
heads (`IndTyAppInj` — the `D2TreeCheckedStep` and R6-constructor-field
consumer) and stuck-`Quot` injectivity (the D1 consumer). The class names
the discipline the tree already half-encodes: certified-block iota rules
with non-Prop-sorted ctor/`.indTy` heads at every firing instantiation
(the existing `CtorBundle.hu0` / `WShape.HasType.proofIrrel` law),
zero-arity definition rules with strictly decreasing `Params.DeltaRank`,
`quotDefEq` at nonzero sorts, registered structure eta, and the
`PatArgProp` condition (derivable from the head law — N0 proves it once
for both this milestone and 18A′). Every D-ladder instance (D0–D4)
already inhabits the class by construction; the milestone makes it a named
`Prop`-valued class instead of an implicit inhabitation boundary.

*Route (decided): typed Kripke logical relation / algorithmic-equality
completeness* (Harper–Pfenning; Abel et al.; Adjedj et al. lineage),
adapted to proof irrelevance by singleton interpretation at Prop-sorted
types — legitimate exactly in the classified class, where no data escapes
a proof. Rejected alternates, recorded: confluence on a proof-erased
quotient (erasure is type-directed, and the transport back to typed
component paths re-encounters the leaf — it becomes the chosen route with
extra steps; the Acc counterexample is the instability witness outside
the class); re-indexing the existing `LogRel`/`WShape` (refuted as a
theorem — probeT's `valTyPi2D_iff_bare`/`uniformStratBound_false`/
`transMiddleCertAt_false`). The 18A′ scope doc's rejection of the typed
relation "for the unrestricted interface" converts into the definition of
rung N0. Substrate reuse from the 16.6k-line `ShapeLogRel` + 8.9k `ADQ`
development: the SExpr judgment and `IsDefEqStrong`, the inversion suite
(`app_inv'`/`lam_inv'`/`forallE_inv_path`), WHNF/`WHRedS` determinism and
the mirror-spine layer, the pattern non-overlap suite and `AssembledPat`,
`HasTypeStratifiedS`/`R` + `DeltaRank` as measures, `TypeDefEqPath`
plumbing, the landed shape-disjointness block, the D-ladder instances as
the evaluation harness, and the depth-fixpoint architecture as the
stratified-definition template. The new relation is a new term-level
structure carrying whnf-existence and judgmental certificates —
deliberately unlike the observationally poor `WShape`.

Rungs, probe-first, sessions per the staged-parallel calibration:

| # | Rung | Status | Deliverable | Kill criterion → fallback | Sessions |
|---|---|---|---|---|---|
| N0 | Class consolidation | **banked** | `Params.Classified`: nonzero-sort head law, `DeltaRank`, iota-RHS structural-descent certificate derived from `Pattern.IotaRule`/generation certificates, `PatArgProp`; instantiate at D0–D2 by `decide` | descent certificate not derivable for Tree's recursion-under-Pi → carry fuel from the generation ordinals as an explicit field | 1–2 |
| N1 | Relation definition | **banked** | reducibility candidates over SExpr, Kripke in `Ctx`, indexed by the existing stratification depth; singletons at Prop; proof-carrying whnf steps (the L4L-18B action discipline applied to the relation) | definition demands well-founded recursion neither depth index can found → step-index by reduction fuel (N0 fallback field) | 2–4 |
| N2 | The Tait core: weak-head normalization | **halted; both measures refuted** | every `HasTypeStratifiedS`-typed term inhabits its type's candidate; cases β / δ (`DeltaRank`) / iota (N0 descent + determinism) / structEta (type-directed) / proofIrrel (singleton + landed disjointness) | the Tree iota case defeats the (rank, size, depth) lexicographic order → re-derive the measure from the block-wide target-family ordinals; if that also fails, the milestone halts and reports — no third fallback | 4–8, case-groups across 2–3 sub-lanes |
| N3 | Fundamental theorem for defeq | **not run** | `IsDefEqStrong` at sorts ⇒ related as types (matching whnf heads, related components); PER laws; `.extra` via N1's expansion closure | `trans` needs candidate-uniqueness at an unsupplied index (the probeS/probeT failure shape recurring) → localize to the Pi-observation fragment (all N4 consumes) | 3–6 |
| N4 | Escape | **interface banked; producer not run** | related-Pi ⇒ `TypeDefEqPath` components; `LRS.PiPathInv` = per-edge N3 + PER + escape | escape needs `TypeDefEqPath.collapse` after all → acceptable if a dependency-walker probe confirms no cycle | 1–3 |
| N5 | Consumer discharge | **not run** | supply both leaf inputs — `LRS.PiPathInv` (from N4) and `LR.MajorLinkRect` (from the N2/N3 semantic content at `FixedHeadResult` strength; `lift_ctor_inv`/`CtorFrame.shape_ctor`/`CtorSpineDefEq.cons_inv` pre-banked 2026-08-20) — and fire `iotaWitnessStep_of_piPathInv` at D0–D2; `sort_invS`/`d2SortInvSExact` unconditional; corollaries `IndTyAppInj`, `QuotAppInj` | — | 2–4 |

The estimated route was 13–27 staged sessions, with wall-clock set by N2.
Its recorded worst case is now the actual outcome: the conditional regime
persists, every consumer stays premised on the named inputs, and the failure
record is machine-checked. The N0/N1 artifacts remain useful substrate for a
future, separately approved normalization design; they do not constitute a
proof of N2 or partial discharge of either leaf.

*Stretch tiers beyond the classified class* (the public statements
quantify over arbitrary `VEnv.WF`, which may register Prop-sorted-
constructor iota rules): **P1** — small-elimination Prop recursors:
exclude from `Pat`; registered equations remain derivable by
`proofIrrel` (both sides are proofs), so exclusion is conservative —
engineering after one design session, owned by 16F (it is the already-
floated hu0/Prop-wall resolution, and what D1-quot at `u = 0` waits on).
**P2** — index-determined/K-class large elimination (`Eq.rec`): needs a
proof-irrelevant-constructor observation class and K-style firing;
literature-adjacent but impredicativity is exactly where Abel–Coquand
strikes — a named successor slice whose rung 0 is a truth-status probe.
**P3** — the full anomaly class (`Acc.rec`-style at `Type` motives):
known to break normalization; open research. Pre-approved fallback that
keeps §5.0 honest for R1–R4: if P2/P3 do not land, the public statements
take an explicit environment-class premise (`Params.Classified`-derived) —
a statement repair reflecting known metatheory, exactly parallel to R6's
head-classification premise; every environment the verified checker
itself constructs from currently supported declaration forms produces the
certificate as a transaction invariant. The premise-vs-funding decision
is 16X's named exit decision.

**L4L-16N′ — normalization by inductive candidates (Lane R re-opened;
next).** The approved third route, superseding 16N's refuted measure
architecture. Rung-0 truth-status evidence:
`plans/probes/probeZ16-indcand.lean` (2026-08-20; compiled, zero sorries,
nine pinned closures at `[propext, (Classical.choice,) Quot.sound]`)
machine-validates the replacement **at the exact transition that killed
N2**: mutual-inductive membership candidates for the real D2 spine shapes
close the whole block's iota case by one application of the joint
membership recursor — the grown `Tree.branch` contractum (verbatim the
production `generatedMajor`) is reached because its membership is a
sub-derivation premise, and the reverse `TreeList → Tree` edge that
refuted every Nat rank is an ordinary mutual-recursor case. No term
measure, no family rank.

*Architecture — the one structural change to the landed N1 development:*
the candidate at an inductive type stops degenerating to
`Base` (edge + assumed `KripkeNormalizes`) and becomes
constructor-generated membership: WH-reachability (untyped `WHRedS`
trace, per the permanent `betaFire` boundary — typed data may ride on
clause *arguments*, never on the exposed trace) of a neutral term or a
classified constructor spine whose recursive fields, applied under their
Pi telescopes, are members of the sibling families' candidates.
Positivity is settled by the probe: the domain-candidate-as-**parameter**
form is accepted and suffices for the entire kernel-accepted non-nested
class (a checked block can never put a sibling family in a recursive
field's Pi domain — the rejected sibling-in-domain form is pinned as
evidence and never needed; Girard interleaving does not activate; nested
blocks stay out of scope — D3 registers their rules as equations only).
Write the clauses Kripke-style from the start (the probe's recorded
lift-stability residual; fallback shape: Kripke-ize at the
`Base.normalizes` level). Reuse: `LRS.CtorView` (head observation,
WHRedS-stable both ways), `LRS.CtorSpineDefEq.cons` (the constructor
clause's shape with the candidate in the `IH.DefEq` slot),
`CtorChain.RawAlgebra`/`foldRaw` (the elimination discipline), `Neutral`
+ its whnf/noMatches suite, and the block-side `RecArg`/`blockRuleCall`
data. The seam is unchanged: this milestone owes exactly the three open
producers — the `Fundamental 0` source (was `TypedWHNormalization`),
`HeadFundamental 0`, and `ConstFundamental` — and everything downstream
through `Fundamental.succ` to `LRS.PiPathInv.of_candidateFundamental` is
already proved and pinned. Scope stays per-instance (D0 Nat, D2
Tree/TreeList; D1's definitions need only `DeltaRank`, which the
refutations did not touch — δ-steps strictly decrease rank; D1-quot
stays P1-gated); the generic-block candidate engine joins the generic
`Params` instance at 16F, concrete-then-generic as always.

| # | Rung | Deliverable | Kill criterion → fallback | Sessions |
|---|---|---|---|---|
| N′0 | Candidate architecture | transplant probe Z16 into `SExprReducibility`-adjacent modules: mutual-inductive candidates for D0/D2 with Kripke-style clauses, expansion closure over untyped `WHRed`, neutral clause, nonvacuity witnesses (incl. a non-normal and a higher-order-field member) | the Kripke reshaping breaks the clause shape → Kripke-ize at `Base.normalizes` instead (both shapes named in the probe) | 1–2 |
| N′1 | Real-rule inhabitation + membership normalization | the five `WHRed.extra` steps from the `Pattern.IotaReductionSite` assembly (overlaps Lane D's three mechanical D2 steps; the `Pattern.Check` discharge remains 18A′-gated — D0's `d0IotaSite_nonempty` is the landed analogue); stuck cases via the `WHNF.subpattern`/pattern-uniqueness suite; membership ⇒ `KripkeNormalizes` at inductive types (`Base.normalizes` becomes a theorem) | the check discharge blocks the Tree rules → condition on `D2TreeCheckedStep` exactly as the D2 rows already do; no regime change | 2–4 |
| N′2 | `ConstFundamental` + `HeadFundamental 0` | constants via `DeltaRank` descent (δ only); head observations at sorts/Pi from the landed `HeadLayer` machinery + membership | a head observation needs adequacy-strength input → isolate as a named Prop with nonvacuity witness; the conditional regime absorbs it | 1–3 |
| N′3 | The fundamental theorem | rewrite the `∀ depth` proof suite (~450 lines; case content unchanged) to membership induction; complete the missing `SubstFundamental` cases — `lamDF`, `beta` (the landed `Env` substitution machinery), `.extra` (`PatternArgumentNonProp` + action soundness), `proofIrrel` (singletons + the landed disjointness block), `defeqDF`, structure eta — on top of the landed `symm`/`trans`/`bvar`/`sort`/`appDF`/`forallEDF` | a case demands a new semantic input → isolate as a named Prop; conditional regime absorbs it | 4–8, case-groups parallel |
| N′4 | Assembly + consumer discharge | index-free `Fundamental` → `LRS.PiPathInv.of_candidateFundamental` fires verbatim modulo the index; discharge both leaf inputs at D0–D2 — `LR.MajorLinkRect` from membership + the pre-banked rectangle helpers (`lift_ctor_inv`/`CtorFrame.shape_ctor`/`CtorSpineDefEq.cons_inv`) — `sort_invS`/`d2SortInvSExact` unconditional; corollaries `IndTyAppInj`, `QuotAppInj` | `MajorLinkRect` needs more than membership + rectangles → it remains exactly the named input it is today; no worse than the current state | 2–4 |

Total 10–21 staged sessions; wall-clock set by N′3. The honest risk
concentration: N′3's `proofIrrel`/`.extra` cases and N′4's
`MajorLinkRect` discharge — each with a named isolate-don't-force
fallback that leaves the conditional regime intact. The stretch tiers
(P1–P3) and their pre-approved statement-premise fallback carry over from
16N unchanged.
*Exit:* both named leaf inputs discharged at the D-ladder instances; the
16C′w conditional endpoints fire unconditionally; the escape's measured
closure stays `[propext, Classical.choice, Quot.sound]`; L4L-16X
unblocks.

**L4L-16E — promotion mechanics (slack lane).** Execute
`plans/l4l-16e-promotion-map.md`: module moves out of `Experimental/`
with stable APIs, the `SorryFrontier` import-block regeneration — and the
`surfacePrefixes` extension so `stop`-hidden admissions can never enter
the audited surface unseen (§2.2 blindspot mitigation) — the
`UniqueTyping.lean` filename collision, and the exact `#print axioms`
pins (the `AxiomProbe` inventory is the ready template). Probes retire in
favour of in-source `#guard_msgs` pins as their modules promote (the
scheduled disposition for `plans/probes/`). Promotion is legal once
Experimental is sorry-free (post-16C′w) even while endpoints are
conditional; supported roots still never import experiments — promotion
is the move that makes them non-experiments.

**L4L-16X — unconditional closure and the P-tier exit decision (queued
behind L4L-16N′-N′4).** Its original predecessor halted; the approved
successor L4L-16N′ supplies both named leaf inputs at N′4. Until then
instance-level closure remains conditional, R1–R3 remain open, and the
audit allowlist does not shrink. On N′4: take the P-tier decision
(environment-class premise vs funding P2) and record it here.
*Deferred exit:* the Injectivity trio's instance forms are sorry-free with exact
accepted closures; no `sorryAx`, no `extra_pat`-style axiom, no
environment oracle on any path; residual public-form debt is exactly the
recorded premise decision.

**L4L-16F — generic instance and the public statements.** Per
`plans/l4l-16-generic-instance-design.md`: the generic
`VEnv.WF → Params`/`Params.Semantic` construction (the D-ladder's
transport pattern is the induction step), carrying the P1 design
(Prop-recursor exclusion with `proofIrrel`-derived registered equations;
`CtorBundle.hu0` stays — its deletion is refuted by probeA1) and the
probeK δ-cycle constraint (`VEnv.WF` admits δ-cycles: exclude cyclic
definitions from `Pat` or carry acyclicity as a hypothesis — decide at
design). Closes R1's public form at the achievable class.

**L4L-18A′ — Church–Rosser completion.** Land `PatArgProp` as a `Params`
field with the probeCR2 proof ported and discharge it at the instances by
`decide` (resolving the scope doc's fired §7.1 tripwire: the field is the
estimate reshape), closing `NormalEq.parRed`'s last token (R5) with the
roadmap's four enumerated support lemmas (`NormalEq` match
inversion/spine descent; `Check.OK` transport along `≡ₚ` and
`≈`-equivalent level lists; level-congruence for `RHS.apply` on closed
templates via the landed `EqUpToLevels.instL_equiv`; routine typing side
conditions), `ParRed.triangle`'s `.extra` case as template. Then the
Theory-side live `Params`/`Params.Extension.join` instance consumed by
`IsDefEq.church_rosser`, its four inversion-strength fields fed by the
future replacement for the halted 16N/16X outputs. The rung ladder and reify-transport implementation
guidance live in `plans/l4l-18a-prime-scope.md` (§8.1/8.2 deleted — the
ladder is a consumer of the leaf, not a route to it).
*Exit:* `ParRed.church_rosser`, normal-form uniqueness, and the live
standardization/head-reduction endpoints contain no hidden placeholder
assumptions; allowlist → 18.

**L4L-18S — stratified standardization slice.** R4 + repaired R6 as one
coupled slice, per both design passes' recommendation. The SST module
plan (`Theory/Typing/Strengthening.lean` between `Strong.lean` and a
slimmed `UniqueTyping.lean`), the W4 option-(a) `Pattern.Action`
repackaging decision (shared with E3 if still open), the W5+W6 coupled
cores as the risk concentration, then `weakN_iff` forward and the
repaired `registeredStructureHeadInversion` (its non-constructor fields
from R4 + `TrProj.result_eq`; constructor fields from `IndTyAppInj`).
First action available now: the W4 packaging decision plus the
one-session `InferType.weakU_inv` de-circularization.
*Exit:* `church_rosser` unconditional; projection consumers shed
`sorryAx` automatically; allowlist → 16, Tier R closed.

### Banked refutations (do not reopen)

Machine-checked negative results that shaped the 16-series; each is a
theorem or exact-probe record, not an opinion. Full statements in the
named design docs and probe files.

- **CR-ladder circularity:** `piPathInv_iff_parRedSDefeq` — the ladder
  and the leaf are interderivable; the β *contraction* charges the leaf
  (`BetaFire`), the sort restriction provably does not dodge it, and
  `PiEdgeInv` is a re-presentation of the leaf (`probeR13-loop.lean`;
  premortem residue doc). The CR ladder is a downstream *consumer* that
  fires at N4.
- **Stratification:** voucher-as-data is conservative
  (`valTyPi2D_iff_bare`); the uniform bound is false
  (`uniformStratBound_false`, unbounded-minimal-depth β-redex tower);
  `ChainAnchorAt` is false at every depth; `LogRel` re-indexing inherits
  the wall at `trans` middles (`transMiddleCertAt_false`)
  (`l4l-16-stratified-observation-design.md`, `probeT-stratpi.lean`).
- **Registered narrowing:** `PiPathInvReg` closes the chain-fold interior
  only (`regSpine_result_uniq`); the two root callbacks provably escape
  the registered class, and the class is not closed under one edge (U8)
  (`l4l-16-registered-pi-design.md`, `probeU-regpi.lean`).
- **Typed-view production:** retention dissolves the root callbacks
  (`CtorChainT.foldRaw_of_anchorDiscipline` — the retained consumption
  interface) but production is impossible at every closure law: forward
  `whr` ≡ the subject reduction being dissolved, `unwhr` refuted
  outright, `conv` collapses registered head types
  (`l4l-16-typedview-design.md`, `probeV-typedview.lean`).
- **hu0 deletion:** refuted — `build_spine` is false post-deletion for
  Prop-sorted ctor-classified pattern-argument heads; `hu0` mirrors
  `WShape.HasType.proofIrrel` (`probeA1-hu0.lean`); resolution is the P1
  classification design, not deletion.
- **`TypeWHNFEx` is not needed** for the leaf (sufficient-not-necessary
  decomposition), and 16C″ shape disjointness dissolved as a milestone —
  its four facts landed from `LE_Interp.sound` + rung 0 with a negative
  control (`sortInv_bit_only`).
- **appDF×`.extra` under bare `[Params]` is false** — Lean's own
  large-eliminating Prop inductives realize the counterexample; the
  repair is the `PatArgProp` field (`probeCR2-extra.lean`), and the
  unrestricted statement's failure is the P2/P3 boundary.
- **`FixedHeadTerminalRetarget`/`FixedHeadTerminalLink`** false as
  originally stated (premortem residue doc); the repaired dominance
  interface is landed.
- **Syntactic termination measures for iota (L4L-16N/N2):** the
  `(rank, size, depth)` lexicographic order cannot decrease on the
  production `Tree.branch` rule — the RHS grows 123 → 127 nodes and iota
  is not a δ-step (`L4L16NFailure.treeBranch_primaryMeasure_fails`,
  kernel-checked `decide`); and NO `Nat → Nat` family rank exists for the
  mutual block — the `Tree ⇄ TreeList` edges force contradictory
  inequalities, and the `TreeList → TreeList` self-edge kills strict
  ranking outright (`tree_familyOrdinalFallback_false`,
  `tree_strictFamilyRanking_false`). These refute Nat-stratification, not
  normalization; the least-fixed-point membership replacement is
  probe-validated (Z16). Do not re-rank.
- **Typed normalization traces (the `betaFire` boundary):** any
  normalization interface whose trace links carry a displayed-type
  equality already proves `LRS.BetaFire` — circular with the leaf
  (`SubjectPreservingWHNormalization.betaFire`). Permanent constraint:
  the exposed trace of any normalization result must be untyped
  (`WHRedS`-valued); typed data may ride only on clause arguments.
- **Sibling-family-in-domain candidate clauses:** rejected by the kernel's
  positivity checker (pinned in probe Z16) — and never needed: checked
  non-nested blocks cannot put a sibling family in a recursive field's Pi
  domain, so the domain-candidate-as-parameter form covers the class.
- **Literal `RectFrame` at the rec-app observation:** refuted 2026-08-20
  (`RectFrame.tyShape_rigid` + the `RecAppMoving` witness — the rec-app
  observation moves its type shape along `mono`, which the frame's rigid
  type observation forbids). The honest transport is the landed widening
  `RecAppFrame`/`RecAppSync` (probe W16, banked in `ShapeLogRel.lean`);
  do not attempt to widen `RectFrame.mono` in place.
- **The dominance ∀-`outTyP` producer hypothesis (pre-repair form):**
  machine-proved undischargeable — every inhabitant forced
  `out.T ≤ bot` while every call site assumed the negation (probe X16,
  `producerHyp_forces_bot`/`producerHyp_unusable`); repaired 2026-08-20
  with an `out.HasType outTyP` premise. Level adequacy
  (`capturePaths.length ≤ head.1`) is a necessary premise of any
  producer (`forces_headLevel`), not bookkeeping.

### Checker closure (L4L-19A–L4L-19C)

Lane V pre-closes V1/V2 (and V4 unless PR #32 lands it first) during the
lane phase; L4L-19 proper picks up the remainder on the reconciled
checker text.

**L4L-19A — recursor reduction verification.** V5: prove
`reduceRecursor.WF` for Quot and certified inductive rules, obtaining the
selected rule, match, checks, RHS translation, and result typing from the
generated/translated metadata — not from a global oracle. For nested
blocks this requires the σ̂ β-collapse bridge left open in
`NestedTransport` — transporting the flattened block's rule defeqs and
pattern facts onto the restored `appendIndexAfter` artifacts — and
extending the certificate pattern surface accordingly
(`NestedBlockCertificate` currently exposes no `ruleClosure`/`IotaPat`
facts). The σ̂ bridge goes first: it is the only piece with design
content.
*Exit:* Quot, singleton, mutual, and nested recursor reductions pass;
enclosing WHNF roots have exact guards.

**L4L-19B — environment-to-checker closure.** V3 (`addDecl.WF`'s
`inductDecl` case via the §5.0 route) plus whatever Lane V left, and full
`TrEnv` over fixture environments containing ordinary declarations, Quot,
single/mutual/nested inductives, literals, structures, and extension
defeqs; state and audit the final executable-checker soundness theorem
over this full environment class. Re-verify the recorded `--fresh`
whole-core replay failure (`(kernel) type checker does not support loose
bound variables` at `Lean.PersistentHashMap.Node`, observed on v4.29;
CI's `--fresh Init.System.IO` is green, so it is either fixed or
corpus-dependent) and fix or file it.
*Exit:* the complete environment corpus and final checker root build with
exact closures; only the mechanical zero-sorry policy switch remains.

**L4L-19C — zero-sorry gate.** Remove every remaining supported
Theory/Verify sorry. Keep the audit allowlist exact throughout: every
proof PR deletes entries, and no PR may rename/move a sorry and merely
update the allowlist. At zero, reduce the allowlist to the deliberately
kernel-rejected fixture recoveries so any sorried declaration fails
outright.
*Exit:* the proof-debt frontier is zero, only fixture-recovery entries
remain, and full gates pass.

### Trust closure and release (L4L-20A–L4L-20C)

**L4L-20A — axiom reachability and retirement.** Generate the actual
transitive closure for every supported root rather than hand-maintaining
§3. The root set contains at minimum the exported
checked-inductive/transaction/preservation roots and the consumer-facing
checked-inductive/projection API; the unique-typing, Church-Rosser,
standardization, and head-reduction endpoints; and the public checker
operations with the final executable-checker soundness theorem. Each row
records the root, layer, standard axioms, project axioms, §3
classification, pinned Lean revision, and disposition; keep normalized
output under version control or as a deterministic CI artifact so a
dependency change produces a reviewable diff, generalizing the existing
local `#guard_msgs` mechanism.

Acceptance states: (1) logical baseline; (2) platform contract — narrowly
stated, manifested, version-pinned, tested, absent from Theory roots;
(3) transitional bridge — named, classified, with a removal issue, never
a silent release assumption; (4) forbidden — known false on a supported
toolchain or unproved after the implementation changed.

Pre-work already scoped: delete the three dead axioms
(`Level.mkLevelIMaxCore_eq`, `Expr.liftLooseBVars_eq`, `Expr.equal_eq`)
after a reachability re-run on the current tree; upstream PR #27, if
merged, turns `Level.hasParam_eq`/`hasMVar_eq` — two of the three
forbidden cached-field axioms — into theorems (absorb at the next
reconciliation rather than proving in-fork), and the unmerged
`origin/ap/prove-treemap-all` branch would do the same for
`TreeMap.all_eq_all_toList`. Then retire in risk order: the remaining
cached-field equation(s); the reference equations (convert to logical
definitions with `@[implemented_by]` only when extensionally correct);
the collection and opaque/layout equations (replace with upstream
theorems or narrowly bounded WF lemmas); then decide the final platform
budget explicitly (expected: the two pointer-equality implications,
possibly lawful level `BEq`). CI must reject a new unclassified project
axiom, any project axiom in a Theory root, any forbidden axiom in a
supported root, a retained platform contract without manifest entry and
tests, and `[simp]` on any project-specific axiom (28 of 32 currently
carry it — §3's containment debt).
*Exit:* the report regenerates from a green build with every dependency
in an accepted state; no project axiom reaches Theory.

**L4L-20B — complete differential corpus.** Automate a harness that
elaborates fixture declarations with Lean, translates the resulting raw
environment metadata, constructs the justified analysis view, and
compares it with Theory generation, across the fixed inductive,
projection, prelude, and extension corpus. Compare failures as data:
accepted/rejected, raw/view normalization stage, generated constants,
universe lists, field counts, recursive positions, K flag, rule count,
and every RHS. Upstream's `differential` branch (C++-kernel parity
harness with DEQ trace instrumentation) is convergent tooling — check it
before building from scratch.
*Exit:* CI compares acceptance phase, metadata, generated constants,
universes, recursive positions, flags, rules, and every RHS; all
supported cases pass.

**L4L-20C — upstream series and release.** Submit dependency-ordered
semantic PRs: (1) level-normalizer proofs and small generic lemmas;
(2) Theory API extraction with compatibility re-exports; (3) the staged
inductive vertical slice and fixtures; (4) indexed/normalization/
small-elimination/recursive-argument support; (5) mutual and nested
support; (6) the pattern package and Verify `AddInduct` alignment —
coordinating with whatever became of PR #43's competing iota design;
(7) the projection structure view, laws, and checker proofs, including
the `reduceProjCore.WF` discharge offered at L4L-16R; (8) injectivity/
Church-Rosser completion; (9) the remaining checker and
axiom-minimization work. Standing separately: the replay teardown-
segfault fix (PR already open; ammunition — backtrace symbol, region/RC
mechanism, v4.29 repro, production evidence — recorded in that PR) and
the Nix flake PR (open). Do not rewrite published `jcb/formalization2`
checkpoints: each PR series is extracted onto a fresh review branch
rebased on its current upstream target. Do not mix the large
Nix/fork-infrastructure delta into proof PRs unless upstream asks. Record
every PR in the divergence ledger.
*Exit:* the final release revision is green; every fork delta is
upstreamed or has an owner, issue, and removal condition; release
artifacts and manifests are reproducible.

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
`Lean4Lean.Experimental` is a separate lib outside every §6/Nix gate and
builds only via `lake build Lean4Lean.Experimental`. A green gate
therefore claims nothing about `Experimental/` — promotion at L4L-16E is
what moves the semantic development into the gated surface. One
correction to the old "a red experiment never blocks anything" phrasing
(audited 2026-08-20): the GitHub workflow runs
`lake build Lean4Lean.Experimental` as its own CI job, so a
non-compiling experiment does fail remote CI even though no checkpoint
gate depends on it — keep experiments compiling or adjust that job
deliberately, never by letting it rot red.

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
wording with each checkpoint. The prepared PR-description artifact for the
published branch is `plans/jcb-formalization2-pr.md` (untracked scratch);
refresh it whenever a publication moves the claim surface.

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
- **Research-core honesty (L4L-16N → L4L-16N′).** The named worst case
  occurred on 2026-08-20 — both N2 measures failed on the checked
  Tree/TreeList block (`SExprNormalizationFailure.lean`;
  `plans/l4l-16n-failure-report.md`) — and the kill discipline held: no
  third fallback was invented inside 16N. The approved successor
  L4L-16N′ replaces ranking with least-fixed-point membership induction
  and enters with rung-0 machine evidence (probe Z16 proves the exact
  killed transition). Its honest risk concentration is N′3's
  `proofIrrel`/`.extra` fundamental cases and N′4's `MajorLinkRect`
  discharge, each with an isolate-don't-force fallback that leaves the
  conditional regime intact — the worst case remains the current state,
  not a regression.
  Separately, the unrestricted public statements sit behind the P2/P3
  large-elimination boundary, where the pre-approved fallback is an
  explicit environment-class premise; treat any temptation to "just
  axiomatize past" that boundary as a §3 violation. Do not re-run the
  banked refutations (§5) — do-not-reopen is a theorem in three of the
  four cases.
- **Unsound bridge axioms.** Some cache equations were documented false on
  older pins and remain unproved. Zero sorries is not a soundness claim until
  final-root axiom reachability is clean.
- **Upstream collision.** Repeat the ancestry and overlap check at every
  milestone boundary; if upstream advances again, insert another explicit
  integration checkpoint rather than hiding merge work inside a semantic
  milestone. The 2026-08-20 drift (five commits) was absorbed the same
  day at L4L-16R (merge `29d67a7c`); two large in-flight PRs remain the
  live exposure. **PR #43 is a competing
  iota-reduction design** touching 16 fork-modified files — if Mario
  merges it, the next reconciliation confronts `VEnv.pats`/`IsDefEq.pat`
  head-on against the fork's L4L-18B proof-carrying interface, and the
  L4L-20C series item (6) must become a coordination, not a submission;
  mitigations are the 16R design-comparison record, communicating the
  appDF×`.extra` refutation upstream early, and keeping D020 minimal and
  ledgered. **PR #32** overlaps Lane V's files; the V4 tripwire and the
  `Readiness.lean` isolation keep a merge cheap. Re-check both PRs at
  every checkpoint boundary during the lane phase.
- **Scope leakage from Experimental.** No supported root may import
  experiments. Promote a proof only after removing its experimental sorries
  and giving it a stable API.
