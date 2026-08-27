<!--
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-->

# Remaining-proof experiment inventory

Snapshot: 2026-08-31. This is the implementer handoff for the experiments,
scratch probes, and side workspaces related to the supported proof frontier.
The machine-checked source of truth for the frontier itself remains
[`Lean4Lean/Audit/SorryFrontier.lean`](../Lean4Lean/Audit/SorryFrontier.lean).
The separate [`digama0 branch audit`](digama0-branch-audit.md) inventories all
upstream remote heads and the isolated portability tests for useful patches.

The audit currently contains 14 known `sorryAx` declarations:

- eight actionable proof obligations: V3, V5, and R1-R6 below; and
- six deliberately rejected inductive fixtures produced by elaborator error
  recovery. The six fixtures are test data, not proof debt.

There are exactly eight source `sorry` tokens in the supported tree, one for
each actionable declaration. `Lean4Lean/Experimental` has no source `sorry`
tokens, although some comparison endpoints deliberately expose inherited
`sorryAx` dependencies in pinned `#print axioms` output.

## How to read this inventory

The status labels below are intentionally strict:

| Label | Meaning |
|---|---|
| **production** | Landed code on the active implementation line; suitable for direct extension. |
| **banked** | A proved lemma or interface with useful mathematical content, but not the final producer. Check its current imports and axiom closure before moving it. |
| **conditional** | A theorem whose conclusion is useful only after named hypotheses are produced. It does not close the target. |
| **refuted** | An attempted statement or route has a counterexample or a machine-checked obstruction. Do not revive it unchanged. |
| **tainted** | A proof script consumes the target `sorry` or another frontier theorem transitively. It establishes assembly shape, not an independent proof. |
| **stale** | Statement-only or tied to an older interface. Use as archaeology only. |
| **feeder** | Uncommitted work that was incorporated into a later consolidated change. Do not integrate it separately. |

## Frontier at a glance

| ID | Audited declaration | Best existing artifact | Honest state | Implementer entry point |
|---|---|---|---|---|
| V3 | `Lean4Lean.addDecl.WF` | Active production chain; G2/G3 leverage probes; one-input closure skeleton; projection metadata probe | One safe `inductDecl` branch remains. Lean 4.33.1 guard retention and shape-total family assembly are landed. The ordinary frontier is A4 plus M3/M4; the nested frontier is N0-N4. | Derive the audit and recursor telescope producers from retained execution, assemble ordinary or nested readiness, and call the landed primitive-split endpoint. |
| V5 | `Lean4Lean.TypeChecker.Inner.reduceRecursor.WF` | `SelectedBranchWF` factorization plus the concrete Rose vertical slice | Operational branching is factored. Main/nil/cons still need `IndTyAppInj`; Quot needs `QuotAppInj`; K/structure/literal/failure semantics remain. | Supply NORM-DI M4-M6 outputs to the existing consumers; do not reopen the dispatcher analysis. |
| R1 | `VEnv.IsDefEqU.sort_inv` | NORM-DI round 2 and conditional adequacy endpoints | Direct route reaches T3 only under six precisely named inputs. | Repair the coherent induction/interface at the first provenance-loss edge, then continue T4-T7/M4-M6. |
| R2 | `VEnv.IsDefEqU.forallE_inv_stratified` | Same NORM-DI line | Same critical path as R1; current `ShapeLogRelAdequacy` endpoints are consumers of `PiPathInv`/`MajorLinkRect`, not producers. | Same as R1. |
| R3 | `VEnv.IsDefEqU.sort_forallE_inv` | Same NORM-DI line | Same critical path as R1. | Same as R1. |
| R4 | `VEnv.IsDefEqU.weakN_iff` | SST probes E/E2 in the local attic | Only the forward direction is missing. W2/W3 scripts are tainted consumers; W4-W8 remain. | Re-found the per-depth `NormalEq`/CR strengthening core, then assemble the already-pinned stages. |
| R5 | `VEnv.NormalEq.parRed` | Landed repaired signature; CR2 and F4 experiments | One `appDF`/`.extra` case remains. `PatternArgumentNonFunction` is not derivable from the current semantic class; structure compatibility also needs a producer. | Add the smallest truthful constructor admissibility certificate and the D4 structure producer, then finish the existing case. |
| R6 | `VEnv.WF.resolvedRegisteredStructureHeadInversion` | Landed repaired record and Verify consumers | The old statement was false. The repaired statement requires a genuine `ConstructorHead`; its proof remains coupled to R4, `IndTyAppInj`, and projection uniqueness. | Finish SST and NORM M5, then combine the landed `TrProj` structural laws with the repaired premise. |

## Jujutsu workspace inventory

These paths are local to the current machine. The stable changes are the
portable references; the feeder working copies are not.

| Workspace | Revision/status | Contents and disposition |
|---|---|---|
| `default` (`/home/jcb/projects/lean4lean`) | Active, heavily modified implementation line | V3 projection/readiness work and V5 production factoring. This is the authoritative implementation tree, not a NORM-DI consolidation. Preserve unrelated working-copy changes. |
| NORM-DI round 1 | change `sptlpvvrmxuo`, commit `e0ec3aec71b3` | **Banked/superseded.** Refutes `NatSuccFramedPredStep`, repairs the successor branch around fieldwise site data, removes zero-service, pins the zero body at rung 11, and classifies F4 as H-ADM. Round 2 contains the retained result. |
| NORM-DI round 2 | change `stozplypylzq`, commit `80677fef7223` | **Canonical experimental handoff.** Pins the exact T3 frontier, corrects the successor budget from 14 to 20, reduces field service to site-riding provenance, and proves the tower cannot be shrunk by reindexing. It is not integrated into `default`. |
| `normdi-1` (`/home/jcb/projects/l4l-normdi-1`) | Clean empty child `znppzlyy` of round 2 | **Use this to inspect/build round 2.** Integrate the parent change `stozplypylzq`, not the empty child. |
| `normdi-2` | Uncommitted `FieldServiceProvenance.lean`, based on round 1 | **Feeder.** Incorporated and refined in round 2. |
| `normdi-3` | Modified `NatCoherentLeaf.lean`; added `NatSuccSiteBudget.lean`, based on round 1 | **Feeder.** Incorporated and refined in round 2. |
| `normdi-4` | Added `FalsifyRound2.lean`, based on round 1 | **Feeder.** Incorporated in round 2. |
| `normdi-5` | Added `EmptyContextCallbacks.lean`, based on round 1 | **Feeder.** Incorporated in round 2. |

The round-2 changes were developed off an earlier common parent and are not
present in the active working tree. Rebase or merge the single stable round-2
change onto a deliberate checkpoint; do not copy the four feeder files one by
one. In this snapshot the focused round-2 build completed successfully:

```text
nix develop --command lake build \
  Lean4Lean.Experimental.FalsifyF4 \
  Lean4Lean.Experimental.FalsifyF5 \
  Lean4Lean.Experimental.FalsifyRound2 \
  Lean4Lean.Experimental.FieldServiceProvenance \
  Lean4Lean.Experimental.EmptyContextCallbacks

Build completed successfully (134 jobs).
```

The round-2 T3 endpoints have pinned closures containing only Lean's accepted
logical/runtime basis and the named `native_decide` fixture certificates—not
`sorryAx`. That does not make their six hypotheses disappear; it proves the
conditional reductions themselves introduce no admission.

Validation status for `default`: the normal repository build of
`Lean4Lean.Verify.Environment.NormalizationElimination` and the full
`Lean4Lean.Verify.Environment` target are green on Lean 4.33.1. The G2, G3,
closure-skeleton, and projection-metadata probes compile against the normal
`.lake/build` tree; no overlay or `/tmp` olean cache is part of these gates.

## NORM-DI round 2: exact result

The canonical endpoint is in
`Lean4Lean/Experimental/FieldServiceProvenance.lean` at round 2:

- `natCoherentTypedIotaLeafStepT3` consumes four inputs;
- `natT3CoherentRetainedResultT3` consumes all six; and
- `natT3ZeroExitT3` and `natT3SuccExitT3` are the two concrete acceptance
  tests for the complete conditional T3 construction.

The complete residual set is exactly:

| Input | What round 2 established | Classification / likely repair |
|---|---|---|
| `legacyStep : LR.CoherentRetainedNatStep []` | Rung 0 is input-free, but the all-depth legacy family pulls in legacy adequacy and Pi inversion. | Tower-or-forbidden. Avoid making the direct construction call back through the legacy all-depth algebra. |
| `defeqStep : ∀ depth, LRD.SelfAdequateDefeqStepAt [] depth` | Rungs 0 and 1 are constructed for every context. Rung 2 admits genuine Pi-shaped displayed types. Reindexing the consumer is proved to be a no-op, and the forall-depth family is unshrinkable in the frozen recursion. | Real tower boundary. Redesign the recursion/interface; do not package `d - 1` and claim progress. |
| `convert : LRD.FixedHeadConvertStep []` | Receives a raw equality for the displayed type without a typed root path for the right endpoint. Sort/Pi/inductive observations need the missing normalization/adequacy information. | Tower-or-forbidden under the current interface. Preserve or reconstruct the typed endpoint path at the producing edge. |
| `anchor : LR.MajorChainAnchorStep []` | Its fields amount to subject reduction for the constructor spine plus constructor-spine type uniqueness/Pi inversion. | Tower-or-forbidden under the current interface. Carry the classified root and component path rather than rediscovering them. |
| `NatSuccRhsSelfServiceAt20` | The old bound 14 was wrong. The exact successor-body service is needed at rung 20; at the actual site `typeDepth = redexDepth - 5`, the smallest site is rung 15, and type depth at least 19 closes structurally. | A precise low-budget T4 datum, not a global service. Keep it site-local. |
| `NatRegisteredIotaSuccProvenance` | The datum is created at the matched application witness. Its global form is false, and it is equivalent at the site to the constructor-headed-or-bottom distinction. The frozen `LR.DirectLamDefEq` action loses it before the leaf consumes it. | H-ARCH. Carry a sidecar through the relation/induction at the first data-loss edge. |

The next experiment should therefore change the frozen coherent action or
induction interface at the first data-loss edge, initially preserving the
site-riding provenance and then removing the legacy callback. Treat the two
T3 exit theorems as acceptance tests. Trying to prove all six residuals as
unrestricted global classes repeats boundaries that round 2 already showed to
be false or equivalent to the forbidden adequacy/injectivity tower.

### Round-2 file map

| File in the round-2 revision | Result worth retaining |
|---|---|
| `FieldServiceProvenance.lean` | Site-riding successor-major provenance; global form refutation; combined T3 leaf and exact six-input exits. |
| `NatSuccSiteBudget.lean` | Correct rung-20 service, actual-site depth arithmetic, low-budget gap, and structural high-budget closure. |
| `EmptyContextCallbacks.lean` | Direct `defeqStep` producers at rungs 0 and 1, a nonvacuity witness, the rung-2 Pi wall, and proofs that reindexing cannot shrink the tower. |
| `FalsifyRound2.lean` | Adversarial checks and corrected round-2 boundary pins. |
| `SuccFramedPred.lean` | Refutation of the old global predecessor statement and the corrected site-local producer. |
| `FalsifyF4.lean` | R5 classification: checked syntactic anchors plus a hostile-instance argument indicate H-ADM; the full hostile instance is not formalized. |
| `FalsifyF5.lean` | No H-MODEL witness for the corrected direct interface; explicit beta/eta obstructions. Negative evidence only, not a proof of consistency or closure. |
| `NatCoherentLeaf.lean`, `NativeLeafThreading.lean` | Earlier leaf/threading construction retained by the combined T3 endpoint. Prefer the T3 endpoint over earlier T/T2 interfaces. |

## Per-obligation handoff

### V3 — `addDecl.WF`

Target: `Lean4Lean/Verify/Environment.lean`, theorem `addDecl.WF`; only the
safe `inductDecl` case is a `sorry`.

Usable production work:

- `addDecl.inductDecl_WF_of_execution` and the component/transaction wrappers
  already turn a completed producer into the final environment extension;
- `ofSemanticOrdinary` and `ofExactNested` complete the ordinary and restored
  nested readiness packages;
- ordinary and nested `ProjectionResolutionReady` producers now share the
  resolution-aware projection/eta artifact contracts;
- the constructor-prefix, block-generation, nested restoration, atomic
  transaction, exact delta, and primitive split chains are already landed;
- the 4.33.1 original uniform-occurrence, generated-recursor/rule, and
  restored-artifact guard executions are retained by the public producers;
- `canonicalFamilyAssemblySupport_nonempty` and
  `canonicalProducedBlockSemanticRecursorRunOfAudit` cover every retained
  nonempty shape, including singleton and zero-index-second-family blocks; and
- `recursorTypeShapesMatch` exposes the exact proof-erased status of
  `ProducedBlockRecursorTypeShapeRun.build?`, while the companion theorem for
  `semanticMetadataPrefix?` proves that the complete wrapper has the same
  success condition.

Local probes:

- `plans/probes/deep_candidate_gap.lean` is a positive 1100-binder
  operational-boundary regression;
- `plans/probes/deep_alias_candidate_gap.lean` shows why the real public
  validation prefix must own candidate normalization: 100,051 safe aliases
  can exhaust candidate-only deterministic WHNF fuel after public family and
  constructor validation succeeds;
- `plans/probes/G2ProofLeverage.lean` and `G3ProofLeverage.lean` classify the
  new guards as downstream certifiers requiring M4 or N3/N4 respectively;
- `plans/probes/AddDeclWFClosureSkeleton.lean` proves that exactly one named
  nonprimitive-readiness input remains at the final safe branch; and
- `plans/probes/ProjectionMetadataRoute.lean` shows that an accepted
  projection-dependent source is canonicalized to projection-free stored
  metadata, that its actual modeled recursor passes the exact source-ordered
  shape check, and that `build?` plus `metadataPrefix?` succeed on a complete
  semantic run.

Residual: derive the five-field resolved-core audit (A4) directly from every
retained execution, then complete the motive/minor/index/major/result telescope
producers (M3/M4) and ordinary semantic metadata. On the nested side, construct
N0-N4 before invoking the existing exact nested projection-parameter owner.
Feed the resulting readiness value to the compiled one-input closure
skeleton. Shape generality and projection readiness are no longer proof gaps;
the projection probe does not by itself prove universal structural-checker
completeness, so M4 remains the general metadata route.

### V5 — `reduceRecursor.WF`

Target: `Lean4Lean/Verify/TypeChecker/WHNF.lean`, theorem
`TypeChecker.Inner.reduceRecursor.WF`. Its production decomposition lives in
`Lean4Lean/Verify/TypeChecker/Reduce.lean`.

Usable production work:

- `inductiveReduceRec.SelectedBranchWF` isolates the semantic obligation from
  branch selection and state threading;
- quotient initialization and the true/false/none gates are factored;
- the `k = false`, non-structure live path is exhaustively inverted into the
  node/nil/cons selectors; and
- `Lean4Lean/Verify/Environment/NestedReplay.lean` contains the concrete Rose
  main and auxiliary `SelectedBranchWF` wrappers and exact executions.

Residuals are intentionally external interfaces:

- V5.1: use NORM-DI `IndTyAppInj` at the three Rose semantic outputs;
- V5.2: use NORM-DI M6's `QuotAppInj` producer; and
- V5.3: prove semantic preservation for the already-factored K,
  structure-expansion, literal, failure, and supported singleton/mutual/nested
  rule exits.

The NORM-DI workspaces advance the producers for V5.1/V5.2; they do not yet
contain either exported theorem. Preserve the production factorization rather
than re-proving the operational dispatcher.

### R1-R3 — head inversion

Targets: `Lean4Lean/Theory/Typing/Injectivity.lean`.

The main `Lean4Lean/Experimental` tree provides the semantic syntax, guarded
logical relation, exact Nat fixture, registered-iota machinery, and T0-T2
evidence. `ShapeLogRelAdequacy.lean` also provides conditional versions of
sort/Pi disjointness and injectivity. Those endpoints consume
`LRS.PiPathInv` and `LR.MajorLinkRect`; they are comparison/consumer APIs, not
an independent producer for the three sorries.

Round 2 is the latest truthful direct-route result. No experiment reaches
`natContextualAdequacyAtOne`, `natPiPathInvDirect`, `IndTyAppInj`, or
`QuotAppInj` yet. Continue at the six-input T3 interface above, then T4-T7 and
M4-M6.

Useful secondary evidence under `plans/probes/`:

| Probe | Disposition |
|---|---|
| `probeN5-sortedge-beta.lean` | **Refuted route.** Dynamic beta kills the `SortEdgeData` design and motivates NORM-DI. |
| `probeN4-knot.lean` | **Conditional/refuted route.** Records the earlier `SortEdgeData` knot. |
| `probeR11-piedgeinv.lean` | **Banked consumer.** Pi-edge inversion from a CR ladder, so not an independent inversion proof. |
| `probeR12-parredS-clean.lean` | **Dependency audit.** Separates the clean multi-step reduction surface. |
| `probeR12-picomponent.lean` | **Banked.** Removes one conditional Pi-component residual. |
| `probeR13-loop.lean` | **Refuted route.** Machine-checks the circularity of producing inversion through the CR ladder. |
| `probeR13-rectframe.lean` | **Banked design fact.** A paired frame is necessary. |
| `probeS-spinedepth.lean` | **Refuted repair.** Merely erasing/reindexing depth is insufficient. |
| `probeW-disjointness.lean` | **Banked.** Three of four head-disjointness facts follow from soundness; sort-level injectivity still needs adequacy. |
| `probeW16-rectframe-recapp.lean` | **Banked.** Recursor-application frame widening. |
| `probeZ16-indcand.lean` | **Legacy alternative.** Least-fixed-point inductive-candidate architecture; useful comparison, not the funded direct route. |
| `probeG-generic-instance.lean` | **Statement inventory/tainted.** Several results were ported into `SExprTransport` and `SExprGenericReplay`; the probe itself contains intentional holes. |

### R4 — strengthening `IsDefEqU.weakN_iff`

Target: `Lean4Lean/Theory/Typing/UniqueTyping.lean`. The backward implication
is already `h.weakN`; only strengthening from lifted endpoints is missing.

The relevant experiments are local attic files, not an active workspace:

- `plans/probes/attic/probeE-weakn.lean` proves the witness-substitution case
  cleanly and pins O1/O3/O4 plus the final assembly. The remaining bodies are
  explicit `sorry`s or marked tainted by the target and CR;
- `plans/probes/attic/probeE2-weakn-w2w3.lean` contains working W2/W3 scripts,
  but their current dependencies pass through the target sorry and R1-R3.
  They are consumer scripts expected to survive a de-circularized core, not a
  proof of W2/W3 today;
- `plans/probes/attic/CoDeliverableDrafts.lean` and
  `SExprCounterpartDrafts.lean` are statement-only, older-interface drafts.

The staged SST result is: W0-W3 are understood; W4 repairs `.extra`
certificate packaging, W5 supplies a clean `NormalEq` weakening inversion,
W6 re-founds CR/standardization at each stratification depth, W7 assembles the
forward direction, and W8 exports it for a generic environment. Do not move an
E/E2 theorem into production without first checking that `#print axioms` no
longer includes `sorryAx`.

### R5 — `NormalEq.parRed`

Target: `Lean4Lean/Theory/Typing/ChurchRosser.lean`. Its repaired signature
requires `[Params.PatternArgumentNonFunction]` and
`[Params.StructurePatternCompatibility]`; the only proof hole is the
`appDF`/`.extra` overlap.

Experiment results:

- `plans/probes/attic/probeCR2-extra.lean` banked level congruence,
  `EqUpToLevels` bridges, `Check.OK` transport, and the const/extra overlap.
  Those pieces have largely landed in `ChurchRosser.lean`. Its hostile
  eta/proof-irrelevance argument exposed why the app/extra statement needs a
  truthful admissibility premise;
- the consolidated `FalsifyF4.lean` classifies
  `PatternArgumentNonFunction` as not derivable from
  `Params.Semantic.ctor`. Its syntactic anchors are machine-checked; the full
  hostile `Params.Semantic` population is an explicit argument/sketch, not a
  formal countermodel. Treat the result as H-ADM and extend the semantic
  interface with the smallest generated-constructor admissibility certificate
  instead of trying a stronger tactic; and
- `StructurePatternCompatibility` should be produced by D4 registered
  structure eta. It is a separate data source from the F4 certificate.

The R11-R13 probes show that routing this case through the existing CR ladder
does not cheaply produce R1-R3; it closes a dependency loop. Finish R5 on its
repaired accepted class and do not use it as the inversion producer.

### R6 — resolved registered structure-head inversion

Target: `Lean4Lean/Verify/Typing/Lemmas.lean`, theorem
`WF.resolvedRegisteredStructureHeadInversion`.

The old `registeredStructureHeadInversion` statement allowed an arbitrary
runtime constant merely definitionally equal to the projection major.
`plans/probes/attic/CoDeliverableDrafts.lean` identifies an axiom or definition
alias counterexample. That statement is **refuted**.

The production record is repaired: the runtime name must satisfy a genuine
`env.ConstructorHead constructorName`, and the result records the constructor
name, parameter count, projection code, and argument alignment. The ordinary
compatibility theorem is just a projection of this single admitted boundary.
Verify-side producers and projection fixtures now supply the stronger premise.

After R4, the remaining proof ingredients are the landed `TrProj` structural
laws/strengthening and uniqueness, plus `IndTyAppInj` for the classified head.
There is no separate R6 workspace. `BlockProjection`, `ProjectionView`, and
restored-projection fixtures validate the operational surface; they are not a
proof of the metatheoretic head inversion.

## Main Experimental module map

The active tree is the common substrate, not eight independent proof attempts:

| Module | Role |
|---|---|
| `SExpr.lean` | Semantic syntax, `Params`, typed/path-typed weak reduction seam. |
| `ShapeLogRel.lean` | Shapes, logical relations, direct relation, shape algebra, registered-iota infrastructure. |
| `ShapeLogRelAdequacy.lean` | Adequacy machinery, coherent induction, and conditional inversion endpoints. |
| `SExprParamsD0.lean` | Concrete Nat environment and generated zero/successor certificates. |
| `SExprFalsification.lean` | T0-T2 exact redexes, strict-depth and nonvacuity/trust probes. |
| `SExprParamsD1.lean` | Definitions/Quot fixture for M6. |
| `SExprParamsD2.lean`, `SExprParamsD2Registered.lean` | Tree/TreeList mutual fixture and five registered bodies; waits on paired head alignment for `D2TreeCheckedStep`. |
| `SExprGenericReplay.lean` | Generic per-rule replay; some wrappers intentionally show inherited frontier dependencies. |
| `SExprTransport.lean` | Generic syntax transport ported out of probe G. |
| `SExprClassified.lean` | Structural-origin and descent classification. |
| `SExprReducibility.lean`, `SExprInductiveCandidates.lean` | Legacy normalization/candidate comparison route. Retain its negative results; it is not the current critical path. |
| `SExprNormalizationFailure.lean` | Counterexamples to proposed termination measures. |
| `UniqueTyping.lean` | Compatibility endpoint conditional on the inversion premises; not their producer. |

## Historical and local-only artifacts

### Upstream `logrel` bookmark

The upstream change `vkxswqxrvvvm` / `e431dad8e9a6` is described as
“Finished injectivity! 🎉”. It is **historical design provenance, not a proof
to transplant**: at that exact revision `IsDefEqU.sort_inv`,
`forallE_inv_stratified`, `sort_forallE_inv`, and `weakN_iff` still have
`sorry` bodies. Any useful induction idea must be reimplemented against the
current truthful interfaces and checked by the current axiom audit.

### Ignored probe storage

Everything under `plans/` except `plans/roadmap.md` is ignored by version
control. The probes exist only in this checkout, and deleting them is
irreversible unless they are first copied into tracked documentation or source.
The current `plans/probes/README.md` is the local index.

The attic is intentionally unreferenced. Its sorry-related contents group as:

| Group | Files | Disposition |
|---|---|---|
| SST / R4-R6 | `probeE-weakn`, `probeE2-weakn-w2w3`, `probeW3-axioms`, `probeW3-treedata`, `CoDeliverableDrafts`, `SExprCounterpartDrafts` | Mixed banked/tainted/stale; preserve until SST is re-founded. |
| CR / R5 | `probeCR-scope`, `probeCR2-extra` | Banked scope and overlap analysis; check what already landed before copying. |
| NORM legacy routes | `probeA1-hu0`, `probeA6-spine`, `probeB-1`, `probeB-2`, `probeC-ladder-crux`, `probeC2-conststep`, `probeF-telescope`, `probeH-constdefn`, `probeK-deltarank`, `probeN2-collapse`, `probeN2-eval`, `probeP-pipathinv`, `probeT-stratpi`, `probeT-typevalid`, `probeU-convert-retarget`, `probeU-regpi`, `probeV-typedview`, `probeX16-dominance-spine`, `probeY16-leaf` | Superseded, conditional, or refuted approaches. Consult only to avoid repeating a killed route. |
| D2/replay support | `probeD-deltarank2`, `probeD2-body-shapes`, `probeD2-nonoverlap`, `probeH-d2-block-shapes` | Fixture/replay archaeology; current D2 modules are authoritative. |
| Trust scratch | `AxiomProbe.lean` | Audit archaeology, not a proof producer. |

`probeUP6-gcd-direct.lean` is a live probe but unrelated to the eight sorries;
it supports the recursive-state representation work package.

## Recommended implementation order

1. Finish V3 independently on `default`; it is the only remaining frontier
   entry without a research dependency.
2. Integrate NORM-DI round 2 as one change at a clean checkpoint. Preserve its
   exact T3 hypotheses and axiom pins during conflict resolution.
3. Repair the direct coherent interface at the provenance-loss edge. Re-run
   `natT3ZeroExitT3` and `natT3SuccExitT3` after each change; then advance
   T4-T7 and produce `IndTyAppInj`/`QuotAppInj`.
4. Feed those outputs into the already-factored V5 and R6 consumers.
5. In parallel, re-found SST W4-W8 for R4 and produce the two truthful R5
   admissibility classes. Do not reuse tainted assembly as a proof core.
6. Before promoting any experiment, run `#print axioms` on the exported root,
   the compiled sorry audit, the focused library build, and the full build.

This ordering treats experiments as evidence and interface tests. It does not
confuse a green conditional theorem, a source file without `sorry`, or a
promising historical branch with discharge of an audited declaration.
