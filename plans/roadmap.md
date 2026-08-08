# Lean4Lean completion roadmap

**Status:** authoritative local roadmap, audited 2026-08-07 against the
committed fork and the current `jcb/formalization` development bookmark;
publication to `jcb/induct` remains a separate boundary.

**Versioning.** `plans/roadmap.md` is intentionally tracked so the
status-bearing milestone ladder travels with each checkpoint; other files
under `/plans` remain ignored. The root-level `upstream-divergence.md` is the
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
| Ladder position | **L4L-09A active**; L4L-08C and everything above it are complete and pruned from §5; everything below L4L-09A is queued |
| Current formalization source | L4L-08C mutual generation/preservation/replay implementation through `aa10005d`, built on the L4L-08A checked representation `79e1ae4f` and L4L-08B validation semantics; this closure checkpoint adds the migration shim and completion audit at `jcb/formalization`, with publication to `argumentcomputer/lean4lean` `jcb/induct` pending |
| Parent lineage | upstream-reconciliation merge `7f864b459e4a6062b468d6e5416688feac0f9f99` (second parent: digama `upstream/master` `ef849dfbd94a`); Lean and lean4-nix on v4.31 |
| Fixed `master` baseline | `1fb7d6ef9042c5a80b2de9320c88ac0f3ce404cb` |
| Trust frontier | exactly 20 live source `sorry` tokens across 19 proof declarations, plus six kernel-rejection recovery declarations (25 compiled allowlist entries total), and 29 custom-axiom declarations; all are pinned by exact audits |
| Gates | the full §6 gate is green on the L4L-08C closure source, including focused, aggregate, and default Lake builds, the Nix proof/dependency build, all native flake checks, sorry-frontier and Theory import-boundary audits, formatter check, and whitespace check |

### 2.1 What is green

**Theory.** Dependent `VInductDecl.Checked`/`checked?` analysis with
environment-free closure/universe/name/anatomy checks and an
environment-indexed `Checked.WF env` (including Lean's impredicative Prop
exception `l = .zero ∨ u ≤ l`); the raw/view `Normalization source` boundary
with computed `normalizationShape` and semantic `Normalization.WF env`;
`NormalizedChecked` and `GenerationChecked` paired raw/view blocks; mixed
motive/minor/recursor/rule generation that retains raw binder syntax while
consulting the checked view for recursive classification, proved well formed
through the complete ordered rule fold. The one-family transaction
`VEnv.addInductGeneration` and its proof-carrying
`GenerationCertificate`/`addInductCertified` boundary remain available.
`BlockGenerationChecked` generalizes the same artifact path: it emits one
motive and recursor per family, globally flattens constructor minors and rules
in family/source order, and routes recursive hypotheses and rule calls by the
checked target-family ordinal. `VEnv.addInductBlockGeneration` inserts all
families, then all constructors, then all recursors, then all rules; its exact
trace supplies atomicity, freshness, lookups/membership, monotonicity, and
`Ordered` preservation through every phase. The raw public `addInduct` now
selects this block descriptor without singleton projection. A deprecated
`addInductSingleton` wrapper retains the former raw one-family transaction for
the migration window without becoming a competing block path. The shared
checked/generation artifact retains the exact K-target decision separately
from its elimination mode. The slice covers parameters, per-family indices,
direct and sibling recursion, recursive targets below Pi telescopes, small
elimination, subsingleton large elimination, K-target metadata, and exact
zero-/one-constructor generation.

**Mutual validation, generation, and replay.** `VInductDecl.CheckedBlock` and
`checkedBlock?` analyze an arbitrary nonempty `decl.types` list without
singleton destructuring. Shared parameters are retained once, while
`CheckedFamilies source params ordinal types` is indexed simultaneously by
the exact remaining source-family list and its starting ordinal. Each
`CheckedFamily` retains its per-family indices, result level, and ordered
constructors; every `RecArg.targetType` is computed from the block-wide family
header order, including targets beneath positive Pi telescopes. Block-family
mentions are excluded from family formers, recursive domains, and recursive
indices, and generated-name uniqueness is checked across all families,
constructors, and future recursor names.

`Normalization.BlockWF`, `CheckedBlock.WF`, `ValidatedBlock.WF`, and
`ValidationCertificate` give the arbitrary-block representation an exact
environment-indexed semantic package. Family validation retains shared
parameter agreement and one semantic result universe, then all raw family
constants are staged before constructor validation. The block constructor
trace records every family/constructor/ordinary-field target in source order,
including sibling recursion and recursion beneath Pi binders. The real
Tree/TreeList and indexed IndexedTree/IndexedTreeList fixtures execute the
ordinary kernel validators, compute the exact target matrices, and inhabit
complete normalization, checked-block, and block-generation WF certificates.
Their generated inventories have respectively two motives, five/four globally
ordered minors, two recursors, and five/four rules. Exact kernel comparisons
cover every `InductiveVal`, `ConstructorVal`, `RecursorVal`, and
`RecursorRule` field represented by the Theory boundary, including constructor
indices, block-wide recursion/reflexivity flags, recursor motives/minors/K,
translated types in metadata universe order, rule ownership/field counts, and
every RHS. Both raw `addInduct` and the proof-carrying block transaction produce
the same final Theory environments. The four phase boundaries replay through
`AddInductBlockTrace`, `TrEnv'.inductBlock`, and `Aligned.addInductBlock` to
actual implementation `ConstMap`s, with exact final ordering, lookup, rule
membership, and guarded trust closures. Exact negatives still pin the
parameter-mismatch, result-universe-mismatch, and reordered-family validation
phases, including host Lean diagnostics and transparent validator errors.

**Kernel parity fixtures.** One integrated 14-row matrix covers Nat, Bool,
List, Option, Prod, Unit (honestly represented by the kernel's `PUnit`), Empty,
Or, And, Eq, HEq, Fin, Vector, and Acc. Every row reruns the ordinary producer
and definitionally compares the stored family/constructor types in their
metadata universe order, names, parameter/index/field counts, recursive rule
metadata, elimination/K behavior, recursor type, rule count, and every iota
RHS. The consolidated 32-row rejection matrix covers closure, internal and
pre-existing name collisions, universe and result-shape failures, parameter
and universe-count mismatches, raw/view incoherence, non-defeq normalization,
nested negativity and illegal recursive targets, field-universe boundaries,
and invalid elimination/K expectations. The earlier `IndexedVec` regression
remains as a supporting indexed two-constructor fixture outside this fixed
singleton inventory. `AliasFormer` and `AliasRec` prove normalization is
necessary, not hypothetical: real metadata
retains reducible aliases at the family result and around a recursive field;
their raw declarations fail `checked?` while their certified views succeed.
`NormalizationMatrix` closes the differential breadth for reducible aliases
in family, parameter/index, ordinary-field, direct-recursive, and
Pi-hidden-recursive positions, including retained beta/let bodies. Its exact
kernel candidate succeeds at fuel 10 and fails at 9, opaque and non-defeq
variants reject, and the actual family/constructor/recursor/rule metadata
replays through the final aligned Theory environment.
The edge fixtures additionally pin every `PUnit` and `Empty` inductive,
constructor, and recursor metadata field, exact motive/minor/major order,
zero-field recursive-argument data, rule counts, and every available iota RHS.
They record `Unit` itself as the reducible `PUnit` definition metadata Lean
actually supplies, rather than inventing alias-level inductive metadata.

**Elimination and K-target parity.** The ordinary large-eliminator decision,
elimination-level run, and independent K-target decision now retain exact
operational traces, including inferred singleton field sorts, occurrence
tests, the K constructor walk, the fresh elimination parameter, and both
recursor level orders. Theory generation constructs both elimination modes and
the K flag and is differentially aligned with those executions. Exact kernel
fixtures pin `Eq` as K/large with fresh-first parameters `[u, u_1]`; `And` as
non-K yet legitimately large through its singleton proof fields; `Or` and a
source-universe-bearing family as non-K/small; and `Nat` as non-K/large through
the never-zero branch. The source-universe fixture retains its source
parameter without adding a fresh one. Their exact kernel K flags, recursor
metadata, universe order, and every focused rule RHS match Theory generation.
Verify's `RecursorKMatches` makes a type-correct recursor with the wrong K
metadata fail environment alignment.
The `PUnit`/`Empty` executions close the one-/zero-constructor boundary:
`PUnit` traverses a singleton with no parameter, proof, or data fields and
retains fresh-first recursor levels, while `Empty` takes the ordinary
never-zero large-elimination branch with no singleton, minor, or rule. Both
align with the shared checked generation and remain non-K.

**Verify.** A checker-run certificate layer (`WhnfRun`, `CheckTypeRun`,
`IsDefEqRun`, `DefEqEvidence`, `TelDefEqEvidence`, `NormalizedCtorRun`,
`GenerationRun`) turns exact ordinary-checker executions into Theory typing
and definitional equality through the existing refinement theorems. Level
subsumption is evaluation-preserving for every raw `NormLevel`: active-path
witnesses now guard constant removal, and the proof follows both nested map
folds. Valid normalizer output remains unchanged under the differential audit;
the theorem's exact closure is only `propext`, `Classical.choice`, and
`Quot.sound`, with no project-specific axiom. Level equivalence soundness now
closes the typechecker sort and dependent constant-level-list paths through
the verified project comparator: a transparent structural fast path reflects
equality, canonical ordered-entry comparison gives `NormLevel` evaluator
congruence, and `isEquiv_wf` plus its list theorem have the same standard-only
axiom closure. The executable normalizer is unchanged, and a generated
differential compares the former map-extensional equality with ordered-entry
equality across normalized zero, successor, max, imax, and parameter forms. The
executable candidate producer (`AddInductive.normalizeCandidateExpr`,
`buildNormalizationCandidate`) retains recursively context- and source-indexed
traces with exact full-check/WHNF/binder-equality runs at every node,
structurally certified annotation consumption (agreement with Lean's opaque
`consumeTypeAnnotations` is runtime producer validation, never a semantic
proof field), a `storedSpine` invariant, and arbitrary-length dependent
`Produced` list witnesses. Semantic-hierarchy assembly is automatic under
`Nonempty`; the consolidated generation-readiness gate plus exact dependent
analysis and analyzer-owned view WF derive checked WF and every per-position
shape record, so fixtures supply no component equations. The generic singleton
closure combines that staged owner, the exact dependent analysis, and the
produced generation shape into an exact package while deriving its public
package; no caller supplies a view, view-WF proof, or per-component equation.
The staged semantic-input owner, family-validation semantics with post-family
staging, and the complete retained constructor-validation trace (with
source-list inversion and phase-local failure theorems) are in place. The
source-ordered constructor-universe audit admits structural order and the
impredicative-Prop exception directly; its normalized non-Prop branch requires
both Lean's unchanged core `Level.geq` decision and the verified project
`geq'` decision. `NormLevel.le_eval` and `geq'_wf` prove the project half
semantically, while the core half keeps every accepted audit node inside the
ordinary validator's existing acceptance boundary. The exact proof closure is
only `propext`, `Classical.choice`, and `Quot.sound`; an all-pairs mvar-free
core/project differential covers zero, successor, max, imax, parameters, and
nested combinations, and the former max/parameter exclusion is now a positive
regression. The post-family constructor owner
aligns the retained validator and candidate telescopes by source position,
independent of their fresh-FVar identities, and interprets root, parameter,
field, positivity, and terminal checks in the actual verified post-family
context without claiming pre-family `fieldsWF`.
The executable pre-family owner instantiates the retained family parameters
and replays every analyzer-owned constructor in the exact verified pre-family
context. Ordinary fields are rechecked and retained; recursive outer locals
are omitted while nested Pi binders and recursive/result index spines receive
verified semantic interpretations and proved prefix weakening. Independent
ordinary fields may now follow an omitted recursive outer field and continue
through the generalized semantic replay. The actual `ConstructorValidityMatrix`
metadata now closes this path structurally across its two parameters and six
fields: dependent data/proof fields, direct recursion, recursive-function
recursion, and an independent dependent data/proof suffix after both omitted
recursive locals. The proof derives the retained constructor-validation trace,
universe run, post-family alignment, exact fresh-name independence, zero-index
terminal spine, and final pre-family safety result without a stage-local
decision oracle. Its guarded axiom closure contains only the pre-existing
verified-checker frontier and the single exact L4L-01E producer-execution
witness. `PropRecursiveBoundary` separately pins the impredicative-Prop branch
with recursive-function and index structure. Nearest-kernel negatives reject
nested negativity, family occurrences in nonrecursive and proof fields,
dependency on an omitted recursive local, and an excessive constructor
universe with the exact ordinary-producer errors; the omitted-local case also
reaches and pins the strengthened pre-family rejection.

**Three positive regressions, end to end.** AliasFormer (terminal alias),
AnnotatedPi (nested recursive-Π with retained `outParam Prop`, generated
recursor and iota rule), and `IndexedVec` (one parameter, one index, ordered
`nil`/`cons`, identity normalization) each prove the exact successful whole
`buildNormalizationCandidate` call, inhabit
`ExactProducedGenerationCandidatePackage` through the generic closure, erase
it to `ProducedGenerationCandidatePackage`, and route both the certified
Theory transaction and the checked replay through that package. All three also
pass the strengthened constructor-universe gate and inhabit both produced
post-family and pre-family semantic owners. `IndexedVec` additionally proves
that validator and candidate field FVars differ while their Theory positions
still align. Negatives stay sharp: opaque-`outParam` whole-candidate rejection,
truncated and reordered views, missing/extra constructors, recursive-local
dependency, and the environment-free
closure/universe/name/result/collision matrix.

**Constructor-parameter parity.** `AnnotatedParam` is built from Lean's actual
kernel family, constructor, recursor, and rule metadata. Its complete ordinary
metadata call accepts the stored `outParam Type` constructor prefix against the
annotation-consumed `Type` family local by definitional equality; a closed,
well-typed but genuinely non-defeq prefix reaches the same check and is
rejected with the exact kernel-facing error. Mixed generation retains the raw
constructor surface while using checked family parameters for emitted recursor
binders, and the resulting recursor and iota RHS are definitionally equal to
kernel metadata. The proof-carrying transaction and real-`ConstantInfo` replay
then establish final lookup, WF, alignment, uniqueness, and rule membership.
The operational L4L-01E package authority remains the exact AnnotatedPi
producer case; the parameter fixture deliberately does not claim a second
independently assembled produced package.

**Environment replay.** The sole public L4L-07 inventory contains 19
actual-metadata transactions: all 14 fixed rows plus AliasFormer, AliasRec,
NormalizationMatrix, AnnotatedPi, and AnnotatedParam. Every
`SingletonReplayArtifact` carries its exact input/output `ConstMap` and `VEnv`,
input ordering, the proof-carrying `AddInduct` transaction, final alignment,
and derived output ordering. Fin replays over the real Nat/LT dependency
slice; Vector replays over Nat/Eq/Array/`Array.size`, including the stored
metadata annotation on `Array.size`'s borrowed argument. The fixed and
normalization inventories are definitionally tied to the Theory inventories,
and their 14/5/19 cardinalities are executable. The older `IndexedVec`
fixture still spells indices as `Nat.zero`/`Nat.succ`, deliberately excluding
notation's `OfNat`/`HAdd` instance closure — a reduced dependency claim, not
full prelude replay.

**Not claimed.** Nested blocks, generated patterns, projections, and the
remaining metatheory/checker roots. The mutual fixtures prove the current
non-nested block boundary; they do not claim the kernel's nested flattening or
auxiliary-family transformation.
Bare producer success is never generation-shape authority or Theory semantics.

### 2.2 Live debt

The sorry audit (`Lean4Lean/Audit/SorryFrontier.lean`, a declaration-level
`sorryAx` allowlist over the compiled Theory/Verify surface) currently
accepts exactly 20 live sorries across 19 declarations (`NormalEq.parRed`
carries two), plus six deliberately kernel-rejected fixture recoveries that
are not proof debt:

| Area | Live debt |
|---|---|
| Projection specification | `Verify/Typing/Expr.lean:67`, `TrProj` |
| Projection structural laws | seven sites in `Verify/Typing/Lemmas.lean`: `weak'`, inverse weakening, `defeqDFC`, `wf`, `uniq`, `instN`, `instL` |
| Core metatheory | `Injectivity.lean` x3, `UniqueTyping.lean` x1, `ChurchRosser.lean` x2 |
| Checker verification | `Verify/Environment.lean` x1; `InferType.lean` x1; `WHNF.lean` x2; `IsDefEq.lean` x2 |

The remaining v4.31-added sorry is classified:
`Lean4Lean.addDecl.WF` → L4L-19B. Non-sorry debt:

- The public inductive spec has complete one-family and non-nested mutual
  generation, preservation, metadata parity, and environment replay, but
  remains a growing subset rather than kernel-complete; nested,
  generated-pattern, and projection coverage remain queued.
- Consumer-neutral APIs (`VLocalDecl` core, literal encodings,
  `ContainsLits`, `HasPrimitives`, `TrProj`) still live under `Verify/`,
  forcing downstream checkers to import that layer (L4L-12A/L4L-15C).
- 29 project-specific `axiom` declarations outside `Experimental/`: 27 in
  `Verify/Axioms.lean` and two pointer-equality contracts in `PtrEq.lean`.
  Three cached-field equations from the group once false on older pins
  (`lean4#8554`) remain unproved and therefore forbidden contracts even though
  v4.31 fixed the underlying cache bug.
- The fetched `logrel@upstream` branch at `e431dad8` is a serious experimental
  route to injectivity/unique typing, but it depends on unfinished
  `ShapeLogRel`/adequacy work and cannot be merged as a completed proof.
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

Current custom-axiom inventory (29 declarations; classification records
intended release treatment, not evidence the equations are true):

| Class | Count | Declarations | Release treatment |
|---|---:|---|---|
| Unproved cached-field equations, once false on older pins | 3 | `Level.hasParam_eq`, `Level.hasMVar_eq`, `Expr.looseBVarRange_eq` | Forbidden from every supported theorem root until proved for the pinned implementation |
| Reference equations documented as `@[implemented_by]` candidates | 13 | `Expr.replace_eq`, lift/lower, instantiate/range/reverse, abstract/range, `hasLooseBVar_eq`, `eqv_eq`, `equal_eq` | Replace axioms with logical reference definitions and separately justified implementations |
| Persistent collection semantics | 5 | `TreeMap.all_eq_all_toList`; `PersistentArray.toList'_push`; hash-map insert, find, and contains/find agreement | Prove upstream or narrow to the actual WF/reachable-state invariant |
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
it changes the active design, but implementation and publication stay serial:
this keeps one auditable claim per checkpoint and prevents several
half-migrated public artifact paths from being live simultaneously.

If upstream advances at a milestone boundary, insert an explicit
integration-only reconciliation checkpoint (as was done for v4.31) rather
than hiding merge work inside a semantic milestone.

### Nested inductives (L4L-09A–L4L-09C)

**L4L-09A — nested representation decision (active).** Audit how translated
`inductInfo` represents flattened nested auxiliaries even though the producer
receives `numNested` and `VInductDecl` does not. Commit a design note plus
executable metadata probes. Choose an additive metadata/checked-block type or
proved pre-flattening relation; change existing `VInductDecl` fields only if
neither can express real output, with downstream compatibility evidence
first.
*Exit:* the design is sufficient for real rose-tree and nested-indexed
metadata; no acceptance behavior or public field changes without demonstrated
need; this checkpoint changes no acceptance behavior.

**L4L-09B — nested transformation and positivity.** Implement the chosen
pre-flattening/auxiliary relation, the kernel nested transformation, and its
positivity/validation obligations.
*Exit:* the transformed family and auxiliary descriptors for a rose tree
through List and one nested indexed family, plus nearest rejection
differentials, match kernel acceptance; no generated recursor or replay is
claimed yet.

**L4L-09C — nested generation and replay.** Generate every auxiliary
declaration, recursor, and rule; prove preservation and insertion order.
*Exit:* both fixtures round-trip real `Inductive.Add.run` output through
generic packaging and environment replay, comparing all raw metadata and
rule RHSs rather than a hand-authored declaration.

### Generated patterns (L4L-10A–L4L-10B)

**L4L-10A — generated iota pattern core.** Construct every generated iota LHS
through `SimplePattern.iota` or prove exact equality to its `Pattern`. Prove
match inversion, rule-index/constructor recovery, rule distinctness, pairwise
non-intersection, and the
`Params.pat_uniq`/`pat_app_l_uniq`/`pat_app_uniq` obligations for one
certified block. Add the implementation-independent shape helpers
(`HeadConst`, `HeadConstN`, `of_varN_matches`, `RecursorIotaPattern`,
`matches_shape`) to `Theory/Typing/Pattern.lean`.
*Exit:* a certified block supplies the complete generic pattern facts with
standard Theory axiom closure; no open-environment instance is installed.

**L4L-10B — pattern soundness and environment assembler.** Prove `pat_wf`:
successful match/check instantiates the LHS/RHS defeq registered by
`addInduct`. Add a block-local assembler for an environment whose defeq set
consists of generated inductive rules plus separately certified extension
rules.
*Exit:* the assembler is generic over certified extensions, installs no
global open-environment `Params` instance, and exposes exactly the helpers
Church–Rosser and downstream consumers need.

### Replay breadth and the block-certificate API (L4L-11)

**L4L-11 — consumer block-certificate API.** Generalize the automatic
candidate/package construction and environment replay across the complete
single/mutual/nested fixture matrix, keeping every dependency environment
explicit and checking type, every constructor role, and recursor lookup
uniqueness. Separately add a notation-heavy prelude replay fixture before
claiming whole-environment coverage; do not hide that prefix behind a
hand-built Theory-only environment, and abstract witness-only tests are not
sufficient. Export the consumer-neutral block-certificate consequences:
environment growth (`addInduct`/`addInduct_le`), block WF
(`VDecl.WF.induct`/`addInduct_WF`), translated type/constructor/recursor
lookups, recursor facts from generated rule membership and registered
defeqs, and recursor patterns from L4L-10A/B. If a downstream checker cannot
fill a semantic obligation from these APIs without a new assumption,
strengthen the checked-block API here rather than expecting the consumer to
add trust.
*Exit:* the full supported block class replays from actual metadata; the
block-certificate API is exported with exact guards and no `sorryAx` beyond
the separately tracked projection relation; no Verify state, normalization
oracle, or kernel implementation object crosses the Theory boundary.

### Theory API extraction and literals (L4L-12A–L4L-12B)

**L4L-12A — Theory API extraction.** Split `VLocalDecl` and its VExpr-only
operations/WF/defeq lemmas from the `FVarId`-specific `VLCtx` layer into
`Theory/LocalContext.lean`. Move `VExpr.boolLit`, `natLit`, `listCharLit`,
`trLiteral`, `VEnv.ContainsLits`, the implementation-independent part of
`VEnv.HasPrimitives`, and their lift/inst/instL lemmas into
`Theory/Literals.lean`. Keep `TrExprS` and all
`Lean.Expr`/`Literal.toConstructor` traversal in Verify; re-export old names.
*Exit:* the library builds through compatibility re-exports; no semantic
assumption is removed yet; import-direction and exact axiom gates pass.

**L4L-12B — literal and prelude readiness.** `ContainsLits` says only that
names occur in the environment; it does not imply their types. Define a
Theory-level readiness predicate combining `Ordered` with the exact
Nat/Bool/Char/List/String constant types and required iota rules. Prove that
readiness plus `ContainsLits l` gives `VExpr.WF env U [] (VExpr.trLiteral
l)`; that direct `trLiteral` meaning agrees with the Verify translation of
`Literal.toConstructor`; and that readiness is monotone under `VEnv.LE` and
preserved by unrelated declarations.
*Exit:* literal WF is a derived theorem from the readiness predicate;
notation-heavy fixtures pass; no invalid name-containment shortcut is used.

### Projections and structures (L4L-13A–L4L-15C)

The current API needs a design gate first. `TrProj Γ structName idx e e'` has
no environment, universe count, structure descriptor, constructor metadata,
or projection-name map; `TrProj.uniq` is even stated for unrelated `s₁` and
`s₂`. A recursor encoding cannot simply be dropped into that signature.

**L4L-13A — projection expressibility decision.** Freeze the seven current
lemma statements as regression tests, then check whether a meaningful
relation can satisfy them without strengthening their premises — in
particular structure-name dependence, parameter offsets, dependent fields,
universe instantiation, and uniqueness. If the signature is inadequate, add a
Theory-level env-indexed API such as a `VStructureView` plus
`VEnv.TrProj U Γ view idx e e'`, changing Verify's `TrExprS.proj` through a
compatibility wrapper. Do not encode the missing metadata as unconstrained
existential witnesses.
*Exit:* real parameterized/dependent/universe fixtures demonstrate
representability; the API decision is recorded.

**L4L-13B — projection semantics.** Default to a recursor encoding because it
reuses generated iota rules and is consumer-neutral; compare against applying
a registered projection-function constant, which matches Lean metadata more
directly but requires a projection-name map in Theory. Choose the
representation that makes all of the following derivable from one
`VStructureView`: projection field type (including dependencies on earlier
projections); constructor projection/iota behavior; congruence under defeq
and environment extension; lift, substitution, and universe instantiation;
and structure eta / zero-field behavior, or a precise statement of what
additional Theory rule is required.
*Exit:* the representation computes on real structures and makes every
L4L-14 premise expressible; no structural law or checker proof is claimed
early.

**L4L-14 — projection structural laws.** Prove the seven upstream
obligations — weakening, inverse weakening, context-defeq transport, WF,
uniqueness, term substitution, and universe instantiation — and expose one
bundled structural-laws theorem while preserving the individual compatibility
theorem names for upstream Verify. Add projection-bearing end-to-end
fixtures.
*Exit:* the projection relation and all seven structural-law sorries are
gone from the frontier; projection fixtures pass; compatibility names are
preserved.

**L4L-15A — projection checker verification.** Use the structure view to
prove `inferProj.WF`, `reduceProj.WF` for constructor applications and
strings, and the projection branches of WHNF and translation congruence.
Re-run the enclosing `inferType`, `whnfCore`, and `isDefEq` theorems so the
absence of a local sorry also removes it from every exported root.
*Exit:* focused structure/string fixtures and enclosing checker roots pass
with exact axiom closures; eta/unit-like roots remain queued.

**L4L-15B — structure eta and unit-like comparison.** Derive
`tryEtaStructCore.WF` and `isDefEqUnitLike.WF`. First attempt derivation from
the recursor/iota package, proof irrelevance, and projection uniqueness. If
Lean's structure eta requires a new primitive Theory defeq rule, write a
design note covering subject reduction, injectivity, confluence, and
downstream impact, and obtain upstream agreement before changing `IsDefEq` —
this is a metatheory change, not a local checker lemma.
*Exit:* both roots are sorry-free and audited; any Theory-rule change has
subject-reduction/injectivity/confluence and downstream-impact evidence.

**L4L-15C — Theory-only consumer import surface.** Audit the consumer-neutral
lemmas still living under Verify after L4L-12B and L4L-15B; give each a
Theory home and deprecate the corresponding Verify compatibility shims.
*Exit:* no consumer-neutral lemma requires a `Lean4Lean.Verify` import;
compatibility re-exports are removable without loss.

### Metatheory closure (L4L-16–L4L-18B)

Scheduled completion work; coordinate with Mario because upstream has active
research branches.

**L4L-16 — route selection and sort inversion.** Evaluate two routes in a
small, focused proof branch: (1) finish and bridge the fetched
`logrel@upstream` approach (`ShapeLogRel`, adequacy, and
`Experimental/UniqueTyping`) into live VExpr judgments; or (2) complete the
current stratified `HasTypeStrong` proof directly. The spike must list every
remaining assumption in the chosen route and close the existing public
`IsDefEqU.sort_inv` statement. Merge only that proof, its necessary generic
lemmas, and the documented route decision — not the whole experimental
branch, which changes unrelated code and still contains adequacy sorries.
*Exit:* the public sorry is removed with an exact accepted axiom closure;
the chosen and discarded routes are documented with concrete remaining
obligations.

**L4L-17 — remaining injectivity and weakening inversion.** Building on
`sort_inv`, prove `IsDefEqU.forallE_inv_stratified`,
`IsDefEqU.sort_forallE_inv`, and `IsDefEqU.weakN_iff`; re-run
`IsDefEq.uniq`/`uniqU`, context inversion, and all downstream `#print
axioms` checks.
*Exit:* the remaining public injectivity/inversion statements are sorry-free;
affected Theory and checker roots have exact accepted closures.

**L4L-18A — Church–Rosser `.extra` cases.** The holes in `NormalEq.parRed`
are the constant/application cases where a parallel step meets a user
defeq-pattern step. Use the generic `Params` interface, L4L-10B's match
inversion/non-overlap library, and rule RHS congruence to prove the
commuting diagrams, keeping the theorem generic in `[Params]`.
*Exit:* `ParRed.church_rosser`, normal-form uniqueness, and the live
standardization/head-reduction endpoints contain no hidden placeholder
assumptions.

**L4L-18B — extension contract.** Document `.extra` as the supported hook for
consumer-certified defeqs and add the missing monotonicity/transport lemmas
under `VEnv.LE`. State exactly what a consumer-certified extension oracle
must prove (typedness, symmetry/closure as needed, pattern compatibility) and
what lean4lean does not trust automatically.
*Exit:* generic lemmas build; the consumer extension contract is documented;
no external defeq is trusted automatically or smuggled through generated
`Params`.

### Checker closure (L4L-19A–L4L-19C)

**L4L-19A — recursor reduction verification.** Prove `reduceRecursor.WF` for
Quot and certified inductive rules, obtaining the selected rule, match,
checks, RHS translation, and result typing from the generated/translated
metadata — not from a global oracle.
*Exit:* Quot, singleton, mutual, and nested recursor reductions pass;
enclosing WHNF roots have exact guards.

**L4L-19B — environment-to-checker closure.** Prove the remaining
nonprojection checker refinements (including the v4.31 front-end
`addDecl.WF`) and full `TrEnv` over fixture environments containing ordinary
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

Retire in risk order: the three remaining cached-field equations; the
thirteen reference equations (convert to logical definitions with
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
remaining checker and axiom-minimization work. Do not rewrite the published
`jcb/induct` checkpoints: each PR series is extracted onto a fresh review
branch rebased on its current upstream target. Do not mix the large
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
midway through an artifact or transaction switch). Only `origin/jcb/induct`
moves; local/remote `master` and every digama/upstream ref stay fixed, and
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

- **Checkpoint drift.** The published `jcb/induct` line is ahead of `master`.
  Keep published checkpoints recoverable, require Linux/Darwin CI builds at
  release boundaries, and record any replacement hash here.
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
- **Projection API insufficiency.** The present `TrProj` signature may make a
  faithful semantics impossible. Resolve L4L-13A explicitly instead of hiding
  metadata in an oracle or preserving a false “frozen statement” rule.
- **Structure eta may change Theory.** A new defeq constructor would affect
  injectivity, confluence, standardization, and downstream consumers. Require
  a design proof and upstream agreement first.
- **Research-branch optimism.** `logrel@upstream` is evidence of a viable
  path, not a drop-in solution; measure its remaining adequacy/bridge debt
  with the exact live theorem as the spike gate.
- **Unsound bridge axioms.** Some cache equations were documented false on
  older pins and remain unproved. Zero sorries is not a soundness claim until
  final-root axiom reachability is clean.
- **Upstream collision.** Repeat the ancestry and overlap check at every
  milestone boundary; if upstream advances again, insert another explicit
  integration checkpoint rather than hiding merge work inside a semantic
  milestone.
- **Scope leakage from Experimental.** No supported root may import
  experiments. Promote a proof only after removing its experimental sorries
  and giving it a stable API.
