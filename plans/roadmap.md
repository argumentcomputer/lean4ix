# Lean4Lean completion roadmap, with Ix as the first external consumer

**Status:** authoritative local roadmap, audited 2026-08-04 against the
committed fork, the current `jcb/induct` development branch, and ix's
formalization branch.

**Overall assessment:** progressing, not stalled. The fork has a published,
green vertical slice through checked single-family generation, normalized
Verify replay, and a proof-carrying non-identity Theory transaction. The live
critical path has moved past `IndexedVec`'s executable outer producer:
the real one-parameter, one-index family and its ordered `nil`/`cons`
constructors now pass exact family validation, post-family constructor
validation, dependent candidate-list assembly, and the complete successful
`buildNormalizationCandidate` call. The published identity-replay bridge can
interpret syntactically identity-normalizing traces at caller-selected Theory
endpoints. The published semantic checkpoint uses that bridge to assemble the
complete `IndexedVec` semantic generation package, producer-selected
certificate, proof-erased Theory transaction, and checked E1 environment
replay. The executable list boundary is now reusable: dependent
`CandidateFamilyTypeListProduced`, `CandidateConstructorListProduced`, and
`CandidateFamilyListProduced` witnesses prove exact family-type, ordered
constructor, and complete-family traversal results at arbitrary list lengths.
AliasFormer and AnnotatedPi use the singleton instances, while `IndexedVec` is
the two-constructor regression. The outer singleton boundary is also reusable:
`GenerationCandidateSemanticRun.producedPackage` attaches an exact successful
whole-metadata equation to the same source- and candidate-indexed semantic
owner, and all three fixtures now use it instead of hand-assembling outer
records.
The retained semantic boundary is now reusable and automatically assembled.
`CandidateExprSemanticRootInput` lets the retained checker run select one
Theory view from a verified context and strict source translation. Dependent
constructor, family, and normalization inputs combine with the arbitrary-length
operational `Produced` witnesses to return a
`Nonempty ProducedNormalizationCandidateSemanticRun`; no caller supplies a
view, and no choice-based data extractor is added. Semantic generation owners
project every family and constructor spine from that same hierarchy, so
normalization, generation, packaging, and produced packaging cannot drift onto
parallel roots. AliasFormer, AnnotatedPi, and `IndexedVec` all use this path.
The `IndexedVec` regression additionally proves that the automatically
assembled hierarchy retains exact `nil`/`cons` source order and rejects a
swapped view at the computational normalization-shape gate. Exact compile-time
axiom guards cover the generic constructors and projections plus all three
fixture roots. The published analyzer-provenance checkpoint closes two more
structural gaps. `GenerationCandidateRun` now retains the exact equation that
the candidate normalization's dependent `generation?` analysis returned its
`GenerationChecked`; a successful analysis generically determines the retained
normalization. Post-family `VEnv.WF` is reconstructed from the verified
pre-family context, candidate raw/view definitional equality, checked family
typing, and exact raw-family insertion. AliasFormer, AnnotatedPi, and
`IndexedVec` consequently supply neither an independent `normalization_eq` nor
`typeEnv_wf`. The generation shape-alignment checkpoint closes the remaining
component-alignment gap. `GenerationCandidateSemanticShapeRun` accepts only
checked WF plus source-indexed family/constructor `storedSpine` and total
spine-length data. Exact dependent analysis determines the raw family, full
checked family view, normalized constructor pairs, and complete constructor
order; the total binder counts determine raw telescopes/results, while exact
checked shape determines view terminals. Its generic projection reconstructs
the established semantic generation owner without `zip`, truncation,
reordering, a caller-selected pair, or fixture component equations.
AliasFormer, AnnotatedPi, and the two-constructor `IndexedVec` regression now
use this reduced boundary. Together with the preceding structural-evidence
checkpoint, fixtures no longer supply `viewTel`, terminal typing, raw/result or
view-terminal equations, normalized pair identities, normalization equality,
post-family WF, or dependent-list alignment. The consolidated
generation-readiness checkpoint removes the remaining fixture-owned checked WF
and per-position generation-shape records. One source-indexed executable gate
checks the complete singleton family and constructor hierarchy, including
retained emitted Pi spines, full raw telescope lengths, and exact constructor
list cardinality; missing and extra raw constructors are rejected explicitly.
`ProducedGenerationShapeCandidate` retains both that successful gate and the
exact ordinary `buildNormalizationCandidate` equation. Exact dependent
analysis plus WF of the analyzer-owned view declaration then derives checked
WF and expands the one Boolean result into every dependent family/constructor
stored-spine/count record. AliasFormer, AnnotatedPi, and `IndexedVec` all use
this path. Bare producer success deliberately remains neither generation-shape
authority nor Theory semantics: WHNF can change the visible Pi spine, and the
ordinary producer checks neither `storedSpine` nor semantic WF. Complete
one-family parity (L4L-07) and the ix oracle handoff (L4L-11) remain beyond the
narrowed boundary.
Ix Pin A is complete against the
certificate-bearing
`5e5bb767b3491d21a71908d4c58bcbaa007283bb` checkpoint; it deliberately makes
no oracle claim.

**Completed milestone: L4L-01A — staged semantic-input consolidation.** Source
checkpoint `7c7922091f94b4a4f51c6834b376de376be22e71` introduces one
source-indexed staged owner over verified pre-family/post-family candidate
contexts, strict source translations, exact insertion alignment, and the
existing family/constructor `Produced` traversals. AliasFormer, AnnotatedPi,
and `IndexedVec` use that owner, preserve exact constructor order, and no
longer define the repeated per-root semantic-input tower. The theorem returns
only `Nonempty ProducedNormalizationCandidateSemanticRun`; no view-WF,
generation-package, or choice-extraction claim was added. The explicit
downstream witnesses and analyzer-owned `viewWF` proofs remain visibly
temporary for L4L-01D/L4L-01E.

**Completed milestone: L4L-01B — family-validation semantics and staging.**
Source checkpoint `da45b536220a3eff5ed78cf2f5afcf5e7491c40f` interprets the
exact singleton `checkInductiveTypes`/family-candidate execution from one
verified entry candidate context. It derives the analyzer-owned
parameter/index telescope, terminal-sort typing, raw-family constant WF through
semantic definitional equality, exact raw-family insertion, and the verified
post-family candidate stage. AliasFormer, AnnotatedPi, and `IndexedVec` no
longer supply independently verified post-family environments, contexts, or
fixture-specific post-family `VEnvs.WF` reconstructions. Exact axiom guards and
the universal Lake/Nix gates pass; constructors are not semantically
interpreted.

**Completed milestone: L4L-01U — upstream v4.31 reconciliation.**
The source reconciliation is complete at
`7f864b459e4a6062b468d6e5416688feac0f9f99`: digama `upstream/master`
through `ef849dfbd94a` is a merge parent, Lean and lean4-nix are on v4.31, the
overlapping inductive/checker/Verify/level proofs build, and the fork's staged
family APIs remain intact. The merge removes four cached-`Expr` axioms and the
obsolete hand-declared `Expr.mkAppRangeAux.eq_def`, reducing the custom-axiom
inventory from 34 to 29. It adds two classified sorry-frontier entries:
`NormLevel.isEquiv_wf` (L4L-02B) and `addDecl.WF` (L4L-19B), taking the exact
frontier from 20 to 22 without increasing the supported-root trust budget.
All local Lean/Lake/Nix, exact-axiom, and sorry-frontier gates pass. An isolated
ix v4.31 probe replayed the merged Lean4Lean modules and built ix's runtime
typechecker modules; the remaining failures are ix-owned Lean/Batteries proof
API migrations. Because L4L-01U is not an ix pin, that consumer migration is
deferred and does not block this checkpoint. The source and this completion
ledger are published to origin `jcb/induct`; neither master nor the digama
remote moved. This was an integration-only checkpoint: it added no
constructor-trace work.

**Active milestone: L4L-01C — retained constructor-validation trace.** Retain
the complete successful singleton `checkConstructors`
traversal as dependent, source-ordered operational evidence and prove exact
decomposition/recomposition while preserving phase-specific failures. This
checkpoint makes no Theory-WF claim; semantic interpretation remains L4L-01D.

The former generic-package milestone was not independently closable: its
requested view-WF conclusion depends on a semantic interpretation of
`checkInductiveTypes` and `checkConstructors`, while those proofs were assigned
to later validation milestones. Section 13 now decomposes that boundary into
L4L-01A through L4L-01E: consolidate staged inputs; derive family-validation
semantics and the post-family verified stage; retain the complete constructor
validation trace; interpret that trace as analyzer-owned view WF; and only
then close and migrate the produced-package theorem. The mandatory L4L-01U
upstream-reconciliation checkpoint is interposed between L4L-01B and L4L-01C
because upstream moved at that boundary; it does not combine or reorder the
five semantic deliverables. No checkpoint may claim
the strengthened theorem from bare `buildNormalizationCandidate` success.
Checked WF, raw/view identities, telescope/result/view-terminal equations,
constructor-pair order, per-position shape records, dependent-list alignment,
normalization equality, post-family WF, view telescopes, and terminal typing
remain generic consequences and must not return as final package premises. Do
not use erasure equality, unchecked `zip`, whole-Pi injectivity, a
caller-selected view, or a normalization oracle. Ix Pin A is complete:
the local ix `jcb/ix-formalization2` snapshot
`1f73f5c016907eadb8ed0dc86ac65b07eb24a145` pins Lean4Lean
`5e5bb767b3491d21a71908d4c58bcbaa007283bb`, builds the complete `IxTcVerify`
target, and reconciles the exact sorry and root-axiom audits. The complete
post-L4L-01E order is defined only by §13; the track labels below are
work-package references, not competing milestones. The independent 22-entry metatheory,
checker, projection, and trust work remains release work rather than evidence
that the inductive producer track is stalled.

**Baselines.** The current formalization source is the L4L-01U merge checkpoint
`7f864b459e4a6062b468d6e5416688feac0f9f99`, with parents
`da45b536220a3eff5ed78cf2f5afcf5e7491c40f`
(`feat: derive family validation staging`) and
`ef849dfbd94a` (`upstream/master`). This roadmap-only ledger child records that
immutable source hash without changing the formalization. The source follows
roadmap decomposition checkpoint
`f82ee77f7181`, generation-readiness source
`bbb45e0e950724cdbbd405d75e304e2020cecf82`, and its ledger child
`c4fd62b23a89500154b113d849d183afbf84907f`.
The earlier structural checkpoint derives exact checked family and
constructor shapes in Theory, types the inserted family constant once, derives
every checked constructor result target, recovers candidate view telescopes
from their exact terminals, and removes all fixture-supplied `viewTel` and
`rightType` fields. The analyzer-provenance checkpoint replaces fixture
normalization equalities with exact dependent analyzer-success equations,
derives the retained normalization in Theory, reconstructs post-family
environment WF in Verify, and removes all fixture-supplied `normalization_eq`
and `typeEnv_wf` fields. The generation-readiness checkpoint derives exact raw/check
family identity, normalized constructor pairing and order, raw
telescope/results, view terminals, and the complete dependent constructor list
from analysis plus minimal stored-spine/count shapes. That checkpoint
adds the complete executable hierarchy gate, retains it with exact ordinary
producer provenance, derives checked WF and every dependent shape record from
that one gate plus exact analysis and analyzer-owned view WF, and migrates all
three fixtures away from hand-built checked WF or per-position shape evidence.
It also pins missing- and extra-constructor rejection. Fixtures no longer name
normalized pairs or provide any component equation. The executable gate,
strengthened producer, and exact-success theorem have exactly the accepted
`propext`/`Classical.choice`/`Quot.sound` closure; semantic derivations inherit
only the already recorded checked-semantic closure. L4L-01A adds the staged
semantic-input owner and migrates all three positives without changing that
trust boundary or extracting its `Nonempty` result. L4L-01B interprets the
exact singleton family-validation run and derives the post-family stage from
the entry context, eliminating every independently verified post-family
fixture context while leaving constructor interpretation for L4L-01C/L4L-01D.
No new axiom or normalization oracle was added. On the v4.31 merge, the
154-job default Lake build, default Nix build, all six current-host flake
checks, all-system no-build flake evaluation, exact 22-entry sorry frontier,
29-declaration custom-axiom inventory, formatter, CLI replay, and whitespace
checks pass. Local `master` and
`origin/master` remain fixed at the prior candidate-context-provenance
checkpoint, `1fb7d6ef9042c5a80b2de9320c88ac0f3ce404cb`; only local
`jcb/induct` and `origin/jcb/induct` are published by this work. The live
digama `upstream/master` tip `ef849dfbd94a` is the merge's second parent and
was not modified by this branch. The published
development checkpoint contains a green Stage-3
generalized one-family port, two checked-analysis slices, E1 environment alignment, and a
completed bounded I2 recursive-Pi slice, plus the first explicit
normalization/definitional-equality boundary, its paired checked-block
slice, complete mixed-artifact preservation, the identity-normalization
public artifact switch, and one traced normalized Theory transaction with
identity and non-identity preservation fixtures, a normalized Verify
transaction trace, six actual-metadata Verify replays, and the first verified
WHNF-to-Theory normalization-certificate producer instantiated on both alias
cases. The executable side now also has the first generic candidate-view
traversal: `AddInductive.normalizeCandidateExpr` runs the ordinary checker
full check and WHNF at every inspected node, descends through Pi domains and
bodies under the exact annotation-consumed local declarations used by the
kernel, and retains every full checker context/input/result in a positionally
indexed trace with exact check, WHNF, and binder-domain `isDefEq` run
equalities. Raw binder syntax is preserved. A structural certificate records
whether `outParam`, `semiOutParam`, `optParam`, or `autoParam` was peeled, and
its executable result is checked against Lean's actual
`Expr.consumeTypeAnnotations` before the body context is extended.
Because that helper is an opaque partial definition with no usable equation
theorem, `CandidateTypeAnnotations` deliberately does not claim a
propositional equality to it. The producer rejects a runtime disagreement as
an implementation-consistency failure; Verify derives semantic authority only
from the structural peeling trace and the exact successful raw-to-consumed
`isDefEq` execution. This separates a useful executable cross-check from the
proof boundary and avoids a new axiom, native evaluator, or opaque-function
equation.
`buildNormalizationCandidate` stages family
normalization before raw family insertion and constructor normalization in
the post-family environment. `CandidateWhnfStep.innerRun` recovers the
state-bearing recursive execution erased by `M.run`, and
`WhnfRun.ofCandidateStep` converts a step to the existing Verify certificate
once strict translations are supplied. Candidate families and constructors
also retain exact full `checkType` observations, with the parallel
`CheckTypeRun.ofCandidateStep` adapter. The AliasFormer family WHNF plus its
family and post-family constructor full checks now use these adapters.
The trace tree itself is now recursively context- and source-indexed, so a Pi
child cannot be forged for a different raw domain, instantiated body, local
context, or fresh binder identifier.
`CandidateNodeRun` pairs each retained full check with its retained WHNF in one
verified context. `CandidateNodeRun.exists_ofCandidate` now obtains the
checker-returned inferred-type and WHNF-result translations directly from the
two verified executions once the matching context and root source translation
are known. `CandidateExprRun` recursively interprets those pairs into
`DefEqEvidence`, including Pi congruence under the exact raw free-variable
context and explicit type transport when a checker-inferred type is merely
definitionally equal to the structural sort; `source_tr` and `view_tr` prove
that both semantic endpoints translate the context/source-indexed kernel
syntax. AliasFormer's actual terminal trace now feeds this interpreter and
supplies its normalization and generation evidence. The current development
checkpoint constructs the verified candidate root from `VEnvs.WF`, extends
its exact `VContext`/`MLCtx` positionally at every retained Pi binder, proves
fresh-name reservation for a newly initialized checker state, and recursively
certifies arbitrary annotated-domain traces. The root full-check refinement
selects the strict source translation automatically from only the syntactic
free-variable condition; Pi result decomposition supplies child translations
and raw binder typing. At every Pi, `IsDefEqRun.ofCandidateStep` refines the
retained raw-to-consumed equality run to Theory `IsDefEqU`;
`CandidateExprRun` transports the strict body translation, typing evidence,
reconstructed-view translation, and Pi congruence between the raw,
annotation-consumed, and normalized binder contexts.
AliasFormer's actual candidate exercises that automatic root path without any
fixture-supplied Theory expression. `CandidateExprRootRun` now binds each
root trace to explicitly translated raw and exact candidate-view endpoints.
`CandidateConstructorListRun` folds constructor evidence positionally without
`zip` or truncation, and `NormalizationCandidateRun` accepts only a singleton
source-indexed family list and singleton raw Theory declaration, constructs
the corresponding `Normalization`, and assembles its `NormalizationRun`.
AliasFormer's real family and post-family constructor traces now flow through
that generic list boundary; its resulting view computes to the existing
checked alias view, and a truncated constructor view is rejected by
`normalization?` before dependent analysis or transaction construction.
The candidate boundary now continues through complete generation
certification. `CandidateExprTrace.storedSpine` requires WHNF to preserve the
raw emitted Pi spine while still permitting normalization inside binder
domains and the terminal result; `spineLength` records its exact length.
`CandidateExprRun.spineEvidence` recursively extracts raw/view binder
equality and terminal-result evidence from the same context-indexed checker
runs. `TelResultDefEqEvidence` packages those two components, supports exact
prefix replacement without forall injectivity, and preserves the induced raw
contexts. `CandidateFamilyGenerationRun`, `CandidateNormalizedCtorRun`, and
the dependent `CandidateNormalizedCtorListRun` align the extracted components
with the successful dependent analysis and forbid constructor truncation,
reordering, or evidence reuse. `GenerationCandidateRun` then assembles the
existing `GenerationRun` and `GenerationChecked.WF` certificates.
AliasFormer's actual non-identity family and constructor candidate runs now
exercise this complete generic assembler; its existing checked
`AddInductTrace`, final transaction, WF, and alignment replay consume the
result rather than a parallel hand-filled generation witness. Candidate
output remains untrusted unless this exact source-indexed run, stored-spine
condition, dependent analysis, and semantic assembly all succeed.
`AnnotatedPi.mk : ((p : outParam Prop) → AnnotatedPi) → AnnotatedPi` now closes
the missing recursive-Pi-plus-annotation vertical slice. Its exact ordinary
checker traces cover family and constructor full checks, WHNF of the retained
`outParam Prop` domain, the complete lazy-delta `isDefEq` path to `Prop`, and
the recursively extended raw/consumed binder contexts. Those runs assemble a
nonempty nested-Pi `NormalizationCandidateRun`,
`GenerationCandidateRun`, and `GenerationChecked.WF`; the resulting checked
`AddInductTrace` replays the final environment, generated recursor, and iota
rule while preserving the raw annotated binder in emitted metadata. A staged
whole-candidate negative reuses that exact metadata with a correctly typed but
opaque `outParam`; it reaches candidate traversal and is rejected at the
raw-to-consumed binder equality boundary.

The published certified-consumer slice adds the proof-carrying boundary
needed by ix without pretending that executable metadata production is already
fully certified. Theory's `GenerationCertificate source env` couples one exact
`GenerationChecked source` with its `GenerationChecked.WF env` proof, and
`VEnv.addInductCertified` erases the proof and computes through the existing
`addInductGeneration` transaction. Its trace, atomicity, and `Ordered`
preservation theorems stay wholly in Theory. Verify's dependent
`GenerationCandidatePackage` binds the exact kernel source, source-indexed
candidate, normalization run, dependent generation result, and
`GenerationCandidateRun`; `.certificate` is the only erasure into the Theory
API, while `.addInductTrace` forces metadata replay to use the generation and
WF proof owned by that package. AliasFormer and AnnotatedPi both exercise this
public non-identity path and retain exact axiom guards. The separate
`ProducedGenerationCandidatePackage` records the stronger outer equation that
`buildNormalizationCandidate` produced the packaged candidate. AliasFormer and
AnnotatedPi now inhabit this layer with exact successful whole-call equations
in their real pre-family and post-family environments, and both Theory
certificates and Verify metadata replays project from their produced packages.
General construction for an arbitrary successful metadata call remains open.
Arbitrary-length source-indexed operational list assembly and automatic
semantic-hierarchy assembly from verified per-position inputs are complete, so
the missing work is deriving those inputs plus structural generation alignment
and the terminal package from the outer success, followed by producer breadth;
another transaction API is not needed.
The next positive outer fixture is now complete. `AddInductive.hasIndOcc` is a
transparent structural traversal, so recursion and positivity branches reduce
in exact producer theorems without a new opaque-traversal contract. AnnotatedPi
has exact equations for singleton family validation, name freshness,
recursive-occurrence detection, raw-family declaration, constructor
validation, annotation consumption, nested-Π candidate traversal, dependent
candidate-list assembly, and the complete successful whole call. Its Theory
certificate and Verify replay now project from
`annotatedPiProducedGenerationCandidatePackage`.
`VInductDecl.checked?` returns a dependent, data-bearing `Checked`
descriptor. `stage3` and the public `VEnv.addInduct` compatibility entry point
still begin with raw-normal-form acceptance analysis. Verify's
`AddInductTrace`, however, now retains the exact `GenerationChecked decl` and
its `GenerationChecked.WF` certificate and proves the same
`VEnv.addInductGeneration` transaction used by explicit views;
`VDecl.WF.induct` records that normalized transaction in environment histories.
The public identity-path preservation proof constructs the canonical
`GenerationChecked.WF` bridge and delegates to it. The public `Checked` motive, minors,
recursor, and rules now delegate to its canonical identity
`GenerationChecked`, so artifact construction has one mixed implementation
even before the transaction accepts a non-identity normalization. The
descriptor records normalized parameter and
index telescopes, result level, elimination mode, generated names, constructor
fields, and recursive arguments including Pi-binder telescopes and terminal
index spines. Its environment-free analysis rejects loose metadata, duplicate
generated names, invalid universe annotations anywhere in family or
constructor metadata, self-reference in the family telescope, malformed
result heads/spines, parameter-count errors, and
declaration/type/constructor universe-count mismatches. `Checked.WF env` adds
the semantic telescope, recursive-target, field, and result-spine obligations
over the input environment, is equivalent to the legacy `VInductDecl.WF env`
when paired with the exact analyzer result, and is what `VEnv.addInduct_WF`
converts to the normalized generation certificate. Its non-recursive-field
universe obligation now states Lean's
impredicative Prop exception explicitly: `l = .zero ∨ u ≤ l`.

The normalization audit ruled out the tempting assumption that translated
kernel metadata is already in the syntax expected by `checked?`. Lean retains
reducible aliases in real `InductiveType.type` and constructor types:
`AliasFormer` stores the alias `TypeFamilyAlias` instead of its sort WHNF, and
`AliasRec.mk` stores `RecAlias AliasRec` instead of the direct recursive
target. The fork now has a named `Normalization source` with a
shape-preserving analysis `view`, `Normalization.checked?`, and a semantic
`Normalization.WF env` contract. The contract relates the raw and view family
types before insertion and their constructor types after insertion of the raw
family constant. `NormalizedChecked source` now retains the singleton raw
family, the normalization, the dependent checked view, and the exact analyzer
equation in one value. Structural theorems recover source/view arities and
ordered family/constructor headers; identity normalization computes back to
the legacy analyzer. `GenerationChecked` adds an executable outer-telescope
layout certificate and ordered raw/checked constructor pairs. Its additive
mixed motive/minor/recursor/rule definitions emit raw parameter, index, and
constructor-field binders while consulting the checked view for recursive
arguments and result indices. Identity specialization reduces exactly for
Nat, Eq, `IndexedVec`, and `Acc`; both alias recursors and iota rules reduce
exactly to Lean's kernel metadata, including preservation of the raw
`RecAlias AliasRec` minor binder. `VEnv.TelDefEq` now states pointwise
raw/view binder equality in the context generated by the earlier raw binders,
and constructs the corresponding Theory context equality without using the
unfinished `forall`-injectivity theorem. The strengthened
`GenerationChecked.WF` is staged: it certifies the raw family telescope and
result before family insertion, then certifies both the exact stored
constructor telescope and the raw family/field telescope emitted by artifacts
after insertion. Generic lemmas prove the raw family and every paired raw
constructor insertion-ready from that certificate. `GenerationEnv` proves the
mixed motive, every paired minor, the complete minor telescope, the recursor
type and recursor constant, each rule component, every generated iota rule,
and the ordered full rule fold well formed. The minor/rule lists have exact
length and positional lookup facts, so no proof silently relies on `zip`
truncation. Exact guards pin the mixed transport, minor, recursor, rule, and
fold roots to subsets of `[propext, Classical.choice, Quot.sound]`.
`Checked.identityGeneration` constructs the canonical identity block from any
retained analyzer witness; generic theorems show that all four public artifacts
equal the legacy identity-normal forms, and Nat, Eq, `IndexedVec`, and `Acc`
check those equalities by reduction. Both alias examples still construct the
granular certificate explicitly and retain exact `[propext, Quot.sound]`
guards. `Checked.WF.identityGeneration` supplies the ordered semantic bridge
for the compatibility path. `AddInductSuccess` and `addInduct_WF` now project
from the normalized trace/preservation theorem rather than reconstructing the
legacy `Stage3Env` transaction. `AliasFormer` and `AliasRec` execute that core
directly: their final environments preserve exact raw family and constructor
payloads, contain the kernel recursor and every generated rule, grow their
inputs, and are `Ordered`, with exact axiom guards.

Verify now has the first checked normalization producer rather than only
hand-written Theory equality witnesses. `TypeChecker.WhnfRun` packages an
exact `Inner.whnf'` execution, its well-formed checker state, and strict
translations of the input and result; the existing checker-refinement theorem
turns that execution into an ordinary Theory definitional equality.
`TypeChecker.CheckTypeRun` similarly packages an exact full
`Inner.inferType _ false` execution and identifies the verified existential
result with named strict translations; it exposes both `HasType` and
sort-valued `IsType` consequences, including the case where the inferred type
must itself be normalized by a `WhnfRun`.
`TypeChecker.DefEqEvidence` composes reflexivity, WHNF, application, beta,
transitivity, and forall congruence without adding a normalization oracle.
`TypeChecker.TelDefEqEvidence` extends that evidence pointwise through raw
binder contexts. `VInductDecl.NormalizedCtorRun` and `GenerationRun` assemble
the declared/emitted constructor paths, exact post-family insertion state, and
complete `GenerationChecked.WF`; their interpretation roots are exactly
guarded.
`VInductDecl.NormalizationRun` stages the family comparison in the input
environment and constructor comparisons in the exact environment obtained by
inserting the raw family, and `.wf` constructs `Normalization.WF`. The
actual-metadata `AliasFormer` fixture runs WHNF on `TypeFamilyAlias`; the
`AliasRec` fixture runs WHNF on `RecAlias.{1}` and composes application, beta,
transitivity, and outer-forall congruence. `AliasFormer` also executes
`inferType (.const ``TypeFamilyAlias []) false` to obtain its family-is-a-type
premise and executes a second full check on the actual `AliasFormer.mk` type in
the exact post-family environment. That constructor check returns the retained
`TypeFamilyAlias`; the verified WHNF certificate turns it into the required
sort. `AliasRec` now likewise executes a full check on the actual raw
`RecAlias AliasRec` field in the exact post-family environment; its field
certificate uses that checked typing premise and composes the verified
`RecAlias` WHNF, application, and beta steps. Neither checked normalization
proof now borrows typing from the older hand-built generation certificate.
Both fixtures instantiate the generic
`GenerationRun` assembler to obtain complete checked
`NormalizedChecked.WF` and `GenerationChecked.WF` roots and inject those roots
into dedicated data-bearing `AddInductTrace`/`TrEnv'` replays. Every
operational, semantic, block, generation, and checked-trace boundary has an
exact axiom guard.

The remaining parity boundary is now generalization of the outer executable
producer, not the consumer transaction. `stage3` and `VEnv.addInduct` remain
the raw-normal-form compatibility path and therefore still reject the raw
alias declarations.
`VEnv.addInductCertified`, however, accepts any source-indexed Theory
generation certificate; its proof is erased, and generic trace/atomic/WF facts
show that it is exactly the normalized transaction already proved sound.
Verify packages candidate provenance, dependent analysis, semantic assembly,
and checked metadata replay without allowing an unrelated generation witness,
and AliasFormer, AnnotatedPi, and `IndexedVec` reach the public certified
transaction through packages selected by exact whole
`buildNormalizationCandidate` calls: family validation, raw-family
declaration, constructor validation, recursive candidate traversal, and
dependent candidate-list assembly all run in the same retained contexts. What
is not yet generic is deriving such a package from every arbitrary successful
metadata call. The executable family-type, ordered-constructor, and complete
family traversals now have arbitrary-length dependent `Produced` witnesses,
and all three fixtures delegate their list equations to those generic
theorems. `GenerationCandidateRun.producedPackage` also provides the generic
outer singleton constructor once the exact semantic run exists.
`CandidateExprSemanticRootInput` and the dependent semantic input hierarchy now
invoke that retained interpreter at every exact source position. Combined with
the operational list witnesses, `.exists_ofProduced` returns the complete
source-ordered semantic hierarchy under `Nonempty`. The corresponding semantic
generation owners project every family and constructor spine from the same
value, and all three fixtures route package construction through those
projections. What remains generic is deriving the structural generation
alignment and verified inputs from the successful dependent analyzer/outer
producer itself, then returning a complete produced generation package without
fixture-supplied equations. The opaque-`outParam` whole-candidate rejection and
the reordered-`IndexedVec` view rejection remain the negative gates. The
identity API stays as a compatibility wrapper until kernel parity and
downstream migration are green.

The bounded recursive-Pi convergence slice is coherent and green.
`recTarget?`/`recArg?` recognize a family target below a strictly positive Pi
telescope; `minorTypeRec`, `recConstRec`, `ruleCall`, `ruleRec`, and `rulesRec`
generate functional induction hypotheses and lambda-wrapped recursive calls;
and the exact `Acc.rec` type and iota RHS reduce by `rfl` to those generalized
artifacts. The semantic proof chain now closes through normalization and
list-level application of every functional induction hypothesis,
`minorAppRec_hasType`, `recRuleAppRec_hasType`, `ruleRec_WF`, and the generated
rule fold in `addInduct_WF`. `Checked.minorTypes`, `Checked.recursor`,
`Checked.generatedRules`, `VEnv.addInduct`, and `AddInductSuccess` all select
the generalized artifacts. Public `Acc` checking, transaction consequences,
`Ordered` preservation, and actual-kernel-metadata E1 replay are green. This
closes the planned recursive-Pi widening, but not L4L-07: WHNF/definitional-equality
parity, full positivity, small elimination, K behavior, and the complete
one-family differential matrix remain.

The complete checkpoint gate was rerun on 2026-08-02 over parent `d553930a`
plus the complete `IndexedVec` semantic replay, now published at `cf3d5a47`.
The 124-job
`lake build Lean4Lean.Theory Lean4Lean.Verify`, exact 20-entry sorry audit,
focused `IndexedVecSemanticReplay` build, default `nix build`, all-system no-build
evaluation, and current-host `nix flake check` are green. The host flake check
builds the proof library, sorry frontier, downstream consumer, and all three
CLI checks. The two public semantic-package/E1 roots have exact compile-time
axiom guards. Formatter, diff, and import-boundary gates also pass.

Two successive checkpoints move the outer family validator beyond the former
zero-parameter/immediate-sort seam. Revision `9a865ea02d4326e60d0e5fd663d6efe79c735b1c`
adds a generic, source-indexed replay theorem for any singleton candidate
family spine, computing the exact parameter expressions, index count,
terminal local context, result universe, and emitted family constant selected
by `checkInductiveTypes`. Revision
`a62736281ea419d7d0ee13d76f0e0fd9a4d9d90f` instantiates that theorem on
Lean's real universe-polymorphic `IndexedVec` family (`α : Type u`, index
`Nat`, result `Type u`). It proves the actual full `checkType`, WHNF, binder
domain `isDefEq`, fresh-local, annotation, `buildCandidateExpr`, and complete
family-validation executions. The candidate computes with spine length two,
parameter vector containing the first fresh local, index-count vector `#[1]`,
result level `u + 1`, and family constant `IndexedVec.{u}`. The proof retains
the checker-produced `mkLevelIMax'` expression instead of assuming an opaque
reduction equation. No new axiom declaration, native evaluator, or
fixture-specific normalization principle was added. The next exact slice was
the post-family `IndexedVec.nil`/`IndexedVec.cons` constructor validation and
ordered dependent-list assembly; this historical checkpoint did not yet claim
a whole executable `IndexedVec` result.

Revision `f0d80f8ba21e44a694566ea3d6469be85a809307` adds an early
`Expr.eqv` success path to `TypeChecker.Inner.isDefEq`. The verifier transports
the strict source translation across the existing expression-equivalence
lemma and derives the same `IsDefEqU` result, while the executable run returns
without consulting or mutating `EquivManager`. Existing exact-state fixtures
now assert that stronger behavior; the old reflexivity-specific manager
simulations were deleted. Non-reflexive comparisons still traverse
`isDefEqCore` and add a successful equivalence exactly as before. This is a
sound checker simplification, not a new axiom or normalization assumption, and
it is the reusable state-stability fact needed by exact `IndexedVec.nil` and
`IndexedVec.cons` application traces.

Five later published checkpoints close that executable boundary. Revisions
`6732659058fe770e2b768ffaeb10d147ef1f466b` and
`c40a471dce8403d236284e3e10c85e7b84281a56` certify the exact `nil` and `cons`
constructor candidates in the post-family environment;
`c739d412302da94a962fb986ff0f380962692df3` stabilizes their candidate-context
provenance; and `82f4a54cf38d1ca510cdb05fcc1c4af4c5e3737a` proves that the complete
one-parameter, one-index, two-constructor request returns the exact retained
`IndexedVec` normalization candidate. Revision
`d553930affdb3690ad43fbf9acddf68d476fe260` adds the generic recursive
identity-normalization interpreter needed to keep caller-selected Theory
endpoints through those traces. Revision
`cf3d5a47d35867e0e6ebe023c0803982e3e36cd1` instantiates identity witnesses
for the family, `nil`, and `cons`, converts identity root runs into
generation-ready spine evidence, and uses `IndexedVecSemanticReplay` to
assemble the complete `GenerationCandidatePackage`, certified Theory
transaction, and checked E1 replay. Both public roots have exact guards and the
complete checkpoint gate passes.

The exact CI evaluation command
`nix flake check --all-systems --no-build --accept-flake-config` is also green.
Its earlier `path '*-source' is not valid` failure was reproducible: the nested
`fileset.toSource` used for `leanSrc` could be demanded during evaluation
before that store path was realized. The flake now reuses the lazy
`inputs.self.outPath`, which restores app and check evaluation on all four
declared systems. The tradeoff is broader source invalidation, so restoring a
narrow *evaluation-safe* source filter remains packaging optimization debt.
The non-fatal `system` to `stdenv.hostPlatform.system` warning remains in the
pinned Nix dependency stack. Actual Linux and Darwin builds are still supplied
by their platform CI jobs; cross-system evaluation is no longer the blocker.
Descriptor invariants, semantic compatibility and normalization witnesses,
Theory and Verify transaction APIs, and the environment-WF roots retain exact
compile-time axiom-closure guards.

The executable-candidate checkpoint at
`bc37d436dfd6f7d6fa1ae186c0951e48677b931f` passed the same complete local
gate on 2026-08-01. It proves AliasFormer's exact successful whole producer,
constructs `aliasFormerProducedGenerationCandidatePackage`, and routes both
the certified Theory transaction and checked Verify replay through it. Exact
guards at that pre-v4.31 checkpoint exposed the additional
`Expr.hasExprMVar_eq`, `Expr.hasLevelMVar_eq`, and `Expr.hasFVar_eq` cache
contracts reached while checking closed constructor constants; L4L-01U later
proves those properties and removes their axiom declarations. No native
evaluator or assumed normalization equation was added. Only `origin/jcb/induct` moved;
both master refs and every digama/upstream ref remain unchanged.
The core E1 Verify path is no longer
vacuous: typed witnesses align kernel `ConstMap` insertions with Theory
constants and rules, and the `TrEnv'` inductive case is live. The concrete
replay layer quotes Lean's actual Nat, Eq, index-changing `IndexedVec`, and
recursive-Pi `Acc` metadata plus the actual alias definitions and metadata for
`AliasFormer` and `AliasRec`. It drives all six complete
metadata-to-normalized-Theory transactions and proves that an older
value-bearing definition remains translatable through the Nat transaction.
Every quoted kernel rule RHS is pinned to the generated Theory rule by
definitional equality. The alias replays additionally pin raw source/view
separation, exact raw binders, final environment equality, WF, alignment, and
family/constructor/recursor lookup uniqueness.

**Ix companion.** `~/projects/ix/plans/lean4lean-upstream-gaps.md` (the file
named `lean4lea-upstream-gaps.md` in the request has a one-character typo) is
the 2026-07-29 demand-side analysis. Keep its A1-A7 and P1-P4 identifiers for
cross-repo discussion. Its fork status and M0-M5 progress are now stale, so
this later audit wins on current state and sequencing; the companion remains
authoritative for the shape of ix's consumer obligations.

**Versioning note.** `plans/roadmap.md` is intentionally unignored and tracked
so the sole status-bearing L4L ladder travels with each checkpoint. Other files
under `/plans` remain ignored. The root-level `upstream-divergence.md` remains
the tracked per-delta ledger; it complements this roadmap rather than replacing
its milestone state.

---

## 1. Mission and exact meaning of “complete”

Lean4Lean has two products:

1. `Lean4Lean/Theory/`: an implementation-independent model of Lean's kernel
   language, typing, definitional equality, environment growth, and the
   metatheory needed to use that model safely.
2. `Lean4Lean/Verify/`: a proof that the executable checker over `Lean.Expr`
   refines Theory.

Ix is the first demanding external consumer. Its `Ix/Tc/Verify/` development
translates content-addressed `KExpr` into the same Theory and proves the Ix.Tc
checker sound there. Success therefore means more than deleting the original
three inductive sorries.

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
- **Checker refinement:** the six remaining Level/TypeChecker proof roots are
  proved, including recursor reduction, projection inference/reduction,
  structure eta, and unit-like comparison.
- **Trust is explicit:** all final roots have an audited `#print axioms`
  closure. No bridge axiom known to be false for the pinned Lean toolchain is
  reachable. Any unavoidable runtime contracts (for example pointer equality
  or opaque C++ implementations) are narrowly stated, tested, documented, and
  separated from the mathematical Theory.
- **Ix is enabled:** ix pins a published revision, imports only
  `Lean4Lean.Theory.*`, constructs `InductiveOracle` from checked blocks,
  obtains a concrete `TrProjOK`, derives literal well-formedness from its
  prelude contract, and removes the corresponding upstream sorry origins from
  its executable audit manifests. `NativeOracle` remains an explicit ix trust
  boundary by design, not a lean4lean proof hole.
- **Upstreamability:** the fork delta is split into reviewable PRs, every
  deliberate divergence is tracked, and both repositories build at each pin
  boundary.

This definition deliberately separates **proof-complete** (no sorries or
fake relations) from **trust-minimal** (no unnecessary custom axioms). Both are
required for the final release; they can be reached in separate milestones.

## 2. Audited current state

### 2.1 What has landed on the green baseline

The old gap plan started at `0c38ab8`, where `VInductDecl.WF`,
`VEnv.addInduct`, and `VEnv.addInduct_WF` were all sorries. That is no longer
the fork's state.

- The sorry-frontier audit and Nix CI are tracked. The audit currently accepts
  exactly 22 live sorries and excludes `Experimental/`; the two v4.31 additions
  are classified under L4L-02B and L4L-19B. The exact CI all-system evaluation
  command is green on the L4L-01U source;
  the remaining `system` deprecation warning comes from the pinned Nix stack
  and is non-fatal.
- Stage 1 introduced real computational recursor/iota generation for a single,
  parameter-free, non-indexed type and proved `addInduct_WF`.
- Stage 2, at `efb2a2b2`, supports any number of parameters for one
  non-indexed type with direct recursive fields in a syntactically never-zero
  sort. `addInduct_WF` is sorry-free for that class.
- Nat, Bool, List, Prod, and Option fixtures compare generated recursor types
  and rules definitionally with the actual kernel declarations.
- The current Stage-3 development branch extends that proof to one generalized
  family, including subsingleton large elimination, indexed recursive calls,
  constructor-result spines, and recursive targets below Pi telescopes. Eq,
  HEq, `IndexedVec`, and `Acc` compare generated recursors and/or iota rules
  definitionally with Lean's kernel declarations.
- The fork also contains the `0c38ab8` kernel soundness fix and the Nix
  downstream-consumer artifact work. Ix Pin A now pins the certificate-bearing
  fork revision `5e5bb767` instead of upstream `8865b155`; its complete
  `IxTcVerify` target and exact trust audits consume the proved normalized
  generation/certificate boundary and remove the three former inductive
  `sorryAx` origins.

### 2.2 Green Stage-3/I1/E1, recursive Pi, and mixed-preservation frontier

The Stage-3/I1 and current I2 implementation spans `Theory/Inductive.lean`,
`Theory/InductiveFixtures.lean`, `Theory/Typing/InductiveLemmas.lean`, and a
small generic environment extension in `Theory/Typing/Lemmas.lean`. E1 also
changes `Verify/Typing/Lemmas.lean`, `Verify/Environment/Basic.lean`, and
`Verify/Environment/Lemmas.lean`, and adds
`Verify/Environment/InductiveFixtures.lean`; the sorry-frontier wording is
updated. Relative to current common ancestor `8865b155`, source checkpoint
`da45b536` changes 33 files with 45,662 insertions and 66 deletions. Its direct
tree diff against the now-diverged `upstream/master` changes 68 files with
46,136 insertions and 1,097 deletions. Use per-checkpoint diffs, rather than
either accumulated total, for review sizing.

The development branch contains:

- parameter-and-index spines (`SpineWF`, `recPairs`, indexed motives and
  minors);
- a single-family Stage-3 guard with a syntactic subsingleton/large-elimination
  test;
- a dependent `VInductDecl.Checked` result and `checked?` analyzer. The public
  Stage-3 Boolean is now descriptor existence rather than an independent pass;
  public `addInduct` and its success/WF proofs unwrap the same checked value and
  specialize it to identity normalization. Verify's `AddInductTrace` has moved
  to the more general exact `GenerationChecked decl` plus
  `GenerationChecked.WF` certificate;
- an explicit `Normalization source` boundary separating raw stored metadata
  from the view inspected by the analyzer. `normalizationShape` fixes universe
  arity, parameter count, family/constructor identities, order, and counts
  while allowing expression payloads to change. `Normalization.WF env` requires
  family-type defeq in the input environment and pairwise constructor-type
  defeq after the raw family constant is inserted. This semantic staging is
  intentionally one-family; I3 must generalize it to insertion of every family
  constant in a mutual block;
- a dependent `NormalizedChecked source` boundary value built by
  `Normalization.check?`, `normalizedChecked?`, or the identity compatibility
  analyzer. It retains `sourceType` and its singleton equation alongside the
  normalization, the exact `norm.view.Checked`, and the analyzer equation that
  produced it. `Normalization.shape` exposes source/view universe arity,
  parameter count, and ordered family/constructor header agreement;
  `NormalizedChecked.source_anatomy` specializes that agreement to the raw
  singleton family and checked singleton view. Identity normalization has a
  computational Nat fixture and an `isSome` compatibility theorem.
  `Checked.analyzer_eq`, `identityBlock`, and `identityGeneration` now package
  any retained identity analyzer witness without re-running or choosing a
  second result. The legacy `addInduct` transaction remains an identity-only
  compatibility wrapper, but its semantic bridge and preservation proof now
  run through this boundary and the live `Checked` artifact accessors have
  moved here. The additive `GenerationCertificate`/`addInductCertified` API
  accepts a semantically certified non-identity generation without exposing
  Verify state or changing that compatibility behavior;
- a `GenerationChecked source` layout gate and mixed artifact layer.
  `generationShape` checks raw parameter/index arity, constructor coverage,
  header agreement, raw constructor parameter count, and raw/view field-count
  alignment. `GenerationChecked.shape`, `rawCtors_eq`, and `viewCtors_eq`
  expose those facts without downstream zipping or truncation. Mixed
  parameters, indices, motives, minors, recursors, and rules retain raw binder
  syntax and use only retained view descriptors for recursive classification
  and result indices; no mixed helper re-runs `recArg?` on raw metadata.
  Identity fixtures for Nat, Eq, `IndexedVec`, and `Acc` reduce to the existing
  artifacts. Both alias cases reduce to the actual kernel recursor and rule;
  the `AliasRec` fixture separately pins the raw alias as the emitted minor
  binder. `VEnv.TelDefEq` records binder-by-binder raw/view equality under the
  preceding raw binders and exposes raw-telescope well-formedness, universe
  instantiation, and an `IsDefEqCtx` bridge. `GenerationChecked.WF` now carries
  the pre-family family telescope/result and, after exact raw family insertion,
  both the constructor's stored raw telescope/result and the raw
  family/field telescope/result emitted in mixed artifacts. The two paths are
  intentionally separate so definitionally equal constructor parameters need
  not be syntactically identical. Generic guarded lemmas derive raw family and
  constructor `IsType` facts from this granular contract without `forall`
  injectivity. Both alias fixtures construct it at the standard Theory
  closure. The mixed preservation layer now proves the motive, exact raw
  constructor application under the mixed telescope, every individual minor,
  the complete constructor-aligned minor telescope, the recursor type and
  constant, every rule application and rule, and the complete ordered rule
  fold well formed. Supporting length/lookup lemmas preserve constructor
  position, and `familyApp_transport` supplies the common
  insertion/weakening step. Exact compile-time guards cover every stabilized
  mixed root. The public `Checked` motive/minor/recursor/rule accessors are
  identity specializations of this implementation; generic compatibility
  theorems recover the old identity forms, and Nat/Eq/`IndexedVec`/`Acc`
  compare all four accessors by `rfl`. The additive artifact refactor is
  closed. A single `VEnv.addInductGeneration` transaction now inserts the raw
  family and constructors and the mixed recursor/rules; its data-bearing
  `AddInductGenerationTrace` is exposed axiom-minimally through `Nonempty`,
  with freshness, lookup, membership, monotonicity, atomicity, and normalized
  `Ordered` preservation theorems. The raw public `addInduct` entry point is
  an exact identity-normalization wrapper around that core. The proof-carrying
  public `addInductCertified` entry point is an equally exact wrapper around
  the same core: its certificate owns `generation` and `generation.WF env`,
  but only `generation` affects computation. Generic trace, atomicity, and WF
  theorems give ix a Theory-only non-identity consumer boundary.
  `Checked.WF.identityGeneration` now constructs its semantic certificate
  through a post-family invariant, and the legacy public success/WF
  certificates delegate to the normalized trace and preservation theorem.
  The redundant `Stage3Env` transaction proof has been removed;
- actual-metadata alias fixtures proving that normalization is necessary, not
  hypothetical. `AliasFormer` retains a reducible alias at the family result
  and `AliasRec.mk` retains one around a recursive field. Their raw declarations
  fail `checked?`, their explicit views compute to accepted descriptors, and
  their `Normalization.WF` proofs derive the required delta/application/beta
  equalities in Theory. Exact guards pin both roots to `propext` and
  `Quot.sound`. Each fixture now also constructs a `NormalizedChecked` block
  and proves its combined `NormalizedChecked.WF` certificate at the same exact
  axiom closure. The normalized transaction is now live and preserves raw
  constants and kernel-shaped generated binders while pairing them
  constructor-by-constructor with normalized analysis facts. Direct
  `AliasFormer`/`AliasRec` transactions now pin exact raw payloads, kernel
  recursors and iota rules, all lookup/membership consequences, monotonicity,
  and final `Ordered`, while their raw `checked? = none` regressions remain.
  Verify ingestion and actual-metadata replay are now complete for both aliases:
  the trace consumes the same certified generation as Theory, preserves the
  actual raw `ConstantInfo` payloads, and proves final equality, WF, alignment,
  and lookup uniqueness. The public identity wrapper still rejects their raw
  declarations, as intended. The checked producer now derives each fixed
  fixture's normalization equality from an exact verified WHNF run and
  compositional defeq evidence. A generic `CheckTypeRun` derives named Theory
  typing consequences from exact full-check executions; `AliasFormer` uses it
  for both the raw family and actual constructor premises, with the latter
  staged after family insertion, while `AliasRec` uses it for the actual raw
  recursive field in that same exact post-family state. Both aliases now
  assemble complete checked block
  and `GenerationChecked.WF` roots through the generic
  `TelDefEqEvidence`/`NormalizedCtorRun`/`GenerationRun` layer, without
  bootstrapping from the older hand-built generation-WF proofs. Dedicated
  checked traces carry those certificates through `TrEnv'` to final
  WF/alignment. `AddInductive.normalizeCandidateExpr` now supplies the first
  generic executable metadata-to-candidate traversal: it uses the checker's
  configured full check, WHNF, and inductive fuel; recursively exposes Pi
  domains while checking bodies under structurally certified
  annotation-consumed local declarations; preserves raw metadata headers; and
  retains exact full-check, WHNF, and binder-equality runs at every applicable
  position.
  `buildNormalizationCandidate` repeats the existing family/constructor
  validity checks, normalizes families in the input environment, inserts the
  raw families, and only then normalizes constructor payloads. An exact
  `AliasFormer` leaf regression pins this traversal to the already verified
  checker WHNF run and guards its operational axiom closure.
  `CandidateWhnfStep.innerRun`/`WhnfRun.ofCandidateStep` and the parallel
  full-check adapters now bridge stored `M.run` equalities to state-bearing
  Verify certificates once translations are provided. Every family,
  constructor, Pi domain, and instantiated body retains its full check in the
  exact pre-/post-family and raw-local context; the AliasFormer semantic WHNF,
  family check, and constructor check all use this route. Matching verified
  contexts and translations are now constructed recursively for every retained
  position, and generic spine/result extraction plus dependent constructor-list
  assembly produce `GenerationChecked.WF`. `GenerationCandidatePackage`
  retains those exact dependent indices, erases to a Theory
  `GenerationCertificate`, and builds a checked `AddInductTrace` whose
  generation cannot be unrelated to the package. AliasFormer and AnnotatedPi
  both run through `addInductCertified`, prove exact successful whole
  `buildNormalizationCandidate` equations, inhabit the stronger
  `ProducedGenerationCandidatePackage`, and route their Theory and Verify
  consumers through those values. `IndexedVec` now supplies the next exact
  executable result: its parameter/index family and ordered two-constructor
  list reduce through the complete outer producer to the retained candidate.
  The published `cf3d5a47` checkpoint carries that exact value through semantic
  generation/package assembly and E1 replay. What remains is generalization
  beyond the three fixture-specific successful calls;
- normalized descriptor data for parameters, indices, result universe,
  elimination mode, generated names, constructors, and recursive arguments.
  `RecArg` now records a possibly nonempty Pi-binder telescope, field position,
  terminal index spine, and the target-family slot reserved for I3. The current
  one-family analyzer populates the binder telescope and still fixes
  `targetType = 0`;
- exact closed-metadata, complete universe-annotation range, family-telescope
  self-reference, direct result-shape, and internal generated-name `Nodup`
  checks. Their proof API includes `Checked.analysis_accepted`,
  `type_closed`/`ctor_closed`, `type_levelWF`/`ctor_levelWF`, `names_nodup`, and
  `direct_anatomy`, so consumers do not unfold the analyzer. Environment-relative
  name freshness remains correctly enforced by the transactional `addConst`
  chain and exposed by `AddInductSuccess`;
- an environment-indexed `Checked.WF env` contract over the normalized
  parameter/index telescope and each constructor's field/result spine, with
  `Checked.wf_of_decl`, `Checked.to_declWF`, and
  `VInductDecl.wf_iff_exists_checked` proving exact compatibility with the
  legacy declaration-level `WF`. The preservation theorem now obtains its
  semantic premises through this descriptor contract rather than destructing
  the raw declaration relation. Its field-universe condition explicitly
  models Lean's impredicative Prop exception (`l = .zero ∨ u ≤ l`), which is
  required by `Acc : Prop` while preserving the bound for non-Prop families;
- computed positive descriptor-shape fixtures for Nat, Eq, and `IndexedVec`, and
  a computed negative matrix covering duplicate/internal generated-name
  aliases, loose variables, self-reference in parameter domains, invalid
  universe annotations in family and constructor fields, non-sort family
  results, wrong constructor heads and parameter spines, excessive `nparams`,
  family/constructor universe-count mismatches, illegal recursive-Pi domains,
  changed recursive-target parameters, family occurrences in recursive target
  indices, and pre-existing type, constructor, and recursor names. The three
  recursive-Pi cases have exact kernel `#guard_msgs` comparisons, and every
  case is rejected before any partial environment is observable;
- public generalized recursor and iota generation for direct indexed recursion
  and recursive arguments below Pi telescopes: functional minor IHs,
  generalized recursor types, lambda-valued recursive calls, and generalized
  iota rules. Exact computational fixtures match `Acc.rec` and its rule after
  universe permutation. The older direct definitions remain only as
  specialization/reference code; no public `Checked` accessor or transaction
  selects them;
- a closed generalized semantic chain through recursive-target transport,
  `minorTypeRec`/`recTypeRec` well-formedness, recursor application, rule
  binders/type, recursive-call normalization, list-level application of all
  functional IHs, `minorAppRec_hasType`, `recRuleAppRec_hasType`,
  `ruleRec_WF`, and the generalized generated-rule fold in `addInduct_WF`;
- Eq, HEq, and index-changing `IndexedVec` kernel-equality fixtures;
- a complete indexed environment invariant, recursor typing proof, constructor
  fold, indexed iota LHS/RHS proofs, rule well-formedness proof, and final
  `addInduct_WF`;
- `#guard_msgs` axiom checks proving that the checked-analysis and semantic
  compatibility roots depend only on `propext` and `Quot.sound`, while the
  recursive-Pi typing/preservation roots and `VEnv.addInduct_WF` depend only
  on those plus `Classical.choice`;
- an `AddInductSuccess` transaction certificate plus `addInduct_le`, freshness,
  type/constructor/recursor lookup, generated-rule membership, atomicity, and
  early-rejection theorems for downstream consumers. The certificate now also
  retains the exact `checked? = some checked` result, so ix-facing consumers
  need not re-run analysis after a successful transaction;
- `AddInductConstant`, `AddInductConstants`, and `AddDefEqs` witnesses in
  Verify, with fold realization, lookup, freshness, monotonicity, map-WF, and
  value-preservation lemmas;
- a real `AddInduct` transaction aligning `inductInfo`, ordered `ctorInfo`s,
  `recInfo`, and generated iota rules; real proofs of
  `AddInduct.to_addInduct`, `AddInduct.le`, and `Aligned.addInduct`; and a live
  `TrEnv'.of_value` inductive case;
- compile-time axiom-closure guards for the new Verify bridge roots. They
  intentionally expose the inherited `TrProj` `sorryAx` until Track P closes
  it; they do not bless it as a release axiom;
- `TrTypeExpr`, a representation-only metadata-type translation whose
  `to_trExprS` theorem recovers application and pi typing premises from the
  declaration's real Theory well-formedness proof;
- a replay-driven Nat fixture that quotes the actual `inductInfo`, both
  `ctorInfo`s, and `recInfo` from Lean, translates them in the exact
  intermediate environments, constructs `AddInduct`, executes
  `TrEnv'.induct`, and checks final `WF`, alignment, and recursor lookup
  uniqueness;
- an actual-metadata Eq replay with the same transaction, final-WF,
  alignment, and lookup-uniqueness checks. This additionally exercises a real
  index, Prop-valued elimination, and the kernel/generated recursor universe
  permutation;
- an actual-metadata `IndexedVec` replay layered over the completed Nat
  transaction. It exercises two constructors, a recursive field, a changing
  result index, final replay equality/WF/alignment, and uniqueness of the
  translated type, constructor, and recursor lookups. The source fixture uses
  explicit `Nat.zero`/`Nat.succ`, so this tests the semantic dependency while
  deliberately excluding notation's unrelated `OfNat`/`HAdd` instance
  closure;
- an actual-metadata `Acc` replay that checks kernel constructor/recursor
  counts, parameters, indices, recursive fields, rule constructor and field
  count, translates each metadata declaration in its exact intermediate
  environment, constructs `AddInduct`, executes `TrEnv'.induct`, and proves
  final equality, WF, alignment, and lookup uniqueness. Its quoted kernel
  `RecursorRule.rhs` is definitionally equal to the generalized Theory RHS,
  including the lambda under the recursive Pi and the kernel universe order;
- actual-metadata `AliasFormer` and `AliasRec` replays, including the real
  `DefinitionVal` prefixes for `TypeFamilyAlias` and `RecAlias`. They retain
  the raw alias-bearing family/constructor payloads, translate the actual
  `inductInfo`, `ctorInfo`, `recInfo`, and kernel rules in exact intermediate
  environments, execute the normalized transaction, and prove final equality,
  WF, alignment, and family/constructor/recursor lookup uniqueness. The
  recursive-field case separately pins the raw alias-bearing minor binder;
- a candidate-produced `AnnotatedPi` replay whose actual constructor shape
  combines a recursive target below a Pi with retained `outParam Prop` syntax.
  It builds the complete normalization/generation certificate from exact
  checker traces, executes the checked transaction, and pins the generated
  recursor, iota membership/RHS, lookup uniqueness, WF, and alignment;
- explicit definitional equalities for every quoted kernel rule RHS in all six
  actual-metadata replays plus the AnnotatedPi generated iota rule, rather than
  only the previously highlighted `Acc` rule;
- a real dependency-free definition replayed before Nat, followed by a
  concrete `TrEnv'.of_value` theorem whose proof must traverse the outer
  inductive transaction and pull the old lookup through every metadata
  insertion;
- a complete post-Verify-migration Lean gate on 2026-08-01: the exact 20-entry
  sorry audit, `lake build Lean4Lean.Theory Lean4Lean.Verify`, formatter check,
  and `git diff --check` pass; the normal current-host `nix build` also passes.
  The current-host full flake check and exact all-system no-build evaluation
  also pass at `5e5bb767`; representative Linux/Darwin builds remain CI jobs.

Stage 3 remains intentionally narrow: it accepts only one type and only large
eliminators. Its structural field check recognizes direct recursion and
recursive targets beneath family-free Pi domains, and its public checked
artifact path now uses that generalized representation throughout. Its
closure and internal-name checks, metadata-wide universe-range checks, and
normalized semantic contracts are real kernel-facing checks. The explicit
  normalization boundary now demonstrates how raw syntax can be related to a
  checked view. Verify can replay an explicitly certified normalized generation
  and now derives the two fixed alias normalization certificates plus the
  recursive AnnotatedPi annotation certificate from exact ordinary-checker
  executions. AliasFormer, AnnotatedPi, and `IndexedVec` have complete checked
  dependent generation certificates, exact whole-call produced packages, and
  use the public proof-carrying non-identity transaction; the third case
  exercises a parameter, an index, and an ordered two-constructor list, and
  the identity compatibility path still peels the raw syntax. No generic outer
  producer yet constructs the semantic package directly from an arbitrary
  successful whole metadata call. AnnotatedPi closes the nested-Π and
  annotation-consumption fixture through exact constructor validation,
  candidate-list assembly, and the final produced-package equation.
  Constructor-parameter agreement is still
  syntactic where the kernel uses definitional equality. It also lacks full
  positivity, small-elimination, and K analyses. The
negative Or fixture demonstrates that small elimination is not modeled yet.
Further alias shapes, non-defeq normalization negatives, nested negativity,
mutual blocks, nested inductives, notation-heavy prelude replay, and the full
inductive environment fixture matrix remain future work. A successful default
`nix build` alone is not a release gate.

### 2.3 Live debt outside inductive breadth

The sorry-frontier script currently reports exactly:

| Area | Live debt |
|---|---|
| Projection specification | `Verify/Typing/Expr.lean:67`, `TrProj` |
| Projection structural laws | seven sites in `Verify/Typing/Lemmas.lean`: `weak'`, inverse weakening, `defeqDFC`, `wf`, `uniq`, `instN`, `instL` |
| Core metatheory | `Injectivity.lean` x3, `UniqueTyping.lean` x1, `ChurchRosser.lean` x2 |
| Checker verification | `Verify/Level.lean` x2; `Verify/Environment.lean` x1; `InferType.lean` x1; `WHNF.lean` x2; `IsDefEq.lean` x2 |

There is important non-sorry debt too:

- The empty Verify `AddInduct` relation and both vacuous `nomatch` proofs have
  been removed. Nat, Eq, `IndexedVec`, and `Acc` now supply actual-metadata
  witnesses, lookup-uniqueness, `TrEnv'.wf`, and alignment tests; `Acc` also
  checks the actual lambda-under-Pi rule RHS, and Nat has a pre-existing-value
  preservation regression. E1 is not fully closed until the remaining I2-I4
  fixture matrix is replayed.
- The public inductive spec is a growing subset, not kernel-complete.
- `VLocalDecl` core facts, literal encodings, `ContainsLits`,
  `HasPrimitives`, and `TrProj` are implementation-independent but live under
  `Verify/`, forcing ix to import that layer.
- There are 29 project-specific `axiom` declarations outside
  `Experimental/`: 27 in `Verify/Axioms.lean` and two pointer-equality
  contracts in `PtrEq.lean`. Three cached-field equations remain from the
  group known false on the older Lean pin (`lean4#8554`). Lean v4.31 repairs
  the underlying cache behavior, but these equations are still unproved and
  therefore remain forbidden implementation contracts. Count, classification,
  and per-root reachability—not just sorry count—are release criteria.
- The fetched `logrel@upstream` branch at `e431dad8` contains a serious
  experimental route to injectivity/unique typing, but the live
  `Theory/Typing/Injectivity.lean` still has all three sorries. The branch's
  route depends on unfinished `ShapeLogRel`/adequacy work and cannot simply be
  merged as a completed proof.

#### Current custom-axiom inventory

This classification records the intended release treatment; it is not itself
evidence that an implementation equation is true. In particular, the ten
collection/opaque-layout equations still require validation and may move into
the forbidden class if a counterexample is found.

| Class | Count | Declarations | Release treatment |
|---|---:|---|---|
| Unproved cached-field equations, known false on older pins | 3 | `Level.hasParam_eq`, `Level.hasMVar_eq`, `Expr.looseBVarRange_eq` | Forbidden from every supported theorem root until proved for the pinned implementation |
| Reference equations documented as `@[implemented_by]` candidates | 13 | `Expr.replace_eq`, lift/lower, instantiate/range/reverse, abstract/range, `hasLooseBVar_eq`, `eqv_eq`, `equal_eq` | Replace axioms with logical reference definitions and separately justified implementations |
| Persistent collection semantics | 5 | `TreeMap.all_eq_all_toList`; `PersistentArray.toList'_push`; hash-map insert, find, and contains/find agreement | Prove upstream or narrow to the actual WF/reachable-state invariant |
| Other opaque or representation-layout bridges | 5 | `Syntax.structEq_eq`; Level and Expr data-layout equations; `Level.mkLevelIMaxCore_eq` | Expose/prove upstream, narrow to the properties and bounds actually needed, or reject |
| Candidate platform contracts | 3 | `ptrEqExpr_eq`, `ptrEqConstantInfo_eq`, `Level.instLawfulBEqLevel` | May remain only in a named, version-pinned platform manifest with differential tests |

**L4L-01U axiom/sorry result.** Relative to source checkpoint `da45b536`,
upstream commit `3dc52e0` proves and removes the four cached-`Expr` axioms
`hasFVar_eq`, `hasExprMVar_eq`, `hasLevelMVar_eq`, and `hasLevelParam_eq`;
`66172a2` removes the hand-declared `Expr.mkAppRangeAux.eq_def` because Lean
v4.31 generates its defining equation. The exact custom-axiom inventory is
therefore 29, down five from 34. `Level.hasParam_eq`, `Level.hasMVar_eq`, and
`Expr.looseBVarRange_eq` remain unproved; although v4.31 fixes the cached-data
bug, they remain forbidden implementation contracts and are not logical
foundations. The exact sorry frontier is 22, up two from 20: upstream adds
`NormLevel.isEquiv_wf`, mapped to L4L-02B, and the front-end theorem
`Lean4Lean.addDecl.WF`, mapped to L4L-19B. Exact guards confirm that the five
retired declarations disappeared. Existing `Expr.mkData_eq` and
`Expr.mkAppData_eq` become visible in several v4.31 Verify closures because the
new cached-field implementation routes through those already-inventoried
layout contracts; no new axiom declaration or supported-root trust category
was added. Raw count changes are acceptable only with this declaration-level
and per-root classification.

The current reachability audit is **partially established**, not release-clean:

- the Stage-3 proof builds; executable `#print axioms` guards pin the descriptor
  analysis, closure/level/name/anatomy facts, semantic `Checked.WF` compatibility
  bridges, the generic normalization-shape/source-anatomy projections, the two
  concrete `Normalization.WF` witnesses and their combined paired-block
  certificates,
  transaction/collision facts, and `VEnv.addInduct_success` to
  `propext`/`Quot.sound`, and `VEnv.addInduct_WF` to those plus
  `Classical.choice`. Identity checked-block compatibility and the semantic
  `Checked.WF.identityGeneration` bridge are separately pinned to the same
  three-axiom Theory upper bound; their proof components reach Lean's lawful
  Boolean-equality/weakening facts, while the analyzer and shape tests remain
  executable definitions rather than postulated oracles. The six recursive-Pi
  preservation roots are separately pinned to the same three-axiom Theory
  baseline. The normalized transaction trace, atomicity, monotonicity, lookup,
  and rule-membership roots are pinned to exactly `propext` and `Quot.sound`;
  normalized transaction preservation, the identity-wrapper computation
  theorem, and final ordered alias environments additionally reach only
  `Classical.choice`. Each alias trace, raw lookup, kernel recursor lookup, and
  iota-membership fixture remains at the smaller two-axiom closure;
- `Theory/` currently declares no custom axioms and imports neither
  `Verify/Axioms` nor `PtrEq`, which is the required architectural boundary;
- the full generated closure report for the remaining Theory endpoints,
  Verify checker roots, and ix-imported theorem set does not yet exist;
- the new E1 bridge roots have checked closures, but they inherit `sorryAx`
  through the type dependency `TrConstVal → TrExprS → TrProj`; this is Track
  P's projection-specification hole, not a new E1 axiom declaration;
- the five L4L-01U-retired names are absent from the source and exact guards;
  their former textual uses have kernel proofs or generated v4.31 equations;
- all three remaining cached-field equations are simp lemmas and can enter a
  proof without a textual reference to their names, so their absence must be
  established by exact root guards rather than source search.

Consequently, source import/name searches are useful diagnostics but are not
the release audit. Only the generated transitive axiom closure of each named
root is authoritative.

#### Current root-level axiom snapshot

The exact current closures below answer two different questions. The Theory
set is reasonable for this formalization: it is Lean's usual logical baseline
and contains no project-specific bridge axiom. The Verify set is reasonable
only as an explicitly guarded *transitional diagnosis*; `sorryAx` is not an
acceptable release dependency.

The acceptance decision is deliberately stricter than “Lean compiled it”:

- `propext`, `Classical.choice`, and `Quot.sound` are the permitted standard
  logical baseline. `propext` supports equality of extensionally equivalent
  propositions, choice permits classical witness selection in proofs, and
  `Quot.sound` is Lean's quotient identification principle. A root may use only
  the subset it actually reaches;
- no project-specific axiom is authorized for `VInductDecl.Checked`, inductive
  generation/preservation, the future E2 oracle-construction theorem, or any
  other Theory API exported to ix. A perceived need for one is a specification
  or proof-design blocker, not a reason to extend the allowlist;
- `sorryAx` and the persistent-map contracts in the Verify rows are recorded so
  their removal can be tested. They are not part of the accepted release set;
- the three cached-field equations known false on older toolchains remain
  forbidden until proved for v4.31, even though the implementation bug is
  fixed. Reachability, rather than declaration presence alone, is the release
  criterion.

| Root | Current transitive closure | Assessment / removal path |
|---|---|---|
| `Checked.analysis_accepted`, `names_nodup`, `type_closed`, `ctor_closed`, `type_levelWF`, `ctor_levelWF`, `direct_anatomy` | `propext`, `Quot.sound` | Accepted logical baseline; every exported structural-analysis fact is compile-time guarded. `checked?` itself is computational and declares no axiom. |
| `Checked.wf_of_decl`, `Checked.to_declWF`, `VInductDecl.wf_iff_exists_checked` | `propext`, `Quot.sound` | Accepted logical baseline; these guarded theorems show that the new environment-indexed semantic certificate adds no trust and is exactly compatible with the legacy relation. |
| `Normalization.shape`, `NormalizedChecked.source_anatomy`, `GenerationChecked.shape`, `GenerationChecked.rawCtors_eq`, `GenerationChecked.viewCtors_eq` | `propext`, `Quot.sound` | Accepted logical baseline; exact generic guards establish declaration arities, ordered family/constructor identities, raw/view layout, and complete positional constructor coverage. They do not assert expression equality or authorize a view semantically. |
| `TelDefEq.raw_onTel`, `TelDefEq.instL`, `TelDefEq.ctx`, `GenerationChecked.WF.rawFamily_isType`, `GenerationChecked.WF.rawCtor_isType` | subset of `propext`, `Quot.sound`, exactly guarded per root | Accepted logical baseline; the structural semantic contract yields raw telescope well-formedness, universe transport, definitionally equal completed contexts, and insertion-ready raw family/constructor types. No injectivity theorem, `sorryAx`, project-specific axiom, or Verify import is reachable. |
| `GenerationEnv.motive_isType`, `familyApp_transport` | `propext`, `Quot.sound` | Accepted and compile-time guarded. These roots cover the mixed motive and the common raw-family application transport without reaching choice or any project axiom. |
| `GenerationEnv.minor_isType`, `minorTypes_onTel`, `recType_isType`, `recursor_wf`, `ruleCall_hasType`, `rule_WF`, `generatedRules_WF`, `generatedRulesFold_ordered` | `propext`, `Classical.choice`, `Quot.sound` | Accepted logical baseline; every stabilized mixed minor/recursor/rule/fold boundary has an exact compile-time guard. No `sorryAx`, Verify import, or project-specific axiom reaches the complete mixed artifact preservation path. |
| `VEnv.addInductGeneration_trace`, `addInductGeneration_atomic`, and `AddInductGenerationTrace.le`/family/constructor/recursor lookup/`rule_mem` | `propext`, `Quot.sound` | Accepted and exactly guarded. The data-bearing trace is returned under `Nonempty`, so proof consumers recover the exact intermediate environments without adding `Classical.choice`; the trace is a certificate of the executable transaction, not a semantic oracle. |
| `VEnv.addInductGeneration_WF`, `addInduct_eq_addInductGeneration` | `propext`, `Classical.choice`, `Quot.sound` | Accepted and exactly guarded. Preservation consumes `GenerationChecked.WF` in insertion order and never reconstructs `Stage3Env`; the wrapper theorem pins the raw API to identity normalization. Choice is inherited from the mixed artifact/identity proof chain, not from extracting transaction states. |
| `VEnv.addInductCertified_eq_addInductGeneration` | `propext`, `Quot.sound` | Accepted and exactly guarded. The theorem is definitionally `rfl`, so it machine-checks the proof-erasure boundary: the public certified entry point computes only with `certificate.generation`, and its WF proof cannot select or alter artifacts. The reported logical closure is reached through the dependent certificate/generation types in the statement, not through computational inspection of the proof. |
| `VEnv.addInductCertified_trace`, `addInductCertified_atomic` | `propext`, `Quot.sound` | Accepted and exactly guarded. The proof-carrying public wrapper computes through `addInductGeneration`; these theorems recover the same transaction trace and atomicity result without exposing or importing Verify. The certificate's WF field is not inspected by computation. |
| `VEnv.addInductCertified_WF` | `propext`, `Classical.choice`, `Quot.sound` | Accepted and exactly guarded. The certificate carries the exact semantic premise consumed by normalized preservation, so ix does not need a separate checker-trace argument or a normalization oracle. This is the intended Theory-only non-identity transaction boundary. |
| `VDecl.WF.induct` | `propext`, `Quot.sound` | Accepted and exactly guarded. Environment histories now record the exact certified `GenerationChecked` transaction, so non-identity normalization is represented honestly rather than being forced through the identity-only public wrapper. |
| `identityChecked?_isSome` | `propext`, `Classical.choice`, `Quot.sound` | Accepted logical baseline; the identity wrapper has exactly the legacy analyzer's success behavior. The standard closure enters through the proof carried by reflexive normalization shape, including symbolic-name `BEq` lawfulness; the underlying analyzer and identity wrapper still compute and declare no oracle. Keep this exact guard so an implementation-proof dependency cannot silently grow. |
| `Checked.analyzer_eq` | `propext`, `Quot.sound` | Accepted logical baseline; any retained dependent descriptor is the unique exact analyzer result, so the identity bridge does not rerun analysis or choose a competing witness. |
| `Checked.identityBlock_generationShape`, `motiveType_eq_legacy`, `minorTypes_eq_legacy`, `recursor_eq_legacy`, `generatedRules_eq_legacy` | `propext`, `Classical.choice`, `Quot.sound` | Accepted and exactly guarded. The `Classical.choice` dependency is inherited from the already-guarded reflexive normalization-header proof; artifact construction remains computational. These roots prove that the live public accessors use the mixed generator while preserving the exact legacy identity output. |
| `aliasFormerNormalization_wf`, `aliasRecNormalization_wf`, both block-WF roots, and both generation-WF roots | `propext`, `Quot.sound` | Accepted logical baseline; exact fixture guards demonstrate that family-result and recursive-field alias normalization can be justified by existing Theory definitional equality and combined with the checked view's semantic, layout, and granular raw-binder certificates. These are evidence for the boundary design, not axioms authorizing arbitrary normalized views. |
| `AddInductive.CandidateTypeAnnotationTrace.build`, `buildCandidateTypeAnnotations`, `buildCandidateExpr`, `buildCandidateCheckType`, `buildNormalizationCandidate`, all three `CandidateExpr.*Step_valid` roots, and all three `Candidate*Step.innerRun` roots | subsets of `propext`, `Classical.choice`, `Quot.sound`, exactly guarded per root | Accepted. The executable producer retains concrete evidence: each WHNF/full-check/binder-equality node stores its actual `M.run` equality, and the `innerRun` adapters only recover erased final states. The structural annotation trace exposes the retained argument; the producer independently rejects disagreement with Lean's opaque `consumeTypeAnnotations` helper and refuses a negative `isDefEq`. The certificate intentionally stores no proposition equating its result with that opaque partial definition: the runtime agreement test is implementation validation, while semantic authority comes from the structural trace plus exact checker equality run. The standard closure is inherited from the checker/container implementation; there is no `sorryAx`, native evaluator, opaque-helper equation, normalization axiom, or project-specific axiom. |
| `TypeChecker.WhnfRun.ofCandidateStep`, `CheckTypeRun.ofCandidateStep`, `IsDefEqRun.ofCandidateStep` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` | Transitional and exactly guarded. The adapters supply no semantic proof by themselves: callers must provide a verified context plus strict endpoint translations. `sorryAx` is inherited from the existing Verify context/translation frontier and must disappear there; the adapters add no pointer or cache axiom. |
| `candidateTypeAnnotation_fvarsIn`, `candidateTypeAnnotation_exists_translation`, `IsDefEqRun.isDefEqU` | respectively axiom-free; `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`; and the exact checked semantic set | Transitional and exactly guarded. Structural recursion proves consumption cannot add free variables and extracts the retained argument's strict translation. `IsDefEqRun.isDefEqU` then refines the exact successful checker execution through the existing verified `isDefEq` theorem. The larger closure is inherited from that checker refinement; the annotation bridge declares no axiom and does not convert Lean's Boolean `Expr.equal` agreement check into an unproved propositional equality. |
| `TypeChecker.CandidateNodeRun.ofCandidate`, `CandidateNodeRun.exists_ofCandidate`, `CandidateNodeRun.evidence`, `CandidateExprRun.evidence`, `source_tr`, `view_tr` | the adapter set for direct construction; the exact checked semantic set for existential output recovery, interpretation, and endpoint translation | Transitional and exactly guarded. Recursive context/source indices tie Pi children to the exposed raw domain, exact instantiated body, actual local-context extension, and generated binder identifier. `exists_ofCandidate` derives the returned inferred/result translations from the verifier refinements once given a matching context and source translation. The interpreter consumes the paired runs, uses unique typing to transport alias-valued inferred types to structural Pi sorts, composes Pi congruence under the raw binder, and proves translations of both endpoints; it declares no oracle or axiom. The larger closure is inherited from the existing verifier refinement/context-conversion frontier. |
| `AddInductive.CandidateList.singleton` | axiom-free | Accepted structural helper. The singleton index proves the only possible family-list shape and removes any need for `head!` or a default element. |
| `AddInductive.CandidateFamilyTypeListProduced.normalize`, `CandidateConstructorListProduced.normalize`, `CandidateFamilyListProduced.normalize` | `propext`, `Classical.choice`, `Quot.sound` | Accepted operational structural glue, exactly guarded. The dependent source indices preserve length, order, and family/constructor provenance for arbitrary lists; the proofs only compose exact per-position executable results and introduce no project axiom, erasure equality, unchecked `zip`, or semantic authority. `IndexedVec` exercises the two-constructor case, while AliasFormer and AnnotatedPi exercise the singleton cases. |
| `TypeChecker.CandidateExprRootRun.evidence`, `VInductDecl.CandidateConstructorListRun.evidence`, `NormalizationCandidateRun.normalizationRun` | exactly the checked semantic set listed below | Transitional and exactly guarded. Callers name raw and exact candidate-view translations; the verified recursive run proves their equality. Constructor evidence is folded with `List.Forall₂`, and the singleton family wrapper constructs the semantic `NormalizationRun` without selecting a proof-only existential or accepting an unrelated view. The closure is inherited unchanged from the checker refinement. |
| `VInductDecl.CandidateConstructorListRun.sameHeaders`, `NormalizationCandidateRun.normalization` | respectively `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`; and the same set | Transitional and exactly guarded. These roots derive header/shape preservation from the dependent run itself. They add no semantic equality and cannot truncate either list; the inherited `sorryAx` is type-level Verify debt, not a new shape axiom. |
| `TypeChecker.VState.WF.empty_of_reserves`, `candidateFreshFVarId_reserved`, `CandidateContextRun.root`, `CandidateContextRun.pushLocalDecl` | exact subsets of the transitional context set: the fresh-ID lemma uses only `propext`, `Classical.choice`, `Quot.sound`; root/context extension additionally inherit `sorryAx` plus the already recorded expression/level/container contracts | Transitional and exactly guarded. These roots construct—not assume—the precise verified root and binder contexts retained by a candidate trace. Body contexts contain the annotation-consumed domain; the separately retained exact equality run ties that domain back to raw syntax. The producer records the binder freshness equation, the candidate and checker name prefixes are proved distinct, and every empty-state restart reserves the accumulated free variables. No normalization, evaluation, or context-coherence axiom was added. `sorryAx` remains inherited from the existing `VContext`/`VState` well-formedness frontier and is therefore still release-blocking. |
| `candidateCheckTypeStep_exists_translation`, `CandidateExprRun.exists_ofCandidate`, `CandidateExprRun.exists_ofCandidateFVars` | exactly the checked semantic set (`propext`, `sorryAx`, `Classical.choice`, the two pointer implications, `Quot.sound`, and the named Expr/Level/container refinement contracts listed below) | Transitional and exactly guarded. The first theorem recovers strict source/inferred translations and typing from an exact retained full check. The recursive roots obtain all node outputs, extend the verified context with the annotation-consumed binder, refine raw-to-consumed equality, transport the body translation and typing between definitionally equal contexts, and certify an arbitrary annotated-domain trace. The `FVars` wrapper removes the last caller-chosen Theory expression. This is proof reconstruction over concrete runs, not an oracle; the former `CandidateRawBinderDomains` restriction has been removed. |
| `TypeChecker.TelDefEqEvidence.telDefEq`, `VInductDecl.NormalizedCtorRun.wf`, `GenerationRun.wf` | exactly the checked semantic set listed below | Transitional and exactly guarded. These generic roots interpret compositional checker evidence as the pointwise telescope, constructor, and complete generation certificates required by Theory. Their statements mention exact verifier-run evidence, so inheriting the verifier closure is expected; the assembler declares no axiom and does not enlarge that set. |
| `CandidateExprTrace.storedSpine`, `CandidateExprTrace.spineLength` | `propext`, `Classical.choice`, `Quot.sound` | Accepted structural/computational guards. They inspect the retained trace, require every emitted raw Pi node to remain the same outer Pi, and count exactly those nodes. They permit domain/result normalization but do not postulate Pi injectivity, normalization completeness, or semantic equality. |
| `InductiveReplayFixtures.candidateIsDefEqSelfValid` | `propext`, `Classical.choice`, `Quot.sound`, `Expr.eqv_eq`, `Level.instLawfulBEqLevel`, `Syntax.structEq_eq` | Reasonable as an exactly guarded Verify-layer reflexive execution lemma, but not an ix-facing release allowlist. It proves the ordinary checker accepts `e ≡ e`; it declares no equality or normalization axiom. The three implementation contracts are inherited from Lean expression/level/name equality and must stay confined to Verify until Track T justifies or replaces them. |
| `InductiveReplayFixtures.indexedVecFamily_candidateTrace`, `indexedVecCandidateInductiveStats_nindices`, `indexedVecCandidateInductiveStats_params` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, `Expr.eqv_eq`, `Expr.instantiate1_eq`, `Expr.instantiateRev_eq`, `Expr.instantiate_eq`, `Expr.looseBVarRange_eq`, `Expr.mkAppData_eq`, `Expr.mkData_eq`, `Expr.replace_eq`, `Level.hasParam_eq`, `Level.instLawfulBEqLevel`, `PersistentArray.toList'_push`, `PersistentHashMap.findAux_isSome`, `Syntax.structEq_eq`, `PersistentHashMap.WF.find?_eq`, `PersistentHashMap.WF.toList'_insert` | Transitional and exactly guarded. These roots replay the real `IndexedVec` family through two dependent binders and expose the computed one-parameter/one-index statistics. `sorryAx` and container/reference/layout equations are inherited from the existing Verify environment/context frontier; the fixture adds no axiom and gives these contracts no Theory authority. |
| `InductiveReplayFixtures.indexedVec_checkInductiveTypes` | the preceding `IndexedVec` candidate set plus `Level.hasMVar_eq` | Transitional and exactly guarded. This is the complete executable singleton-family validation, including the closedness checks. The four cached-`Expr` facts are now proved on v4.31; their proofs expose only the already listed data-layout contracts. The closure remains development evidence because every dependency is visible, but its `sorryAx` and implementation contracts are release-blocking and must not flow into the Theory certificate consumed by ix. |
| `AddInductive.observeCandidateIsDefEq_of_run`, `buildCandidateExpr_loop_of_whnf_nonForall`, `buildCandidateExpr_loop_of_whnf_forall` | `propext`, `Classical.choice`, `Quot.sound` | Accepted operational reduction seams, exactly guarded. They expose a supplied exact ordinary-checker execution and assemble one terminal or Π traversal step; they add no normalization oracle, evaluator equation, or fixture-specific axiom. |
| `TypeChecker.TelDefEqEvidence.ofTelDefEq` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` | Transitional and exactly guarded. This constructs evidence from already proved pointwise telescope equality; its `sorryAx` is inherited through the Verify translation/context statement, not introduced by extraction. It reaches none of the pointer, expression-reflection, or container contracts used by executable checker refinement. |
| `CandidateExprIdentity.storedSpine`, `CandidateExprRun.exists_ofIdentity`, `CandidateExprRootRun.spineOfIdentity` | a subset of the checked semantic set listed below, reached transitively by both exact `IndexedVec` public-root guards | Transitional. These roots recursively interpret a syntactically identity-normalizing candidate at caller-selected Theory endpoints and recover its generation-ready stored spine from the same source-indexed run. They declare no axiom and do not assume a normalization equation; their closure is inherited from the existing verifier, translation, unique-typing, and container frontier. Add direct guards if they become independently exported audit roots. |
| `CandidateExprSemanticRootRun.exists_ofCandidate`, `.root`, `CandidateExprRootRun.semanticOfIdentity`, `CandidateConstructorSemanticListRun.roots`, `CandidateFamilySemanticRun.root`, `NormalizationCandidateSemanticRun.root`; separately `CandidateExprSemanticRootRun.spine` | the first group has exactly the checked semantic set listed below; `spine` has exactly `propext`, `sorryAx`, `Classical.choice`, and `Quot.sound` | Transitional, directly audited with `#print axioms` at `f0caf16c`. The root theorem lets the retained checker run select its Theory view from verified context/source evidence, while the dependent projections preserve exact source positions through normalization. The spine is a direct projection of that same run. Their new composite construction and generation callers are exact compile-time guarded in the next row; add individual guards here only if one becomes an independently exported audit root. None declares an axiom, assumes normalization, invokes a native evaluator, or gives the operational producer independent semantic authority. The broad closure is inherited from the existing checked-semantic translation/refinement frontier and remains release-blocking for ix-facing evidence. |
| `TypeChecker.CandidateExprSemanticRootInput.exists`, `CandidateConstructorSemanticListInput.exists`, `NormalizationCandidateSemanticInput.exists_ofProduced`, `CandidateFamilySemanticGenerationRun.run`, `CandidateSemanticNormalizedCtorListRun.run`, `GenerationCandidateSemanticRun.run`, `.package`, `.producedPackage` | exactly the checked semantic set listed below, compile-time guarded per root | Transitional and exactly guarded at `7e5f4f77`. The input hierarchy combines verified contexts and strict translations with exact operational list witnesses, then returns the complete source-ordered semantic hierarchy under `Nonempty`; the producer selects the indexed candidate but does not select its Theory view. The semantic-generation projections reuse that hierarchy's recursive runs and spines, eliminating parallel normalization/generation ownership. `Nonempty` is intentional: extracting a data-bearing run would require choice, whereas proof consumers need only semantic existence. No new axiom, normalization oracle, native evaluator, unchecked positional operation, or caller-selected endpoint is introduced. |
| `aliasFormerProducedSemanticHierarchy_exists`, `annotatedPiProducedSemanticHierarchy_exists`, `indexedVecProducedSemanticHierarchy_exists`, the three `*GenerationCandidateSemanticRun` roots, `indexedVecProducedSemanticHierarchy_constructorHeaders`, and `indexedVecReorderedView_rejected` | all positive roots have exactly the checked semantic set; reordered-view rejection has exactly `propext` | Transitional fixtures, all exactly guarded. The three positive blocks exercise terminal-alias, annotated recursive-Π, and parameter/index/two-constructor assembly. `IndexedVec` proves that the existential semantic result retains `nil`/`cons` order, while swapping those headers fails the computational normalization-shape gate before semantic or generation evidence can be attached. The v4.31 cache proofs remove the former AnnotatedPi-only axiom delta. |
| `CandidateExprRun.spineEvidence`, `CandidateExprSpineRun.evidenceAt`, `TelResultDefEqEvidence.replacePrefix`, `CandidateNormalizedCtorRun.normalizedCtorRun`, `GenerationCandidateRun.wf` | exactly the checked semantic set listed below | Transitional and exactly guarded. These generic generation-level roots recursively recover binder equality and the terminal result from the exact run, prove raw-spine length, replace a constructor's declared parameter prefix with the definitionally equal emitted family prefix in the exact induced contexts, fold a source-indexed dependent constructor list, and produce `GenerationChecked.WF`. They use neither forall injectivity nor a choice-selected candidate view and declare no axiom; the closure is inherited unchanged from checker refinement, unique typing, translation, and container contracts. |
| `Checked.type_eq`, `GenerationChecked.viewCtorType_eq`, `GenerationChecked.checkedResultTarget_hasType` | exactly `propext`, `Quot.sound` | Accepted Theory baseline and exactly guarded at `2b1d802f`. These roots expose the analyzer's exact family/constructor telescope decomposition and type a constructor's normalized result application from the retained family constant plus checked parameter/index spines. No Verify import, custom axiom, normalization oracle, or whole-Pi injectivity enters Theory. |
| `Normalization.check?_normalization`, `Normalization.generation?_normalization` | exactly `propext`, `Quot.sound` | Accepted Theory baseline and exactly guarded at `a64fe982`. These theorems invert exact successful dependent analysis to recover the normalization retained by its indexed result. They unfold the computational analyzers and introduce no Verify dependency, choice, custom axiom, or normalization oracle. |
| `GenerationCandidateRun.familyView_eq`, `CandidateNormalizedCtorRun.viewTel_eq` | exactly `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` | Transitional Verify glue and exactly guarded at `2b1d802f`. Singleton normalization indices force the exact checked family view, while a known non-forall terminal plus exact checked constructor shape recovers the complete candidate view telescope. The inherited `sorryAx` is already present in the retained semantic-run types; neither theorem declares an axiom or adds semantic authority. |
| `GenerationCandidateRun.normalization_eq` | exactly `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` | Transitional Verify projection and exactly guarded at `a64fe982`. The theorem consumes the exact `generation? = some generation` field and delegates normalization recovery to the Theory theorem above. The inherited `sorryAx`/choice closure comes from the dependent Verify evidence type in its statement; fixtures no longer provide the equality. |
| `NormalizationCandidateRun.sourceType_eq`, `NormalizationCandidateRun.familyViewType_eq` | exactly `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` | Transitional Verify alignment and exactly guarded at `5aa9ab69`. Singleton source indices and exact dependent analysis determine the retained raw family and complete checked family view. The inherited closure comes from the dependent Verify evidence in the statements; neither theorem declares an axiom, asserts normalization, or lets a caller select a view. |
| `GenerationCandidateSemanticShapeRun.run` | exactly the checked semantic set listed below | Transitional and exactly guarded at `5aa9ab69`. Source-indexed minimal shapes retain only stored-spine success and the total binder count. Exact analysis derives every raw/view pair and the complete ordered constructor list; total length derives raw telescope/results, and checked shape derives view terminals. The projection reconstructs `GenerationCandidateSemanticRun` without `zip`, truncation, reordering, a caller-selected pair, or component premises. Its closure is exactly the existing checked semantic set, so the structural recursion and telescope decomposition add no axiom. |
| `candidateConstructorSemanticGenerationShape`, `normalizationCandidateGenerationShape`, `CandidateConstructorSemanticGenerationShapeList.ofCheck`, `produceGenerationShapeCandidate`, `produceGenerationShapeCandidate_eq_ok` | exactly `propext`, `Classical.choice`, `Quot.sound` | Accepted executable boundary and exactly guarded at `bbb45e0e`. The source-indexed Boolean covers the complete family/constructor hierarchy, checks retained emitted spines and full raw telescope lengths, and rejects missing or extra constructor positions. The strengthened producer retains the exact ordinary producer equation plus this separately successful gate. These roots make no Theory claim, declare no axiom, and cannot turn bare producer success into stored-spine evidence. |
| `NormalizationCandidateSemanticRun.generationShape`, `GenerationCandidateSemanticRun.ofGenerationShape`, `NormalizationCandidateSemanticRun.producedPackageOfGenerationShape`, `ProducedGenerationShapeCandidate.producedPackage` | exactly the already recorded checked semantic set, compile-time guarded per root | Transitional and exactly guarded at `bbb45e0e`. Exact dependent analysis and WF of the analyzer-owned view declaration derive checked WF; the successful complete Boolean expands structurally into every source-indexed family/constructor stored-spine/count record. Packaging then reuses the existing semantic owner for the same producer-selected candidate. The broader closure is inherited from verified checker/context evidence, not introduced by the shape gate; no new axiom, normalization oracle, native evaluator, unchecked positional operation, or caller-selected view is added. |
| `GenerationCandidateRun.typeEnv_wf` | exactly the checked semantic set listed below | Transitional and exactly guarded at `a64fe982`. It reconstructs the post-family environment from retained pre-family WF, the verified raw/view definitional equality, checked family typing, and the exact raw-family insertion. The broad closure is inherited from the existing checker/context evidence; fixtures no longer provide this WF judgment, and no new axiom or environment oracle is introduced. |
| `GenerationCandidateRun.familyConst_hasType`, `CandidateNormalizedCtorRun.rightType_ofChecked` | exactly the checked semantic set listed below | Transitional and exactly guarded at `2b1d802f`. The family constant is typed once in the post-family environment by combining exact insertion, candidate equality, and checked family WF. Every constructor terminal then follows from the checked result spine and telescope-context transport. Fixtures no longer supply terminal typing judgments; the broad closure is inherited from existing Verify checker/context evidence and does not reach the three Theory roots above. |
| `GenerationCandidateRun.package`, `GenerationCandidateRun.producedPackage` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` | Transitional and exactly guarded. The first packaging root retains the already indexed source/candidate/run fields without interpreting them. The second attaches an exact successful whole-call equation for that same dependent candidate and cannot be reused for a different run, reordered list, or caller-selected view. The small closure comes from the dependent Verify evidence types in their statements; neither root introduces checker, producer, or normalization authority. |
| `GenerationCandidatePackage.certificate`, `GenerationCandidatePackage.addInductTrace` | exactly the checked semantic set listed below | Transitional and exactly guarded. Certificate erasure derives both the Theory generation and its WF proof from the same package. The metadata replay constructor likewise fixes its trace's generation/WF fields to package projections, so callers may supply insertion witnesses but cannot substitute an unrelated normalized view. The inherited Verify closure remains release-blocking and does not reach the resulting Theory API declaration. |
| `InductiveReplayFixtures.aliasFormerGenerationCandidateRun` | exactly the checked semantic set listed below | Transitional and exactly guarded. This concrete non-identity fixture supplies exact analysis, WF of the analyzer-owned view declaration, and one successful complete generation-shape gate; it no longer supplies checked WF or any per-position shape record. The generic projection derives checked WF, raw/view family identity, normalized pairing/order, all raw telescope/results and view terminals, and the dependent constructor list. Its existing `GenerationRun`, checked `AddInductTrace`, final environment, WF, and alignment replay delegate through this value, so the vertical path adds no axiom beyond the already visible Verify frontier. |
| `InductiveReplayFixtures.aliasFormerNormalizationCandidate_produced` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, `Expr.eqv_eq`, `Expr.looseBVarRange_eq`, `Expr.mkAppData_eq`, `Expr.mkData_eq`, `Level.instLawfulBEqLevel`, `PersistentHashMap.findAux_isSome`, `Syntax.structEq_eq`, `PersistentHashMap.WF.find?_eq`, `PersistentHashMap.WF.toList'_insert` | Transitional and exactly guarded. This is the exact successful whole `buildNormalizationCandidate` call on real AliasFormer metadata. It proves the family check, family insertion, constructor check, and source-indexed list assembly in their actual contexts; it does not assert an erasure equality or authorize a caller-selected view. The v4.31 closed-expression cache facts are proved; their implementation proof reaches the two existing data-layout contracts. |
| `InductiveReplayFixtures.aliasFormerProducedGenerationCandidatePackage` | exactly the checked semantic set | Transitional and exactly guarded. The value uses the generic strengthened outer constructor to combine the exact ordinary producer equation, complete generation-shape success, and the semantic owner. The producer equation selects the candidate but grants no Theory or shape meaning. Generic construction of the verified per-position semantic inputs and analyzer-owned view WF from an arbitrary verified outer context and exact traversals is still open. Checked WF, every per-position shape record, raw/result and view-terminal equations, normalized-pair/order, dependent-list alignment, view telescopes, terminal typing, normalization equality, and post-family WF are generic consequences and are no longer part of that gap. |
| `InductiveReplayFixtures.aliasFormerFamily_whnf`, `aliasFormerCtor_whnf` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, `Expr.eqv_eq`, `Level.instLawfulBEqLevel`, `PersistentHashMap.findAux_isSome`, `Syntax.structEq_eq`, `PersistentHashMap.WF.find?_eq`, `PersistentHashMap.WF.toList'_insert` | Transitional and exactly guarded. These are the pre-family alias reduction and post-family opaque-constructor `Inner.whnf'` traces. They reach no pointer-equality axiom and use no `native_decide` or newly declared reduction principle; the remaining contracts are inherited Verify/platform debt. |
| `InductiveReplayFixtures.aliasFormerFamily_candidateTrace`, `aliasFormerCtor_candidateTrace`, `aliasFormerFamily_candidate` | the exact AliasFormer operational set plus `Expr.looseBVarRange_eq` from retained full checks | Transitional and exactly guarded. These pin both positions of the real singleton family/constructor candidate list plus the erased family view. They do not certify an arbitrary translated candidate or add semantic authority to `NormalizationCandidate`. |
| `InductiveReplayFixtures.aliasFormerFamily_candidateRun_exists`, `aliasFormerFamily_candidateSource_tr`, `aliasFormerFamily_candidateView_tr` | respectively the exact checked semantic set, retained-check set, and checked semantic set | Transitional and exactly guarded. The existential fixture instantiates automatic root-context and source/output recovery on actual metadata without supplying a Theory expression. The endpoint fixtures pin the strict raw and reconstructed view translations. AliasFormer's normalization and generation evidence consume the same interpreted trace; none of these fixtures authorizes an arbitrary candidate. |
| `InductiveReplayFixtures.aliasFormerNormalizationCandidateRun`, `aliasFormerCandidateNormalization_eq` | exactly the checked semantic set | Transitional and exactly guarded. The complete source-indexed singleton list now computes the established AliasFormer view and supplies its live `NormalizationRun`; all downstream checked generation and replay roots therefore exercise the generic list boundary. `aliasFormerTruncatedView_rejected` separately uses only `propext` and proves a shorter view fails before transaction construction. |
| `InductiveReplayFixtures.recAlias_whnf` | the preceding exact set plus `Expr.mkAppData_eq`, `Expr.mkData_eq`, `Expr.replace_eq`, and `Level.hasParam_eq` | Transitional and exactly guarded. The additional contracts arise from instantiating and reducing the universe-polymorphic `RecAlias` value. The former `Expr.hasLevelParam_eq` axiom is now a theorem whose implementation proof reaches the two data-layout contracts. This is still an execution theorem, not an oracle that asserts its result. |
| `InductiveReplayFixtures.aliasFormerFamily_checkType`, `aliasFormerCtor_checkType` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, `Expr.eqv_eq`, `Expr.looseBVarRange_eq`, `Level.instLawfulBEqLevel`, `PersistentHashMap.findAux_isSome`, `Syntax.structEq_eq`, `PersistentHashMap.WF.find?_eq`, `PersistentHashMap.WF.toList'_insert` | Transitional and exactly guarded. These are exact operational full-check traces. The family check returns `Sort 2`; the constructor check runs after raw-family insertion and returns the retained `TypeFamilyAlias`. Both record the cache result, reach no pointer-equality contract, and introduce no evaluation axiom. |
| `InductiveReplayFixtures.aliasFormerFamily_isType_checked`, `aliasFormerCtor_isType_checked`, both `*Normalization_wf_checked`, both `*Block_wf_checked`, and both `*GenerationChecked_wf_checked` roots | `propext`, `sorryAx`, `Classical.choice`, `ptrEqConstantInfo_eq`, `ptrEqExpr_eq`, `Quot.sound`, `Expr.abstractRange_eq`, `Expr.abstract_eq`, `Expr.eqv_eq`, `Expr.hasLooseBVar_eq`, `Expr.instantiate1_eq`, `Expr.instantiateRange_eq`, `Expr.instantiateRevRange_eq`, `Expr.instantiateRev_eq`, `Expr.instantiate_eq`, `Expr.looseBVarRange_eq`, `Expr.lowerLooseBVars_eq`, `Expr.mkAppData_eq`, `Expr.mkData_eq`, `Expr.replace_eq`, `Level.hasMVar_eq`, `Level.hasParam_eq`, `Level.instLawfulBEqLevel`, `PersistentArray.toList'_push`, `PersistentHashMap.findAux_isSome`, `Syntax.structEq_eq`, `PersistentHashMap.WF.find?_eq`, `PersistentHashMap.WF.toList'_insert` | Transitional and exactly guarded. The semantic bridge correctly inherits the existing verified checker's pointer/reflection, data-layout, and container contracts; completing the paired block and generation certificates adds no dependency beyond the normalization endpoint. `sorryAx` remains on the separately tracked translation frontier. The v4.31 closure drops the generated `mkAppRangeAux` axiom and the previously reachable TreeMap contract. This is development evidence, not a release allowlist, and it must not reach Theory or ix semantic roots. |
| `InductiveReplayFixtures.aliasFormerGenerationCandidatePackage`, `aliasRecAddInductTraceChecked`, `aliasRec_trEnv'_checked` | exactly the preceding checked semantic set | Transitional and exactly guarded. The semantic package owns the generation/WF pair, and the AliasRec replay retains the established checked semantic closure. No outer producer equation is involved in these roots. |
| `InductiveReplayFixtures.aliasFormer_addInductCertified_checked`, `aliasFormerGenerationChecked_wf_checked`, `aliasFormerAddInductTraceChecked`, `aliasFormer_trEnv'_checked` | exactly the preceding checked semantic set | Transitional and exactly guarded. These concrete consumers now project from the produced package, making exact whole-call provenance visible in their axiom reports. Proof erasure still keeps those contracts out of transaction computation, and the generic Theory API remains Theory-clean; the inherited `sorryAx` and platform equations remain release-blocking for this Verify-produced value. |
| `InductiveReplayFixtures.annotatedPiCtor_candidateTrace`, `annotatedPiFamily_candidateTrace` | exact guarded operational subsets of the checked semantic set; the nested constructor root inherits `sorryAx`, `ptrEqExpr_eq`, and the existing Expr/Level/container refinement equations, while the family root uses only `propext`, `Classical.choice`, `Quot.sound`, `Expr.eqv_eq`, `Expr.looseBVarRange_eq`, `Level.hasParam_eq`, `Level.instLawfulBEqLevel`, and `Syntax.structEq_eq` | Transitional and exactly guarded. These are the exact recursive candidate traversals selected by the real constructor and family producer calls. The family profile remains narrow; the constructor profile exposes existing checker-refinement debt because it traverses annotation consumption beneath a recursive Π. Neither trace is semantic authority by itself. |
| `InductiveReplayFixtures.annotatedPiNormalizationCandidate_produced` | `propext`, `sorryAx`, `Classical.choice`, `ptrEqExpr_eq`, `Quot.sound`, `Expr.eqv_eq`, the existing instantiate/replace/loose-variable contracts, `Expr.mkAppData_eq`, `Expr.mkData_eq`, `Level.hasMVar_eq`, `Level.hasParam_eq`, `Level.instLawfulBEqLevel`, and the existing persistent-array/hash-map/syntax contracts | Transitional and exactly guarded. This is the exact successful whole `buildNormalizationCandidate` equation for AnnotatedPi, including nested Π traversal and dependent list assembly. The four former cached-`Expr` axioms are now proved; their data-layout dependencies remain visible and do not assert semantic normalization. |
| `InductiveReplayFixtures.annotatedPiProducedGenerationCandidatePackage` | exactly the checked semantic set | Transitional and exactly guarded. The record combines AnnotatedPi's exact whole operational result with its semantic-generation owner. As for AliasFormer, the producer equation selects the candidate while the retained semantic hierarchy supplies all Theory meaning; inherited `sorryAx` and platform equations remain release-blocking. |
| `InductiveReplayFixtures.annotatedPiNormalizationCandidateRun`, `annotatedPiGenerationCandidateRun`, `annotatedPiGenerationCandidatePackage`, `annotatedPi_addInductCertified`, `annotatedPiGenerationChecked_wf_checked`, `annotatedPiAddInductTraceChecked`, `annotatedPi_trEnv'_checked` | exactly the preceding checked semantic set | Transitional and exactly guarded. `AnnotatedPi` exercises the complete recursive-Pi annotation path: exact full checks, WHNF, annotation consumption, lazy-delta definitional equality, recursive candidate contexts, generation assembly, the public certified transaction, and final checked replay. The fixture adds no oracle, and the inherited `sorryAx`/platform closure remains release-blocking exactly as for the alias fixtures. |
| `InductiveReplayFixtures.indexedVecNormalizationCandidateProduced` | the exact `IndexedVec` operational set: `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, the retained Expr/Level/cache equations, and the persistent-array/hash-map/syntax contracts printed at the root | Transitional and exactly guarded. This is the complete one-parameter, one-index, ordered `nil`/`cons` outer producer equation. It selects the exact candidate but supplies no Theory meaning by itself. |
| `InductiveReplayFixtures.indexedVecSemanticProducedGenerationCandidatePackage`, `indexedVecSemantic_trEnv'_checked` | exactly the checked semantic set used by the existing produced-package replays | Transitional and exactly guarded. These roots interpret every family/constructor node at the identity endpoint, assemble the source-indexed generation package, project the proof-erased Theory certificate, and carry that same package through the final E1 replay. The former closedness cache axioms are proved on v4.31; the fixture adds no oracle or axiom, and inherited `sorryAx` and platform contracts remain release-blocking and visible in both exact guards. |
| `InductiveReplayFixtures.annotatedPiFinalEnv_iota_mem` | `propext`, `Quot.sound` | Accepted logical baseline and exactly guarded. Once the checked generation value is supplied, membership of the generated recursive-Pi iota rule in the final Theory environment does not inherit the Verify checker closure. This is the ix-relevant separation to preserve in the general producer/public path. |
| `VEnv.addInduct_success`, `addInduct_checked`, constructor/recursor collision rejection | `propext`, `Classical.choice`, `Quot.sound` | Accepted logical baseline; compile-time guarded. The success certificate carries analyzer evidence rather than postulating it. `Classical.choice` now enters because the transaction's public artifacts are identity-normalization specializations of the mixed generator. |
| `VEnv.addInduct_WF` | `propext`, `Classical.choice`, `Quot.sound` | Accepted logical baseline; compile-time guarded. |
| Recursive-Pi roots (`recTypeRec_isType`, `recConstRec_wf`, `ruleCallRec_hasType`, `minorAppRec_hasType`, `recRuleAppRec_hasType`, `ruleRec_WF`) | `propext`, `Classical.choice`, `Quot.sound` | Accepted logical baseline; every named root has an exact compile-time guard, including the final generalized iota-rule preservation theorem. No custom or Verify axiom reaches the public generalized Theory path. |
| `TrTypeExpr.to_trExprS` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` | Transitional only. The helper itself is projection-free, but its `TrExprS` result type reaches the still-sorried `TrProj`; compile-time guarded. |
| `AddInductTrace.to_addInductGeneration`, `AddInduct.to_addInduct`, `AddInduct.le`, `Aligned.addInduct`, `TrEnv'.wf`, `TrEnv'.aligned` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` | Transitional only. The Verify trace now proves and its public wrapper existentially exposes the exact normalized Theory transaction. The `sorryAx` is inherited because `TrExprS` has a projection constructor whose relation `TrProj` is still a sorry; P0-P2 must remove it. The stabilized roots are compile-time guarded so any closure change is reviewed. |
| `TrEnv'.of_value` | the preceding set plus `Lean.PersistentHashMap.findAux_isSome`, `Lean.PersistentHashMap.WF.find?_eq`, and `Lean.PersistentHashMap.WF.toList'_insert` | Transitional Verify/platform debt. T2 must prove or narrowly manifest the persistent-map contracts, while P removes `sorryAx`. |
| `InductiveReplayFixtures.nat_trEnv'`, `eq_trEnv'`, `indexedVec_trEnv'`, `acc_trEnv'`, `aliasFormer_trEnv'`, `aliasRec_trEnv'`, their WF/alignment roots, and `seed_after_nat_of_value` | the `TrEnv'` set plus the same three persistent-map contracts | Transitional fixture closure, compile-time guarded. The collection contracts enter while proving freshness for the concrete sequence of `SMap` insertions; the fixtures declare no axiom and must shrink with P/T2. The two aliases add no dependency beyond the existing replay closure despite exercising non-identity normalization. |

Do not summarize this table as “four acceptable axioms.” A theorem's axiom
set includes dependencies occurring through its statement and inductive
types, not just constants named in its proof body. In particular, E1 can be
locally sorry-free while its exported roots remain transitively sorry-bearing.

#### Axiom-set decision and release thresholds

**Decision:** the axiom set of the current inductive **Theory** roots is
reasonable. It contains only the standard Lean logical principles
`propext`, `Classical.choice`, and `Quot.sound` (often a strict subset), and no
axiom asserting facts about the behavior or representation of Lean's
implementation. The axiom set of the current end-to-end **Verify** roots is not
release-acceptable: its `sorryAx` and collection/opaque implementation
contracts are useful diagnostics while proofs migrate, not foundations to
endorse. The checked normalization producer and the candidate-generation
assembler do not change that verdict: their design is reasonable because they
record concrete checker executions, recursively extract exact binder/result
evidence, and derive Theory equality through existing refinement theorems.
Their exact guarded closures still expose the inherited `sorryAx`,
pointer/reflection, translation, and container debt that must be discharged or
isolated before release. The `AnnotatedPi` slice confirms that verdict at the
hardest current annotation seam: retaining only the structural annotation
trace and exact `isDefEq` run is sufficient, while the opaque helper agreement
remains a runtime producer check rather than an assumed theorem. The four
cached-`Expr` properties it exercises are proved on v4.31; their proofs route
through the two already classified data-layout contracts, which remain exactly
guarded and outside the release allowlist. The automatic semantic-input,
produced-hierarchy, and semantic-generation projection roots have exactly the
same checked semantic set as the retained interpreter; their compile-time
guards show no trust growth. Returning the assembled hierarchy under
`Nonempty` is deliberate: it states semantic existence without using choice to
extract a data-bearing checker-selected view. The exact AliasFormer whole-call
proof no longer reaches three separate closedness cache axioms; it reaches
`Expr.mkData_eq` and `Expr.mkAppData_eq` through the new kernel proofs instead.
Those dependencies are exactly guarded and remain transitional layout
contracts. No new axiom or oracle was added.
The certified public path sharpens this separation: its generic Theory
transaction theorems use only the accepted logical baseline, while concrete
AliasFormer/AnnotatedPi/`IndexedVec` certificate values retain the exact
transitional Verify closure that produced their semantic proofs. Proof erasure prevents
that closure from influencing transaction computation, but does not erase it
from the axiom report of a concrete proof-carrying value. The optional
`ProducedGenerationCandidatePackage` adds only an exact executable producer
equation; it grants no semantic authority without the enclosed checked
package. All three concrete certificates and replays intentionally project
from their produced values; their exact guards therefore retain the
fixture-specific closedness/cache equations reached by ordinary checker
execution. The generic Theory `GenerationCertificate` and transaction
theorems retain their smaller accepted logical closure.
This distinction is part of the formalization's specification.

| Boundary | Allowed during development | Required at its release gate |
|---|---|---|
| Computational `Checked` analysis, normalization shape, and generation | No axiom declaration; evaluation and equality fixtures must compute | Same; no oracle or opaque semantic bridge in acceptance/generation |
| Theory normalization validity, preservation, patterns, projection semantics, and ix-facing Theory API | Any subset of `propext`, `Classical.choice`, `Quot.sound`; exact closure guarded per exported root | Same subset policy; zero `sorryAx`, zero project-specific axiom, and no import path to `Verify/Axioms` or `PtrEq` |
| Verify's mathematical refinement roots | Transitional bridges may remain only when named, classified, and exposed by an exact guard | Standard logical baseline only, unless the theorem is explicitly a platform-refinement theorem rather than a mathematical soundness theorem |
| Version-pinned platform adapter | A narrowly stated candidate contract with an owner, pinned Lean revision, removal issue, and tests | Only reviewed manifest entries; expected upper bound is the two pointer-equality implications and possibly lawful level `BEq`. These must not reach Theory or ix's semantic theorem roots |
| Fixtures and differential tests | May expose transitional dependencies to diagnose their path | They do not justify an axiom; release fixtures must have the closure required by the root they certify |

Audit computation and proof closure separately. For example,
`normalizationShape`, `checked?`, and `identityChecked?` are executable
definitions with no normalization oracle, while a theorem or dependent value
carrying the proof `normalizationShape source source = true` may report the
standard logical closure used by Lean's generic `BEq` lawfulness proof. That
is acceptable under the Theory threshold; it is not permission to replace the
Boolean test or semantic `Normalization.WF` evidence with an axiom.

Apply the following rules mechanically:

1. Treat the accepted logical baseline as a **set upper bound**, not a demand
   that every theorem use all three axioms. Keep exact `#guard_msgs` checks for
   today's named roots so either growth or unexpected shrinkage receives
   review.
2. Reject `sorryAx` from every release root. A proof whose statement reaches a
   sorried relation is not release-clean merely because its proof body contains
   no `sorry`.
3. Reject every known-false cache equation from every supported root and ban
   project-specific axioms from the global simp set. Removing `[simp]` is only
   containment; the declaration must still be proved, narrowed, or made
   unreachable.
4. Require an explicit design decision before expanding the logical baseline
   or platform manifest. Proof difficulty, convenience, or pre-existence in
   `Verify/Axioms.lean` is not sufficient justification.
5. Keep ix's `NativeOracle` in ix's own named consumer boundary. It does not
   authorize a corresponding lean4lean Theory axiom, an assumed
   `InductiveOracle`, or an opaque projection relation.
6. Treat a normalization view as untrusted data until it has both computed
   shape coherence and an environment-indexed `Normalization.WF` proof.
   Verify must derive that proof from translated checker/defeq behavior, and ix
   must derive it from its ordinary Theory typing/defeq world. Neither consumer
   may assume a normalization oracle or add a project-specific reduction axiom.

For the I2 normalization migration, apply that policy to a fixed root set
rather than auditing whichever helper happens to be convenient:

1. The executable roots `normalizationShape`, `Normalization.check?`,
   `generationShape`, and the mixed motive/minor/recursor/rule constructors
   must continue to compute without an oracle. Their kernel-equality fixtures
   are computational tests, not substitutes for semantic preservation.
2. Guard the component preservation roots
   `GenerationEnv.motive_isType`, `minor_isType`, `minorTypes_onTel`, the
   completed `recType_isType`/`recursor_wf` pair, `ruleCall_hasType`,
   `rule_WF`, `generatedRules_WF`, and the complete generated-rule fold.
   Record the exact closure of each;
   the permitted set is a subset of
   `{propext, Classical.choice, Quot.sound}`, not permission to acquire all
   three.
3. Guard the block-level theorem that turns `GenerationChecked.WF` into
   well-formed raw constants, a mixed recursor, and mixed rules. Then guard the
   normalized `addInduct_success`, lookup/membership/atomicity consequences,
   and `addInduct_WF` separately. A clean component proof does not certify a
   wrapper whose statement or result type reaches a forbidden axiom.
4. Keep identity-normalization compatibility roots separate from the general
   normalization roots. The identity wrapper must reduce to the legacy result;
   the general path must consume explicit `Normalization.WF` evidence and may
   not infer semantic validity from shape coherence.
5. Before closing the I2 artifact or transaction checkbox, run both the exact
   guards and a generated transitive closure report for the public roots.
   Reject `sorryAx`, every `Verify/Axioms` or `PtrEq` dependency, and every
   project-specific declaration even when it enters only through a theorem's
   type.
6. Apply the same audit to the eventual E2 theorem consumed by ix. Its Theory
   closure must meet the standard upper bound. Verify's actual-metadata trace
   may expose named transitional platform debt during development, but it
   cannot be the release proof of the ix-facing semantic theorem until that
   debt has been removed or isolated outside the theorem's closure.

### 2.4 Ix demand surface, re-audited

Ix has advanced beyond the original “construct the first oracle” framing.
Its E2b milestone now constructs `InductiveOracle` for a staged, closed
singleton-enumeration fragment and its next local critical path is E3-S,
which composes that fragment with the production environment driver. This does
not complete lean4lean's handoff: L4L-11 widens the construction from that
deliberately small fragment to the full safe single/mutual/nested block class
established by L4L-07 through L4L-10B. The fork should strengthen the shared
Theory certificate and lookup/pattern consequences, not duplicate ix's
address, catalog, ingress, or driver proofs.

The current ix working tree contains about 55,449 lines under
`Ix/Tc/Verify/` and 1,192 root entries across its two audit manifests. It
imports these lean4lean modules:

```text
Theory.VLevel
Theory.VEnv
Theory.Typing.Env
Theory.Typing.Lemmas
Theory.Typing.Pattern
Verify.Typing.Expr
Verify.Typing.Lemmas
Verify.VLCtx
```

The ix obligations and their lean4lean owners are:

| Ix boundary | Lean4Lean deliverable |
|---|---|
| `InductiveOracle` | full inductive spec/generation, the Theory-only `GenerationCertificate`/`addInductCertified` consumer boundary, environment alignment, lookup/monotonicity lemmas, and block-local pattern facts; ix must construct certificates from its ordinary semantic world rather than import Verify checker state |
| upstream sorry origins `VInductDecl.WF`, `VEnv.addInduct`, `addInduct_WF` | already removed on the fork baseline; publish and pin to shrink ix's audit, then broaden the spec enough to construct the oracle |
| abstract `RawProjRel` + `TrProjOK` | Theory-level projection relation and its lift/inst/WF/uniqueness/transport package |
| `literalWF`/`hlit` assumptions | Theory-level primitive/prelude readiness implies typing of `trLiteral` |
| ix recursor-pattern soundness | generated rules in `SimplePattern.iota` form plus `Params`-shaped soundness and non-overlap facts |
| `forallE_inv_stratified` and `sort_inv` sorry origins | live metatheory track, not permanently deferred |
| `NativeOracle` | remains an explicit consumer oracle; lean4lean documents and proves stability of the `.extra` extension point |

### 2.5 Retired milestone vocabulary

The companion's M0-M5 labels and this roadmap's former C0-C8 labels are
historical only. They mixed infrastructure, proof breadth, consumer handoffs,
and release work at incompatible scales, which made “M0 complete” ambiguous.
Section 13's L4L-00 through L4L-20C ladder supersedes both status systems and is
the only source of current milestone status.

For historical discussion: companion M0/M1 are covered by completed L4L-00;
M2 is decomposed across L4L-01A through L4L-09C; M3 across
L4L-10A/L4L-10B/L4L-11; M4 across L4L-13A through L4L-15C; and M5's
nested/upstream pieces are L4L-09A through L4L-09C and L4L-20C respectively.
The old C0-C8 mapping is recorded after the new
milestone table. None of these legacy names may be used to report current
status.

<details>
<summary>Archived M0-M5 assessment before the L4L ladder</summary>

| Companion milestone | Archived assessment (superseded) |
|---|---|
| **M0** | Partially complete: upstream remote, token-aware sorry frontier, Nix CI, and a root-level non-ignored divergence ledger exist. The coherent generalized one-family/checked-analysis slice now includes recursive-Pi `Acc`, annotation-complete recursive candidate certification, generic generation-certificate assembly, the proof-carrying public non-identity transaction, three published produced packages, generic parameter/index family validation, exact `IndexedVec` family/`nil`/`cons` candidates, a complete executable outer producer equation, generic exact identity replay, checked `IndexedVec` E1 replay, arbitrary-length source-indexed operational list assembly, generic outer produced-package construction, retained source-indexed semantic ownership, automatic produced semantic-hierarchy assembly under `Nonempty`, semantic-owned generation/package projections, generic derivation of family/constructor view telescopes and terminal typing, exact dependent analyzer provenance, derived normalization identity, reconstructed post-family WF, analyzer-determined raw/view family and constructor alignment, generic raw telescope/result and view-terminal derivation, exact dependent constructor-list reconstruction, and a complete executable generation-readiness gate that derives checked WF plus every per-position shape record when combined with exact analysis and analyzer-owned view WF. At archival, the source checkpoint was `bbb45e0e950724cdbbd405d75e304e2020cecf82`, with tracked ledger child `c4fd62b23a89500154b113d849d183afbf84907f`, on `argumentcomputer/lean4lean`'s `jcb/induct` branch. Constructing the verified semantic inputs and analyzer-owned view WF from one arbitrary verified outer context and its exact traversals, then combining them with the strengthened gate to return a complete produced package, was the immediate M0 boundary. Ix Pin A and full downstream `IxTcVerify`/trust-audit validation are complete at the recorded pair Lean4Lean `5e5bb767b3491d21a71908d4c58bcbaa007283bb` and local ix snapshot `1f73f5c016907eadb8ed0dc86ac65b07eb24a145`; actual platform builds remain assigned to Linux/Darwin CI. |
| **M1** | Complete and exceeded on committed `master`: the vertical slice now covers parameters plus Nat/Bool/List/Prod/Option, with sorry-free `addInduct_WF`. |
| **M2** | In progress: the generalized one-family slice is green for Eq, HEq, an index-changing recursive family, and recursive-Pi `Acc`. Shared `Checked` analysis covers closure, all universe annotations, generated-name uniqueness, family-telescope self-reference, direct result shape, and recursive Pi targets; `Checked.WF env` carries normalized semantic evidence including the Prop impredicativity exception. Generalized artifacts, preservation, public accessors, and the `Acc` transaction agree. Actual alias metadata established the separate raw/view `Normalization` boundary; `NormalizedChecked` packages the raw singleton and checked view, both alias cases have combined semantic certificates, and the complete mixed generator/preservation path feeds a single traced `addInductGeneration` core. Verify's generic run/evidence bridge turns exact checker executions into Theory typing, equality, and `Normalization.WF`. `CandidateExprRun.spineEvidence` extracts raw/view telescopes and terminal results under an explicit stored-spine invariant; `TelResultDefEqEvidence.replacePrefix` transports constructor evidence to the family-emitted parameter prefix; and the dependent `GenerationCandidateRun` assembler produces complete `GenerationChecked.WF` without truncation, forall injectivity, or a selected arbitrary view. Exact checked decomposition, dependent analyzer provenance, and retained semantic evidence now derive view telescopes, terminal typing, normalization identity, post-family WF, raw/view family and constructor alignment, and the complete dependent constructor list. The consolidated executable hierarchy gate additionally derives checked WF and every per-position stored-spine/count record from exact analysis and analyzer-owned view WF; fixtures provide neither class of evidence, and missing/extra constructor regressions pin cardinality. `GenerationCandidatePackage` owns the resulting assembly and erases to the Theory-only `GenerationCertificate` consumed by `addInductCertified`; semantic-owned projections attach exact strengthened whole-call provenance to that same candidate. AliasFormer, the nested recursive-Pi AnnotatedPi, and the parameter/index/two-constructor `IndexedVec` all route their consumers through this boundary, including checked E1 replay. Generic construction of the verified semantic inputs and analyzer-owned view WF from arbitrary verified outer metadata, full environment-relative WHNF/defeq integration, positivity, small elimination, K, mutual/nested blocks, and kernel-complete coverage remain absent. |
| **M3** | In progress: the core Verify `AddInduct` trace retains `GenerationChecked` and its semantic certificate; normalized alignment, monotonicity, `TrEnv'` WF, and environment-history proofs are live. Actual-metadata Nat, Eq, `IndexedVec`, `Acc`, `AliasFormer`, and `AliasRec` replays pin all kernel rule RHSs, final equality, WF/alignment, and lookup uniqueness. The `AnnotatedPi` transaction additionally replays a nonempty recursive-Pi candidate whose raw constructor retains `outParam Prop`, including the generated recursor and iota rule. Generic candidate-spine extraction, exact constructor-prefix replacement, analyzer-determined normalized pairing/order, dependent constructor-list generation assembly, generic raw/view component and terminal derivation, generic view-telescope/result-typing derivation, analyzer-derived normalization alignment, reconstructed post-family WF, candidate-derived `GenerationChecked.WF`, exact outer package construction, automatic produced semantic-hierarchy assembly, retained semantic ownership, and derivation of checked WF plus every per-position shape record from one complete hierarchy gate are live. The generic package fixes generation/WF ownership across the public certified transaction and metadata replay; AliasFormer and AnnotatedPi provide two non-identity exact strengthened-producer instances, and `IndexedVec` provides the parameter/index/two-constructor identity-normalizing instance. Generic construction of the verified semantic inputs and analyzer-owned view WF from an arbitrary verified outer context, the broader I2-I4 replay matrix, and the block-local `Params` package remain absent. |
| **M4** | Not started: `TrProj` and all seven structural laws remain sorries. |
| **M5** | Not started: nested parity and the semantic upstream PR series have not begun. |

</details>

## 3. Architecture and trust contract

These are invariants at every milestone.

1. **Theory points downward only.** `Lean4Lean/Theory/` imports no
   `Lean4Lean/Verify/`. Mathematical declarations mention `VExpr`, `VLevel`,
   `VEnv`, and proof objects, not `Lean.Expr`, `FVarId`, `ConstMap`, or ix's
   `KExpr`/addresses/catalogs.
2. **Consumer-neutral semantics.** No ix namespace, hash, address, cache, or
   checker-state type enters lean4lean. Ix-specific transport stays in ix.
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
   contract covers the full safe implementation. Never replace a missing case
   with `sorry`, an oracle, or an overstrong premise that real kernel output
   cannot satisfy.
6. **Checked analysis and normalization have explicit roles.** The raw
   `VInductDecl` is the stored constant payload. `Normalization` supplies a
   shape-compatible analysis view, and `Normalization.WF env` justifies that
   view by Theory defeq at the kernel's declaration stages. `Checked` is the
   environment-independent result computed from the view; `Checked.WF env`
   supplies its semantic typing evidence. Do not fold `VEnv`, `Lean.Expr`, or
   ix-specific evidence into the computational analyzer, and do not treat a
   shape-compatible view as semantically valid without its WF proof.
7. **One accepted source/view pair, one artifact path.** A normalized block
   accepted by the public transaction must preserve the raw metadata payload,
   use the same checked view for every WHNF-sensitive decision, generate and
   preserve one artifact set, expose it through `AddInductSuccess`, and replay
   it in Verify. Parallel raw/view or direct/generalized generators are
   permitted only as short-lived proof migrations; no checkpoint may accept a
   case for which the public accessor returns a weaker or different
   recursor/rule set.
   The consumer-facing erasure is `GenerationCertificate`: it must couple the
   exact generation with its WF proof, and `addInductCertified` must remain
   definitionally the same computation as `addInductGeneration`. The proof may
   authorize preservation but may not affect generated artifacts or transaction
   control flow.
8. **Additive migrations first.** Before changing an existing Theory
   signature, grep `ix:Ix/Tc/Verify/` and the upstream Verify layer. Add a new
   API and compatibility theorem first, flip ix, then remove the old path.
9. **Classic-module compatibility.** Ix currently uses classic imports because
   lean4lean does. Do not introduce `module` headers in reachable files without
   a coordinated migration.
10. **Axiom budget is checked per root.** New Theory roots may depend only on
   the accepted logical baseline (`propext`, `Classical.choice`, `Quot.sound`,
   usually a subset). Verify bridge contracts need a separate, named manifest.
   “It was already in `Verify/Axioms.lean`” is not acceptance.
11. **Every fork divergence is tracked.** Create a tracked
   `upstream-divergence.md` (or deliberately track `/plans`) with one entry per
   semantic/API delta, its ix impact, test, upstream issue/PR, and removal
   condition. Empty means fully upstreamed.

## 4. Dependency spine

The `S`/`I`/`E`/`L`/`P`/`M`/`V`/`T` labels below are stable work-package
references. They describe proof ownership and preserve detailed checklists;
they do **not** carry milestone status. Section 13 is the only execution order
and the only place where a milestone may be `queued`, `active`, or `complete`.
There is no `partially complete` milestone state: useful prerequisites for a
future milestone remain recorded in their track, but that milestone stays
queued until every exit condition passes.

The primary execution order is deliberately serial. Letter suffixes are real
milestones, not subitems that may be completed as a batch:

```text
published baseline
  -> staged singleton semantic inputs
  -> family-validation semantics and post-family staging
  -> constructor-validation trace and semantics
  -> generic singleton package closure
  -> isolated level proof
  -> singleton validation/normalization/positivity/elimination closure
  -> mutual representation, validation, then generation/replay
  -> nested representation, transformation, then generation/replay
  -> generated-pattern core, then environment assembler
  -> ix inductive-oracle handoff
  -> Theory local-declaration surface, then literal/prelude readiness
  -> projection API decision, semantics, and laws
  -> projection checker, eta, and import closure
  -> metatheory route selection and sort inversion
  -> remaining injectivity and weakening inversion
  -> Church-Rosser proof, then extension contract
  -> recursor reduction, environment/checker closure, and zero-sorry gate
  -> axiom retirement, differential corpus, and upstream release
```

No later milestone begins until the active one is complete. Read-only design
reconnaissance for a later milestone is allowed when it changes the active
design, but implementation and publication stay serial. This prevents several
half-migrated public artifact paths from being live simultaneously and gives
each checkpoint one auditable claim. Projection semantics intentionally waits
for the full inductive/structure descriptor even though preliminary design
work could be done earlier.

## 5. Track S — stabilize and publish the work already done

### S0 — make the active indexed port green (completed by L4L-00)

- **Status: complete in the development branch on 2026-07-30.** The exact Theory and
  Verify build gate passes; keep the following as the regression checklist.
- [x] Finish the `Stage2Env` to `Stage3Env` conversion from line ~2000 onward in
  `InductiveLemmas.lean`.
- [x] Update every old helper application to the indexed signatures: motives now
  take `ty`, minors take both `ty` and constructor lists, recursive positions
  carry index spines, and result typing consumes `SpineWF`.
- [x] Reprove the recursor type, recursor constant, constructor fold, iota LHS/RHS,
  rule WF, and final `addInduct_WF` in that order. Do not patch from the bottom;
  each generated component should have a named typing lemma used by the next.
- [x] Rename residual Stage-2 declarations/comments only after the proof compiles,
  to keep review mechanical.
- [x] Restore an executable `#print axioms`/`#guard_msgs` check for
  `VEnv.addInduct_WF`; it currently accepts exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- [x] Finish the exact gates in §13. The sorry audit,
  `lake build Lean4Lean.Theory Lean4Lean.Verify`, formatter check, and
  `nix flake check --accept-flake-config --print-build-logs` all pass. A
  successful default `nix build` alone remains insufficient.

### S1 — publish safe checkpoints (ongoing gate; baseline in L4L-00)

- [x] Publish the coherent Stage-3/I1/E1/bounded-I2 checkpoint after rerunning
  the full gate. Revision `472a6f0417e574aaf277fc0150284d0b733aec3a`
  is published on `argumentcomputer/lean4lean` after the sorry-frontier,
  Theory/Verify build, formatter, diff, and Nix-build gates passed. Generalized
  recursive-Pi preservation, the public artifact switch, `Acc` transaction and
  replay, the additive paired normalization boundary/alias certificates,
  and exact axiom guards are green. At that checkpoint, the broader
  cross-system evaluation gate in §13 was still outstanding. The public transaction
  remains the coherent raw-normal-form subset; do not checkpoint midway
  through the later raw/view artifact or transaction switch. Keep
  `efb2a2b2` as the recoverable Stage-2 checkpoint and never publish an
  intermediate red or semantically split state.
- [x] Publish the candidate-context-provenance checkpoint after the same local
  source and default-Nix gates. Revision
  `1fb7d6ef9042c5a80b2de9320c88ac0f3ce404cb` context/source-indexes every
  recursive candidate trace, derives checker-output translations from verified
  executions, and transports alias-valued inferred types to structural Pi
  sorts without adding an axiom. It remains the fixed `master` baseline; at
  that checkpoint, the broader cross-system evaluation gate was outstanding.
- [x] Publish the recursive-normalization-candidates checkpoint only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Revision
  `9fde4c6b6c34cdb5b7c71aebfff25ac75a269a56` constructs exact verified root
  and Pi-binder contexts, proves binder freshness and empty-state name
  reservation, recovers the root Theory translation from the retained full
  check, and recursively certifies raw-domain traces. The actual AliasFormer
  metadata exercises the automatic-root path, and every new semantic root has
  an exact axiom guard. The exact sorry-frontier, full Theory/Verify build,
  formatter, diff, Theory import-boundary, and default-Nix gates passed on
  2026-07-31. `master`, `origin/master`, and the digama upstream were not
  moved; the cross-system evaluation gate was then outstanding.
- [x] Publish the annotated-normalization-binders checkpoint only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Revision
  `b2839120ee3c743fd621154096346c7319141f14` preserves raw annotation syntax,
  structurally certifies all four `consumeTypeAnnotations` paths, retains an
  exact successful ordinary-checker equality run, refines it to Theory
  equality, and transports recursive body evidence across the raw, consumed,
  and normalized binder contexts. The former raw-domain restriction is gone;
  fixtures cover all four positive gadgets and one exact non-defeq rejection.
  The exact sorry-frontier, full Theory/Verify build, formatter, diff, Theory
  import-boundary, fixture-target, and default-Nix gates passed on 2026-07-31.
  `master`, `origin/master`, and the digama upstream were not moved; the
  cross-system evaluation gate was then outstanding.
- [x] Publish the singleton-normalization-candidates checkpoint only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Revision
  `a84aa19c3e243f9b35bd5baa988c16a0cce39093` adds exact root endpoint
  certificates, source-indexed constructor-list runs, and a singleton family
  assembler that constructs Theory `Normalization` and `NormalizationRun`
  without `head!`, unchecked `zip`, or a caller-selected unrelated view.
  AliasFormer's real pre-family and post-family candidate positions now drive
  its live normalization, dependent checked analysis still succeeds, and a
  truncated constructor view is rejected before transaction construction.
  The exact 20-entry sorry frontier, full Theory/Verify build, formatter, diff,
  Theory import-boundary, fixture-target, and default-Nix gates passed on
  2026-07-31. `master`, `origin/master`, and the digama upstream were not
  moved; the cross-system evaluation gate was then outstanding.
- [x] Publish the candidate-generation-certificates checkpoint only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Revision
  `c2b1c4fb5f0f992391301c1486e076f13a3af1b3` extracts the exact raw/view
  telescope and terminal-result evidence from stored-spine candidate runs,
  transports declared constructor parameter prefixes to the emitted family
  prefix in exact induced contexts, folds a dependent source-indexed
  constructor list, and assembles generic `GenerationChecked.WF`.
  AliasFormer's real non-identity family/constructor candidates now supply its
  existing checked end-to-end transaction through this generic assembler.
  The exact 20-entry sorry frontier, full Theory/Verify build, formatter, diff,
  Theory import-boundary, fixture target, exact axiom guards, and default
  `nix build` gate passed on 2026-07-31. `master`, `origin/master`, and the
  digama upstream were not moved; the cross-system evaluation gate was then
  outstanding.
- [x] Publish the annotated recursive-Pi replay checkpoint only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Revision
  `a1d8943a7b831b050fb8bc0689db2a186850a7f1` adds
  `AnnotatedPi.mk : ((p : outParam Prop) → AnnotatedPi) → AnnotatedPi`, proves
  the exact ordinary-checker full-check, WHNF, and complete lazy-delta
  raw-to-consumed equality traces, recursively certifies the nested candidate,
  and assembles `NormalizationCandidateRun`, `GenerationCandidateRun`, and
  `GenerationChecked.WF`. Its checked `AddInductTrace`/`TrEnv'` replay pins the
  final environment, generated recursor, and iota rule while retaining raw
  annotation syntax. The annotation producer's opaque-helper agreement is
  recorded as runtime validation rather than a semantic proof field; no new
  axiom, oracle, native evaluator, or opaque equation was added. Six exact
  root guards pin the inherited transitional Verify closure and the smaller
  `[propext, Quot.sound]` iota-membership closure. The exact 20-entry sorry
  frontier, full Theory/Verify build, formatter, diff, Theory import boundary,
  fixture target, and default `nix build` gate passed on 2026-08-01. `master`,
  `origin/master`, and the digama upstream were not moved; the cross-system
  evaluation gate was then outstanding.
- [x] Publish the certified non-identity consumer checkpoint only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch at
  `6a7788245831b24ae690cfb83659e892c2065be8`. The complete local gate,
  including the current-host full flake checks, is green, and remote-ref
  verification confirms only `origin/jcb/induct` moved.
  This checkpoint adds the Theory `GenerationCertificate` and
  `addInductCertified` API, its trace/atomic/WF theorems, the dependent Verify
  candidate package and checked replay constructor, the AliasFormer and
  AnnotatedPi public transaction fixtures, and the opaque-`outParam`
  whole-candidate rejection. Exact guards demonstrate the clean generic
  Theory closure and the retained concrete Verify closures. `master`,
  `origin/master`, and every digama/upstream ref remain unchanged.
- [x] Publish the executable-candidate producer checkpoint only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch at
  `bc37d436dfd6f7d6fa1ae186c0951e48677b931f`. AliasFormer now proves the
  exact successful `buildNormalizationCandidate` equation across family
  validation, raw-family insertion, constructor validation, and dependent
  candidate-list assembly. The resulting
  `ProducedGenerationCandidatePackage` supplies both its proof-erased Theory
  certificate and checked Verify replay. The exact 20-entry sorry frontier,
  focused and full Theory/Verify builds, formatter, diff and import-boundary
  audits, default `nix build`, and all six current-host flake checks passed on
  2026-08-01. Exact guards record the three existing expression-cache
  contracts added by the outer execution proof. `master`, `origin/master`, and
  every digama/upstream ref remain unchanged; `--all-systems` was still the
  pre-ix/release gate at this checkpoint.
- [x] Publish the AnnotatedPi outer-validation checkpoint only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch at
  `5e5bb767b3491d21a71908d4c58bcbaa007283bb`. The recursive occurrence test is
  now transparent and structural, and the fixture proves exact family
  validation, freshness, recursion detection, raw-family declaration, and
  recursive inner-Π `inferType`/`ensureType` execution. This is progress toward,
  not completion of, AnnotatedPi's whole-call produced package. The same commit
  restores CI all-system evaluation by replacing the nested unrealized
  `fileset.toSource` with `inputs.self.outPath`; the narrower source filter is a
  follow-up optimization. The 119-target source build, exact 20-sorry audit,
  current-host full flake check, and exact
  `nix flake check --all-systems --no-build --accept-flake-config` gate pass.
  `master`, `origin/master`, and every digama/upstream ref remain unchanged.
- [x] Publish exact AnnotatedPi constructor validation and positivity on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch at
  `33b99f4e462eaa02b78aba061dcac37bd64d84c4`. The checkpoint validates the
  complete annotated recursive-Π constructor in the real post-family
  environment and keeps both master refs and digama/upstream unchanged.
- [x] Complete AnnotatedPi's exact recursive candidate traversal, dependent
  family/constructor list assembly, successful whole
  `buildNormalizationCandidate` equation, and
  `ProducedGenerationCandidatePackage`; published only on `jcb/induct` at
  `a3ff9921cc7ef23ebbc808b4dcbab6a119378507` after the full Lean/Nix
  checkpoint gate.
- [x] Publish generic singleton family validation through arbitrary
  parameter/index candidate spines only on `argumentcomputer/lean4lean`'s
  `jcb/induct` branch at
  `9a865ea02d4326e60d0e5fd663d6efe79c735b1c`. The candidate trace now exposes
  its root WHNF, terminal context/result, positional parameter locals, index
  count, and exact emitted `InductiveStats`; the executable
  `checkInductiveTypes` loop is replayed from these source-indexed facts rather
  than a zero-parameter fixture theorem. Exact core axiom guards remain within
  the permitted logical baseline.
- [x] Publish the first real parameter/index family instance only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch at
  `a62736281ea419d7d0ee13d76f0e0fd9a4d9d90f`. The new
  `IndexedVecCandidate` module proves exact full-check, WHNF, fresh-local,
  reflexive domain-equality, recursive candidate, and complete family-validator
  executions for `IndexedVec.{u} (α : Type u) : Nat → Type u`, including the
  computed parameter/index statistics. The focused module build, 120-job full
  Theory/Verify build, exact 20-sorry audit, formatter/diff gates, default Nix
  build, and all six current-host flake checks pass on 2026-08-02. Exact guards
  record the existing Verify implementation contracts and inherited `sorryAx`;
  no axiom was declared. `master`, `origin/master`, and every digama/upstream
  ref remain unchanged. The ordered `nil`/`cons` package is deliberately the
  next checkpoint, not part of this claim.
- [x] Publish the verified syntactic-equivalence fast path only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch at
  `f0d80f8ba21e44a694566ea3d6469be85a809307`. Reflexive `isDefEq` calls now
  return before `isDefEqCore` and preserve the incoming checker state;
  `TypeChecker.Inner.isDefEq.WF` proves soundness by transporting the strict
  translation across `Expr.eqv`. Exact AnnotatedPi, AliasRec, and IndexedVec
  fixtures were updated and their obsolete equivalence-manager simulations
  removed. The exact 20-sorry audit, focused and 120-job full Lean builds,
  formatter/diff/import-boundary gates, default Nix build, all-system flake
  evaluation, and all six current-host flake checks pass on 2026-08-02. No
  axiom was added; `master`, `origin/master`, and every digama/upstream ref
  remain unchanged.
- [x] Publish the `IndexedVec` constructor and outer-producer series only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Revisions `67326590` and
  `c40a471d` certify `nil` and the dependent recursive `cons` candidate in the
  exact post-family environment; `c739d412` stabilizes candidate-context
  provenance; and `82f4a54c` proves the complete one-parameter, one-index,
  ordered two-constructor `buildNormalizationCandidate` result. Revision
  `d553930a` adds generic exact identity replay at caller-selected Theory
  endpoints. At that checkpoint local, Git, and `origin/jcb/induct` agreed at
  `d553930a`; both master refs and every digama/upstream ref remained unchanged.
- [x] Complete the `IndexedVec` semantic package from that exact executable
  result and publish it at `cf3d5a47d35867e0e6ebe023c0803982e3e36cd1`.
  Recursive identity for the family, `nil`,
  and `cons` supplies the family/constructor `GenerationCandidateRun`; the
  resulting `ProducedGenerationCandidatePackage` drives both the certified
  Theory transaction and checked E1 replay. Exact guards pin the public package
  and `TrEnv'` roots to the existing transitional Verify closure.
- [x] Run formatter/diff/import-boundary gates, describe, and publish the
  `IndexedVec` semantic replay checkpoint without moving either master or any
  digama/upstream ref. The semantic commit is `cf3d5a47`; local, Git, and
  `origin/jcb/induct` agree at its ledger-only follow-up `d35a2f6c`.
- [x] Generalize exact executable list assembly and publish it only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Commit
  `c9e4ae2d26f28e0adb0c21ffde0e11b42bb691c2` adds arbitrary-length dependent
  family-type, constructor, and complete-family `Produced` witnesses, routes
  AliasFormer and AnnotatedPi through the singleton instances, and routes
  `IndexedVec` through the ordered two-constructor instance. The three generic
  `.normalize` theorems are guarded at exactly
  `[propext, Classical.choice, Quot.sound]`. Focused and full Lake builds, the
  exact 20-sorry audit, all Nix gates, formatter, diff, and import-boundary
  checks pass. Local, Git, and `origin/jcb/induct` agree at ledger child
  `9ff6be1cac7a3b604b1209d11e0380a858d49574`; neither master nor any
  digama/upstream ref moved.
- [x] Generalize the outer produced-package construction and publish it only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Commit
  `a7d101b5e16f1258c6f5c2a7ea08e55f45eb17f1` adds
  `GenerationCandidateRun.producedPackage`, requires one exact
  source/candidate-indexed semantic run plus the matching whole-call producer
  equation, and migrates AliasFormer, AnnotatedPi, and `IndexedVec`. Its exact
  inherited `[propext, sorryAx, Classical.choice, Quot.sound]` closure is
  guarded. Focused and full Lake builds, the exact 20-sorry audit, all Nix
  gates, formatter, diff, and import-boundary checks pass. Local, Git, and
  `origin/jcb/induct` agree at ledger child
  `80f9dce41d0798bbb38d41c5abf9a21e25f74bc1`; neither master nor any
  digama/upstream ref moved.
- [x] Retain one source-indexed semantic hierarchy for normalization and
  generation and publish it only on `argumentcomputer/lean4lean`'s
  `jcb/induct` branch. Commit
  `f0caf16c5788d094fdbf1e990884c0c061d6fc75` adds
  `CandidateExprSemanticRootRun`, its automatic existential root constructor,
  and dependent constructor-list/family/singleton-normalization ownership;
  AliasFormer, AnnotatedPi, and `IndexedVec` all project their existing
  normalization and generation evidence from it. Focused and full Lake builds,
  the exact sorry-frontier check, default Nix build, all six current-host flake
  checks, whitespace checks, and a direct axiom audit pass. Local, Git, and
  `origin/jcb/induct` agree at ledger child
  `ea14f31ee172bef30b94c8b5f111bc109965f00d`; neither master nor any
  digama/upstream ref moved.
- [x] Assemble the produced semantic hierarchy and publish it only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Commit
  `e3cf22d293b081ba11be63e910d0d1e1510a042f` adds
  `CandidateExprSemanticRootInput`, dependent constructor/family/normalization
  inputs, and `NormalizationCandidateSemanticInput.exists_ofProduced`.
  Together they pair the arbitrary-length operational list witnesses with the
  exact verified contexts and strict translations at the same source-indexed
  candidate and return `Nonempty ProducedNormalizationCandidateSemanticRun`.
  The retained checker selects each Theory view; the operational result does
  not. Semantic-owned family/constructor generation structures and their
  compatibility/package projections remove parallel roots and spines.
  AliasFormer and `IndexedVec` exercise the complete path. Neither master nor
  any digama/upstream ref moved.
- [x] Harden semantic ownership and publish it only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Commit
  `7e5f4f7715cf71be8d09a583f0ec0d8f7aa02e72` migrates AnnotatedPi's remaining
  hierarchy and generation/package path, adds exact compile-time guards for
  the generic semantic inputs and projections plus all three fixture roots,
  proves automatic `IndexedVec` hierarchy assembly retains `nil`/`cons` order,
  and rejects the swapped view at `normalization?`. The exact 20-sorry audit,
  focused 118-job semantic replay, 157-job default Lake build, 124-job Nix
  proof build, default Nix build, all six current-host flake checks, all-system
  no-build evaluation, formatter, diff, and Theory import-boundary checks pass.
  Local, Git, and `origin/jcb/induct` agree at ledger child
  `1093311b9c4e74f3d1750676429acc5d112724fa`; neither master nor any
  digama/upstream ref moved.
- [x] Derive structural generation evidence and publish it only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Commit
  `2b1d802fc6796e7317ec1d24708a3ebdda416655` adds exact checked
  family/constructor shape theorems, derives the family terminal sort and every
  constructor result-target typing judgment, recovers view telescopes from
  exact non-forall terminals, and removes fixture-owned `viewTel`/`rightType`
  fields across AliasFormer, AnnotatedPi, and `IndexedVec`. The exact 20-sorry
  audit, focused direct compiles, 124-job Theory/Verify build, 157-job default
  Lake build, 124-job Nix proof check, default Nix build, all six current-host
  flake checks, all-system no-build evaluation, formatter, diff, and Theory
  import-boundary checks pass. Local, Git, and `origin/jcb/induct` agree at
  tracked ledger child `0270843dccd2e0599a48b40aa31d4fe6eb8c94af`;
  neither master nor any digama/upstream ref moved.
- [x] Derive generation analyzer provenance and publish it only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Commit
  `a64fe982bc2a7f1c6c34ec82565ec5fe1c26350b` replaces each semantic
  generation fixture's bare normalization equality with the exact successful
  dependent `generation?` equation. Theory derives the retained normalization
  from successful `check?`/`generation?`; Verify reconstructs post-family
  environment WF from retained semantic evidence and exact raw-family
  insertion. AliasFormer, AnnotatedPi, and `IndexedVec` now omit both
  `normalization_eq` and `typeEnv_wf`. Exact guards pin the two Theory roots and
  two Verify derivations. The exact 20-sorry audit, focused direct compiles,
  124-job Theory/Verify build, 157-job default Lake build, default Nix build,
  all six current-host flake checks, all-system no-build evaluation, formatter,
  diff, and Theory import-boundary checks pass. Local, Git, and
  `origin/jcb/induct` agree at tracked ledger child
  `4b66e50e3df95baab3f93a97867c4e31dc6ed21d`;
  neither master nor any digama/upstream ref moved.
- [x] Derive generation shape alignment and publish it only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Commit
  `5aa9ab69fce1c7dab3f4ca357f6ed8f349fd9397` introduces the reduced
  `GenerationCandidateSemanticShapeRun` boundary. Exact dependent analysis
  determines raw/check family identity, normalized constructor pairing and
  source order, while total stored-spine counts determine raw
  telescope/results and exact checked shape determines view terminals. The
  dependent recursive assembler reconstructs the full constructor run list
  without caller-selected pairs, `zip`, truncation, or reordering. AliasFormer,
  AnnotatedPi, and the two-constructor `IndexedVec` fixture now provide no
  component equations or normalized-pair alignment. Exact guards pin both
  singleton alignment roots to the small inherited Verify set and the public
  shape projection to the unchanged checked semantic set. The exact 20-sorry
  audit, focused direct compiles, 124-job Theory/Verify build, 157-job default
  Lake build, default Nix build, all six current-host flake checks, all-system
  no-build evaluation, formatter, diff, whitespace, and Theory import-boundary
  checks pass. Local, Git, and `origin/jcb/induct` agree at tracked ledger child
  `fda0016632e3b64d14e0628dbccd230338c531c0`; neither master nor any
  digama/upstream ref moved.
- [x] Consolidate generation readiness and publish it only on
  `argumentcomputer/lean4lean`'s `jcb/induct` branch. Commit
  `bbb45e0e950724cdbbd405d75e304e2020cecf82` adds one executable Boolean gate
  over the full singleton family/constructor hierarchy and couples its success
  to the exact ordinary producer equation in
  `ProducedGenerationShapeCandidate`. The gate checks emitted-spine
  preservation, full raw telescope lengths, and constructor-list cardinality;
  the `IndexedVec` regressions reject both missing and extra raw constructors.
  Exact dependent analysis and WF of the analyzer-owned view declaration
  derive checked WF and every source-indexed family/constructor shape record.
  AliasFormer, AnnotatedPi, and `IndexedVec` now supply neither checked WF nor
  per-position generation-shape structures. Bare producer success remains
  operational provenance only and is not promoted to Theory meaning or
  stored-spine authority. Exact guards pin the pure executable roots to
  `propext`/`Classical.choice`/`Quot.sound`; semantic package roots inherit only
  the existing checked-semantic closure. The exact 20-sorry audit, focused
  direct compiles, 124-job Theory/Verify build, 157-job default Lake build,
  124-job Nix proof check, default Nix build, all six current-host flake checks,
  all-system no-build evaluation, formatter, whitespace, and Theory
  import-boundary checks pass. The tracked ledger child is
  `c4fd62b23a89500154b113d849d183afbf84907f`; neither master nor any
  digama/upstream ref moved.
- [x] Update the sorry-frontier comments to describe the current Stage-3
  generalized one-family proof.
- [x] Create the root-level, non-ignored divergence ledger and record the
  current development delta from upstream `0c38ab8`; the tracked ledger is now
  refreshed against source parent `bbb45e0e` for this checkpoint.
- [x] Run ix Pin A against a green certificate-bearing `jcb/induct` checkpoint,
  build the complete `IxTcVerify` target, and reconcile its audits. The local ix
  `jcb/ix-formalization2` snapshot
  `1f73f5c016907eadb8ed0dc86ac65b07eb24a145` pins Lean4Lean
  `5e5bb767b3491d21a71908d4c58bcbaa007283bb`; the exact local sorry frontier and
  completed/statement root audits pass, and the former `VInductDecl.WF`,
  `VEnv.addInduct`, and `VEnv.addInduct_WF` direct `sorryAx` origins are gone.
  The full `InductiveOracle` handoff remains L4L-11, after the
  L4L-08A–L4L-09C breadth and L4L-10A/L4L-10B pattern package.

## 6. Track I — kernel-complete inductives

The present generalized one-family generator is a valuable vertical slice,
not the final data model. The shared checked analysis and semantic layer now
exist:
`VInductDecl.Checked` exposes normalized type/index telescopes, result sort,
recursive-argument descriptions, elimination mode, names, constructors,
motives, minors, recursor, and generated rules. `checked?`, `stage3`,
`addInduct`, the preservation proof, fixtures, and Verify alignment all consume
that result, while `Checked.WF env` gives the normalized data its
environment-relative meaning. Extend these contracts monotonically as I2-I4
add cases; do not reintroduce parallel Boolean analyses or downstream de
Bruijn reconstruction. The alias audit adds a second invariant: raw kernel
metadata and normalized analysis syntax are distinct objects.
`NormalizedChecked` is now the one-family data boundary joining those objects
and, through `Checked.identityGeneration`, the public identity artifact input.
It is not passed directly to the general transaction: a
`GenerationCertificate` erases the normalized/checker provenance to the exact
`GenerationChecked` value plus its semantic WF proof, and
`addInductCertified` consumes that Theory-only boundary. Preserve raw constant
payloads and generated binder syntax while using the semantically justified
view for WHNF-sensitive classification. Do not silently overwrite one with the
other or let each consumer choose its own normalization.

### I1 — finish direct indexed families (completed by L4L-00)

- [x] Complete S0 for one type with parameters, indices, direct recursive fields,
  never-zero or syntactically subsingleton elimination, and generated Eq/HEq
  recursors.
- [x] Add `addInduct_le`, generated-constant lookup lemmas, generated-rule
  membership lemmas, name-freshness consequences, and failure/atomicity lemmas.
  Ix's oracle needs these consequences directly; it should not unfold a large
  `foldlM` proof. These are exposed through `VEnv.AddInductSuccess` and
  convenience theorems, with a dedicated axiom-closure guard.
- [x] Add `IndexedVec` as a nontrivial indexed fixture whose recursive
  occurrence changes indices; compare its recursor and both iota rules exactly
  with the kernel.

### I2 — complete one-family kernel behavior (L4L-01A–L4L-07)

**Status: the direct-indexed and bounded recursive-Pi slices are green through
checked analysis, generalized artifacts, preservation, the public transaction,
and actual-metadata E1 replay. The normalization/defeq representation decision
is made; the paired raw/view checked-block data boundary, structural
projections, identity compatibility, and first semantic block fixtures are
green. The raw-syntax-preserving mixed artifact implementation matches the
identity and two alias kernels and is proved well formed through the complete
ordered rule fold. All live `Checked` artifact accessors are now canonical
identity specializations of that mixed implementation, with exact generic and
Nat/Eq/`IndexedVec`/`Acc` compatibility checks. The normalized Theory
transaction core, trace consequences, atomicity, and preservation theorem are
now green, as are the public semantic delegation and direct alias
transactions, normalized Verify trace, six actual-metadata replays, and first
checked full-check/WHNF-to-Theory producer. Both fixed alias cases now have
complete checked `GenerationChecked.WF` roots and checked end-to-end
`AddInductTrace`/`TrEnv'` replays. The complete `AnnotatedPi` candidate adds a
nested recursive-Pi annotation normalization/generation/replay path, including
the generated recursor and iota rule. A dependent Verify package and
proof-erased Theory certificate now provide public non-identity transaction
wiring for both AliasFormer and AnnotatedPi. `IndexedVec` now extends exact
outer execution to a parameter, an index, and two ordered constructors, and
the identity-replay bridge needed for its semantic spine is live. Published
checkpoint `cf3d5a47` completes its producer-selected semantic package,
certified Theory transaction, and checked E1 replay. One-family parity is not
complete because
generic arbitrary-constructor construction remains, alongside full positivity, small
elimination, K behavior, and the full differential matrix.**
The following order mirrors `Inductive/Add.lean` and keeps each widening
executable and proved:

- [x] Introduce dependent `VInductDecl.Checked`/`checked?` and make descriptor
  existence the public acceptance result. Route recursor/rule generation,
  `VEnv.addInduct`, `addInduct_success`, `addInduct_WF`, Theory fixtures, and
  Verify's `AddInductTrace` through the same checked value.
- [x] Record normalized parameters, indices, result level, elimination mode,
  generated names, constructor fields, and recursive positions/index spines.
  `RecArg.binders` is now populated for recursive Pi fields; retain
  `targetType` so I3 mutual recursion does not force a second consumer-facing
  redesign.
- [x] Check closed family/constructor metadata and internal generated-name
  uniqueness computationally. Export proof-level closure/`Nodup` consequences,
  add positive Nat/Eq/`IndexedVec` descriptor fixtures, and add duplicate-name
  and loose-variable rejection fixtures. Keep environment-relative freshness
  in the `addConst` transaction. Type-, constructor-, and recursor-collision
  regressions now exercise stable rejection theorems rather than depending on
  the internal fold order.
- [x] Finish the environment-independent, VExpr-normal-form portion of
  `checkInductiveTypes`: declaration/type/constructor universe counts,
  parameter count, raw parameter/index telescopes, sort result and result-level
  well-formedness, range validity of every universe annotation, prohibition of
  family self-reference in parameter/index domains, constructor parameter
  spine, and direct result family/head/arity. Export the combined facts through
  `Checked.analysis_accepted` and `Checked.direct_anatomy`; cover every branch
  with the malformed-result/universe/telescope fixture matrix.
- [x] Add `Checked.WF env` for the environment-relative `OnTel`, constructor
  field, universe-bound, and result-spine obligations. Prove both migration
  directions and `decl.WF env ↔ ∃ checked, decl.checked? = some checked ∧
  checked.WF env`; make `addInduct_WF` consume this certificate. Guard all
  three compatibility roots at exactly `propext` and `Quot.sound`.
- [x] Implement the one-family raw-VExpr counterparts of `isValidIndApp?` and
  `isRecArg` beneath Pi telescopes. `recTarget?` requires family-free domains,
  accepts only a terminal application of the current family to the declaration
  parameters and family-free indices, and populates the complete binder
  telescope. Computed `Acc` facts pin its field index, two binders, target type,
  and terminal index spine. Exact kernel-differential fixtures cover a family
  in a recursive-Pi domain, a changed fixed parameter at the recursive target,
  and a family occurrence inside the recursive target's index; each also
  reduces through public `checked?`/`addInduct` rejection. This is
  raw-normal-form parity only; the later normalization task still owns
  WHNF/defeq parity.
- [x] Define the generalized artifacts as a reviewable migration step:
  `minorIH`/`minorTypeRec`, `recTypeRec`/`recConstRec`, `ruleBinders`,
  `ruleCall`/`ruleIH`, and `ruleRec`/`rulesRec`. Exact fixtures prove by
  reduction that the generalized constant and rule are `Acc.rec` and its
  functional iota RHS (modulo the kernel universe permutation).
- [x] Finish generalized preservation. The proof now covers semantic
  `RecArg.WF`, universe transport, binder/index typing, generalized minor and
  recursor well-formedness, rule-binder/rule-type typing, recursive-field
  application, normalization of lifted `minorIH` entries to `ruleIH`,
  list-level application of every functional recursive call,
  `minorAppRec_hasType`, `recRuleAppRec_hasType`, `ruleRec_WF`, and the
  generalized rule fold. Exact guards keep all six exported recursive-Pi roots
  at the standard Theory axiom baseline.
- [x] Collapse the migration to one public path. Make
  `Checked.minorTypes`/`recursor`/`generatedRules`, `VEnv.addInduct`,
  `AddInductSuccess`, and `addInduct_WF` consume the generalized artifacts.
  The direct definitions remain only as specialization/reference code and are
  not semantically live through a public accessor. Completion is gated by
  exact public `accDecl.checked?`, `addInduct`, generated lookup/rule
  membership, `Ordered`, and failure-atomicity fixtures.
- [x] Replay `Acc` through E1 using Lean's actual `inductInfo`, `ctorInfo`, and
  `recInfo`; compare recursive-argument metadata, recursor universe order, and
  the lambda-wrapped rule RHS. The replay proves exact transaction equality,
  lookup uniqueness, final WF/alignment, and definitional equality between the
  actual kernel `RecursorRule.rhs` and `ruleRec`. Generic `TrEnv'.of_value`
  supplies preservation of older values for this transaction class; the
  seed-before-Nat fixture exercises the same persistent-map path concretely
  without duplicating it for every family.
- [x] Resolve the normalization representation decision empirically. Actual
  Lean metadata is not already in analyzer normal form: `AliasFormer` retains
  a reducible alias where the checker sees a result sort, and `AliasRec.mk`
  retains a reducible application where positivity sees a recursive target.
  Keep the raw declaration as the stored/source object and introduce a named
  `Normalization source` carrying a shape-compatible analysis view.
  `normalizationShape` already fixes all identities, arities, ordering, and
  counts, and `Normalization.checked?` keeps analysis computational and
  environment-independent.
- [x] Give the first one-family normalization witnesses semantic meaning.
  `Normalization.WF env` compares the raw/view family types in the input
  environment and compares constructor types pairwise after insertion of the
  raw family constant. The family-result and recursive-field alias fixtures
  construct those defeq derivations explicitly; both exact axiom guards are
  `[propext, Quot.sound]`. This proves the boundary is compatible with Theory,
  but not yet that every checker-produced normalization can be reconstructed
  or that generated artifacts preserve the kernel's raw syntax.
- [x] Introduce one paired, data-bearing checked block.
  `NormalizedChecked source` contains the normalization, the raw singleton
  `sourceType` and source equation, `norm.view.Checked`, and its exact computed
  analyzer equation. `Normalization.check?` constructs it without repeating
  analysis; `normalizedChecked?` checks an explicit pair; `identityChecked?`
  is the compatibility path. `Normalization.shape`,
  `NormalizedChecked.source_anatomy`, `uvars_eq`, and `nparams_eq` expose
  source/view arities and ordered family/constructor header agreement.
  Identity Nat and both alias fixtures compute, and the alias blocks have
  complete `NormalizedChecked.WF` certificates. Generic structural roots and
  concrete semantic roots have exact axiom guards. At that checkpoint this
  completed only the additive data boundary; the now-completed artifact
  refactor below added constructor-by-constructor pairing of raw field
  telescopes with normalized recursive-target/binder/index facts.
  Whole-expression defeq plus matching names is not, by itself, enough to
  recover raw binder positions.
- [x] Refactor artifact generation around that paired block before changing
  acceptance. Family and constructor constants must be inserted with the raw
  metadata payloads; recursor/minor/rule generation must retain the
  kernel-observable raw binder syntax while consulting the view for result
  sorts, recursive classification, target indices, and elimination facts.
  **Complete:** `GenerationChecked` supplies the executable layout gate,
  ordered `NormalizedCtor` pairs, raw/view coverage lemmas, and the sole live
  mixed motive/minor/recursor/rule implementation. Identity generation
  specializes by reduction to the current Nat/Eq/`IndexedVec`/`Acc` artifacts.
  The family-result and recursive-field alias recursors and iota rules match the
  actual kernel by `rfl`; `AliasRec` additionally proves that the emitted minor
  telescope retains the raw `RecAlias AliasRec` field while recursion comes
  from the view. Do not generate everything from the rewritten view: the alias
  audit shows that would erase syntax retained by kernel metadata and recursor
  types.

  The completed artifact-preservation sequence is:

  - [x] Establish the structural contract. `VEnv.TelDefEq` tracks pointwise
    equality in raw predecessor contexts; `GenerationChecked.WF` separates
    pre-family family evidence from post-family stored-constructor and
    emitted-artifact evidence; generic guarded lemmas prove the raw family and
    constructors well formed without the unfinished
    `IsDefEqU.forallE_inv_stratified`.
  - [x] Prove the mixed motive and all mixed minors well formed.
    `GenerationEnv.motive_isType`, exact raw constructor-application transport,
    recursive-argument/IH transport, `minor_isType`, and `minorTypes_onTel`
    cover the full constructor list. `minorTypes_length` and positional
    `minorTypesAux_getElem?` prevent silent list misalignment.
  - [x] Factor `familyApp_transport`, covering the common operation of
    inserting motive/minor binders below the indices and then weakening by a
    top stack. The targeted
    `Lean4Lean.Theory.Typing.InductiveLemmas` build is green.
  - [x] Prove `GenerationEnv.recType_isType` telescope-by-telescope in the
    order parameters, motive, minors, lifted indices, major premise, and final
    motive application; `GenerationEnv.recursor_wf` closes the mixed recursor
    constant.
  - [x] Prove every mixed rule well formed. `ruleBinders_onTel`,
    `ctorAppRule_hasType`, `ruleCall_hasType`, `minorApp_hasType`,
    `recRuleApp_hasType`, and `rule_WF` cover the raw telescope, constructor,
    recursive calls, RHS, and rule type; `generatedRules_WF` and
    `generatedRulesFold_ordered` close the ordered list without a separate
    direct-recursion branch.
  - [x] Add exact axiom guards for the stabilized mixed component roots,
    recursor, rule, and block-level fold as specified in §2.3. The motive and
    family transport use `[propext, Quot.sound]`; the minor, recursor, rule,
    and fold roots use the permitted
    `[propext, Classical.choice, Quot.sound]` ceiling.
  - [x] Make the legacy `Checked` artifact accessors identity-normalization
    compatibility specializations of the mixed implementation, prove exact
    Nat/Eq/`IndexedVec`/`Acc` public equalities, and confirm both alias
    differentials. `Checked.analyzer_eq` gives the unique retained result,
    `identityBlock`/`identityGeneration` construct the canonical bridge, and
    generic `*_eq_legacy` theorems pin all four artifact forms. The old
    `*Rec` functions remain only as compatibility/specification targets until
    the transaction contract is migrated; no live public accessor generates
    through them.
- [x] Replace the raw-only transaction with one normalized transaction and an
  identity-normalization compatibility wrapper. Route `stage3` (or its
  successor public predicate), `VEnv.addInduct`, `AddInductSuccess`,
  atomicity/freshness/lookups, `addInduct_WF`, and generated-rule membership
  through the paired checked block. The preservation theorem must consume
  `Normalization.WF`, the checked view's semantic certificate, and the raw
  declaration WF facts at their correct pre-/post-family environments. At a
  checkpoint there must be one semantically live artifact path, not unrelated
  raw and normalized transactions.

  Implement this in the following order:

  - [x] Add a single computational core,
    `VEnv.addInductGeneration (gen : GenerationChecked source)`, which inserts
    `gen.block.sourceType`, folds its raw constructor list (proved equal to
    `gen.block.ctorPairs.map (·.raw)` by `rawCtors_eq`), inserts
    `gen.recursor`, and folds `gen.generatedRules`. It does not inspect the
    view again and accepts no semantic proof as an oracle.
  - [x] Give that core a dependent success certificate retaining the exact
    `gen`, intermediate environments, raw family/constructor lookups, recursor
    lookup, every generated-rule membership fact, monotonicity, freshness, and
    atomic failure behavior. State the primary lookup/rule fields using mixed
    artifacts; derive legacy `recConstRec`/`rulesRec` consequences only in the
    identity wrapper. `AddInductGenerationTrace` is data-bearing, while
    `addInductGeneration_trace` returns `Nonempty` so proof consumers do not
    acquire choice solely to unpack transaction bookkeeping.
  - [x] Prove normalized preservation in transaction order. Use
    `GenerationChecked.WF.rawFamily_isType` for the first insertion, its
    staged `rawCtor_isType` facts for the constructor fold, promote the
    certificate with `GenerationChecked.WF.toGenerationEnv`, then apply
    `GenerationEnv.recursor_wf`, `generatedRules_WF`, and
    `generatedRulesFold_ordered`. Do not reconstruct a `Stage3Env` or rerun
    legacy recursive analysis. `addInductGeneration_WF` now follows exactly
    this chain.
  - [x] Redefine the current `VEnv.addInduct env source` as: obtain the exact
    `Checked` result once, form `checked.identityGeneration`, and call the
    normalized core. `addInduct_eq_addInductGeneration` pins that computation.
  - [x] Add the semantic identity bridge
    `env.Ordered → Checked.WF env → checked.identityGeneration.WF env`, then make
    `AddInductSuccess`, its atomicity/freshness/lookups/rule-membership
    consequences, and `addInduct_WF` delegate to the normalized trace and
    preservation theorem. Delete the now-redundant legacy `Stage3Env`
    transaction proof only after those public statements and exact closures
    remain unchanged. `DirectFamilyEnv` captures precisely the state after the
    family insertion and before any constructor lookup exists; the bridge uses
    it to validate direct/functional recursive fields and exact raw constructor
    results without reconstructing `Stage3Env`.
  - [x] Add direct Theory transactions for `AliasFormer` and `AliasRec` using
    their explicit `GenerationChecked.WF` witnesses. Check raw family and
    constructor payload preservation, exact kernel recursor/rules, complete
    lookup membership, monotonicity, and final `Ordered`; the raw
    `checked? = none` facts must remain true to demonstrate that normalization,
    rather than analyzer weakening, enables them. Both final environments now
    have trace, freshness, raw lookup, kernel recursor/iota, monotonicity, and
    ordering fixtures.
  - [x] Complete the exact guard set. Core trace/atomicity/lookups,
    normalized preservation, and identity-wrapper computation are already
    guarded at the exact closures recorded in §2.3; add guards for the
    identity semantic bridge, delegated public roots, and both alias
    transaction roots. The identity bridge and ordered alias endpoints use
    exactly `[propext, Classical.choice, Quot.sound]`; alias trace/lookups and
    rule membership use exactly `[propext, Quot.sound]`.
- [ ] **L4L-01A–L4L-01E (01A–01B complete; 01U active before 01C):** complete generic Verify-side production of
  normalized transactions in five separately green checkpoints. The
  trace/consumer migration and six actual-metadata replays are complete. The
  generic checker-to-Theory `WhnfRun`, `CheckTypeRun`, `DefEqEvidence`, and
  `NormalizationRun` APIs are complete, as are both fixed alias normalization
  instantiations and both complete checked `GenerationChecked.WF` roots.
  AnnotatedPi additionally builds the complete nested candidate, checked
  generation certificate, and transaction from exact checker traces. These
  checked roots no longer bootstrap from older hand-built generation-WF
  proofs. Semantic-input plumbing and family-validator/environment staging are
  complete in L4L-01A/L4L-01B. L4L-01U first reconciles the live upstream and
  Lean v4.31 without adding a semantic deliverable. Constructor trace
  retention, constructor-validator soundness, and final package closure remain
  the separate L4L-01C through L4L-01E checkpoints. Bare
  `buildNormalizationCandidate` success is insufficient at every stage. The
  whole-candidate non-defeq rejection is a required regression; an arbitrary
  user-supplied view or assumed normalization oracle is forbidden.

  The Verify migration order is:

  - [x] Replace the trace's free `decl.Checked` field with the exact
    `GenerationChecked decl` artifact and `GenerationChecked.WF` certificate
    used by Theory; retain raw `ConstantInfo` payloads in every
    `AddInductConstant`.
  - [x] Add the first checked normalization-certificate producer.
    `TypeChecker.WhnfRun` records the exact `Inner.whnf'` run, checker context,
    state-WF proof, and input/output translations; its refinement theorem
    yields typed Theory defeq. `DefEqEvidence` composes `refl`, `whnf`, `app`,
    `beta`, `trans`, and `forallE`, while
    `VInductDecl.NormalizationRun.wf` stages family and constructor evidence in
    the correct environments. `AliasFormer` uses a real family-head WHNF run;
    `AliasRec` uses a real `RecAlias.{1}` run plus application, beta,
    transitivity, and forall congruence. Exact operational and semantic axiom
    guards pin both paths.
  - [x] Add the first full-check typing producer and close the fixed-alias
    dependent certificates. `TypeChecker.CheckTypeRun` records exact
    `Inner.inferType _ false` runs and exposes named `HasType`/`IsType`
    consequences. `AliasFormer` checks the real `TypeFamilyAlias` constant,
    then checks the actual constructor type in the exact post-family
    environment; the latter returns the retained alias and is combined with
    verified WHNF. `AliasRec` checks the actual raw `RecAlias AliasRec` field
    in the exact post-family environment, then uses that checked typing premise
    in the compositional WHNF/application/beta equality for its constructor.
    All three operational traces record their inferred/cache result and have
    exact axiom guards.
    Both aliases now assemble checked
    block-WF and complete `GenerationChecked.WF` roots without using their
    older fixture generation-WF proofs. Generic `TelDefEqEvidence`,
    `NormalizedCtorRun`, and `GenerationRun` package the pointwise binder,
    declared/emitted constructor, and exact post-family evidence, so the fixed
    cases exercise the same assembler intended for arbitrary metadata. Exact
    guards show that these complete certificates add no dependency beyond the
    checked semantic endpoint.
  - [x] Feed both fixed-alias checked generation certificates through complete
    data-bearing `AddInductTrace` values and `TrEnv'`. The checked traces reuse
    the already audited metadata-translation witnesses, preserve the same
    final environments, and derive final WF/alignment. Exact guards show that
    this end-to-end wiring adds no dependency beyond the checked semantic set.
  - [x] Complete candidate-list traversal and semantic certification of the
    retained indexed runs at Lean's transparency and fuel boundary. Exact
    whole-call package production is tracked separately below.

    - [x] Add the generic executable traversal.
      `AddInductive.normalizeCandidateExpr` calls the ordinary checker `whnf`
      at every node, traverses exposed Pi domains and instantiated bodies
      under the kernel's structurally certified annotation-consumed local
      declarations, retains the raw binder syntax plus an exact equality run,
      and consumes the configured inductive fuel. Source-indexed candidate
      family and constructor lists preserve metadata headers and positions by
      construction.
      `buildNormalizationCandidate` first repeats
      `checkInductiveTypes`, computes family views in the input environment,
      inserts all raw families, repeats `checkConstructors`, and computes
      constructor views in that exact post-family environment. Its dependent
      `NormalizationCandidate source` result prevents accidental reuse for a
      different source but is not itself semantic authority.
    - [x] Retain and operationally certify generic positional run data.
      `CandidateExpr` records the full
      `AddInductive.Context`, raw input, WHNF result, and recursive Pi
      domain/body split at every node. Source-indexed dependent lists retain
      exact family and constructor positions; views are reconstructed from
      those traces while all names and non-expression headers come from the
      indexed source. Every trace node carries
      `CandidateWhnfStep.Valid`, the exact ordinary-checker run equality
      obtained by dependent matching on the computation; `step_valid`
      exposes it without an oracle or native evaluation.
    - [x] Bridge retained steps to the existing semantic certificate boundary.
      `CandidateWhnfStep.innerRun` constructively recovers the final checker
      state erased by `TypeChecker.M.run`, while
      `TypeChecker.WhnfRun.ofCandidateStep` combines that run with a matching
      verified context and caller-supplied strict translations. The
      AliasFormer family `WhnfRun` now comes from its produced candidate step
      through this adapter rather than a parallel hand-filled `run_eq`.
    - [x] Retain full checks at both declaration stages and every trace node.
      Family traces run before raw family insertion; constructor traces run in
      the exact post-family environment. Every recursive Pi domain and
      instantiated body is checked in its recorded raw local context before
      WHNF/traversal. `CandidateCheckTypeStep.innerRun` and
      `CheckTypeRun.ofCandidateStep` mirror the WHNF adapters, while
      `checkStep_valid` exposes every run. AliasFormer's family and actual
      constructor `CheckTypeRun` values now use these candidate steps,
      including the retained alias result after insertion.
    - [x] Pin one exact operational leaf. The actual retained
      `AliasFormer` family alias reduces through
      `buildCandidateExpr` to a terminal trace containing the exact context,
      source, and expected sort using the same verified checker WHNF run;
      erasing that trace gives the expected `normalizeCandidateExpr` result.
      Exact axiom guards record the inherited operational closure. This is
      intentionally a leaf test rather than a second, fixture-specific
      implementation of whole-expression WHNF.
    - [x] Define and verify the recursive semantic interpretation boundary.
      `CandidateExprTrace` is recursively context- and source-indexed at Pi
      domains and exact instantiated bodies. Its body index is the literal
      `Context.pushLocalDecl` update with the producer's next fresh identifier
      and structurally certified consumed domain, eliminating the previous
      independently supplied child context. `CandidateNodeRun.ofCandidate`
      pairs the two retained
      executions in one verified context, while
      `CandidateNodeRun.exists_ofCandidate` extracts both output translations
      from the verifier refinements rather than requiring them from the
      caller. `CandidateExprRun` folds terminal nodes and Pi domain/body
      children into `DefEqEvidence`, retaining raw Pi syntax while checking
      the body under the kernel's consumed binder context. Its Pi case
      accepts arbitrary checker-inferred types and transports them to the
      structural domain/body/result sorts using unique typing, so a relevant
      Pi-producing alias need not be reported syntactically as a sort.
      `source_tr` retains the strict raw translation, while `view_tr` abstracts
      the exact retained free variable, transports the body across the
      raw/normalized domain context, and translates the reconstructed
      candidate view. All construction, interpretation, and translation roots
      have exact guards. AliasFormer's actual candidate trace supplies its live
      `NormalizationRun` and `GenerationRun` family evidence through this path.
    - [x] Construct matching verified contexts and translations automatically
      for every retained position in a candidate trace.
      `CandidateContextRun.root` aligns the exact executable root with a
      verified `VEnvs`; `.pushLocalDecl` builds the corresponding
      `VContext`/`MLCtx`, proves binder freshness and checker-name reservation,
      and restarts the empty checker state soundly. The trace now retains the
      exact freshness equation. `candidateCheckTypeStep_exists_translation`
      recovers strict source/inferred translations and typing from the root
      full check, and `CandidateExprRun.exists_ofCandidateFVars` invokes the
      node interpreter recursively, deriving child translations and raw
      domain/body typing from Pi decomposition. AliasFormer exercises the
      automatic root path without a fixture-supplied Theory expression. Exact
      guards cover every new state/context/recursive root.
    - [x] Remove the explicit `CandidateRawBinderDomains` restriction and
      certify annotation consumption. `CandidateTypeAnnotationTrace` mirrors
      the four top-level peeling cases structurally, and
      `buildCandidateTypeAnnotations` checks its result against Lean's actual
      `consumeTypeAnnotations` implementation. Because that implementation is
      an opaque partial definition, the retained `CandidateTypeAnnotations`
      stores only the consumed expression and structural trace; the agreement
      branch is executable producer validation, not a semantic proof field.
      Every Pi retains an exact
      successful `isDefEq domain consumed` execution before extending the
      body context. `IsDefEqRun.ofCandidateStep` and `.isDefEqU` refine that
      execution; strict translation of the consumed argument is extracted
      from the raw application trace, so a redundant second full check is not
      required. `CandidateExprRun.forallE` now transports domain typing, body
      translation/equality, evidence, and the reconstructed view across the
      raw, consumed, and normalized contexts. Positive executable fixtures
      cover `outParam`, `semiOutParam`, `optParam`, and `autoParam`; a negative
      fixture pins both the checker's `.ok false` result and the producer's
      dedicated rejection. Exact axiom guards cover every new producer and
      verifier root.
    - [x] Convert the candidate list to the one-family Theory
      `Normalization`, run its dependent checked analysis, and assemble
      `NormalizationRun` from retained family and constructor runs.
      `CandidateExprRootRun` ties named Theory endpoints to exact candidate
      syntax; `CandidateConstructorListRun` folds exact positional evidence;
      and `NormalizationCandidateRun` statically accepts only a singleton
      source family and singleton raw declaration. AliasFormer's actual family
      and post-family constructor candidate traces now drive its live
      normalization certificate. A truncated view fails the computational
      shape gate before transaction construction. Exact guards cover singleton
      elimination, root evidence, list shape/evidence, normalization assembly,
      the migrated fixture, and the negative.
    - [x] Extract raw/view binder telescopes and terminal results from the
      retained recursive runs, align them with the successful dependent
      analysis, and assemble generic `GenerationChecked.WF`.
      `CandidateExprTrace.storedSpine` prevents WHNF from inventing or deleting
      emitted raw binders while allowing binder-domain and terminal-result
      normalization. `CandidateExprRun.spineEvidence` returns exact
      `TelResultDefEqEvidence` with a proved raw-spine length.
      `CandidateFamilyGenerationRun` and `CandidateNormalizedCtorRun` align
      that evidence with the dependent checked view;
      `TelResultDefEqEvidence.replacePrefix` proves the declared/emitted
      constructor bridge through exact contexts; and the dependent
      `CandidateNormalizedCtorListRun` cannot truncate, reorder, or reuse a
      constructor certificate. `GenerationCandidateRun.wf` produces the
      existing Theory `GenerationChecked.WF`. Every extraction and assembly
      boundary has an exact axiom guard and introduces no new axiom.
    - [x] Route one non-identity candidate-derived generation certificate
      through an existing complete checked consumer. AliasFormer's exact
      pre-family and post-family candidate spines now build
      `aliasFormerGenerationCandidateRun`; its former hand-filled
      `GenerationRun` delegates to that generic value, so the checked
      `AddInductTrace`, final environment, `TrEnv'`, WF, and alignment roots all
      exercise the candidate assembler.
    - [x] Add a complete positive candidate-list fixture with an annotation
      inside an actual recursive Pi constructor type. `AnnotatedPi.mk` retains
      `outParam Prop` in the raw recursive-function domain while the candidate
      view consumes it to `Prop`. Its exact full-check, WHNF, and complete
      lazy-delta `isDefEq` traces recursively construct the raw and consumed
      contexts, pass `storedSpine`, extract the nonempty nested telescope and
      terminal result, assemble `GenerationCandidateRun.wf`, and replay the
      final environment, recursor, and iota rule through checked
      `AddInductTrace`/`TrEnv'`. Exact guards cover normalization, generation,
      checked generation, transaction replay, and the small Theory iota root.
    - [x] Add the corresponding whole-candidate rejection for non-defeq
      annotation domains. The fixture keeps the real AnnotatedPi family and
      constructor metadata and gives `outParam` its correct polymorphic type as
      an opaque constant. Family/constructor staging therefore reaches the
      recursive candidate, but the ordinary checker cannot prove
      `outParam Prop` definitionally equal to the syntactically consumed
      `Prop`; `buildNormalizationCandidate` returns the dedicated binder-domain
      error before any semantic package or transaction exists. Keep this with
      the four leaf annotation positives, exact non-defeq leaf rejection,
      truncated-view rejection, and positive AnnotatedPi transaction so the
      failing phase remains unambiguous.
  - [x] Add the generic proof-carrying consumer boundary and route two
    non-identity packages through it. Theory's `GenerationCertificate` owns an
    exact generation and `GenerationChecked.WF`; `VEnv.addInductCertified`
    erases the proof and computes through `addInductGeneration`, with exact
    trace, atomicity, and WF theorems. Verify's
    `GenerationCandidatePackage` retains the exact kernel source, candidate,
    normalization, generation, and semantic run; `.certificate` is the
    ix-facing erasure, and `.addInductTrace` prevents metadata replay from
    receiving an unrelated generation/WF pair. AliasFormer and AnnotatedPi
    both exercise the package, public certified transaction, and checked
    replay. Keep `VEnv.addInduct` as the identity compatibility wrapper until
    kernel parity and downstream migration are green.
  - [x] Instantiate the exact whole-call producer boundary on real positive
    metadata. AliasFormer and AnnotatedPi prove
    `buildNormalizationCandidate ... = .ok package.candidate` through the
    exact family-declaration and constructor-check contexts, constructs
    `ProducedGenerationCandidatePackage`, and routes both its public certified
    transaction and checked metadata replay through that produced value. The
    proof retains exact source-indexed candidate equality, not candidate
    erasure equality or a hand-selected view, and exact guards expose every
    inherited cache/platform dependency.
  - [ ] **L4L-01A–L4L-01E (01A–01B complete; 01U active before 01C):** generalize exact produced-package construction to
    arbitrary strengthened singleton metadata runs. The executable seam now
    covers `IndexedVec`'s family telescope, parameter, index, and ordered
    two-constructor list; generic identity replay and the concrete
    identity-spine witnesses feed a complete dependent semantic package and E1
    replay. Automatic semantic hierarchy assembly is complete once exact
    verified per-position inputs are supplied. L4L-01A consolidates that
    repeated input assembly over two explicitly verified stages. L4L-01B
    derives the post-family stage from the family validator. L4L-01U reconciles
    current upstream before L4L-01C and L4L-01D retain and interpret
    constructor validation. L4L-01E alone applies the already generic
    generation alignment and deletes the temporary fixture view-WF proofs.
    Bare outer-producer success remains insufficient.

    - [x] Abstract exact executable family-type, constructor, and complete
      family-list assembly into arbitrary-length dependent `Produced`
      witnesses. Route AliasFormer, AnnotatedPi, and the two-constructor
      `IndexedVec` regression through their generic `.normalize` theorems, with
      exact standard-baseline axiom guards.
    - [x] Add the generic outer singleton constructor
      `GenerationCandidateRun.producedPackage`. It requires an exact successful
      `buildNormalizationCandidate` equation indexed by the same kernel source
      and dependent candidate as the semantic run, so it cannot attach
      executable provenance to another view or reordered list. Route
      AliasFormer, AnnotatedPi, and `IndexedVec` through it and guard its exact
      inherited `[propext, sorryAx, Classical.choice, Quot.sound]` closure.
    - [x] Introduce generic retained semantic ownership.
      `CandidateExprSemanticRootRun` owns the exact recursive run and its
      checker-selected view; `.root` and `.spine` feed normalization and
      generation from that same value. Source-indexed semantic constructor
      lists, families, and singleton normalization candidates preserve every
      position. AliasFormer, AnnotatedPi, and `IndexedVec` now use this hierarchy
      instead of parallel root/run/spine records.
    - [x] Combine the operational list witnesses with automatic construction
      of the retained semantic family/constructor hierarchy.
      `CandidateExprSemanticRootInput`, the dependent constructor and family
      inputs, and `NormalizationCandidateSemanticInput.exists_ofProduced`
      invoke the retained checker interpreter at every exact source position
      and return `Nonempty ProducedNormalizationCandidateSemanticRun`.
      `CandidateFamilySemanticGenerationRun`,
      `CandidateSemanticNormalizedCtorListRun`, and
      `GenerationCandidateSemanticRun` make those same roots and spines own the
      generation path. Exact generic and fixture axiom guards are live;
      `IndexedVec` proves exact constructor order and rejects a reordered view.
    - [x] Derive view telescopes and terminal typing instead of accepting them
      from fixture generation records. `Checked.type_eq` and
      `GenerationChecked.viewCtorType_eq` expose exact accepted family and
      constructor shape at the standard Theory axiom baseline.
      `GenerationCandidateRun.familyView_eq` fixes the singleton candidate view;
      family terminal sort typing follows from the checked result level; the
      raw family constant is typed once in the post-family environment; and
      `GenerationChecked.checkedResultTarget_hasType` plus exact telescope
      context transport derives every constructor target judgment.
      AliasFormer, AnnotatedPi, and `IndexedVec` now omit `viewTel` and
      `rightType`; the two circular `IndexedVec` right-typing helpers are gone.
      Exact guards cover all new Theory and Verify roots.
    - [x] Retain exact dependent analyzer provenance and derive its immediate
      semantic consequences. `GenerationCandidateRun` and
      `GenerationCandidateSemanticRun` store
      `normalization.generation? = some generation` instead of an unrelated
      normalization equality. Theory proves successful `check?` and
      `generation?` retain the analyzed normalization; Verify derives
      post-family environment WF from the verified pre-family context,
      raw/view equality, checked family typing, and exact insertion.
      AliasFormer, AnnotatedPi, and `IndexedVec` now provide neither
      `normalization_eq` nor `typeEnv_wf`, and exact axiom guards cover every
      new public root.
    - [x] Derive analyzer-owned component and dependent-list alignment from a
      minimal semantic generation shape. `GenerationCandidateSemanticShapeRun`
      retains checked WF, exact analysis, and only stored-spine/total-length
      shape data. Singleton indices recover the raw family and complete checked
      family view; analyzer maps recover every normalized constructor pair and
      exact source order; total length determines raw telescope/results; and
      exact checked shape determines view terminals. Its public `.run`
      reconstructs `GenerationCandidateSemanticRun`. AliasFormer, AnnotatedPi,
      and `IndexedVec` no longer select pairs or provide component equations.
    - [x] Consolidate checked-WF and per-position shape derivation behind one
      strengthened executable generation-readiness result.
      `normalizationCandidateGenerationShape` checks the complete singleton
      family and source-indexed constructor list, including stored emitted
      spines and total raw telescope lengths, and rejects list mismatch in both
      directions. `ProducedGenerationShapeCandidate` retains the exact ordinary
      producer equation without pretending that equation proves the stronger
      gate. `GenerationCandidateSemanticRun.ofGenerationShape` uses exact
      dependent analysis and WF of the analyzer-owned view declaration to
      derive checked WF and expand the successful Boolean into every dependent
      shape record. All three fixtures use this boundary and exact axiom guards
      show no trust-budget increase.
    - [x] **L4L-01A:** add one source-indexed staged-input owner over explicitly
      verified pre-family and post-family candidate contexts, strict family and
      constructor source translations, exact insertion alignment, and the
      existing dependent `Produced` traversals. Its only semantic output is
      `Nonempty ProducedNormalizationCandidateSemanticRun`. Migrate all three
      positives to this owner and delete their per-root
      `CandidateExprSemanticRootInput` and constructor-list input definitions.
      Because this output is intentionally `Nonempty`, the existing explicit
      downstream semantic-run/package witnesses and one fixture-level `viewWF`
      remain permitted and visibly temporary until L4L-01E; do not extract data
      with `Classical.choice`. Complete at source checkpoint `7c792209`: all
      three positives use the staged owner, exact constructor order is retained,
      the repeated old input definitions are absent, and focused/universal gates
      pass without changing the axiom frontier.
    - [x] **L4L-01B:** interpret the exact singleton family-validation run from
      one verified entry context. Derive the candidate view parameter/index
      telescope, terminal sort typing, raw-family constant WF through the
      candidate's semantic defeq, the exact raw-family insertion, and the
      verified post-family candidate stage. Remove the second independently
      verified stage and the three fixture-specific post-family `VEnvs.WF`
      reconstructions. Do not inspect or prove constructor validity here.
      Complete at source checkpoint `da45b536`: the exact singleton validator
      derives parameter/index views, terminal/raw-family WF, exact insertion,
      and the post-family candidate stage; none of the three positives retains
      an independent post-family `VEnvs`/context; constructors remain
      uninterpreted; family-phase negatives remain sharp; exact axiom guards
      and universal gates pass.
    - [x] **L4L-01U:** completed at source checkpoint
      `7f864b459e4a6062b468d6e5416688feac0f9f99`. It merges digama
      `upstream/master` through `ef849dfbd94a` into origin `jcb/induct`
      without rewriting the published checkpoints or moving either master.
      The source reconciles the overlapping
      inductive/checker/Verify/level and replay/CI/Experimental changes,
      upgrades Lean and lean4-nix to v4.31, retains the fork's Nix and ix-facing
      certificate surfaces, and removes upstream's four now-proved
      cached-`Expr` axioms plus the obsolete hand-declared `mkAppRangeAux`
      equation. The exact inventory is 29 custom axioms and 22 non-Experimental
      sorries. `NormLevel.isEquiv_wf` is assigned to L4L-02B and `addDecl.WF`
      to L4L-19B; neither enlarges a supported-root allowlist. Completion
      evidence includes the upstream tip as a source parent, passing
      L4L-01A/L4L-01B regressions and universal Lean/Nix gates, and publication
      of only origin `jcb/induct`. The isolated ix v4.31 probe
      is diagnostic evidence, not an ix pin: merged Lean4Lean replay and ix
      runtime modules pass, while ix-owned proof/API migration is deferred to
      the next pin. Keep this checkpoint integration-only; constructor traces
      belong to L4L-01C.
    - [ ] **L4L-01C (active):** retain the complete successful singleton constructor
      validator as dependent operational data: duplicate/closedness checks,
      closed root `checkType`, parameter equalities, field `ensureType` and
      universe comparisons, positivity/recursive-target traversals, and the
      final family application. Prove decomposition/recomposition with the
      actual `checkConstructors = .ok ()` execution. This milestone makes no
      Theory WF claim and must preserve failure-phase diagnostics.
    - [ ] **L4L-01D:** interpret the L4L-01C trace using the verified checker and
      the retained candidate normalization. Derive every accepted view field's
      `fieldsWF`, every constructor result `SpineWF`, and therefore WF of the
      exact analyzer-owned view declaration. This is soundness for the
      currently accepted normalization/validation subset, not the later
      acceptance-breadth work of L4L-03/L4L-05. Remove all three fixture
      `viewDecl_wf` proofs and guard the generic roots at their exact inherited
      axiom closures.
    - [ ] **L4L-01E:** combine the L4L-01A–L4L-01D owner, exact dependent
      analysis, and `ProducedGenerationShapeCandidate` into an exact
      `Nonempty ProducedGenerationCandidatePackage`. The theorem must retain
      the successful ordinary producer equation but may not infer the
      strengthened gate or Theory meaning from that equation. It must not
      accept a view or view-WF premise. Raw/view pairing, component equations,
      checked WF, per-position shape records, dependent-list alignment, view
      telescopes, terminal typing, normalization identity, and post-family WF
      remain derived. AliasFormer, AnnotatedPi, and `IndexedVec` use only this
      theorem; missing/extra/reordered/truncated/non-defeq negatives remain
      sharp. Mutual/nested generalization begins only after L4L-07.

    AliasFormer, AnnotatedPi, and `IndexedVec` remain the terminal-alias,
    nested annotated-Π, and parameter/index/multi-constructor regressions. Do
    not weaken the boundary to erasure equality or an assumed normalization
    theorem; the opaque-`outParam` whole-candidate rejection must stay green
    and fail before package construction.
  - [x] Make `AddInduct.to_addInduct`, `.le`, `Aligned.addInduct`,
    `TrEnv'.wf`, and `TrEnv'.aligned` consume the normalized Theory success
    certificate instead of converting back to legacy raw artifacts.
  - [x] Replay Nat, Eq, `IndexedVec`, `Acc`, `AliasFormer`, and `AliasRec`
    from actual metadata. For every case pin source/view data, recursor
    universes, raw binder syntax, all rule RHSs, final environment equality,
    lookup uniqueness, WF, and alignment.
  - [ ] **L4L-11:** export the ix-facing oracle ingredients only after the normalized
    trace has exact axiom guards and no `sorryAx` beyond the separately tracked
    projection relation. The API should expose generation/lookup/pattern facts,
    not a normalization oracle or kernel implementation object.
- [ ] **L4L-03:** match the remaining singleton environment-sensitive behavior of
  `checkInductiveTypes`/`checkConstructors`: `checkType` before declaration,
  fuel- and transparency-appropriate WHNF-driven Pi/result-sort peeling,
  WHNF-driven recursive-target traversal, and definitional rather than
  syntactic constructor-parameter agreement. Add a positive constructor
  parameter case whose domains differ syntactically but are definitionally
  equal, paired with a genuinely non-defeq negative and exact kernel outcome.
  Result-level equivalence across different family types belongs to I3, not
  this singleton milestone.
- [ ] **L4L-04:** complete the normalization differential matrix before calling this
  sub-slice done. Cover aliases at family results, parameter/index domains,
  ordinary fields, direct recursive targets, and recursive targets hidden
  behind a Pi-producing alias; include beta/let reduction where real metadata
  can retain it, irreducible/opaque or otherwise non-defeq counterexamples,
  and the checker fuel boundary. For each accepted case compare the raw
  constant payloads, normalized descriptor, recursive positions, recursor
  type, and every rule RHS with the kernel, then replay it through E1. Add
  generic axiom guards for the paired-block preservation and transaction roots,
  not only the two concrete fixture witnesses.
- [ ] **L4L-05:** complete positivity and constructor checks: nested negative occurrences,
  non-recursive fields mentioning the family, dependent fields, recursive
  functions, proof-valued fields, and constructor universe bounds. The last
  obligation is already represented semantically in `Checked.WF`; this task
  connects it to kernel acceptance and differential tests. Every rejection
  branch gets a fixture whose nearest kernel analogue is also rejected; the
  checker remains an underapproximation until agreement is demonstrated.
- [ ] **L4L-06A:** implement `isLargeEliminator`, `getElimLevel`, `getRecLevels`, and
  `getRecLevelParams` faithfully. Make `ElimMode.small` constructible and
  parameterize motive/recursor generation by it, so Or/And are accepted with
  Prop-only recursors while Eq-like and never-zero families retain legitimate
  large elimination.
- [ ] **L4L-06B:** add `isKTarget` data to the descriptor and reproduce the kernel's Eq-like
  K flag/behavior without using K as a shortcut for invalid large elimination.
  Verify the exact universe ordering rather than normalizing away meaningful
  permutations.
- [ ] **L4L-06C:** cover empty and singleton-constructor families and prove exact recursor
  binder ordering, minor ordering, field counts, recursive-argument metadata,
  rule counts, and iota RHSs. Refactor the preservation proof one generated
  component at a time; no new case may bypass `Checked` or add a proof-only
  premise that real kernel metadata does not supply.
- [ ] **L4L-07:** replay every newly accepted family through E1 immediately. Theory parity
  without actual `ConstantInfo` translation is insufficient for ix, because
  `InductiveOracle` needs both semantic generation and environment alignment.

The fixed positive matrix is Nat, Bool, List, Option, Prod, Unit, Empty, Or,
And, Eq, HEq, Fin, Vector, and Acc, plus the focused alias-normalization cases
listed above. For each, compare acceptance, raw stored type, type and
constructor names, parameter/index counts, field/recursive-argument metadata,
universe lists, elimination level, K flag where relevant, recursor type, rule
count, and every iota RHS with the real kernel. The paired negative matrix must
cover loose variables, duplicate/internal and pre-existing names, bad universe
levels, malformed result applications, parameter mismatch, non-defeq
normalization views, negative recursion, illegal recursive targets, and invalid
elimination. I2 exits only when both matrices, the E1 replay subset, exact axiom
guards, sorry audit, Theory/Verify build, and full flake gate are green.

The current negative matrix already covers the closure, generated-name,
universe-annotation, self-reference, raw result-shape, parameter-count,
universe-count, transaction-collision, recursive-Pi domain, changed-target
parameter, and recursive-index-family branches. I2's remaining negative work
is therefore concentrated on rejecting semantically invalid raw/view pairs,
nested positivity beyond this one-family recursive target, constructor field
universes at the acceptance boundary, and elimination/K behavior rather than
duplicating completed cases.

### I3 — mutual blocks (L4L-08A–L4L-08C)

- [ ] **L4L-08A — mutual checked representation.** Replace singleton
  destructuring in analysis with dependent lists over `decl.types`; represent
  shared parameters, per-family indices/results, ordered constructors, and
  cross-family recursive targets. Compute checked Tree/TreeList and one mutual
  indexed descriptor, but do not generate or insert constants yet.
- [ ] **L4L-08B — mutual validation and normalization.** Generalize the
  L4L-01C/L4L-01D validator traces and semantic interpretations to shared parameter
  agreement, equal result universes, all-family staging before constructor
  validation, cross-type recursive occurrences, and recursive Pi arguments.
  Produce the exact mutual semantic package and sharp mismatch/reordering
  negatives; no generator theorem is part of this checkpoint.
- [ ] **L4L-08C — mutual generation, preservation, and replay.** Generate one
  motive and recursor per family, flatten all constructor minors in kernel
  order, and route each recursive call to the correct motive/recursor. Add all
  type constants before constructors, all constructors before recursors, and
  all recursors before rules; prove `Ordered`, lookups, and preservation through
  the chain. Tree/TreeList and the mutual indexed fixture compare every
  `inductInfo`, `ctorInfo`, `recInfo`, and rule and replay through E1. No
  singleton destructuring remains on the public path.

### I4 — nested inductives (L4L-09A–L4L-09C)

- [ ] **L4L-09A — nested representation decision.** Audit how translated
  `inductInfo` represents flattened nested auxiliaries even though the producer
  receives `numNested` and `VInductDecl` does not. Commit a design note plus
  executable metadata probes. Choose an additive metadata/checked-block type or
  proved pre-flattening relation; change existing `VInductDecl` fields only if
  neither can express real output, with ix compatibility evidence first. This
  checkpoint changes no acceptance behavior.
- [ ] **L4L-09B — nested transformation and positivity.** Implement the chosen
  pre-flattening/auxiliary relation, the kernel nested transformation, and its
  positivity/validation obligations. Pin the transformed family and auxiliary
  descriptors for a rose tree through List and one nested indexed family,
  including rejection differentials, but do not yet claim generated recursors
  or E1 replay.
- [ ] **L4L-09C — nested generation and replay.** Generate every auxiliary
  declaration, recursor, and rule; prove preservation and insertion order; and
  round-trip both fixtures through real `Inductive.Add.run`, generic packaging,
  and E1. The exit compares all raw metadata and rule RHSs rather than a
  hand-authored declaration.

### I5 — generated-pattern package (L4L-10A/L4L-10B, ix-critical)

- [ ] **L4L-10A — generated iota pattern core.** Construct every generated iota
  LHS through `SimplePattern.iota` or prove exact equality to its `Pattern`.
  Prove match inversion, rule-index/constructor recovery, rule distinctness,
  pairwise non-intersection, and the `Params.pat_uniq`/
  `pat_app_l_uniq`/`pat_app_uniq` obligations for one certified block. Port the
  implementation-independent ix helpers `HeadConst`, `HeadConstN`,
  `of_varN_matches`, `RecursorIotaPattern`, and `matches_shape` into
  `Theory/Typing/Pattern.lean`.
- [ ] **L4L-10B — pattern soundness and environment assembler.** Prove
  `pat_wf`: successful match/check instantiates the LHS/RHS defeq registered by
  `addInduct`. Add a block-local assembler for an environment whose defeq set
  consists of generated inductive rules plus separately certified extension
  rules. Do not install a global `Params` instance for an open environment.

## 7. Track E — Verify environment alignment and ix's inductive oracle

### E1 — replace the empty `AddInduct` path (L4L-01A–L4L-01E/L4L-07/L4L-11)

- **Status: core normalized relation/proof path, actual-metadata Nat, Eq,
  index-changing `IndexedVec`, recursive-Pi `Acc`, `AliasFormer`, and
  `AliasRec` replays, plus the pre-existing-value regression, are complete.
  The first verified WHNF-to-normalization certificate producer is complete
  and instantiated on both aliases. Automatic candidate traversal, dependent
  semantic packaging, and the proof-carrying public non-identity transaction
  are complete for AliasFormer and AnnotatedPi; both additionally have exact
  whole-call produced packages in their real pre-/post-family environments.
  Published checkpoint `cf3d5a47` extends the same complete path to
  `IndexedVec`, including its parameter/index family, ordered `nil`/`cons`
  candidate list,
  producer-selected semantic package, certified transaction, and checked E1
  replay. Generic arbitrary-metadata whole-call package construction and the
  remaining I2-I4
  breadth matrix remain.**
- [x] Introduce reusable fold witnesses for typed metadata constants and defeq
  rules. `AddInductConstants` and `AddDefEqs` expose fold realization, output
  lookup/rule membership, input freshness, and `VEnv.LE`; the map-side lemmas
  additionally preserve `SMap.WF` and show that new metadata cannot fabricate
  a value-bearing declaration. Quot's fixed four-step CPS chain remains the
  small fixed-shape analogue.
- [x] Define proposition-valued `AddInduct` as the nonemptiness of an internal
  data-bearing `AddInductTrace` that aligns one Stage-3 `inductInfo`, the
  ordered `ctorInfo` list, one `recInfo`, and all generated iota rules with the
  corresponding Theory operations. This preserves the original public
  `AddInduct … : Prop` shape while the hidden trace retains intermediate
  maps/environments so proofs do not reconstruct a `foldlM` execution. The
  trace now carries the exact dependent `GenerationChecked decl` and
  `GenerationChecked.WF` certificate and derives its raw family, constructor,
  recursor, and rule payload from that single normalized artifact instead of
  duplicating Stage-3 acceptance and generation fields.
- [x] Prove `AddInduct.to_addInduct`, `AddInduct.le`, and
  `Aligned.addInduct`; remove both vacuous `nomatch` proofs. Complete the
  formerly impossible `TrEnv'.of_value` inductive case by proving that
  inductive metadata has `value? = none` and pulling old value lookups back
  through every insertion.
- [x] Add compile-time closure guards for `AddInduct.to_addInduct` and
  `Aligned.addInduct`. Their present `sorryAx` is inherited from the sorried
  `TrProj` in `TrExprS`; E1 adds no axiom declaration. P0-P2 must make these
  guards fail and then be tightened to a non-`sorryAx` closure.
- [x] Add a reusable replay/translation layer. `TrTypeExpr` separates the
  structural metadata translation from typing, and `to_trExprS` obtains the
  latter from the real Theory `WF` derivation. The elaborator fixture quotes
  `ConstantInfo` records from Lean rather than hand-building lookalikes.
- [x] Complete the Nat vertical slice: quote `inductInfo`, both `ctorInfo`s,
  and `recInfo`; prove their translations in the exact intermediate
  environments; construct `AddInduct`; execute `TrEnv'.induct`; and check
  `TrEnv'.wf`, `TrEnv'.aligned`, final replay equality, and recursor lookup
  uniqueness. Guard the fixture's exact transitional axiom closure.
- [x] Prepend a concrete value-bearing definition and prove that
  `TrEnv'.of_value` still translates it after the Nat inductive transaction.
  This must force the proof through the inductive branch; a quantified or
  impossible metadata-value premise is not an adequate test. The fixture does
  so with the actual `defnInfo` for `ReplaySeed`, and guards the resulting
  closure.
- [x] Repeat the actual-metadata transaction for Eq, including its
  parameter/index telescope, Prop recursor, universe permutation, final
  replay equality, `WF`, alignment, and recursor lookup uniqueness. Guard the
  exact closure and require it to equal Nat's rather than merely contain no
  newly declared axiom.
- [x] Repeat the actual-metadata transaction for `IndexedVec` over the actual
  Nat replay, and exercise type, changing-index constructor, and recursor
  lookup uniqueness. The fixture deliberately spells its indices as
  `Nat.zero` and `Nat.succ n`. The notation form exposed `OfNat.ofNat`,
  `instOfNatNat`, `HAdd.hAdd`, `instHAdd`, and `instAddNat` (and transitively
  `Nat.add`), which tests generic prelude-definition replay rather than the
  inductive transaction. Record this as a reduced dependency claim, not as
  evidence that the full notation-generated prefix has been replayed.
- [x] Repeat the actual-metadata transaction for `Acc`. Check the real metadata
  counts and recursive rule fields, translate the declarations in their exact
  intermediate environments, prove final replay equality/WF/alignment and
  lookup uniqueness, and pin the quoted kernel `RecursorRule.rhs`
  definitionally to the generalized Theory rule. Guard the fixture at the same
  exact transitional closure as the other E1 replay roots.
- [x] Migrate `AddInductTrace` to I2's paired raw/view generation block and
  replay the family-result and recursive-field alias declarations from actual
  metadata. Both replays include their actual alias definitions, exact
  intermediate environments, all kernel rule RHSs, final equality/WF/alignment,
  and lookup uniqueness.
- [ ] **L4L-11:** extend L4L-01E's generic automatic candidate/package
  construction across I2-I4's complete fixture matrix,
  keeping every dependency environment explicit and checking type, every
  constructor role needed by the family, and recursor lookup uniqueness.
  Separately add a notation-heavy prelude replay fixture before claiming
  whole-environment coverage; do not hide that prefix behind a hand-built
  Theory-only environment. Abstract witness-only tests are not sufficient.

### E2 — expose an oracle-construction theorem for ix (L4L-11)

Provide consumer-neutral lemmas from which ix can fill every
`InductiveOracle` field:

- `after` and `envLE` from `addInduct`/`addInduct_le`;
- `blockWF` from `VDecl.WF.induct` and `addInduct_WF`;
- translated type/constructor/recursor lookups from E1;
- `recursorFacts` from generated rule membership and registered defeqs;
- `recursorPatterns` from I5.

Ix remains responsible for address/catalog membership, freshness of KIds, and
the `nameOf` bridge. If any semantic oracle field cannot be produced without a
new assumption, strengthen lean4lean's checked-block API rather than weakening
the ix theorem.

## 8. Track L — move consumer-neutral APIs into Theory

This track can proceed independently once compatibility imports are designed.

### L1 — Theory API extraction (L4L-12A)

- Split `VLocalDecl` and its VExpr-only operations/WF/defeq lemmas from the
  `FVarId`-specific `VLCtx` layer into `Theory/LocalContext.lean`.
- Move `VExpr.boolLit`, `natLit`, `listCharLit`, `trLiteral`,
  `VEnv.ContainsLits`, the implementation-independent part of
  `VEnv.HasPrimitives`, and their lift/inst/instL lemmas into
  `Theory/Literals.lean`.
- Keep `TrExprS` and all `Lean.Expr`/`Literal.toConstructor` traversal in
  Verify. Re-export old names so upstream code does not break during migration.

### L2 — prove literal/prelude readiness, not an invalid containment shortcut (L4L-12B)

`ContainsLits` says only that names occur in the environment; it does not imply
their types. Define a Theory-level readiness predicate combining `Ordered`
with the exact Nat/Bool/Char/List/String constant types and required iota
rules. Prove:

- readiness + `ContainsLits l` gives
  `VExpr.WF env U [] (VExpr.trLiteral l)` (ix's `literalWF`/`hlit`);
- direct `trLiteral` meaning agrees with the Verify translation of
  `Literal.toConstructor`;
- readiness is monotone under `VEnv.LE` and is preserved by unrelated
  declarations.

Then change ix's `WhnfTheory.literalWF` field into a derived theorem from its
world/prelude contract.

### L3 — finish the Theory-only ix import surface (L4L-15C)

Audit the three remaining Verify imports after L1/L2 and Track P. Add Theory
equivalents for genuinely mathematical lemmas, flip ix imports, build, and
only then remove compatibility shims. The target is zero
`import Lean4Lean.Verify.*` lines under `Ix/Tc/Verify/`.

## 9. Track P — projection semantics and structures

The old companion recommends a recursor encoding, but the current API needs a
design gate first. `TrProj Γ structName idx e e'` has no environment, universe
count, structure descriptor, constructor metadata, or projection-name map;
`TrProj.uniq` is even stated for unrelated `s₁` and `s₂`. A recursor encoding
cannot simply be dropped into that signature.

### P0 — prove the API is expressible (L4L-13A)

- Freeze the seven current lemma statements as regression tests, then check
  whether a meaningful relation can satisfy them without strengthening their
  premises. In particular test structure-name dependence, parameter offsets,
  dependent fields, universe instantiation, and uniqueness.
- If the signature is inadequate, add a Theory-level env-indexed API such as a
  `VStructureView` plus `VEnv.TrProj U Γ view idx e e'`. Change Verify's
  `TrExprS.proj` through a compatibility wrapper. Do not encode the missing
  metadata as unconstrained existential witnesses.
- Coordinate the additive API with ix's `RawProjRel`; ix can close over its
  concrete `VEnv` when constructing `TrProjOK`.

### P1 — choose and define the semantics (L4L-13B)

Default to a recursor encoding because it reuses generated iota rules and is
consumer-neutral. Compare it against the alternative of applying a registered
projection-function constant, which matches Lean metadata more directly but
requires a projection-name map in Theory. Choose the representation that makes
all of the following derivable from one `VStructureView`:

- projection field type (including dependencies on earlier projections);
- constructor projection/iota behavior;
- congruence under defeq and environment extension;
- lift, substitution, and universe instantiation;
- structure eta and zero-field/unit-like behavior, or a precise statement of
  what additional Theory rule is required.

### P2 — structural law package (L4L-14)

Prove the seven upstream obligations—weakening, inverse weakening,
context-defeq transport, WF, uniqueness, term substitution, and universe
instantiation—and expose a bundled theorem matching ix's `TrProjOK`. Preserve
the individual compatibility theorem names for upstream Verify.

### P3 — projection checker verification (L4L-15A)

Use the same structure view to prove:

- `inferProj.WF`;
- `reduceProj.WF` for constructor applications and strings;
- the projection branches of WHNF and translation congruence.

### P4 — structure eta and unit-like comparison (L4L-15B)

Prove the semantic theorem needed by `tryEtaStructCore.WF` and
`isDefEqUnitLike.WF`. First attempt derivation from the recursor/iota package,
proof irrelevance, and projection uniqueness. If Lean's structure eta requires
a new primitive Theory defeq rule, write a design note covering subject
reduction, injectivity, confluence, and ix impact, and obtain upstream agreement
before changing `IsDefEq`. This is a metatheory change, not a local checker
lemma.

### P5 — ix handoff (L4L-14)

Instantiate ix's `RawProjRel`, derive `TrProjOK`, remove the `TrProj` sorry
origin from both audit manifests, and add projection-bearing end-to-end
fixtures. `RawProjRel.none` remains useful only for explicitly projection-free
worlds.

## 10. Track M — finish the live metatheory

These results are scheduled completion work, while still requiring
coordination with Mario because upstream has active research branches.

### MT1 — route selection and sort inversion closure (L4L-16)

Evaluate two routes in a small, focused proof branch:

1. finish and bridge the fetched `logrel@upstream` approach
   (`ShapeLogRel`, adequacy, and `Experimental/UniqueTyping`) into live VExpr
   judgments; or
2. complete the current stratified `HasTypeStrong` proof directly.

The spike must list every remaining assumption in the chosen route and close
the existing public `IsDefEqU.sort_inv` statement. Merge only that proof, its
necessary generic lemmas, and the documented route decision. Do not merge the
whole experimental branch: it changes unrelated implementation and pattern
code and still contains adequacy sorries.

### MT2 — close remaining injectivity and weakening inversion (L4L-17)

Building on L4L-16's completed `IsDefEqU.sort_inv`, prove the remaining public
statements:

- `IsDefEqU.forallE_inv_stratified`;
- `IsDefEqU.sort_forallE_inv`;
- `IsDefEqU.weakN_iff` in `UniqueTyping.lean`.

Re-run `IsDefEq.uniq`/`uniqU`, context inversion, and all downstream
`#print axioms` checks. This milestone removes ix's two remaining upstream
metatheory sorry origins.

### MT3 — close Church-Rosser's two `.extra` cases (L4L-18A)

The holes in `NormalEq.parRed` are the constant/application cases where a
parallel step meets a user defeq-pattern step. Use the generic `Params`
interface, L4L-10B's match inversion/non-overlap library, and rule RHS congruence to
prove the commuting diagrams. Keep the theorem generic in `[Params]`; concrete
environment assembly is a separate theorem.

Consume the concrete `Params` package already closed by L4L-10B and check that
`ParRed.church_rosser`, normal-form
uniqueness, and the live Standardization/HeadReduction endpoint contain no
hidden placeholder assumptions.

### MT4 — stabilize the `.extra` extension contract (L4L-18B)

Document `.extra` as the supported hook for consumer-certified defeqs and add
the missing monotonicity/transport lemmas under `VEnv.LE`. State exactly what
an ix `NativeOracle` must prove (typedness, symmetry/closure as needed, pattern
compatibility) and what lean4lean does not trust automatically.

## 11. Track V — finish Verify after the specifications exist

### V1 — independent level-normalizer proofs (L4L-02A/L4L-02B)

First prove `NormLevel.subsumption_eval` in L4L-02A. Ix's sorry-free level
normalizer uses a different representation but offers a proof decomposition to
port. Then prove the v4.31-added `NormLevel.isEquiv_wf` in L4L-02B from the
normalizer evaluation/subsumption facts and close its downstream list theorem.
Keeping these as two commits gives each upstream placeholder one exact removal
and prevents the small algorithmic invariant proof from being hidden inside a
larger checker patch. Neither proof has a technical dependency on inductive
APIs, but publication remains serialized after L4L-01E so §13 has one active
checkpoint at a time.

### V2 — recursor reduction (L4L-19A)

After I5 and E1, prove `reduceRecursor.WF` for Quot and inductive rules. The
proof must obtain the selected rule, match, checks, RHS translation, and result
typing from the generated/translated metadata—not from a global oracle.

### V3 — projection/eta checker roots (L4L-15A/L4L-15B)

Track P discharges `inferProj.WF`, `reduceProj.WF`,
`tryEtaStructCore.WF`, and `isDefEqUnitLike.WF`. Re-run the enclosing
`inferType`, `whnfCore`, and `isDefEq` theorems so the absence of a local sorry
also removes it from every exported root.

### V4 — complete environment-to-checker theorem (L4L-19B)

Build `TrEnv` for fixture environments containing ordinary declarations, Quot,
single/mutual/nested inductives, literals, structures, and extension defeqs.
State and audit the final executable-checker soundness theorem over this full
environment class.

## 12. Track T — trust closure, release engineering, and upstreaming

### T1 — make the sorry frontier shrink to zero (L4L-19C)

Keep the token-aware script exact. Every proof PR deletes entries; no PR may
rename/move a sorry and merely update the allowlist. At zero, invert the script
to reject every live sorry without an allowlist.

### T2 — audit and retire custom axioms (L4L-20A)

Treat the inventory in §2.3 as an initial declaration audit, then generate the
actual transitive closure for every supported root. At minimum the root set
contains:

- `Checked.analysis_accepted`, its closure/level/name/anatomy consequences,
  `Checked.wf_of_decl`, `Checked.to_declWF`,
  `VInductDecl.wf_iff_exists_checked`, `VEnv.addInduct_success`,
  `VEnv.addInduct_checked`, `VEnv.addInduct_WF`, the recursive-Pi
  recursor/rule-preservation roots, and every later checked-inductive/projection
  API exported to ix;
- the unique-typing, Church-Rosser, standardization, and head-reduction
  endpoints used downstream;
- `TypeChecker.whnf.WF`, `inferType.WF`, `checkType.WF`, `isDefEq.WF`, the
  remaining public checker operations, and the final executable-checker
  soundness theorem;
- every theorem name imported by ix's audit manifests.

Generate the report rather than hand-maintaining it. Each row must record the
root, layer (`Theory`, `Verify`, or ix), standard Lean axioms, project-specific
axioms, classification from §2.3, pinned Lean revision, and disposition. Keep
normalized output under version control or as a deterministic CI artifact so
that a dependency change produces a reviewable diff.

The first Theory rows are already enforced locally: all exported checked
structural facts, the three semantic compatibility bridges, the success/exact
analysis/collision transaction facts, and `VEnv.addInduct_success` close over
exactly `propext` and `Quot.sound`; `VEnv.addInduct_WF` and the six
recursive-Pi preservation roots additionally reach `Classical.choice`.
Compile-time `#guard_msgs` checks pin those results. No custom axiom was added
for either `Checked`, `Checked.WF`, or generalized inductive preservation.
Generalize this mechanism into the generated multi-root report rather than
replacing the local guards.

Use four acceptance states:

1. **Logical baseline:** `propext`, `Classical.choice`, and `Quot.sound` (usually
   a subset) are accepted where required.
2. **Platform contract:** an unavoidable runtime property may remain only when
   narrowly stated, named in the platform manifest, version-pinned, covered by
   differential and adversarial tests, and absent from Theory roots.
3. **Transitional bridge:** a plausible opaque/reference equation has a removal
   issue and may support intermediate Verify work, but cannot silently become a
   release assumption.
4. **Forbidden:** an equation known false on a supported toolchain, or not yet
   proved after the relevant implementation changed, may not occur in any
   supported root, even if the kernel cannot reduce the opaque/native function
   far enough to derive `False` internally.

Retire the classes in risk order:

1. Finish the cache-equation retirement started by L4L-01U. Five declarations
   are gone; remove the remaining three from reachable proofs, then prove the
   corrected v4.31 contracts, make the checker execute proved structural
   functions, prove sufficient reachable-input invariants, or weaken the
   refinement claim honestly. Merely deleting `[simp]` reduces accidental use
   but does not discharge an assumption.
2. Convert the thirteen reference equations into logical definitions with
   `@[implemented_by]` only when the replacement is known extensionally
   correct; otherwise use the reference implementation in the verified path.
3. Replace the five collection and five opaque/layout equations with upstream
   theorems or narrowly bounded/WF lemmas. Do not assume equality on malformed
   states when only constructor-reachable states are needed.
4. Decide the final platform budget explicitly. The expected candidates are the
   two pointer-equality implications and, if it cannot be eliminated,
   `Level.instLawfulBEqLevel`; retention is a reviewed decision, not a default.

CI must reject a new unclassified project axiom, any project axiom in a Theory
root, any forbidden axiom in a supported root, or a retained platform contract
without its manifest entry and tests. It must also reject attaching `[simp]` to
a project-specific axiom: simplifier reachability is too implicit for a bridge
contract. T2 is complete only when the report can be regenerated from a green
build and every remaining dependency is in an accepted state.

### T3 — differential adequacy (L4L-20B)

Add a test harness that elaborates fixture declarations with Lean, translates
the resulting raw environment metadata, constructs the justified analysis
view, and compares it with Theory generation. Run it over the fixed fixture
matrix in CI and over ix's declaration corpus at pin time. Compare failures as
data: accepted/rejected, raw/view normalization stage, generated constants,
universe lists, field counts, recursive positions, K flag, rule count, and
every RHS.

### T4 — upstream PR series (L4L-20C)

Keep semantic patches reviewable and dependency ordered:

1. level-normalizer proof and small generic lemmas;
2. Theory API extraction with compatibility re-exports;
3. Stage-1/2 inductive vertical slice and fixtures;
4. indexed/normalization/small-elimination/recursive-argument support;
5. mutual and nested support;
6. pattern package and Verify `AddInduct` alignment;
7. projection structure view, laws, and checker proofs;
8. injectivity/Church-Rosser completion;
9. remaining checker and axiom-minimization work.

Do not rewrite the published `jcb/induct` checkpoints. L4L-01U merges current
upstream into that development line once; each later upstream PR series is
then extracted onto a fresh review branch rebased on its current upstream
target. Do not mix the large Nix/fork-infrastructure delta into proof PRs
unless upstream asks for it. Record every PR and downstream pin in the
divergence ledger.

## 13. Milestones and gates

This is the sole status-bearing execution ladder. Exactly one milestone may be
`active`; all earlier milestones must be `complete`, and all later milestones
remain `queued`. A milestone becomes complete only when its entire deliverable
and every applicable gate below pass on one committed checkpoint. Earlier
partial implementation counts as a prerequisite, never as partial milestone
credit. A suffixed identifier such as L4L-01A is a full checkpoint with its own
commit and gates; completing L4L-01A does not confer partial completion on
L4L-01B or permit work to skip directly to L4L-01E. L4L-01U is the mandatory
upstream-integration checkpoint inserted after L4L-01B; the physical row order
is authoritative, and L4L-01C may not start before L4L-01U is complete.

| Milestone | Status | Exact deliverable | Completion evidence and ix result |
|---|---|---|---|
| **L4L-00 — published generation-readiness baseline** | **complete** | Stabilized fork infrastructure; one generalized source/view artifact path; proof-carrying non-identity transaction; retained semantic hierarchy; complete executable generation-shape gate; AliasFormer, AnnotatedPi, and `IndexedVec` checkpoints. | Source `bbb45e0e`, ledger child `c4fd62b2`, all gates green. Ix Pin A remains the separately recorded `5e5bb767`/`1f73f5c0` pair and has removed the three former inductive sorry origins without making an oracle claim. |
| **L4L-01A — staged semantic-input consolidation** | **complete** | Introduce one source-indexed builder over explicitly verified pre-family/post-family candidate stages, strict family/constructor translations, exact raw-family insertion alignment, and the existing dependent `Produced` traversals. Return the existing `Nonempty ProducedNormalizationCandidateSemanticRun`; make no view-WF or generation-package claim. | Source `7c792209`. AliasFormer, AnnotatedPi, and `IndexedVec` use the builder; their per-root semantic-input definitions are gone and exact constructor order is retained. Existing explicit downstream witnesses and one `viewWF` proof per positive are marked temporary until L4L-01E; no choice extractor was added; focused and universal gates pass. |
| **L4L-01B — family-validation semantics and staging** | **complete** | Interpret the exact singleton `checkInductiveTypes`/family-candidate run from one verified entry context. Derive view telescope and terminal-sort WF, raw-family constant WF through candidate defeq, exact insertion, and the verified post-family candidate stage. | Source `da45b536`. Exact singleton validation semantics derive the parameter/index view split, terminal/raw-family WF, exact insertion, and post-family candidate stage. AliasFormer, AnnotatedPi, and `IndexedVec` supply no independent post-family `VEnvs`/context; family terminal, annotation, fuel, and non-sort negatives remain phase-sharp; constructors remain uninterpreted; exact guards and universal gates pass. |
| **L4L-01U — upstream v4.31 reconciliation** | **complete** | Merge digama `upstream/master` through `ef849dfbd94a` without rewriting fork checkpoints or moving either master. Retain the v4.31 proof/API ports, upstream's five custom-axiom removals, the fork's Nix/CI and certificate surfaces, and the exact classifications of `NormLevel.isEquiv_wf` (L4L-02B) and `addDecl.WF` (L4L-19B). Add no constructor-trace work. | Source `7f864b459e4a6062b468d6e5416688feac0f9f99`. The 154-job Lake build, `nix build`, current-host six-check flake build, all-system no-build evaluation, formatter, CLI replay, exact 22-entry sorry guard, and exact 29-declaration axiom inventory pass. Root guards show no supported-root trust growth. The isolated ix v4.31 probe is diagnostic only; ix migration is deferred. The source and ledger are published on origin `jcb/induct`, and only that branch moved. |
| **L4L-01C — retained constructor-validation trace** | **active** | Add dependent operational evidence for the complete successful singleton `checkConstructors` traversal: duplicate/closedness/root-check, parameter equality, field type/universe, positivity/recursive-target, and terminal-family-application steps. Prove decomposition and recomposition with the executable result. | The trace is source ordered and exact; missing/extra/reordered and each validation-phase negative remain sharp; successful trace equivalence has only the executable baseline closure and makes no Theory-WF claim. |
| **L4L-01D — constructor-validation semantics and view WF** | queued | Interpret the L4L-01C trace with verified checker refinements and retained candidate normalization. Derive `fieldsWF`, constructor result `SpineWF`, and WF of the exact analyzer-owned view declaration for the currently accepted singleton subset. | All three fixture `viewDecl_wf` proofs are deleted; no `Checked.WF`, view, or view-WF premise is renamed or reintroduced; exact axiom guards pass; no normalization or validation breadth is widened. |
| **L4L-01E — generic singleton package closure** | queued | Combine the L4L-01A–01D owner, exact dependent analysis, and `ProducedGenerationShapeCandidate` into `Nonempty ProducedGenerationCandidatePackage`, retaining the exact ordinary producer equation without granting it shape or Theory authority. | All three positives use only the generic closure theorem; missing/extra/reordered/truncated/non-defeq regressions remain sharp; no manual semantic-input/view-WF scaffolding remains; universal gates pass. |
| **L4L-02A — level subsumption evaluation** | queued | Prove `NormLevel.subsumption_eval` with its existing statement and remove exactly that sorry-frontier entry. Keep the patch independent of inductive APIs. | Focused Level and full builds pass; the theorem's exact axiom closure is accepted; the frontier drops from 22 to 21; the change is a small upstream-ready commit. |
| **L4L-02B — level equivalence soundness** | queued | Prove the v4.31-added `NormLevel.isEquiv_wf` from the evaluator/subsumption library and close the dependent list-level soundness path without changing the executable normalizer. | Focused Level and full builds pass; exact root guards add no custom axiom; the frontier drops from 21 to 20; the change is a separate upstream-ready commit. |
| **L4L-03 — singleton environment-sensitive validation parity** | queued | Complete remaining singleton `checkInductiveTypes`/`checkConstructors` acceptance behavior: pre-declaration `checkType`, transparency/fuel-correct WHNF Pi/result peeling, WHNF recursive-target traversal, and definitional constructor-parameter agreement. | A syntactically different but definitionally equal positive and a genuinely non-defeq negative match kernel outcomes and traverse the L4L-01E package/E1 path. Result-level equality across mutual families remains excluded. |
| **L4L-04 — singleton normalization differential matrix** | queued | Cover family-result, parameter/index-domain, ordinary-field, direct-recursive, and Pi-hidden recursive aliases, including beta/let, opacity/non-defeq, and fuel boundaries. | Every case compares raw payload, normalized descriptor, recursive positions, recursor, and all rules with kernel metadata and replays through E1; generic rather than fixture-only axiom guards pass. |
| **L4L-05 — singleton positivity and constructor-validity parity** | queued | Extend acceptance/rejection to the kernel matrix for nested-negative occurrences, family mentions in nonrecursive/dependent/proof fields, recursive functions, and constructor universe bounds. | Each branch has the nearest-kernel differential; all accepted cases use L4L-01E and replay through E1; no proof-only premise or oracle broadens acceptance. This is breadth/completeness, distinct from L4L-01D soundness. |
| **L4L-06A — elimination mode and recursor levels** | queued | Implement `isLargeEliminator`, `getElimLevel`, `getRecLevels`, and `getRecLevelParams`; make `ElimMode.small` constructible and drive motive/recursor generation. | Or/And have exact Prop-only recursors; Eq-like and never-zero families retain legitimate large elimination; level parameter order matches kernel metadata and all rules. |
| **L4L-06B — K-target parity** | queued | Add `isKTarget` data and generation behavior without using K to bypass invalid elimination. | Eq-like positive and non-K negative fixtures match the kernel flag, recursor, universe order, and rules; L4L-06A regressions stay green. |
| **L4L-06C — empty and singleton edge shapes** | queued | Cover empty families and zero-/one-constructor behavior, including recursor/minor/rule edge cases. | Unit/Empty and focused edge fixtures match binder/minor ordering, field counts, recursive metadata, rule count, and every RHS; preservation uses the common checked path. |
| **L4L-07 — complete one-family parity** | queued | Integrate L4L-01A through L4L-06C into the fixed I2 positive/negative matrix, remove obsolete singleton staging seams, and replay every accepted family through E1. | Nat, Bool, List, Option, Prod, Unit, Empty, Or, And, Eq, HEq, Fin, Vector, Acc, and normalization cases match all recorded kernel fields. Only one public artifact path is live; all fixture/default/Nix gates pass; L4L-11 remains queued. |
| **L4L-08A — mutual checked representation** | queued | Generalize checked analysis to dependent lists of families with shared parameters, per-family indices/results/constructors, and cross-family recursive targets. | Tree/TreeList and a mutual indexed descriptor compute with exact source order; no generation or environment insertion is claimed. |
| **L4L-08B — mutual validation and normalization** | queued | Generalize validator traces, semantic interpretation, all-family staging, normalization, and package construction to mutual blocks. | Shared-parameter/result-universe positives and mismatch/reorder negatives match kernel phases; both fixtures obtain exact semantic packages; no generated recursor claim is made. |
| **L4L-08C — mutual generation and replay** | queued | Generate/preserve all motives, flattened minors, per-family recursors, and rules; insert types, constructors, recursors, and rules in kernel order. | Both mutual fixtures round-trip actual metadata, every RHS, `Ordered`, lookups, and E1 alignment; no singleton destructuring remains public. |
| **L4L-09A — nested representation decision** | queued | Audit `numNested`/flattened auxiliary metadata and commit an additive representation or proved pre-flattening relation with executable probes and ix compatibility evidence. | The design is sufficient for real rose-tree and nested-indexed metadata; no acceptance behavior or public field is changed without demonstrated need. |
| **L4L-09B — nested transformation and positivity** | queued | Model the chosen nested transformation, auxiliary descriptors, and validation/positivity obligations. | Rose-tree/List and nested-indexed transformed descriptors plus nearest negatives match kernel acceptance; recursor generation is not yet claimed. |
| **L4L-09C — nested generation and replay** | queued | Generate/preserve auxiliary declarations, recursors, and rules and replay the nested packages. | Both fixtures round-trip real `Inductive.Add.run` output through generic packaging and E1, comparing every metadata field and RHS. |
| **L4L-10A — generated iota pattern core** | queued | Express generated LHSs as `SimplePattern.iota`; prove inversion, recovery, distinctness/nonintersection, and uniqueness obligations; port consumer-neutral shape helpers. | A certified block supplies the complete generic pattern facts with standard Theory axiom closure; no open-environment instance is installed. |
| **L4L-10B — pattern soundness and assembler** | queued | Prove `pat_wf` and assemble block-local `Params` for generated rules plus separately certified extensions. | The assembler is generic over certified extensions, has no global open-environment instance, and exposes exactly the helpers ix and Church–Rosser consume. |
| **L4L-11 — inductive oracle handoff** | queued | Generalize E1 replay to the complete I2-I4 matrix and a notation-heavy prelude environment; expose E2's consumer-neutral after/LE/WF/lookup/rule/pattern theorem; adapt ix's existing staged E2b construction to the advertised full block class. | Lean4Lean and ix are green at one recorded Pin B pair; ix constructs `InductiveOracle` from ordinary semantic world/certified block evidence for that class and removes the superseded assumed block interface where possible. No Verify state or normalization oracle crosses the Theory boundary. |
| **L4L-12A — Theory API extraction** | queued | Move VExpr-only local-declaration and literal syntax/readiness interfaces into Theory modules with compatibility re-exports; keep `FVarId`, `Lean.Expr`, and traversal in Verify. | Lean4Lean and ix build through compatibility names; no semantic assumption is removed yet; import-direction and exact axiom gates pass. |
| **L4L-12B — literal and prelude readiness** | queued | Define the exact Ordered/type/rule readiness predicate and prove literal WF, Verify-translation agreement, monotonicity, and preservation. | Ix derives and removes `literalWF`/`hlit` assumptions; notation-heavy fixtures pass; no invalid name-containment shortcut is used. |
| **L4L-13A — projection expressibility decision** | queued | Freeze seven obligations, test the current `TrProj` signature, and commit the minimal env-indexed structure-view API if required. | Real parameterized/dependent/universe fixtures demonstrate representability; missing metadata is not hidden in unconstrained existentials; ix API compatibility is recorded. |
| **L4L-13B — projection semantics** | queued | Choose recursor- or projection-constant semantics and define one faithful relation for field types, constructor reduction, congruence, lift/substitution/levels, and eta requirements. | The representation computes on real structures and makes every L4L-14 premise expressible; no structural law or checker proof is claimed early. |
| **L4L-14 — projection structural laws and Ix Pin C** | queued | Prove weakening, inverse weakening, context transport, WF, uniqueness, term substitution, and universe instantiation; bundle them as ix's `TrProjOK` and preserve compatibility theorem names. | Ix instantiates concrete `RawProjRel`/`TrProjOK`, projection fixtures pass, and the `TrProj` sorry origin is removed from both ix audit manifests at a recorded Pin C pair. |
| **L4L-15A — projection checker verification** | queued | Prove `inferProj.WF`, `reduceProj.WF`, and projection WHNF/congruence branches from the L4L-13B view and L4L-14 laws. | Focused structure/string fixtures and enclosing checker roots pass with exact axiom closures; eta/unit-like roots remain queued. |
| **L4L-15B — structure eta and unit-like comparison** | queued | Derive `tryEtaStructCore.WF` and `isDefEqUnitLike.WF`, or complete an approved metatheory change if a primitive eta rule is truly necessary. | Both roots are sorry-free and audited; any Theory-rule change has subject-reduction/injectivity/confluence and ix impact evidence. |
| **L4L-15C — Theory-only ix imports** | queued | Migrate remaining consumer-neutral lemmas and remove Verify imports from ix after L4L-12B/L4L-15B. | `rg '^import Lean4Lean.Verify' Ix/Tc/Verify` is empty; compatibility shims are removed only after both repos build. |
| **L4L-16 — metatheory route selection and sort inversion** | queued | Timebox and compare the logrel and stratified routes; enumerate all assumptions; select one route; and close the existing public `IsDefEqU.sort_inv` theorem on a focused committed checkpoint without importing the unfinished experimental branch wholesale. | The public sorry is removed with an exact accepted axiom closure; only the necessary proof and generic lemmas are merged; the chosen and discarded routes are documented with concrete remaining obligations. |
| **L4L-17 — remaining injectivity and weakening inversion** | queued | Building on L4L-16's `sort_inv`, close `forallE_inv_stratified`, `sort_forallE_inv`, and `weakN_iff`, then re-audit unique typing and context inversion. | Ix removes its two remaining Lean4Lean metatheory sorry origins at a recorded Pin D pair; affected Theory and checker roots have exact accepted closures. |
| **L4L-18A — Church–Rosser `.extra` cases** | queued | Prove both generic `NormalEq.parRed` commuting cases using L4L-10B inversion/nonoverlap and RHS congruence. | Church–Rosser, normal-form uniqueness, and live standardization/head-reduction endpoints contain no placeholder; extension-policy work remains queued. |
| **L4L-18B — extension contract** | queued | Stabilize `.extra` monotonicity/transport under `VEnv.LE` and state the exact consumer `NativeOracle` typedness/closure/pattern contract. | Generic lemmas and ix boundary build; no external defeq is trusted automatically or smuggled through generated `Params`. |
| **L4L-19A — recursor reduction verification** | queued | Prove `reduceRecursor.WF` for Quot and certified inductive rules from selected rule/match/check/RHS metadata. | Quot, singleton, mutual, and nested recursor reductions pass without a global oracle; enclosing WHNF roots have exact guards. |
| **L4L-19B — environment-to-checker closure** | queued | Prove remaining nonprojection checker refinements and full `TrEnv` over ordinary declarations, Quot, all supported inductives, literals, structures, and extension defeqs; close the executable-checker theorem. | The complete environment corpus and final checker root build with exact closures; only the mechanical zero-sorry policy switch remains. |
| **L4L-19C — zero-sorry gate** | queued | Remove every remaining supported Theory/Verify sorry and invert the frontier script to reject any new one. | Token-aware frontier is zero, no allowlist remains, full gates pass, and ix audits shrink accordingly. |
| **L4L-20A — axiom reachability and retirement** | queued | Generate transitive root manifests, classify every dependency, and eliminate all forbidden/transitional project/platform contracts. | No project axiom reaches Theory; every retained platform contract is explicitly accepted and tested; both repos' audits agree. |
| **L4L-20B — complete differential corpus** | queued | Automate actual Lean metadata translation/comparison across the fixed inductive, projection, prelude, extension, and ix declaration corpus, including failures as data. | CI compares acceptance phase, metadata, generated constants, universes, recursive positions, flags, rules, and every RHS; all supported cases pass. |
| **L4L-20C — upstream series and release** | queued | Submit dependency-ordered semantic PRs, publish coherent Lean4Lean/ix final pins, and resolve every divergence-ledger entry. | Both repos are green at final pins; each fork delta is upstreamed or has an owner, issue, and removal condition; final release artifacts and manifests are reproducible. |

Every milestone must pass all applicable gates:

```text
perl .github/scripts/check_sorry_frontier.pl
nix develop --command lake build Lean4Lean.Theory Lean4Lean.Verify
nix develop --command lake build
nix build
nix flake check --all-systems --no-build --accept-flake-config
nix flake check --accept-flake-config --print-build-logs
nix fmt -- --check .
git diff --check
```

The flake is authoritative: milestone evidence must use the pinned Nix
toolchain and dependencies. Elan or a host `lake` invocation may be used only
as a non-authoritative diagnostic and never substitutes for either Nix-wrapped
Lake build, `nix build`, or the flake checks above.

Additionally:

- all new fixtures build in a default proof target;
- new theorem roots have checked `#print axioms` output;
- every named root satisfies the boundary-specific axiom threshold in §2.3,
  with no `sorryAx` or project-specific dependency in a Theory root;
- `rg '^import Lean4Lean.Verify' Lean4Lean/Theory` is empty;
- every source/view pair accepted by the public checked transaction is
  generated and preserved by the same artifact path; temporary
  direct/generalized or raw/normalized migration functions are not both
  semantically live at a checkpoint;
- touched existing Theory names are grepped in ix before merge;
- the kernel differential matrix is green for inductive/projection changes;
- at an ix pin, `lake update lean4lean`, full `lake build IxTcVerify`, and both
  audit executables pass with shrink-only sorry-origin edits.

The retired C0-C8 grouping maps to this ladder as follows: C0 = L4L-00;
C1 = L4L-01A through L4L-07; C2 = L4L-08A through L4L-09C; C3 =
L4L-10A/L4L-10B/L4L-11; C4 = L4L-12A/L4L-12B plus L4L-15C; C5 =
L4L-13A through L4L-15C; C6 = L4L-16 through L4L-18B; C7 = L4L-02A/L4L-02B plus
L4L-19A through L4L-19C; and C8 = L4L-20A through L4L-20C. These mappings are
historical cross-references, not alternative completion gates.

## 14. Ix pin and migration protocol

Pin A is complete and belongs to L4L-00. Pin B is the exit of L4L-11, Pin C
the exit of L4L-14, and Pin D the exit of L4L-17. L4L-12A/L4L-12B and
L4L-15A–L4L-15C also require ix migrations, but they shrink API/import debt
rather than create a new numbered semantic pin. L4L-20C records the final
release pair.

L4L-01U is an upstream/toolchain integration checkpoint, not a numbered ix
pin. Its isolated v4.31 probe establishes that merged Lean4Lean modules replay
and the consumer-facing runtime modules elaborate; it does not require this
repository to port ix's own ByteArray, Batteries `RBTree`, or proof-library
APIs. Perform that migration in ix at the next authorized pin and keep its
worktree, lockfile, and branch out of Lean4Lean commits.

For every Pin A-D:

1. Publish a green lean4lean commit and record its full hash.
2. Set ix's lean4lean dependency to that exact fork hash (or the equivalent
   upstream hash once merged), update the lockfile, and record the manifest
   pair. Do not assume the preceding pin or remote still names the intended
   source tree.
3. Build the complete verification target, not only `lake build ix`.
4. Inspect audit diffs. Delete disappeared sorry origins; investigate any new
   axiom before allowlisting it.
5. Add the new API usage and compatibility import in ix.
6. Only after both repos are green, delete ix-side copies/assumptions and old
   lean4lean shims.
7. Record the known-good revision pair and the remaining demand-ledger rows.

The following stay in ix: `KExpr`/addresses/Blake3/collision freedom,
`KVLCtx`, K-expression substitution and universe instantiation, the `TcM`
Hoare layer, `Methods` knot, catalog/cache/world provenance, execution proofs,
and `NativeOracle`. Move proof *techniques* or VExpr-generic lemmas, not
consumer-specific state.

## 15. Principal risks and decision points

- **Checkpoint/pin drift.** The generalized one-family generator,
  recursive-Pi proof, public transaction, `Acc` replay, paired normalization
  boundary, complete mixed preservation, public artifact switch, normalized
  Verify trace, checked normalization/type-check producers, complete checked
  alias generation certificates, six actual-metadata replays, context-indexed
  candidate provenance, existential checker-output translation recovery,
  exact verified candidate root/binder contexts, and annotation-complete
  recursive certification, singleton candidate-list normalization, generic
  candidate-spine extraction, dependent generation assembly, and the complete
  AnnotatedPi recursive-Pi annotation replay, plus the certified public
  non-identity consumer boundary and exact whole-call produced packages for
  both AliasFormer and AnnotatedPi, plus generic parameter/index family
  validation, the exact real `IndexedVec` family/constructor candidates, its
  complete outer producer equation, generic exact identity replay, complete
  produced semantic package, certified transaction, and checked E1 replay are
  joined by generic arbitrary-length operational list assembly, a generic
  source/candidate-indexed outer produced-package constructor, automatic
  source-ordered semantic hierarchy assembly under `Nonempty`, and
  semantic-owned generation/package projections. Exact checked decomposition,
  singleton family-view recovery, one post-family constant typing proof, and
  checked constructor-result spines now derive every view telescope and
  terminal typing judgment without fixture oracles. Exact analyzer success now
  also determines normalization identity, and retained semantic evidence
  reconstructs post-family WF; no fixture supplies either fact. Exact analysis
  plus minimal stored-spine/count shapes now also determine raw/check family
  identity, normalized pair identity and source order, all raw
  telescope/results and view terminals, and the complete dependent constructor
  list. The consolidated generation-readiness gate now checks this complete
  hierarchy at runtime, rejects missing or extra raw constructors, and lets
  exact dependent analysis plus analyzer-owned view WF derive checked WF and
  every per-position shape record. `IndexedVec` proves the automatic hierarchy
  retains both constructors in exact source order and that a swapped view fails
  the computational normalization-shape gate. All three fixtures retain exact
  strengthened-producer results without treating bare producer success as
  semantic authority. L4L-01A additionally consolidates the staged semantic
  inputs while retaining the exact source order and intentionally returning
  the hierarchy only under `Nonempty`. L4L-01B derives raw-family WF, exact
  insertion, and the post-family candidate stage from the singleton family
  validator, so no positive supplies an independent post-family context. The
  current source is the L4L-01U merge
  `7f864b459e4a6062b468d6e5416688feac0f9f99`, whose parent pair and
  publication evidence are recorded in §13 and this ledger child on
  `jcb/induct`. The exact
  22-entry sorry-frontier check, 154-job default Lake build, default Nix build,
  all six current-host flake checks, all-system no-build evaluation, formatter,
  CLI replay, and whitespace checks were rerun on 2026-08-04 over that source.
  Exact compile-time guards show that the new generic and fixture roots add no
  axiom; their broad Verify closure remains explicitly transitional. Pin A
  uses the earlier certificate-bearing `5e5bb767` checkpoint, paired with local
  ix snapshot `1f73f5c0`; keep that pair and this later producer checkpoint
  recoverable, require the corresponding Linux/Darwin CI builds at a pin or
  release boundary, and record any replacement hash in both roadmaps.
- **A subset masquerading as the spec.** A sorry-free `stageN` definition can
  still be incomplete. Final acceptance is kernel coverage plus negative
  agreement, not the absence of sorries.
- **Analyzer/artifact drift.** This failure mode is now guarded rather than
  present for the raw-normal-form subset: recursive-Pi analysis, public
  `Checked` accessors, preservation, transaction output, and Verify metadata
  all use the generalized artifacts. `NormalizedChecked` now pairs the raw
  singleton payload and view classification; constructor-level raw field
  pairing, the complete mixed generator, the public identity specialization,
  and normalized Verify replay now close the artifact/transaction part of this
  risk. The checked equality/type/certificate layer, generic candidate
  generation assembler, and candidate-derived AliasFormer and `AnnotatedPi`
  transactions are live, and the staged whole-candidate non-defeq rejection is
  pinned. AliasFormer and AnnotatedPi exact whole-call results now select their
  produced semantic packages. Published checkpoint `cf3d5a47` does the same
  for `IndexedVec`'s parameter/index/two-constructor declaration and carries
  the certificate through checked E1 replay. Automatic produced semantic
  hierarchy assembly and semantic-owned package projections now close the next
  ownership seam. The strengthened hierarchy gate now derives checked WF and
  all structural generation alignment; constructing the verified per-position
  inputs and analyzer-owned view WF from a general verified outer context and
  its exact traversals remains.
  Retain public `Acc` checks,
  every actual-rule-RHS equality, and the
  alias fixtures as regressions; older direct/raw-only definitions must remain
  compatibility specifications only or be removed after migration.
- **Normalization as an accidental oracle.** Shape equality alone does not
  justify a rewritten declaration, and whole-type defeq alone does not identify
  the raw binder positions needed by generation. Require `Normalization.WF`,
  a structural raw/view pairing, and derivation from ordinary checker or
  consumer defeq evidence. A runtime comparison with opaque
  `consumeTypeAnnotations` is a producer consistency check, not a theorem and
  not semantic authority. Never accept an arbitrary view supplied by Verify or
  ix, and never repair a missing reduction theorem with a custom axiom.
- **Raw de Bruijn scaling.** Indexed, mutual, and recursive-Pi rules multiply
  lift/inst arithmetic. The shared checked descriptor is now consumed by one
  generalized public path. Preserve that architecture while adding
  broader WHNF/defeq witnesses, complete positivity, and mutual recursion; continue
  moving normalized evidence into the descriptor and telescope lemmas rather
  than duplicating index calculations.
- **Projection API insufficiency.** The present `TrProj` signature may make a
  faithful, functional semantics impossible. Resolve P0 explicitly instead of
  hiding metadata in an oracle or preserving a false “frozen statement” rule.
- **Structure eta may change Theory.** A new defeq constructor would affect
  injectivity, confluence, standardization, and ix. Require a design proof and
  upstream agreement before adding it.
- **Research-branch optimism.** `logrel@upstream` is evidence of a viable path,
  not a drop-in solution. Measure its remaining adequacy/bridge debt with the
  exact live theorem as the spike gate.
- **Unsound bridge axioms.** Some current cache equations are documented false.
  Zero sorries is not a soundness claim until final-root axiom reachability is
  clean.
- **Fork/consumer drift.** The published `jcb/induct` development branch is
  ahead of both master and ix's recorded Pin A checkpoint at `5e5bb767`. Keep
  pinning coherent checkpoints and recording revision pairs; do not wait for
  the final research milestone.
- **Upstream collision.** L4L-01U reconciles the 2026-08-03
  `upstream/master` tip `ef849dfbd94a` as a real merge parent, including the
  overlapping inductive/checker/Verify/level files. Repeat the ancestry and
  overlap check at every later milestone boundary; if upstream advances again,
  insert another explicit integration checkpoint rather than hiding merge work
  inside a semantic milestone. Retain this roadmap's fixtures, consumer
  contracts, and trust gates when adapting overlapping upstream work.
- **Scope leakage from Experimental.** Experiments are useful sources, but no
  supported root may import them. Promote a proof only after removing its
  experimental sorries and giving it a stable API.

L4L-01A and L4L-01B are complete at `7c792209` and `da45b536`
respectively. The repeated semantic-input plumbing sits behind one
source-indexed staged owner, and exact family-validation semantics derive its
post-family stage; all three positives use it and the result deliberately
stops at `Nonempty ProducedNormalizationCandidateSemanticRun`. L4L-01U
reconciled live upstream and Lean v4.31 without starting semantic constructor
work. Active milestone L4L-01C now retains the constructor-validation execution
without making a Theory-WF claim; constructor-validator semantics/view WF and
produced-package closure remain L4L-01D and L4L-01E.
`VEnv.addInductGeneration`, its exact data-bearing trace and stable
consequences, normalized preservation, environment histories, the ordered
identity bridge, delegated public success/WF roots, all six earlier
actual-metadata replays, and the `AnnotatedPi` recursive-Pi annotation replay
are green and exactly guarded. The generic candidate layer now also
extracts family/constructor telescopes and results and assembles
`GenerationChecked.WF`: `CandidateExprRun.spineEvidence` preserves exact raw
emitted binders, `TelResultDefEqEvidence.replacePrefix` handles the
declared/emitted constructor parameter bridge, and `GenerationCandidateRun`
folds the exact dependent family/constructor evidence. AliasFormer's real
candidate and AnnotatedPi's nested candidate supply complete checked generation
certificates and `AddInductTrace`/`TrEnv'` replays through this path. AliasFormer
now additionally proves the exact whole executable call and supplies both
consumers from `aliasFormerProducedGenerationCandidatePackage`.
AnnotatedPi additionally pins the generated recursor and iota rule while
retaining the raw annotation syntax. AliasRec remains the
compositional constructor-normalization specification until its candidate
list is migrated; neither fixed alias is authority for arbitrary metadata.
The published `IndexedVec` result selects the exact parameter/index family and
ordered `nil`/`cons` traces. Its recursive identity witnesses and
`spineOfIdentity` bridge assemble their `GenerationCandidateRun`, produced
package, certified transaction, and checked E1 replay without a second
executable producer implementation.

The executable candidate producer and the exact AliasFormer, AnnotatedPi, and
`IndexedVec` operational proofs are the base for L4L-01A through L4L-01E.
`AddInductive.normalizeCandidateExpr` traverses arbitrary metadata with the
same configured checker full check, WHNF, and inductive fuel, including Pi
domains and bodies under the exact annotation-consumed local declarations
used by the kernel. Each position is fully checked before WHNF. Every Pi also
retains a structural annotation path and an exact successful raw-to-consumed
`isDefEq` run before its body context is extended. The producer separately
checks runtime agreement with Lean's executable but opaque
`consumeTypeAnnotations`; the retained certificate does not treat that test as
semantic evidence. `CandidateExpr` retains the complete
checker context, source, inferred type, WHNF result, Pi-domain/body position,
and all three kinds of exact checker-run equality; dependent lists retain
source family and constructor positions.
`buildNormalizationCandidate` repeats the existing family/constructor checks,
computes families in the input environment, inserts the raw family
declarations, and computes constructors only in the resulting post-family
environment. Its source-indexed result is still untrusted. Such a candidate
becomes a Theory normalization only after exact root translations,
verified contexts, and positional list runs are supplied. The actual
`AliasFormer` and `AnnotatedPi` family and constructor metadata prove their
whole calls equal the candidates enclosed by their checked semantic packages;
`IndexedVec` encloses the corresponding exact whole candidate equality in its
semantic package and routes both consumers through it. All three retain operational regressions
against verified checker runs, with inherited axiom closures guarded.
`CandidateWhnfStep.innerRun` recovers the erased final checker state, and
`WhnfRun.ofCandidateStep` attaches the matching verified context and strict
translations; the AliasFormer family certificate now exercises this complete
adapter. `CheckTypeRun.ofCandidateStep` supplies the parallel bridge for every
retained full check, and the AliasFormer pre-family and post-family checks now
exercise it. `IsDefEqRun.ofCandidateStep` supplies the third bridge for every
consumed binder domain and refines the exact successful run to Theory
`IsDefEqU`.

The generic semantic half is now explicit as well. Pi traces are recursively
context- and source-indexed at the raw domain and exact instantiated body; the
body index fixes the actual annotation-consumed local-context extension and
generated free variable. `candidateTypeAnnotation_exists_translation`
extracts the consumed domain's strict translation from the raw wrapper
application, and the exact `IsDefEqRun` relates their Theory endpoints.
`CandidateNodeRun.ofCandidate` pairs each retained full check and WHNF, while
`CandidateNodeRun.exists_ofCandidate` extracts both returned
translations from the verifier refinements after receiving only the matching
context and root source translation. `CandidateExprRun.evidence` folds
terminal and Pi nodes into the existing `DefEqEvidence` language, transporting
body typing and equality between raw and consumed binder contexts before
forming congruence over the raw Pi syntax. Its Pi case also uses unique typing
and explicit type transport, so checker-inferred aliases need only be
definitionally equal to the structural sorts rather than syntactically
identical to them.
`CandidateExprRun.source_tr` and `.view_tr` tie both endpoints back to kernel
syntax; the Pi case abstracts the retained free variable and transports the
body translation across the definitionally equal raw, consumed, and
normalized binder contexts. Exact guards pin the construction,
interpretation, and translation closures. `CandidateExprTrace.storedSpine`
additionally requires each raw emitted Pi to survive as the same outer Pi;
`spineEvidence` then accumulates pointwise binder equality, the terminal
result, and exact telescope length. AliasFormer's actual candidate trace now
supplies both its `NormalizationRun` and complete candidate-derived
`GenerationRun` through this interpreter. AnnotatedPi exercises the same
interpreter recursively through a raw `outParam Prop` domain, its consumed
`Prop` view, and the nested recursive target.
`CandidateExprIdentity` and `CandidateExprRun.exists_ofIdentity` now provide a
second, stricter interpretation for traces whose raw and normalized syntax are
identical at every recursive position. The current `IndexedVec` work proves
that invariant for the family and both constructors and turns the resulting
root runs into generation-ready spine evidence.

Singleton candidate-list normalization and generation assembly are now
complete. `CandidateList.singleton`
eliminates only the source-indexed singleton shape; `CandidateExprRootRun`
relates explicitly named raw/view endpoints to the exact recursive candidate;
`CandidateConstructorListRun` folds every constructor position into
`List.Forall₂`; and `NormalizationCandidateRun` constructs both the Theory
`Normalization` and its semantic `NormalizationRun`. AliasFormer reuses one
verified pre-family root and the exact post-family verified constructor root,
its resulting view passes dependent checked analysis, and its previously
hand-assembled normalization run now delegates to this generic boundary. A
truncated constructor view is rejected by `normalization?` before transaction
construction. `CandidateFamilyGenerationRun` aligns the family components;
`CandidateNormalizedCtorRun` derives both declared and emitted constructor
paths; `CandidateNormalizedCtorListRun` preserves every source position; and
`GenerationCandidateRun.wf` produces the existing Theory certificate. Every
new structural, operational, and semantic root has an exact axiom guard.
AnnotatedPi now proves this boundary scales past AliasFormer's terminal alias:
its constructor has a nonempty emitted telescope, a recursive target below a
Pi, and an actual `outParam` binder domain. The ordinary checker full-check,
WHNF, and raw-to-consumed equality traces pass `storedSpine`, yield the nested
telescope/result evidence, assemble `GenerationCandidateRun.wf`, and replay
the final environment, recursor, and iota rule.

The matching whole-candidate negative is now green. It reuses the actual
AnnotatedPi family/constructor metadata in an environment where `outParam` has
the correct type but is opaque. Metadata staging reaches candidate traversal;
the raw/consumed equality check then returns the dedicated binder-domain error
before any semantic package or transaction exists. Retain it with the four
leaf annotation positives, exact non-defeq leaf negative, truncated-view
rejection, and positive AnnotatedPi replay so the failure phase remains sharp.

The dependent consumer package and public transaction are now complete.
`GenerationCandidatePackage` contains the exact source-indexed candidate,
successful normalization/dependent analysis, `GenerationCandidateRun`, and
resulting `GenerationChecked.WF`; it alone supplies both the Theory
`GenerationCertificate` and Verify `AddInductTrace`. AliasFormer proves the
terminal-alias consumer is adequate and AnnotatedPi proves the nested
recursive-Pi/annotation consumer is adequate. `addInductCertified` is the
proof-erased non-identity Theory path, while `addInduct` remains the identity
compatibility theorem.

The first three outer producer instances are complete. AliasFormer and
AnnotatedPi explicitly reduce `checkInductiveTypes`, preserve the exact module
header while inserting the raw family, validate their constructors in the
post-family environment, and assemble dependent singleton lists. AnnotatedPi
additionally traverses a nested recursive Π and consumes an `outParam`
annotation under exact raw-to-consumed definitional equality. `IndexedVec`
extends the same path through one parameter, one index, and an ordered
dependent `nil`/`cons` list using exact recursive identity witnesses. Each
`ProducedGenerationCandidatePackage` encloses the semantic package assembled
from those same retained runs, and its Theory certificate plus Verify replay
both project from it. The proofs use exact candidate equality rather than a
coercion or erasure equality. Separate guards cover whole-call computation,
the combined produced packages, semantic certification, and the public
transactions.

The operational ordered-list subproblem is now generalized. The
former public reduction seam,
`checkInductiveTypes_singleton_zero_of_whnf_sort`, handled only a
zero-parameter singleton whose family immediately WHNFs to a sort. The generic
`checkInductiveTypes_singleton_of_candidate` theorem now replays arbitrary
parameter/index splits from a source-indexed candidate spine, and the real
`IndexedVec` family proves the one-parameter/one-index case. The exact
post-family `nil`/`cons` candidate list, complete outer producer equation,
semantic run, produced package, and E1 replay are published. Generic dependent
`Produced` witnesses now reconstruct family-type lists, arbitrary ordered
constructor lists, and complete family lists from exact per-position results;
all three outer fixtures use them, and `IndexedVec` demonstrates a list of
length two. `GenerationCandidateSemanticRun.producedPackage` now generically
performs the final outer packaging step from the same semantic owner, and all
three fixtures use it. `CandidateExprSemanticRootInput`, the dependent semantic
constructor/family/normalization inputs, and `.exists_ofProduced` automatically
assemble the complete source-ordered hierarchy from the operational `Produced`
witnesses plus exact verified per-position contexts/translations, returning it
under `Nonempty`. Semantic family/constructor generation wrappers project from
that hierarchy rather than accepting parallel roots or spines. View telescopes
and terminal typing are now derived from exact checked shape, one family
constant typing proof, and checked constructor result spines. Exact dependent
analyzer success now derives normalization alignment, and the retained verified
context plus raw/view equality and exact insertion derive post-family WF.
`GenerationCandidateSemanticShapeRun` now additionally derives raw/check family
identity, every normalized constructor pair and its exact source order, raw
telescope/results, view terminals, and the dependent constructor list from
analysis plus minimal stored-spine/count shapes. The consolidated
generation-readiness checkpoint now checks all of those shapes once over the
complete family/constructor hierarchy, retains the gate with the exact ordinary
producer equation, and derives checked WF plus every dependent shape record
from exact analysis and analyzer-owned view WF. L4L-01A consolidated verified
per-position inputs over two verified stages; L4L-01B derived the second stage
from family validation; L4L-01U reconciled and published the live-upstream
merge; active milestone L4L-01C now
retains constructor validation; L4L-01D derives analyzer-owned view WF; and
L4L-01E combines the
result with the strengthened gate to return the complete produced package
without fixture-specific alignment. Only
Theory-level generation, lookup,
ordering, pattern, and semantic facts—not checker state or a normalization
oracle—should be exposed to ix.

After L4L-01E, follow §13 without skipping: close the two isolated level proofs
in L4L-02A and L4L-02B; complete singleton environment-sensitive validation,
normalization,
positivity, elimination, K, and integration in L4L-03 through L4L-07; then
advance through mutual L4L-08A–08C, nested L4L-09A–09C, pattern
L4L-10A/L4L-10B, and oracle handoff L4L-11. The identity and alias kernel equalities remain the computational
regression gate, and every newly accepted family replays through E1 in its
own milestone. The completed generalized public path, `Acc`
transaction/replay, recursive-Pi kernel-rejection differentials,
environment-free universe/result/name/collision matrix, semantic `Checked.WF`
and `GenerationChecked.WF` bridges, and exact axiom closures remain regression
gates.

The current formalization source is the L4L-01U merge
`7f864b459e4a6062b468d6e5416688feac0f9f99` of
`da45b536220a3eff5ed78cf2f5afcf5e7491c40f` and upstream
`ef849dfbd94a`; this publication ledger child records the immutable source hash
on `argumentcomputer/lean4lean`'s `jcb/induct` branch. Neither local `master`
nor `origin/master` is moved by this work. On top of automatic produced
semantic-hierarchy assembly and
semantic-owned generation/package projections, it derives exact family and
constructor shape, candidate view telescopes, family terminal typing, and all
constructor result-target typing generically. AliasFormer, AnnotatedPi, and
`IndexedVec` no longer supply `viewTel`, `rightType`, `normalization_eq`, or
`typeEnv_wf`: their exact dependent analyzer equations determine normalization
identity, and verified context/equality/insertion evidence reconstructs the
post-family environment. They also no longer supply normalized pairs, raw
telescope/results, view terminals, or dependent-list alignment: exact analysis
and minimal stored-spine/count shapes determine all of those generically. Exact
analysis and WF of the analyzer-owned view declaration now derive checked WF
and all per-position shape records from one complete executable hierarchy gate;
the fixtures no longer supply either class of evidence. Missing and extra raw
constructor lists are rejected. Exact axiom guards pin the executable roots to
the standard logical baseline and the semantic roots to the existing
transitional sets. Completed milestones L4L-01A and L4L-01B consolidate the
verified staged semantic inputs and derive the post-family stage from exact
family-validation semantics. Completed L4L-01U reconciles the current
upstream/toolchain/axiom delta without beginning constructor work. Active L4L-01C
retains the exact constructor-validation trace without making a Theory-WF
claim; the temporary fixture view-WF proofs remain until L4L-01D, and the
complete produced package is intentionally deferred to L4L-01E. No stage may infer
shape or Theory meaning from bare producer success. Ix Pin A is complete at the
recorded pair Lean4Lean `5e5bb767b3491d21a71908d4c58bcbaa007283bb`
and local ix snapshot `1f73f5c016907eadb8ed0dc86ac65b07eb24a145`.
Pin B is exactly the L4L-11 exit and therefore waits for L4L-01U and L4L-01A
through L4L-10B, including full single/mutual/nested breadth and the
generated-pattern
package. No intervening milestone may paper over a gap with a new oracle
assumption or broaden the accepted axiom budget.
