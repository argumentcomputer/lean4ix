# Lean4Lean completion roadmap

**Status:** authoritative consolidated roadmap, recut 2026-08-24. This is
the only tracked planning document. Completed plans, failed-route narratives,
and detailed gate transcripts remain available in git history; durable fork
differences remain in `upstream-divergence.md`. Files under `plans/probes/`
are local machine-checked evidence, not status-bearing plans.

The recut retires L4L-16 as an active umbrella. Its useful outcome is a
conditional, sorry-free semantic development with two precisely named legacy
inputs. NORM/INV below now funds a direct semantic-adequacy route intended to
remove those inputs rather than prove them through full normalization. Neither
route holds unrelated checker, trust, or instance-engineering work inside an
ever-growing L4L-16 suffix chain.

## 1. Completion contract

Lean4Lean has two supported products:

1. `Lean4Lean/Theory/`, an implementation-independent model of Lean's kernel
   language, typing, definitional equality, environment growth, and the
   metatheory needed to use that model safely.
2. `Lean4Lean/Verify/`, a proof that the executable checker over `Lean.Expr`
   refines Theory.

The supported formalization is complete when all of the following hold:

- **Theory coverage:** every safe inductive declaration accepted by
  `Lean4Lean/Inductive/Add.lean` has a faithful Theory description, generated
  recursors and iota rules, and `Ordered`/`WF` preservation. Temporary staging
  predicates are proved implementation lemmas, not unexplained public
  restrictions.
- **Proof closure:** no supported Theory or Verify declaration depends on
  `sorryAx`. Deliberately kernel-rejected fixture recoveries remain separately
  classified and cannot mask proof debt.
- **No semantic placeholders:** the inductive environment path is inhabited,
  projection and reduction relations describe real checker executions, and
  checker success produces the evidence its Theory theorem consumes.
- **Checker refinement:** environment construction, primitive recognition,
  recursor reduction, projections, structure eta, unit-like comparison, and
  the final checker root are proved over the supported environment class.
- **Trust closure:** every release root has a generated transitive axiom
  report; no false or unclassified project axiom is reachable from Theory;
  unavoidable runtime contracts are narrow, versioned, tested, and kept out
  of the mathematical layer.
- **Consumers:** published Theory APIs suffice to construct inductive block
  certificates, recover lookup/pattern consequences, use concrete projection
  laws, and derive literal WF without importing Verify or trusting a new
  consumer oracle.
- **Upstreamability:** the fork delta is split into reviewable changes, every
  deliberate divergence has a removal condition, and release boundaries build
  on both the fork and its current upstream base.

Proof-complete and trust-minimal are distinct gates. Both are required for a
release.

## 2. Status snapshot

Snapshot date: 2026-08-25. Counts are derived from the compiled audit and
must be updated whenever a proof enters or leaves the frontier.

| Fact | Current state |
|---|---|
| Published development checkpoint | `origin/jcb/formalization3` = `03681c3a`, "conditional close, leaf residual = SortEdgeData". `origin/dev` = `4844eda4`; the local upstream base last reconciled into the development line is `e0e3f6bc`. |
| Current integration checkpoint | **STAB is gate-complete in this revision.** Lane V's readiness, quotient, and AliasFormer proofs and the D2 registered-body/replay slice are present. V3 now has a source-indexed arbitrary-block generation-shape gate whose proof-carrying producer retains one detailed normalization execution, transparent extraction of the complete mutual constructor-validation trace from that execution, and an exact continuation-factorization theorem proving that it also owns the family validator's statistics and terminal reader context. The retained execution continues through the real constructor environment, large-elimination result, recursor-universe layout, K-target decision, actual recursor synthesis, and declaration. Generic data-bearing family, constructor, and recursor interpreters consume those producer-owned equations in source order and construct the matching Theory folds and translated post-state; recursor declaration now retains a producer-owned common-K invariant. A generic rule-completable metadata prefix connects the generated family/constructor/recursor inventory to `AddInductBlockTrace`, and the unindexed and indexed Tree/TreeList fixtures instantiate it against their actual synthesized kernel maps. A generic `BlockGenerationRun` assembles the complete Theory `BlockGenerationChecked.WF` boundary from compositional, generation-indexed family and flattened-constructor evidence; both real fixtures populate it from the retained candidate hierarchy and recover their generation `WF`, while the indexed path transports its Nat projection/eta certificate through the exact multi-constructor declaration trace. The public outer execution now names precheck, nested elimination, ordinary flattening, recursor generation, and mixed nested restoration; all downstream and outer control flow is operationally complete. The former whole-run normalization premise is now derived from a strictly smaller source-ordered contract containing only the recursive family-type and post-family constructor-type candidate observers which the public run does not execute. Ordinary and nested executions preserve quotient initialization and feed generic exact semantic transactions. A decomposed `VEnvsExtension` and transaction-oriented `addDecl` bridge expose the remaining semantic fields precisely. For non-primitive blocks, coherent name-avoiding transactions derive `TrEnv'`, model extension, both Theory and host primitive invariants, and cross-safety monotonicity. A readiness-completed transaction can now follow exact replay with a shared checked list of Theory-only structure-eta registrations, preserving those invariants and projection artifacts; a per-structure registration artifact constructs the exact final `StructureEtaArtifact` and transports coherently across model extensions. Global `StructureEtaReady` is derived from an explicit classification saying that every host nonrecursive structure is either already registered at the transaction boundary or backed by an exact artifact whose rule occurs in that shared list. Checked generation now constructs canonical generated-rule capture spines, derives exact earlier-projector equations, and iterates the dependent selecting-minor prefix to complete `MinorsWF`, `ProgramsWF`, and base-model `RebuildWF` without an external minor contract. Remaining readiness work is the persistent eta-rule certificate: reconstruction must be proved in every arbitrary `VEnv.LE` extension even though that weak relation does not provide target-environment `WF`. Primitive-inductive recognition is proved executable and returns the exact canonical Bool/Nat shape; `addDecl` now splits the nonprimitive and primitive transaction branches. The recognizer's closed host shape now selects the complete canonical Theory Bool/Nat declaration directly, so primitive transaction producers choose neither a parallel raw source nor a semantic normalization run. Checked generation determines the recursor names, and the resulting canonical inventory plus coherent ordinary traces derives primitive reflection, host primitive safety, exact replay, and cross-safety monotonicity. The recognizer certificate and retained public nested-elimination run also prove that canonical Bool/Nat sources are preserved exactly and emit no nested auxiliaries, so neither fact remains a primitive transaction input. Primitive replay is now assembled from retained-execution-indexed family, constructor, and recursor insertion folds, and the public transaction package no longer accepts arbitrary traces. Lightweight aligned interpreters produce those exact folds. The retained family-validation context now exports universe-parameter preservation, and the closed Bool/Nat recognizer shape derives the exact family translations and family insertion; that insertion's canonical family lookup in turn derives both constructor translations and the constructor insertion. The same exact family-add equation now derives the complete canonical Bool/Nat `BlockGenerationChecked.WF` certificates, including validation, recursive-field, and result-spine semantics, so the replay assembler no longer accepts `generation_wf`. Remaining primitive work is generated-recursor translation/insertion, rule folds, and readiness from the retained execution. A concrete RoseTree run carries its actual restored family, constructor, main recursor, and auxiliary recursor through public `Environment.addInductive` and `addDecl` into the certified Theory nested transaction and exact `TrEnv'`. V5 has generic exact local alignment for all three restoration cases. Its concrete flattened side now has exact source inventories, checked analyzer semantics, readiness-parameterized semantic generation, exact synthesized recursor metadata, a deterministic rule fold, and an instantiated `NestedStagedCertificate`; all three flattened constructor positions expose paired ordinary typing/closure/pattern facts and registered restored-rule membership/WF. The completed-`List` readiness decomposition now constructs the pre-family semantic stage and both pre- and post-family projection/structure-eta records from a single residual premise. That premise is exactly `ProjectionReady.constructorNumParams_mono`: a positional `List` constructor invariant quantified over arbitrary future `VEnv` extensions, with no known inhabitant for parameterized `List` under the current open-world interface. Repair or justify that invariant before claiming the concrete certificate unconditionally. On the conditional path, all three host rule selectors now align with the generator's universe/major/capture/field boundaries, their RHSs have deterministic and semantic strict translations to the exact restored rules, completed spines match structurally through a generic Theory lemma, and the complete main/nil/cons flattened redexes restore to their runtime head pairs. A Verify-side certificate consumer discharges the stable `pat_wf` premises while keeping its transitional unique-typing dependency explicit. Generated `Pattern.Check.OK` is now constructed from explicit parameter and computed-index list relations; all three Rose rules are proved unindexed, eliminating their computed-index relation. Strict application translation can split at the reducer's `take`/`drop` boundary, recover a typed prefix spine below the WHNF import boundary, and rebuild strict or weak output applications from a typed capture spine. Canonical captures are proved equal to the host prefix/field slices, their pointwise translations compose generically, and the reducer's pure RHS tail is factored and normalized to prefix/field/trailing list application. The matched certificate consumer now returns that explicit registered-RHS application rather than an opaque pattern-path result. A completed block now exports its full `BlockGenerationEnv`; exact normalized recursor and constructor head typings, owner-family recovery, owner index-arity, and generated major/result shapes follow. At an unindexed site, the two typings of the major are reduced to an explicit definitional equality between applications of the same certified family head. A caller-supplied `IndTyAppInj` consequence turns precisely that equality into parameter agreement, after which generated matching, checks, captures, and reduction compose automatically. Exact constructor spines now expose their field suffix. Shared `instRevAt` algebra proves that a one-parameter common prefix specializes the generated lifted field telescope to ordinary dependent substitution; Pi-tower inversion then extracts the structural telescope equality needed to transport the complete field spine. The selected main and cons rules are certified at this one-parameter boundary, while the zero-field nil specialization remains available. Constant-interpretation transport now maps a saturated flat capture spine through σ̂ and retargets it against an explicitly definitionally equal restored rule type. The staged consumer retains the flattened spine, constructs canonical restored captures under an explicit `ConstInterp` and whole-rule-type alignment, and applies the final registered restored equation. Restored LHS towers β-collapse generically through both canonical captures and post-major arguments. The certified flat reduction now also exposes the exact instantiated generated-body/redex equality; σ̂ commutes with `instRev`, transports that equality, and a generic final-environment join isolates only the local restoreRec-versus-σ̂ body and redex alignments. The reducer's generator-aligned body form consumes that boundary, and its full translated recursor array is correctly guarded by an in-bounds major premise rather than a pre-major length equality. V5 now has a concrete six-point flat-to-final `ConstInterp`, complete flattened and inherited equation transport, arbitrary-level whole-rule type/LHS/body/runtime alignment, generic derived restored-body alignment, and arbitrary-level final runtime-redex alignment for the main/nil/cons rules. A joint one-parameter consumer now retains the flattened capture spine and generated-body match from the local `IndTyAppInj` consequence, and each selected Rose rule carries that result directly to its final runtime redex with no separate flat-match premise. The matched-body reducer tail accepts the result through post-major arguments. Exact nonliteral and constructor-headed `inductiveReduceRec` theorems now compose the real lookup/WHNF/selection path with the translated nested reduct. The public Rose environment exposes exact recursor and node/nil/cons constructor lookups, and concrete main/nil/cons executions discharge ordinary-branch K, literal exclusion, structure conversion, selection, universe metadata. Those executions now lift through the actual pointwise `reduceRecursor` wrapper with exact state preservation. Generic K-conversion, Nat/String-literal, early/late failure, and all three quotient-gate equations factor the remaining operational paths. The complete `Quot.lift` consumer now obtains its typed eliminator and constructor spines from the canonical quotient inventory, retargets mismatched but definitionally equal Quot parameters through an explicit `QuotAppInj`, and applies the registered quotient equation; the corresponding `Quot.ind` consumer derives its reduction by proof irrelevance. These consumers compose into an exhaustive `quotReduceRec.WF` and through the live `reduceRecursor` wrapper, including every non-Quot `none` branch and exact state threading. Producing `QuotAppInj` remains NORM-M6 work. The ordinary `k = false`/non-structure path now also has exhaustive live callback analysis: it executes `whnf.WF`, covers every host expression and literal conversion, closes all failure guards, and leaves only a named `SelectedBranchWF` on actual rule selection. Concrete main and auxiliary Rose wrappers instantiate it without exact WHNF equations, with the auxiliary wrapper jointly covering nil and cons. Successful selectors now invert from `List.find?` into exactly node, nil, or cons, and concrete branch constructors discharge universe, arity, and `FVarsBelow` bookkeeping; the only remaining selected-site premises are the three semantic outputs carrying both major translations needed by NORM's live `IndTyAppInj`. Remaining selected-site work is to discharge those outputs and prove semantic preservation across the factored K/structure-expansion/literal/failure paths. The transport APIs, execution bridges, and declaration interpreters have pinned axiom guards. TRUST now has exact custom, logical, admitted-proof, and compiler-decision manifests plus independently pinned closures for all four release surfaces; five dead bridge axioms and both live TreeMap traversal bridges have been retired, all remaining project axioms have been removed from the global simp set, and the persistent-map proof helpers are Verify-owned with compatibility imports at their former paths. DIFF has exact single-declaration replay plus a versioned JSON case/result contract, positive standalone recursive-alias and mutual-block source elaboration, normalized raw-source/generated metadata comparison, closed raw-to-Theory translation, ordinary and nested normalization/analyzer/generator/restoration comparison, analyzer-owned recursive positions, and packaged accepted plus phase-accurate elaboration/selection/module-load/kernel-replay rejection cases. `NormalEq.parRed` now exposes the two omitted admissibility premises: `PatternArgumentNonFunction` excludes eta-sensitive under-saturated majors, while `StructurePatternCompatibility` names only the registered-iota/structure-eta critical pair. `Params.Extension` inherits both. Their producers and the R5 proof remain open. |
| V3 operational-completeness correction | **Supersedes the observer-residual sentences in the integration and primitive rows above.** The residual nonprimitive `CandidateObserversComplete` contract is not derivable from the former public run: `plans/probes/deep_alias_candidate_gap.lean` exhibits 100,051 safe abbreviations for which the old public family/constructor validation succeeded but candidate-only parameter-domain WHNF timed out. `AddInductive.run` now consumes `buildNormalizationCandidateExecution` as its real validation prefix, after preserving validation, family-declaration, and constructor-validation order. Consequently every accepted ordinary or nested run directly retains the family and constructor candidates, `NormalizationCandidateExecution.completeForRun` and `EnvironmentInductiveExecution.complete` require no callback, and all public `addDecl` transaction bridges now ask only for semantic/readiness evidence. Both deep traversal regressions agree with the public boundary. |
| Primitive readiness delta | The earlier “remaining primitive work” and host-interface-gap sentences are superseded. Generated-recursor translation/insertion, the exact K target, and the generated-rule fold are derived from the retained execution. Exact family, constructor, and recursor provenance classifies every final canonical lookup; owner and singleton-constructor contradictions rule out newly activated dangling metadata. That classification derives final `ProjectionReady` and `StructureEtaReady`. Canonical Bool/Nat family and constructor candidate observers are reconstructed as standalone evidence, but operational completeness now follows directly from the retained public prefix for both primitive and nonprimitive blocks. Thus `CanonicalPrimitiveTransactionalVEnvsExtension.ofExecution` and primitive operational completeness take only input WF plus the executable recognizer result. Closing the global inductive branch now depends solely on the readiness-completed nonprimitive transaction producer. |
| V3 persistent-eta correction | **Supersedes the remaining-readiness sentence in the integration row above.** Raw `VEnv.LE` is intentionally only an inventory-inclusion relation, so the invalid expectation that it alone preserve target-supplied typing derivations has been removed. `VStructEta.WF` now quantifies over future `LE` targets carrying the explicit `VEnv.ConversionRegular` laws; every target `VEnv.WF` derives that capability. The generated projection/minor/rebuild chain is capability-parametric, well-formed environment history recovers the full certificate for registered rules, and checked generation unconditionally constructs both `VStructureView.WF.toStructEtaWF` and `StructureEtaRegistrationArtifact.ofProjection`. Exact host family/constructor/recursor observations plus `ProjectionReady` now construct that artifact directly, and the shared safety-indexed readiness completion computes its endpoint as the deterministic common-rule fold rather than accepting a chosen output. A rule plan, its WF certificates, projection readiness, and coverage now need be established only in the smallest `.safe` model; coherent replay transports the same rule values and coverage to the other safety levels. One exact safe ordinary or nested trace now also replays automatically into the larger partial and unsafe models while retaining a common checked artifact, and that named safe endpoint now feeds readiness completion directly. Generic capability consumers do not inherit the pre-existing unique-typing admission. The final checker theorem now states the completion contract honestly through `DeclarationInductiveSafe`: Lean accepts unsafe inductives, but the current `TrEnv .unsafe` history invariant deliberately excludes their metadata. The retained public precheck now proves closed family and constructor syntax, and the exact two-phase ordinary candidate traversals recover one common source-indexed raw Theory block without a parallel caller-selected raw list. The retained family metadata trace now computes the exact family-only Theory endpoint, constructor enrichment provably preserves that endpoint, and one dependent result carries the complete source-indexed staged semantic hierarchy. Family-only staging is now indexed directly by the retained detailed execution before any final raw-block shape is selected; its all-block index count no longer needs a nonempty premise. At default safe nonprimitive fuel, the outer execution discharges fresh-name provenance, positive checker depth, safety, and primitive mode definitionally, then existentially extracts the family raws from closed flattened sources. The public precheck supplies that closedness when the ordinary nested pass preserves the source list, while the retained constructor-validation hierarchy supplies every constructor closedness fact and enriches the computed family stage without another source premise. Remaining V3 readiness work is to derive terminal-sort evidence and ordinary flattened-source equality, construct readiness at the exact family endpoint, complete the analyzer/metadata/rule transaction, extend it through genuine nested restoration, and close the safe `inductDecl` branch of `addDecl.WF`. |
| V3 family-endpoint delta | **Supersedes the family-endpoint-readiness clause in the persistent-eta row above.** The later retained constructor-declaration trace proves that every constructor named by newly staged family metadata is absent at the exact family-only host endpoint. The arbitrary family fold now preserves `ProjectionReady` and `StructureEtaReady` for both multi-constructor and singleton families, and outer family staging derives those capabilities—and hence constructor enrichment—directly from input `VEnvs.WF`. The remaining pre-enrichment facts are terminal-sort evidence and flattened-family closedness; the ordinary source-equality bridge is one sufficient route to the latter. |
| V3 terminal-sort delta | **Supersedes the remaining terminal-sort clause in the family-endpoint row above.** The detailed normalization prefix now executes an exact source-indexed terminal-sort gate on the retained pre-family candidate traversal before assembling post-family candidates. Every accepted execution carries the resulting proof, its assembled-family projection is derived structurally, and outer family/enriched staging no longer accepts terminal evidence from a caller. Flattened-family closedness is therefore the only remaining pre-enrichment fact; ordinary flattened-source equality is one sufficient route to it. |
| Supported builds | Current Theory + Verify build: 169 jobs green. Current default build/tests: 239 jobs green. |
| Proof frontier | 9 supported proof declarations: 6 metatheory and 3 checker verification. The compiled allowlist has 15 entries after adding 6 deliberately rejected fixtures. Lane V removed 7 proof sorries from the previous 16-entry proof frontier. |
| Experimental surface | Zero source `sorry` tokens and no `stop`-hidden admissions, but endpoints remain conditional. The concrete five-rule `D2RegisteredBodyStep` discharge compiles. Both inherited D2 Nat sites are now replayed internally, so `D2BlockStepExact` contains only the Tree check, a paired five-rule Tree replay, and the discharged registered-body field. D2 also has generic conversion-aware prefix/collapse replay, an exact eight-common-arguments-plus-fields capture inventory, and a named `D2TreeLevelAlignmentStep`; the Tree suffix/body share the NORM-DI-dependent local head-argument/source-level alignment boundary rather than being pure engineering. The current full `Lean4Lean.Experimental` gate is green at 152 jobs (its pre-existing lint warnings are not promoted to errors). |
| Project axioms | 27 declarations: 25 in `Verify/Axioms.lean` and 2 pointer-equality implications in `PtrEq.lean`. The audit assigns stable IDs/classifications, pins the exact inventory, proves Theory reaches none, rejects dead or forbidden entries, and fails if a manifest axiom enters the global simp set. Its exact four-root closure additionally classifies 3 logical leaves, `sorryAx`, 6 rejected-fixture declarations, and 287 generated `native_decide`/`bv_decide` leaves, for 324 exact union leaves. |
| Upstream watch | Local scan last refreshed 2026-08-22. PR #32 remains open with a green 134-commit primitive-conservation stack and a complete proof in its new large primitive-verification module; keep V4 on watch rather than duplicating that broad live refactor. Also watch PR #43 (competing iota design) and PR #27 (cached-field proofs) before overlapping work or reconciliation. |

### Delivered foundation

The following supported surface is green and is not remaining milestone work:

- checked one-family, mutual, indexed, and supported nested-inductive analysis,
  generation, atomic environment transactions, exact lookup/freshness facts,
  and `Ordered`/`WF` preservation;
- proof-carrying `GenerationCertificate`, `ValidationCertificate`, block and
  nested-block consumer APIs, exact iota patterns, pattern combinatorics, and
  typed pattern soundness;
- a 25-transaction real-metadata replay matrix, kernel acceptance/rejection
  differentials, normalization/alias fixtures, and a 296-declaration fresh
  notation/prelude replay;
- consumer-neutral local-context and literal APIs;
- recursor-encoded projection semantics, structural laws, projection checker
  proofs, the completed-inductive `ConstructorHead` classification consumed
  by projection reduction, and the registered structure-eta/unit-like checker
  path;
- proof-carrying extension contractions and explicit registered-equation
  joining, rather than a pattern-membership soundness oracle;
- level comparison/normalization verification on the v4.33 base; and
- a compiled, exact `sorryAx` frontier for all supported Theory/Verify roots.

### Not yet claimed

- The accepted inductive language is a substantial, tested subset, not yet a
  proof that every declaration the executable frontend accepts is covered.
- The existing semantic-inversion endpoint is conditional on `SortEdgeData`
  and `LR.MajorLinkRect`; zero Experimental sorries is not unconditional
  closure. NORM/INV's primary route is to replace both premises with
  path-typed head reductions and concrete registered-rule adequacy.
- Nested block certificates do not yet expose the complete pattern surface
  unconditionally.
  Exact local restoration bridges cover complete auxiliary-family and
  auxiliary-constructor application spines (under explicit restored-head
  inertness for trailing arguments) and recursor renames. A separate paired
  staged certificate now recovers flattened rule typing, closure, and exact
  `IotaPat` facts and pairs each flattened entry with its exact registered,
  well-formed restored rule. The exact ordinary producer metadata prefix now
  constructs this package generically. The concrete RoseTree outer run is
  reindexed onto the exact Theory flattened generation and now supplies exact
  source inventories, checked analyzer semantics, recursor metadata, a rule
  fold, and the paired certificate under the single
  `RoseFlatCandidateReadiness09` premise. Consequently all three flattened
  rule positions have ordinary typing/closure/pattern facts and exact restored
  registration/WF. The six-point flat-to-final `ConstInterp`, all three
  whole-rule type/LHS alignments, and the resulting restored-body alignments
  are now concrete. Generic LHS application eliminates the former local body
  premise, while arbitrary-level main/nil/cons runtime-redex theorems discharge
  the remaining local σ̂ endpoint. A joint generic consumer now retains both
  the flattened capture spine and generated-body match from the single local
  `IndTyAppInj` consequence. All three selected Rose rules instantiate it
  through the final runtime redex, so no separate flattened-match premise
  remains. A matched-body reducer adapter carries that result across
  post-major arguments, and exact nonliteral plus constructor-headed
  `inductiveReduceRec` branch theorems compose the real lookup/WHNF/selection
  control flow with the translated returned reduct. The public Rose
  environment now exposes exact main/aux recursor and node/nil/cons constructor
  lookups; concrete main/nil/cons executions discharge K, literal exclusion,
  structure conversion, rule selection, and metadata arity. A generic
  `k = false`/non-structure live theorem now runs `whnf.WF` directly, analyzes
  every expression shape, transports Nat literals, executes the second String
  callback, and closes missing-rule/field/level exits. Main and auxiliary Rose
  wrappers instantiate it without any exact WHNF premise; their sole success
  obligation is the named `inductiveReduceRec.SelectedBranchWF`, with the
  auxiliary contract covering both nil and cons. Exact K-conversion,
  Nat/String-literal, early/late failure, and quotient-gate equations now
  factor the remaining operational branches. The public Rose executions lift
  through the real pointwise `reduceRecursor` wrapper with exact state
  preservation. Quotient-disabled pure runs now also join the exact live
  `RecM.WF` contract; the nonconstant, non-recursor, and missing-major exits
  close immediately. Both quotient-gate values now have live monadic wrapper
  joins, including state threading from a declining quotient attempt into
  the inductive fallback. A `quotInit = true` environment exposes the full
  canonical Theory quotient inventory, and an explicit `QuotAppInj` consumer
  aligns definitionally equal Quot parameters. Complete typed `Quot.lift`
  reduction uses the registered quotient equation, while `Quot.ind` reduction
  follows by proof irrelevance. An exhaustive `quotReduceRec.WF` composes both
  cases, every non-Quot `none` branch, `FVarsBelow`, translation, and exact
  state threading through the live `reduceRecursor` wrapper. Producing the
  required `QuotAppInj` remains NORM-M6 work. Generic rule application
  preserves `FVarsBelow` from
  the original recursor arguments plus the WHNF major, with checked universe
  instantiation preserving closed rule RHSs. Strict translation projects the
  selected major argument, while the exhaustive callback theorem derives its
  normalized translation and `FVarsBelow` result internally. Live
  `IndTyAppInj` plus the existing main/nil/cons body consumers must now
  discharge `SelectedBranchWF`; no selected callback equation remains at that
  boundary. Successful Rose selectors are now inverted from the executable
  `List.find?` result itself into exactly node, nil, or cons, including
  propositional identification of the retained rule. Concrete main and
  auxiliary branch constructors use that inversion to discharge universe
  instantiation, rule arity, and `FVarsBelow`, leaving exactly three semantic
  output functions which receive the strict original-major and weak
  normalized-major translations required by live `IndTyAppInj`. The
  completed-`List` package
  now derives its primitive,
  safety, semantic-stage, and pre/post-family projection/structure-eta fields.
  Its sole remaining premise is the current open-world
  `constructorNumParams_mono` obligation, which ranges over arbitrary future
  `VEnv` extensions and is not presently constructible for parameterized
  `List`.
- The final checker theorem, zero-sorry gate, transitional-axiom retirement,
  complete differential harness, and upstream series are open.

## 3. Execution model and scope decisions

Work is organized by dependency-bearing streams, not by a single numerical
ladder. Up to three streams may be active when their file surfaces are
disjoint. Each stream is serial internally. Any shared-interface edit forces
a joint checkpoint.

Statuses have exact meanings:

- **committed green:** one committed revision passed every applicable gate;
- **working:** implementation exists in the working copy but is not a
  checkpoint;
- **conditional:** a theorem is proved from named premises that remain open;
- **research:** no approved closure route is currently funded; and
- **external watch:** avoid duplicate work until the named upstream event is
  resolved.

Two scope decisions govern the remaining metatheory:

1. The release baseline may expose an explicit admissible-environment premise
   for the public inversion/normalization theorems when arbitrary `VEnv.WF`
   is known to be too permissive. The verified checker must construct that
   certificate for every declaration form it claims to support. Unrestricted
   large-elimination environments remain a stretch goal, not a reason to hide
   the premise or introduce an axiom.
2. `VEnv.WF` alone cannot yield a delta rank: well-formed mutual definitions
   can be cyclic. The admissible environment contract must exclude cyclic
   definitions from the reduction-pattern set or carry an explicit acyclicity
   witness. It must not pretend to derive termination from bare WF.

For Prop-sorted inductives, keep `CtorBundle.hu0`; deleting it is refuted.
The baseline route excludes small-elimination Prop recursor patterns from the
operational pattern set when proof irrelevance already derives the registered
equation. Index-determined and anomalous large elimination are separate
research tiers.

## 4. Remaining-work map

| Stream | Next deliverable | Depends on | Exit |
|---|---|---|---|
| **D — semantic instances** | Factor the paired D2 Tree field/body replay over local head-argument and source-level alignment supplied by NORM-DI; then D3 nested equations and D4 registered structure eta | finite replay is independent; the five Tree checks wait on NORM-DI's paired head observation; some generic work waits on META | concrete direct-adequacy instances compile with only explicit registered-rule certificates |
| **NORM/INV — direct inversion research** | Replace untyped head observations with path-typed ones, prove Nat/D0 adequacy directly, extract the registered-rule interface, retain paired inductive/Quot head arguments, and derive the three Injectivity theorems | M0-M7 below; full normalization is an optional separate track | R1-R3 and `IndTyAppInj`/`QuotAppInj` close without `SortEdgeData`, `BetaFire`, `PiPathInv`, or `MajorLinkRect` as producer premises |
| **CR — confluence engineering** | Prove the new R5 admissibility producers, use them to close `NormalEq.parRed`, and assemble the live `Params.Extension` instance | saturated-argument non-function follows from generated constructor metadata; `StructurePatternCompatibility` must agree with D4; full assembly also uses NORM/INV, SST, and D | R5 closed on the repaired accepted class; later Church--Rosser endpoints unconditional over that class |
| **SST — strengthening research** | Repair the `.extra` certificate packaging, re-found the per-depth `NormalEq`/CR core, close `weakN_iff`, then prove the repaired projection head inversion | CR and the accepted instance surface | R4 and repaired R6 leave the frontier |
| **ENV — checker environments** | Prove the `inductDecl` case of `addDecl.WF`; operational candidate retention is closed, so derive the remaining generated readiness certificates and the nonprimitive semantic transaction (the primitive branch's canonical metadata staging and readiness are proved) | committed integration checkpoint; generated certificate/replay surface | V3/V4 closed and full environment translation theorem stated |
| **REC — recursor verification** | Supply NORM-DI's explicit inductive-head injectivity result to discharge the exhaustive live `SelectedBranchWF` contracts for the main/node and auxiliary/nil/cons Rose consumers, then prove K, structure-expansion, and remaining literal/failure-path semantics while repairing or justifying the sole open-world `constructorNumParams_mono` premise. Exact selected-WHNF premises have been removed from the live contracts; the complete Quot consumer is landed conditional on NORM-M6's `QuotAppInj` producer. | open-world constructor-parameter repair; NORM-DI/SST for final clean closure | V5 closed for Quot, singleton, mutual, and nested rules |
| **PROMOTE — stable semantic API** | Move the retained SExpr/shape development out of Experimental, regenerate the audit surface, resolve names, and pin root axioms | stable API decision; conditional endpoints are allowed | supported roots import the stable modules and the audit cannot miss them |
| **TRUST — axiom closure** | Keep the landed four-root policy exact and continue retiring the persistent-container, TreeMap, cached-metadata, and opaque-operation bridges | upstream theorem availability; local bridge consumers | final platform budget contains only tested pointer/layout or lawful-equality contracts, absent from Theory |
| **DIFF — differential corpus** | Broaden the landed source/ordinary/nested positive and phase-specific negative goldens | current harness | supported positive and negative corpus runs in CI |
| **RELEASE — upstream series** | Reconcile, extract dependency-ordered PRs, publish reproducible artifacts | all closure streams | final revision green; every fork delta upstreamed or explicitly owned |
| **RENAME — Lean4Ix identity migration** | Rename the public project for its role as the Lean 4 formalization and verifier used by Ix, with a staged compatibility window | a committed green main-theorem checkpoint and a pinned `~/projects/ix` consumer revision | canonical Lean4Ix repository/package/CLI identity is live, Ix consumes it, compatibility policy is fulfilled, and all release gates are green |

### Recommended near-term order

1. **Proceed from the green integration checkpoint.** Preserve the seven
   Lane V proof closures, the completed five-rule D2 registered-body
   discharge, the generic D2 prefix/collapse replay slice, and the exact
   trust manifests while advancing the open streams below.
2. **Use the repaired truthfulness boundaries.** The false projection-head
   statement is repaired: its constructor fields now require a genuine
   completed-inductive `ConstructorHead`, and Verify derives that certificate
   from exact `ctorInfo` lookup readiness. `NormalEq.parRed` now requires
   `PatternArgumentNonFunction` and `StructurePatternCompatibility`; construct
   the former from saturated generated constructors and the latter with D4.
3. **Advance independent product work.** Build the V3 decomposition and proof,
   hold V4 behind the PR #32 tripwire, instantiate the nested transport bridge,
   and continue retiring the bridges exposed by the completed four-root axiom
   closure.
4. **Run NORM-DI and SST as separately funded research.** NORM-DI starts with
   the path-typed reduction seam and an actual Nat zero/successor adequacy
   proof; it does not begin with a generic interface refactor. Each attempt
   has a theorem target, a discriminating probe, and a kill criterion. A
   failed criterion closes that attempt; it does not create another suffix by
   default.
5. **Converge.** Assemble live instances, finish V5 and the final checker root,
   reduce the frontier to the six fixture recoveries, finish trust/differential
   gates, then extract the upstream series.

## 5. Work-package detail

### 5.1 STAB — committed integration checkpoint

The 2026-08-24 STAB checkpoint proves:

- five ordinary-declaration readiness transports through the shared
  `Verify/Environment/Readiness.lean` interface;
- constructive quotient initialization and its `TrEnv'` replay; and
- the v4.33 AliasFormer validation/alignment trace.

These remove seven supported sorries. The same checkpoint also contains the
completed D2 registered-body discharge and generic prefix/collapse replay.
The complete same-revision gate is green: supported Theory + Verify (168
jobs), exact trust-frontier audit (174 jobs: 15 known sorries; 324 exact union
leaves across Theory, Verify, library, and CLI; 27 custom axioms, zero
reachable from Theory, zero globally registered as simp), default build and
tests (238 jobs), Experimental (152 jobs), package outputs, all 11 flake
checks via `path:.`, Nix formatting, `git diff --check`, import boundaries,
and the Experimental source-admission scan. Remote CI builds Experimental
even though the Lake default target does not.

### 5.2 D — concrete and generic semantic instances

**Delivered:** D0 (Nat), D1 definitions, the D1 quotient environment layer,
the D2 checked mutual Tree/TreeList environment, generic syntax transport,
the per-step semantic transport engine, and generic registered-telescope
closure.

**D2 exact bundle:** `D2BlockStepExact` now contains three fields:

1. `D2TreeCheckedStep` — not volume; its current statement asks for parameter
   equality at a stuck inductive application. NORM-DI M5 must discharge that
   equality locally from the paired head observation rather than consume the
   exported `IndTyAppInj` produced downstream;
2. `D2TreeReplayStep` — a paired capture/collapse result for only the five
   Tree/TreeList entries. It is mixed: the common eight-argument prefix is
   finite engineering, while the field suffix and collapsed body must move
   from constructor-side parameters/levels to the generated rule's recursor-
   side telescope and canonical source levels; and
3. `D2RegisteredBodyStep` — discharged by `d2RegisteredBody`; generic
   `closeTel_strong` derives the complete lambda towers from the five opened
   generated-body equalities. `D2BlockStepExact.of_remaining` fills this
   field, leaving callers only the preceding two premises.

`D2TreeLevelAlignmentStep` now names the missing equality
`ctorLs = TreeGen.sourceLevels.map (SLevel.instV recLs)`; in this fixture the
right side computes to `[l]`. NORM-DI M5 must decide whether literal list
equality is justified by exact generation metadata or whether the replay
should consume a weaker typed instantiation transport. Together with the
locally discharged Tree check, that alignment feeds the paired replay field.
The generic engine now delivers `spinePrefixForallN`,
`Pattern.IotaTyping.redexSelf`, and
`ruleReplayOfRawSpine_defeq`; the concrete block proves that every capture
list is exactly the eight common recursor arguments followed by constructor
fields. `d2NatZeroRuleReplay` and `d2NatSuccRuleReplay` discharge both site
obligations for the inherited rules in arbitrary D2 contexts, and compatibility
theorems reconstruct the legacy seven-rule capture/collapse contracts.
Remaining independent D2 work is the finite aligned Tree field/body
calculation. Do not describe `D2TreeReplayStep` as pure volume until alignment
has been factored out of its signature.

Then:

- D3 registers nested rules as equations only; use `AssembledPat.recover` and
  the generic `HeadSep` laws, retaining only the concrete inventory proof.
- D4 exercises a nonempty registered structure-eta environment.
- The D1 quotient semantic instance waits on the Prop-pattern policy plus
  stuck-Quot injectivity.

The generic admissible-instance construction still needs block
classification/`pat_wf`, cross-history `ExtSeparation`, the `uvars > 0`
definition rung, generic iota/check/registered assembly, Prop-pattern policy,
and nonvacuous structure eta. Generic transport and the per-step engine are
already landed. Do not use Theory's currently tainted `pat_wf` as the
semantic source; that would make sort inversion circular.

### 5.3 NORM/INV — direct semantic inversion

**Decision.** The funded release route is direct logical-relation adequacy,
not a proof of `SortEdgeData`. The existing conditional chain remains
compilable as a comparison target until the direct route reaches the same
public theorems, but no new release milestone depends on proving
`SortEdgeData`, `BetaFire`, or `LR.MajorLinkRect`.
The M0-M7 sequence is named **NORM-DI**; **NORM-WHN** below is the optional
full-normalization track.

The decision follows four concrete observations:

- `probeN5-sortedge-beta.lean` proves that after `f` reaches a lambda,
  `WHResult (f.app a) A` is equivalent to `WHResult (body.inst a) A`.
  `HeadObservationData` does not retain a property of `body`, so the current
  `SortEdgeData` induction has no decreasing or reusable premise for dynamic
  beta.
- The present relation already retains the semantic lambda body action, but
  its root weak-head observations are untyped. In particular,
  `LRS.ValTyPi2` stores component `TypeDefEqPath`s while storing only raw root
  reductions, and both `LR.constDefEq` and the constant case of adequacy call
  `WHRedS.defeq_of_piPathInv` to recover the missing root typing. Thus fixing
  only the iota rectangle would leave a second circular edge.
- The published [domain-semantics mechanization][domain-repo] solves the
  analogous beta/iota adequacy problem by carrying typed weak-head reductions
  and by consuming the selected Nat branch's logical-relation hypothesis
  directly. Its [paper][domain-paper] mechanizes Nat large elimination and
  argues for the broader indexed-inductive extension; that extension is a
  design guide, not evidence that this repository's generic generated-iota
  case is already solved.
- This fork has a universe hierarchy. A single homogeneous typing equality is
  therefore not an adequate local replacement. The existing
  `TypeDefEqPath` is the required adaptation: it transports terms one edge at
  a time without assuming heterogeneous transitivity or universe collapse.

[domain-repo]: https://github.com/digama0/domain-semantics-lean
[domain-paper]: https://arxiv.org/html/2607.13662v1

#### Target architecture and dependency direction

Names in this subsection are working names; the contracts and forbidden
dependencies are normative.

1. Add a term-level typed reduction bundle and a type-level path-typed bundle
   near `TypeDefEqPath`:

   ```text
   TypedWHRedS Γ M M' A := IsDefEq Γ M M' A ∧ WHRedS Γ M M'

   TypeWHRedPath Γ A A' :=
     ∃ u, TypeDefEqPath Γ A A' u ∧ WHRedS Γ A A'
   ```

   The raw reduction is retained for determinism/head computation; the typed
   or path-typed component is the only authority for conversion.
2. Make every direct Pi/sort head observation retain its root
   `TypeWHRedPath`. In particular, replace the two raw root reductions inside
   the direct form of `LRS.ValTyPi2`; keep its domain/codomain
   `TypeDefEqPath`s. `LR.constDefEq` can then apply
   `TypeDefEqPath.defeqDF` to the caller's term equality instead of invoking
   `PiPathInv`.
3. Treat beta as a local typed reduction. The adequacy induction supplies the
   exact beta equality and the already retained semantic action of the lambda
   body. It must not normalize `body.inst a` globally.
4. Treat iota as a selected-branch adequacy obligation. Keep
   `Params.Semantic.iotaSite` as the operational, typing, match, capture, and
   contraction certificate. Add a separate adequacy-layer certificate that
   says the exact selected RHS preserves the logical relation, built from the
   semantic RHS branch and recursive semantic hypotheses. Do not add
   logical-relation fields to `SExpr.Params.Semantic`; that would invert the
   current import layering.
5. Strengthen the `.indTy`/Quot logical-relation observations to retain a
   *paired* classified head and related argument spines. First attempt this as
   a syntax-rich sidecar to the existing atomic semantic shape. Introduce a
   new `ShapeS` constructor carrying head arguments only if the M4 probe shows
   that the sidecar cannot be preserved by the fundamental theorem.

During M1-M2, make the richer observations an additive direct sidecar over the
existing `LogRel` (working names `DirectDefEq`/`DirectTyDefEq`) and project the
old relation from it. This keeps `LogRel.whr`, `LogRel.whr_ty`, and the legacy
conditional theorem compiling while the spike is unsettled. The direct
sidecar's reduction closure must require `TypedWHRedS`/`TypeWHRedPath`; it may
not inherit the old untyped closure for its extra evidence. After M2 passes,
M3 decides from actual proof duplication whether to merge the richer fields
into `LogRel` or retain the sidecar as the stable adequacy interface. A merge
is allowed only with a compatibility proof that does not reintroduce the
producer cycle. The corresponding direct contextual-adequacy theorem must
retain the sidecar for head-injectivity consumers and provide an explicit
projection to the current `LR.ContextualAdequacyAt` for
`LRS.PiPathInv.of_adequacy`.

The intended dependency graph is:

```text
typed/path-typed root reductions + concrete Nat branch adequacy
  -> Nat/D0 contextual adequacy at depth 1
  -> LRS.PiPathInv.of_adequacy
  -> path-valued Pi/sort inversion

paired classified-head observation + local generated-rule adequacy
  -> D2 contextual adequacy
  -> IndTyAppInj
  -> D2/REC parameter transport

paired Quot-head observation + Quot rule adequacy
  -> QuotAppInj
  -> public reflection and R1-R3 closure
```

`PiPathInv`, `IndTyAppInj`, and `QuotAppInj` occur only on the right side of
these arrows. A concrete rule certificate may use a recursive branch relation
provided by the semantic interpretation, but may not assume any of those
exported inversion conclusions.

#### Planned file surface

| File | Planned responsibility | Boundary |
|---|---|---|
| `Experimental/SExpr.lean` | Define the two generic reduction bundles and their syntax-only transport API beside `TypeDefEqPath` | no logical relation, fixture, or adequacy dependency |
| `Experimental/ShapeLogRel.lean` | Store root paths in direct Pi/sort observations; add the paired classified-head relation; change shape algebra only after the M4 sidecar probe | no concrete Nat/D2 rule proof |
| `Experimental/ShapeLogRelAdequacy.lean` | Direct `constDefEq`, beta/iota adequacy induction, `RegisteredAdequacy`, contextual extraction, and compatibility wrappers | no fixture-selected generated metadata |
| `Experimental/SExprParamsD0.lean` | Nonvacuous Nat zero/successor certificates, D0 delta certificate, and direct instance theorems | no guessed generic interface before M2 succeeds |
| `Experimental/SExprParamsD2.lean` and `SExprParamsD2Registered.lean` | Local paired-head parameter transport, level-instantiation repair, five Tree certificates, and inherited Nat extension | no exported `IndTyAppInj` as an input |
| `Experimental/SExprParamsD1.lean` and `Lean4Lean/Quot.lean` | Quot-specific certificate and direct application injectivity after the M4 representation decision | no premature generic head redesign |
| `Experimental/SExprInductiveCandidates.lean` and `plans/probes/` | Preserve the conditional comparison route and discriminating failures during M0-M6 | no new release dependency on `SortEdgeData` |
| `Theory/Typing/Injectivity.lean` | Final reflected R1-R3 statements with the accepted explicit environment premise | no import from `Experimental` at a checkpoint |

Promotion may split these responsibilities into stable modules, but it must
preserve this dependency direction. In particular, do not solve an import
cycle by moving fixture facts into the syntax layer.

#### Milestone ledger

| ID | Deliverable | Effort/risk | Exit evidence |
|---|---|---|---|
| **M0 — dependency lock** | Pin the exact circular call sites and a green baseline | small / low | dependency inventory, N5 result, focused build, and axiom output recorded at one revision |
| **M1 — path-typed reduction seam** | Add the two bundles and a Pi-observation/constant evaluator that consumes the stored root path | medium / medium | the direct constant-lambda path compiles with no `PiPathInv` parameter |
| **M2a — Nat direct spike** | Prove zero and successor iota adequacy for `natParams`, then contextual adequacy at depth 1 | large / highest beta/iota risk | premise-free `natPiPathInvDirect` plus nonvacuous zero/successor witnesses |
| **M2b — D0 delta extension** | Extend the same proof to `d0Params` and its zero-arity definition | small-medium after M2a | direct D0 adequacy covers beta, delta, Nat zero, and Nat successor |
| **M3 — interface extraction** | Lambda-lift the minimal per-rule assumptions actually used by M2 | medium / medium | a generic registered-adequacy contract instantiated by Nat/D0 without strengthening its assumptions |
| **M4 — paired head applications** | Retain same classified heads, levels, typed spines, and pointwise argument relations | large / second research gate | direct `IndTyAppInj` on a discriminating same-head application probe; sidecar-vs-domain decision recorded |
| **M5 — D2 closure** | Build all five Tree/TreeList rule certificates and inherited Nat transport | large / medium-high | D2 direct adequacy and `IndTyAppInj`; `D2BlockStepExact` has no global-injectivity premise |
| **M6 — Quot and reflection** | Reuse or minimally generalize the head observation for Quot and reflect inversion publicly | medium / medium | `QuotAppInj` and R1-R3 close at the accepted explicit environment premise |
| **M7 — migration and retirement** | Move consumers to the direct route, promote the stable API, then remove the legacy producer premises | medium / low after M6 | no supported root reaches `SortEdgeData`, `BetaFire`, or `MajorLinkRect`; complete checkpoint gate green |

M2a is the first go/no-go milestone. Passing it removes dynamic type-level
beta as a normalization prerequisite for the release inversion path. M4 is
the remaining genuinely novel design gate for D2/REC; it is deliberately
later so the iota interface is extracted from a real proof rather than guessed
in advance.

#### M0 — dependency lock and baseline

Before editing a shared relation:

1. Record the current definitions and consumers of `LogRel.whr`,
   `LogRel.whr_ty`, `LRS.ValTyPi2`, `LR.constDefEq`,
   `LR.adequacy_of_iotaWitnessStep`, `LR.MajorLinkRect`, and
   `LRS.PiPathInv.of_adequacy`.
2. Retain N5 as the falsifier for any body-blind dynamic-beta proposal. Add
   one small direct-route probe only if it distinguishes whether a proposed
   root path can be built without subject reduction; do not create a new
   numbered plan chain.
3. Pin a focused Experimental build and `#print axioms` for the current D0
   conditional endpoint. Record grep guards for the forbidden producer calls
   so later milestones cannot accidentally close through the legacy route.
4. Keep the direct proof additive through M2b. Do not delete or mass-refactor
   the compiling conditional development before the Nat theorem exists.

M0 exits only when every occurrence of `piInv` in the constant-application
path and every use of `linkRect` in the iota path has an identified replacement
producer. Discovery of another consumer extends M1's inventory; it does not
justify assuming its result.

#### M1 — path-typed weak-head observations

Implement the smallest syntax-level API needed by the direct proof:

- constructors from one typed reduction or one `TypeDefEqPath` plus raw
  reduction;
- reflexive/identity observations where the direct relation needs them;
- composition that preserves the *left* universe index of a heterogeneous
  path;
- symmetry/right-end extraction as existentials, matching
  `TypeDefEqPath.symm` and `.right`;
- weakening, substitution, and environment-extension transport only at call
  sites that require them; and
- term conversion through `TypeDefEqPath.defeqDF`.

Then introduce a direct Pi observation whose two roots are
`TypeWHRedPath`s. Refactor or add a direct variant of `LR.constDefEq` so its
lambda branch obtains

```text
A --TypeDefEqPath--> forallE B F
```

from the Pi observation and retypes `htailTerm` with `.defeqDF`. Apply the
same change in the fundamental theorem's constant case. The ordinary beta
case builds `TypedWHRedS` from its exact `IsDefEq.beta` derivation; delta and
registered contractions use their existing proof-carrying equalities.

M1 acceptance:

- the direct constant evaluator and its caller have no `LRS.PiPathInv`
  argument;
- no theorem converts an arbitrary `WHRedS Γ A A'` plus endpoint typeability
  into `TypeDefEqPath Γ A A' u`;
- the existing universe-polymorphic `TypeDefEqPath` tests still compile; and
- no raw reduction is used as conversion evidence.

Current M1 checkpoint (2026-08-24): `TypedWHRedS` and `TypeWHRedPath` are
syntax-layer bundles with composition, weakening, substitution, exact beta
construction, registered-action construction, and term conversion through
the retained heterogeneous path. `LRS.ValTyPi2Direct` is an additive Pi
sidecar with legacy erasure and laws for left projection, symmetry,
transitivity, path-typed weak-head closure, shape monotonicity, join, and lift
equivalence. Path-aware constructor-spine and leaf adapters consume those
paths edge by edge without `TypeDefEqPath.collapse`. The least-fixed-point
`LR.DirectTyDefEq` now retains a direct domain and a Kripke direct codomain at
every Pi node; it erases to the legacy relation and is closed under left
projection, symmetry, transitivity, path-typed weak-head reduction, and
same-level shape lowering. `LR.constDefEqDirect` consumes that recursive
evidence without `PiPathInv` or a context-WF premise, and
`LR.constDefEqDirectRootLam` is the first syntax-directed caller: it builds
the initial path-aware application spine and feeds every recursive child
back to the direct evaluator. Both have the standard
`[propext, Classical.choice, Quot.sound]` axiom closure.

Attempting to wire that unindexed, type-only sidecar through the complete
fundamental induction exposed a sharper closure failure: a Pi codomain
callback accepts only a legacy-related argument, so a polymorphic context
variable (the Nat motive is the first concrete case) loses its direct
function action before the variable is applied. A merely downward-closed
type package cannot repair that loss. This agrees with the reference
mechanization's level-graded construction, where the complete lower-level
term and type relation occurs in every Pi/lambda action.

The additive replacement `LRD` is now landed. It is guarded by semantic shape
level, stores both direct term and direct type relations at the preceding
level in Pi/lambda clauses, and projects every node to the existing `LR`.
`LR.DirectSubst1`, `LR.DirectSubstWF`, and `LRD.Adequate` carry those actions
through contexts. Bottom remains deliberately head-free; informative sort
and Pi observations alone create typed-root obligations. Erasure, bottom and
sort construction, sort-to-type projection, joint term/type left projection,
joint term/type symmetry and transitivity, dependent conversion, direct-
substitution left/symmetry projections, context lookup, typed type and term
weak-head closure, same-level shape lowering/raising and type-shape join, and
canonical cross-level lift equivalence now compile with pinned standard axiom
closure. The lift theorem is deliberately an equivalence only for shapes
originating at the lower level; it makes no projection claim about arbitrary
higher refinements. Adequacy exposes the shape and lift algebra pointwise, in
addition to left/symmetry/transitivity and the bvar and sort fundamental
constructors. This closes the discriminating motive-variable lookup test
without adding context WF, subject reduction, or a root-manufacturing
callback. Low-level guarded Pi formation, lambda, exposed application, and
syntactic application constructors now package the legacy projection together
with the path-typed sidecar. A direct type extractor and binder-extension
theorem retain arbitrary semantic observations through extended direct
substitutions. Exact informative-shape adequacy constructors now cover
heterogeneous application and self-adequate Pi and lambda branches; the lambda
branch transports its actual beta contractions through `TypedWHRedS`. Full
semantic-shape dispatch now wraps all three cases: application aligns its
function, argument, and joined result observations at one common level before
lowering back to the caller, while Pi and lambda eliminate every incompatible
shape and preserve the informative guarded branch. A paired direct
pattern-leaf spine now keeps the legacy and guarded major relations and Pi
actions at identical endpoints, and the guarded leaf contract keeps the
legacy result explicit. Cross-level guarded constant-lambda rectangles lift
and lower those synchronized edges. The resulting full `LRD.constDefEq`
evaluator recursively rebuilds every informative function layer from typed
roots and retained direct Pi actions, with no `PiPathInv`, context-WF, or
subject-reduction callback; its structural constructor and inductive-head
branches package the additive legacy projection explicitly. All of these
interfaces retain the standard `[propext, Classical.choice, Quot.sound]`
axiom closure.

M1 is not yet wired through the complete fundamental induction. The
syntax-directed guarded root caller `LRD.constDefEqRootLam` now seeds the
one-argument paired spine and passes the established legacy result into
`LRD.constDefEq`. Native registered-iota infrastructure is also present:
paired recursor captures are materialized at level `n + 1`, constructor
captures remain in legacy `LR` at level `n`, the registered semantic site
constructs both typed actions, and `LRD.iotaDefEq_of_ctorExactAt` transports a
guarded generated-RHS result across the two exact contractions without a
subject-reduction premise. The generated-RHS contract deliberately exposes
the mixed capture boundary so each concrete family upgrades only the
constructor fields its RHS actually uses.

The generated-RHS boundary is now concrete. Paired guarded captures can be
lifted to existential canonical levels; a syntax-independent guarded
fixed-head shape chain synchronizes them with the semantic `ShapeSpine`; and
a full path-semantics zipper consumes the actual `PathSpineWF`, retaining raw
conversion edges only behind an explicit guarded conversion callback. An
informative guarded head term now derives its displayed Pi type internally,
so the final generated-rule consumer asks for one exact head self-relation,
not independently selected term and type proofs. The consumer rewrites its
finished folds through the descriptor's literal `rhsTower` and preserves the
caller's exact result term/type observation. The conversion callback is now a
named `LRD.FixedHeadConvertStep`; `of_parts` completes it from the legacy cross
edge and independently justified right endpoint via `LRD.TyDefEq.complete`.
The zipper also no longer asks each capture to precompute guarded validity of
its selected domain type: it applies the actual Pi-domain conversion in the
reverse direction to the guarded exposed domain, then reverses that edge for
the argument conversion. Thus its weaker `DirectTermCaptureDefEqAligned`
payload retains only the guarded term relation, while the older fully paired
capture remains available to existing consumers.

Both generated Nat entries now have literal descriptors and machine-checked
capture inventories. Their real fixed bodies have exact multi-beta paths.
The zero output and its complete `LRD.IotaRHSDefEq` contract compile: bottom
closes internally, all three live paths are upgraded from the recursor-prefix
payload, and the informative result follows from only the recursive fixed-body
self-relation plus guarded conversion at conversion edges actually present in
the path spine. The successor output and complete contract compile with the
same two inputs plus exactly one proof-relevant guarded term upgrade for its
predecessor capture, the sole constructor-field boundary deliberately left at
legacy level `n` by the mixed generic contract. The upgrade is indexed by the
legacy witness's exact element/type shapes; its existential packaging is now
internal, and it carries no redundant direct type sidecar. Bottom and
inductive-type observations have zero-cost upgrade constructors. Neither
contract accepts the final RHS relation as a premise.

The two native exact leaves are now threaded through that boundary as well.
`NatDirectIotaView.of_pat` classifies the proof-relevant generated descriptor
as exactly zero or successor; `natIotaRule_ext` proves descriptor uniqueness
from the registered RHS towers, and the zero/successor native-leaf consumers
canonicalize an arbitrary selected rule internally before invoking the full
guarded RHS contract. Their dependency closures add only the already-audited
native decision leaves for the two generated-rule lookups and RHS
disjointness. Existing legacy fixed-head conversion producers also feed the
guarded zipper through `LRD.FixedHeadLegacyConvertStep.of_legacy` and
`LRD.FixedHeadConvertStep.of_legacy_and_right`; the latter exposes only the
guarded right-endpoint validity still genuinely required.

Native guarded leaves now compose at the rectangle boundary too. Direct
argument lists and `DirectPatternLeafSpine` have structural left/right-prefix
projections, and `LRD.iotaDefEqRect_of_ctorExactAt` runs the existing typed
registered contraction three times to produce the two rows and cross edge at
one literal result observation. Above that native boundary,
`LR.DirectMajorLinkRectAt` names exactly one guarded rectangle per framed link
of a normalized constructor path. `LRD.iotaDefEq_of_ctorDefEqAt` folds those
rectangles using `CtorAnchorDisciplineAt`, then builds the two root
`TypedWHRedS` values from the retained `LastPair` Pi/result certificates before
using guarded weak-head closure. Thus raw root reductions are never treated as
conversion evidence. `LRD.IotaMajorLinkStepAt` now names the precise residual
at one reached fixed-level iota site: it retains the selected recursor and
constructor matches, semantic RHS, normalized direct leaf pair, typing, and
guarded result-type relation, and asks only for that site's
`DirectMajorLinkRectAt`. `LRD.iotaLeafDefEqAt_of_majorLinkStep` performs the
executable match inversion, proves both recursor-prefix major premises from
the direct argument lengths, closes the constructor relation, and folds the
site rectangle into the complete `LRD.IotaLeafDefEqAt` contract. The remaining
major-side work is therefore exactly to construct this site callback across
nontrivial `CtorFrame`s and replace the legacy root-anchor producer; neither
the native exact rectangle nor the surrounding leaf wrapper remains open.

The proof-relevant guarded RHS selector now preserves recursive data as well.
`LRD.IotaRHSDefEq.of_nonbotWitnessResult` selects the non-bottom fixed-head
witness and its attached predicate in one `fixedLowerWitnessResult`
elimination, so retained seeds, child trees, and semantic typing data cannot
be paired with a second witness at the same public indices.
`LE_Interp.Witness.typedRDeepTrue_of_strong` types that exact witness at the
registered strong derivation's native stratification depth while retaining
only trivial recursive-edge data.  The packaged
`LE_Interp.RHS.fixedLowerWitnessTypedResult` and callback-level
`LRD.IotaRHSDefEq.of_nonbotWitnessResultTyped` therefore expose the selected
recursive result and its semantic registered-type observation together,
without restarting the guarded coherence rung.  The further
`LE_Interp.RHS.fixedLowerWitnessCoherentResult` packages that same selected
witness with `CoherentSeedAt.nativeOrLocal`, so root lowering preserves the
genuine/local tag while the native semantic type observation remains paired
with it.  `LRD.IotaRHSDefEq.of_nonbotWitnessResultCoherent` now carries this
package through the live guarded RHS callback: it reuses the exact selected
witness, instantiates the registered strong typing directly in the
valuation's source context, and exposes both the native/local branch and the
proof-relevant `TypedRDeep True` observation to the fixture leaf.
The direct counterpart,
`LRD.IotaRHSDefEq.of_nonbotWitnessResultDirectCoherent`, now consumes
`LRD.CoherentSeedAt` itself, so genuine evaluator children retain all-depth
guarded coherence while strict restarts remain visibly local; it never
forgets the guarded half merely to reconstruct it later.

The fixed-body boundary has been narrowed further without manufacturing a
semantic witness from `HasType`. `LR.DirectFixedHeadTelescopeLE` retains a
guarded term capture at every literal telescope layer. Its fold returns, from
one recursive elimination, the direct application chain together with
`headElemTy.T ≤ headTy`; `LR.DirectFixedHeadProducer` keeps the registered
`LE_Interp.Witness` paired with that telescope, so `Witness.mono` lands it at
the chain's exact selected type. The producer-driven zipper then calls
`LRD.SelfAdequateAt.closedHeadSelf` with that real witness. Additive
`_of_selfAdequate` zero/successor output, full-RHS, and native exact-leaf
contracts compile with standard logical axiom closure (plus the same three
audited native decisions at descriptor canonicalization). The successor
variant still exposes exactly one predecessor term upgrade; neither branch
accepts an arbitrary `headSelf` law or its final RHS relation.

The finite producer side is now explicit as
`LR.DirectFixedHeadDominanceSpine`: its base retains the caller's actual
result typing and dominance by the reached tower, and each literal layer
retains the synchronized semantic spine edge and exact guarded capture. It
constructs both `DirectFixedHeadTelescopeLE` and `DirectFixedHeadProducer`;
`LR.DirectFixedHeadAlignedTyping` now packages that spine with the exact
proof-relevant semantic term/type witnesses, both retained child trees, and
the explicit comparison from its singleton Pi tower to the selected
registered-type observation. Its `.producer` theorem performs the only
allowed weakening. The Nat self-adequate RHS and exact-leaf callbacks now
return this inspectable alignment package rather than an opaque completed
producer. That callback-shaped boundary remains useful for the successor
branch, but the registered zero branch now constructs the comparison from its
trace and no longer asks the caller for `makeAlignment`; it never infers the
comparison from nonfunctional `HasType` evidence.

The exact recursor-prefix bridge now preserves all five canonical readbacks:
left syntax, right syntax, capture types, element shapes, and type shapes.
`LR.DirectCtorArgsDefEqListed`, the registered `FourView` list projections,
`LE_Interp.Matches.iota_materializeDirectRecListedAt`, and
`LRD.iotaActions_of_exactListedAt` carry those lists without reselecting a
witness. `LRD.IotaRHSDefEqListedRecAt` fixes the actual `A`, result shape, and
result type already selected by the leaf; this avoids the false stronger
contract that would demand the same exact leaf at every independently chosen
result type. `LRD.iotaDefEq_of_ctorExactListedAt` consumes that fixed-result
contract and transports the generated RHS across the registered actions.

The registered-type observation is now retained through the live evaluator
rather than reselected at the native leaf. `LR.DirectRegisteredTypeRoot` and
`LR.DirectRegisteredTypeTrace` pair the original proof-relevant semantic
witness with every exact guarded Pi application; the trace is threaded
through `LRD.constDefEq` and its root-lambda caller. One-layer `ConsView`
inversion recovers the literal domain, codomain, capture, and result
comparison, while the dependency-safe `FourView` exposes the four Nat
recursor layers. Semantic `varN` length rigidity and
`LR.DirectCtorArgsDefEq.lengths` synchronize that view with the evaluator's
literal recursor lists. Consequently
`natRegisteredRecursorTrace_fourViewElim` supplies the exact successor-minor,
zero-minor, and motive captures directly from the selected trace, and the
zero/successor `Nat*RegisteredIotaMajorLinkStepAt` contracts split the final
site without recovering the generated descriptor again.

The zero branch now also carries its semantic rule-type observation at that
same selected trace. `ConsView.bodyWitnessLift` follows an exact registered
Pi output under any current valuation, with exact-level companions for both
it and `LE_Interp.Witness.forallE_singleMap`; `FourView.sparsePrefix` records
the three singleton capture binders. Canonical Nat-type and `Nat.zero`
witnesses then specialize the fourth recursor layer by genuine semantic Pi
instantiation. `natZeroRegisteredRuleTypeSemanticWitness` observes the exact
generated zero-rule type at the sparse prefix, and
`natZeroRegisteredRecursorRuleViewElim` packages that witness with the same
literal recursor match, nullary constructor match, registered trace, and
three capture/domain alignments. Its pinned closure contains only the
logical baseline and the exact recursor-type, Nat-type, and generated
zero-rule metadata decisions; in particular it contains no `sorryAx`.

The arbitrary semantic application levels in that trace are no longer an
alignment blocker. `natZeroShapeSpine_relevelDirect` raises all three
semantic layers and their exact captures to one common consecutive level
`k`; it does not project an arbitrary higher refinement downward. The lifted
`FourView.sparsePrefix` is then exactly the producer tower, so
`natZeroIotaRHSDefEq_of_registeredView` builds the fixed-head producer from
the retained semantic rule-type witness, invokes recursive self-adequacy, and
lowers the resulting guarded equality back to the caller's original result
shape. `natZeroIotaDefEq_of_registeredCtorExactAt_selfAdequate` closes the
complete exact registered zero leaf with neither an alignment callback nor an
assumed final RHS relation. Its axiom guard contains only the logical baseline
and the already audited closed Nat metadata decisions.

The full registered zero major-link callback is now closed as well.
`DirectCtorArgsDefEqListed.left`/`.right` retain all five registered lists for
the two rectangle rows, while `SpineWF.LastPair.fullXAt`/`.fullYAt` rebuild a
recursor spine at any framed native endpoint through a heterogeneous
codomain path. `LRD.iotaDefEq_of_exactListedDataAt` then consumes the raw
normalized constructor certificates without requiring the frame's ambient
logical relation. For `Nat.zero`, `CtorFrame.shape_ctor` preserves the
nullary arity, so every framed leaf has no fields and all three edges close
from the same registered view. Consequently
`natZeroRegisteredIotaMajorLinkStepAt_of_selfAdequate` proves the complete
`NatZeroRegisteredIotaMajorLinkStepAt`, and
`natRegisteredIotaMajorLinkStepAt_of_zeroSelfAdequate` installs it in the Nat
dispatcher.

The registered successor branch is now closed up to one named strict
recursive obligation.  The generic direct-listed materializer and action
consumer retain all five constructor-field lists (left/right syntax, raw
types, element shapes, and type shapes) alongside both guarded relations.
`NatSuccPredArgCoherent` packages the unique predecessor at the registered
root field with its exact direct capture and semantic Nat-type witness, while
`NatSuccFramedPredStep` states precisely the remaining transport from a
framed native unary field to that package.  Given this producer,
`natSuccRegisteredIotaMajorLinkStepAt_of_selfAdequate` normalizes every
framed successor leaf, reuses the one proof-relevant predecessor payload for
all three rectangle edges, and closes the generated RHS through recursive
self-adequacy.  `natRegisteredIotaMajorLinkStepAt_of_selfAdequate` combines
the derived zero and successor branches.  This is not yet the concrete T3
leaf: `NatSuccFramedPredStep` must still be produced by the genuine strict
coherent predecessor branch rather than assumed, after which the concrete
`LRD.CoherentTypedIotaLeafStep []` induction remains.

The generic strict-depth retained-typing half is also closed.
`Valuation.Fits.toFitsRDeep` rebuilds an exact child tree at every binding of
an existing valid valuation;
`Valuation.Fits.toCoherentProvenanceFitsRDeep` specializes those trees to the
transportable coherent provenance; and
`LE_Interp.Witness.typedRDeep_of_stratifiedRestart` uses one genuine strict
predecessor rung to type an exact witness together with its registered type
witness and both retained trees.  This strict restart is not the Nat leaf's
universal route.  `HasTypeStratifiedS.weak'` now preserves an exact depth
through certified context embeddings, and the syntax-directed
`lam_inv`/`const_inv` plus the four depth-positivity eliminators make the
literal accounting checkable.  That accounting separates the two native
branches: the zero RHS may share the enclosing constant rung, but
`probeNatSuccRuleRhs_depth_lower_bound` proves that every typing of the
literal successor RHS has depth at least `14`, because its body contains the
explicit recursive recursor call.  Thus the successor cannot universally be
forced into a minimal same-rung local certificate; its selected edge must
retain genuine all-depth provenance or be consumed structurally.  In either
case `LRD.CoherentSeedAt.nativeOrLocal` now exposes the distinction without
changing witnesses or dropping guarded coherence: the genuine branch is
paired with a native-depth typing certificate, while the rebuilt branch
remains visibly local.  The legacy eliminator remains for legacy consumers.
`natSuccDirectIotaRule_rhs_depth_lower_bound` carries the same result through
the literal generated descriptor used by the guarded leaf, so downstream
code no longer has to unfold or re-identify the selected successor rule to
invoke the bound.
`typedRDeepTrue_of_strong` independently supplies the exact registered type
witness at a native depth. The registered zero leaf now aligns that
observation with its dominance spine by upward releveling; the successor
branch still needs its corresponding structural treatment. No
witness-from-`HasType` shortcut is introduced.

The fixed T2 zero computation now also has a fully typed structural
certificate. `TypedWHRedS.app` preserves a path-typed weak-head edge under a
fixed well-typed argument.  The falsification harness directly types the
literal motive, zero minor, and successor minor (including both motive beta
edges), reconstructs the generated rule's three binder-validity facts from
Nat syntax, and composes its three actual beta contractions in
`zeroT2GeneratedApplication_typedBeta`.  The resulting edge starts at the
real registered generated RHS application, ends at the selected zero minor,
and stays at the unreduced dependent `zeroT2ResultType`.  A trust audit
rejected the broader `zeroRuleTypeStrong` route because its semantic
registered-RHS producer imported `sorryAx`; the landed proof instead has only
the standard logical closure plus the three closed Nat metadata decisions for
the Nat type, successor constructor type, and zero-rule RHS.

The fixed zero probe now crosses the registered redex boundary as well.
`zeroT2RuleTypeStrong` rebuilds the complete literal rule telescope without
the broad registered-RHS lookup; `zeroT2RegisteredDefEq` types the generated
LHS body from that certificate, performs its three concrete beta steps, and
composes them with the primitive registered head equality.
`zeroT2Registered_typedWHRedS` packages the literal successful match and its
empty check inventory as the actual typed iota edge.  Finally,
`zeroT2Redex_directSelf` transports the informative generated-RHS relation
backward along that edge on both sides.  All four new roots have pinned
closures containing only the logical baseline and their exact Nat
`native_decide` fixture equalities—neither `sorryAx` nor persistent-map
axioms occur.  This closes the zero half of T2.

The successor half of T2 is now closed at the equally explicit major
`Nat.succ Nat.zero`.  `succT2RuleTypeStrong` reconstructs the literal
five-field successor-rule telescope, and `succT2RegisteredDefEq` validates the
registered four-capture action through four generated-LHS beta steps and the
primitive registered head equality.  On the output side,
`succT2GeneratedApplication_typedBeta` performs the four outer generated-RHS
beta steps while retaining the recursive `Nat.rec` call; that call is typed
from the zero certificate and `natRecStrongOfZeroRuleType`.  Two further
minor-function beta steps reach the concrete contractum.  The literal match,
empty check inventory, dynamic result-type transport, and informative
non-bottom observations are combined in `succT2Redex_directSelf`.  Its pinned
closure contains only the logical baseline and the exact Nat metadata
decisions—again neither `sorryAx` nor persistent-map axioms.  Thus both fixed
informative redexes required by T2 are now landed.

The syntax-and-provenance half of T3 is now landed as well.  The generic
weak-to-strong bridge was rejected because its concrete Nat closure imported
`sorryAx` and persistent-map axioms.  Instead,
`zeroT2RecursorPrefixStrong` structurally rebuilds the dependent recursor
type and application spine; `zeroT2RedexStrong` and `succT2RedexStrong` then
type the two literal redexes directly.  Their `.stratify` results are exposed
as `zeroT2RedexStratified` and `succT2RedexStratified`, while
`succT2StrictDepths` inverts the latter to obtain the actual constructor
major and literal predecessor with
`predDepth < majorDepth < redexDepth`, without monotonicity padding.  Exact
axiom guards contain only the logical baseline and the three Nat metadata
decisions.  What remains of T3 is the complete induction through a concrete
`LRD.CoherentTypedIotaLeafStep []` (equivalently, the missing coherent Nat
typed-iota leaf algebra), not construction of the strong derivations or their
strict depth evidence.

The complete guarded syntax induction is also assembled additively.
`LRD.CoherentRetainedAt` keeps the established coherent package literally and
adds `LRD.SelfAdequateAt`; named direct conversion and constant callbacks,
the sanctioned strict-depth restart, and `LRD.selfAdequateAtStep` construct
every nonconstant syntax case. Lambda and Pi consume the exact same-root
legacy result as a separate input, preserving the quantifier distinction
between arbitrary `SubstWF` and `DirectSubstWF`. Finally,
`LRD.coherentRetainedResult_of_steps` combines a completed legacy coherent
algebra with those two direct callbacks through semantic-first recursion and
Nat-second strict restarts. Its evaluator children now carry
`LRD.CoherentSeedAt` and therefore preserve all-depth guarded results;
arbitrary witness rebuilds receive only the exact local rung. The closure is
implemented by `recRDeepNatProvenance`, not by rebuilding an unchanged legacy
seed tree.

The conversion callback is no longer opaque. `LRD.adequateDefeq` converts a
guarded term through a heterogeneous guarded type-adequacy edge, and
`LRD.SelfAdequateDefeqStepAt.of_lowerAdequacy` supplies that edge strictly
from `LRD.ContextualAdequacyAtDepth` below the current syntax rung. This uses
the retained direct substitution throughout and invokes neither inversion
nor path collapse.

The direct constant callback is now structurally complete for environments
with no zero-argument registered pattern. `LRD.CoherentTypedIotaLeafStep`
additionally exposes the exact constant registration, universe arity, and
registered type certificate at the leaf, while `CoherentIotaLeafStep.toTyped`
keeps the original interface available.  Accordingly,
`LRD.SelfAdequateConstStep.of_noConstPat_typed` is the evidence-preserving
implementation and `of_noConstPat` is its compatibility wrapper; both retain
the ambient direct substitution and full strict predecessors while leaving
the evaluator seeds unchanged.  The Nat adapters
`natSelfAdequateConstStep_of_typedLeaf` and
`natSelfAdequateConstStep_of_leaf` instantiate the two interfaces with
`natPat_no_const`, so Nat inherits no delta-rank premise.

Remaining M1/M2 work is therefore localized to the guarded Nat coherent leaf
and its branch-sensitive provenance/alignment. For zero, the selected
registered-type witness and all three literal capture/domain relations are
now synchronized; the remaining obligation is to turn that package into the
`DirectFixedHeadDominanceSpine` required by the zero self-adequate RHS
producer, including the explicit comparison from its singleton capture
telescope to the selected semantic rule-type observation. Shared
non-bottomness and two `HasType` derivations still cannot supply this
comparison. The successor branch must additionally build its rule-tower
observation under the predecessor binder, preserve or structurally consume
the RHS's all-depth recursive provenance, and obtain the exact predecessor
upgrade from the strictly smaller constructor-field branch. Both native
leaves must then be threaded through the named fixed-site per-link/frame
callback. The later D0 extension must additionally add the guarded delta-rank
branch. After that come contextual-adequacy closure. The exact Pi and lambda
constructors deliberately take ordinary adequacy as an explicit premise for
their additive first projection: guarded adequacy ranges only over
`DirectSubstWF`, so it cannot truthfully be erased to legacy adequacy, which
ranges over every `SubstWF`. The assembled fundamental induction supplies
both projections rather than hiding this quantifier mismatch behind a
conversion theorem. A global callback that manufactures typed root paths
would merely rename subject reduction and remains forbidden.

M1 is killed and redesigned if constructing a root path requires
`PiPathInv`, the target subject-reduction theorem, or a homogeneous equality
between potentially different universe levels. That would merely move the
cycle into a record field.

#### FALSIFY — mandatory NORM-DI truth-status checkpoint

**Status (2026-08-24): active before further M2a generalization.**  The direct
route has reached the point where additional abstraction work is expensive
enough that failure to close a theorem must be separated from failure of the
theorem itself.  This checkpoint tries to refute the smallest concrete claims
first.  It is not a competing normalization route and it is not evidence for
soundness merely because a finite collection of probes survives.

The checkpoint distinguishes six materially different failure modes:

| ID | Candidate explanation | What would distinguish it |
|---|---|---|
| **H-ARCH** | The guarded relation is sound, but its semantic-level, syntax-depth, context, or substitution indices are packaged in the wrong induction unit | the exact Nat redex theorems close, while the first quantified generalization fails at a reproducible binder or predecessor boundary |
| **H-LOCAL** | A producer or intermediate `Prop` is stronger than its consumer needs, or is outright false | an inhabited adversarial shape refutes the producer while the concrete redex conclusion remains provable through a weaker datum |
| **H-ADM** | `Params`, `Params.Semantic`, `VEnv.Ordered`, or `VEnv.WF` lacks an admissibility/coherence condition needed for the advertised theorem | a small inhabitant of the current assumptions exhibits an eta/iota, structure/iota, universe, or registered-equation counterexample |
| **H-MODEL** | The Theory equality or environment rules admit a well-formed equality that destroys sort/Pi discrimination or same-head injectivity | a concrete `VEnv.WF` derivation refutes one of the desired inversion conclusions without using an admitted theorem |
| **H-REFINE** | Theory may be internally coherent, but the executable checker or its translation accepts behavior not justified by Theory or not accepted by Lean's kernel | a differential fixture produces an accepted/rejected or translated/untranslated mismatch at a pinned phase |
| **H-TRUST** | Apparent progress reaches `sorryAx`, a project bridge, a compiler-decision axiom used semantically, or a legacy inversion producer | exact transitive axiom or dependency output exposes the forbidden leaf |

The current prior is **H-ARCH first, H-LOCAL/H-ADM second, H-MODEL and
H-REFINE lower but release-blocking, and H-TRUST mechanically testable**.  The
ordering controls investigation cost only; it is not a conclusion.  Any
counterexample overrides it immediately.

##### Scope and hard rules

The checkpoint covers the current direct Nat route, the assumptions under
which it is meant to generalize, and the narrow checker/model boundary capable
of invalidating its intended use.  It does not attempt full normalization,
global consistency of Lean, or exhaustive model checking.

1. Every truth-status probe is additive.  Do not weaken `IsDefEq`,
   `IsDefEqStrong`, `LR`, `LRD`, `Params.Semantic`, `VEnv.Ordered`, or `VEnv.WF`
   in order to make a probe pass.
2. No positive probe may use `sorry`, a new `axiom`, the public sorried
   Injectivity declarations, `SortEdgeData`, `BetaFire`, `PiPathInv`,
   `MajorLinkRect`, or an adapter whose dependency closure reaches them.
3. `native_decide` is permitted only for closed finite metadata facts such as
   generated-rule lookup, descriptor equality, or list disjointness.  It may
   not decide a semantic adequacy, typing, conversion, or soundness claim.
4. A theorem with an impossible premise is not positive evidence.  Every new
   proposition used as a certificate must receive both an inhabitant at the
   intended concrete site and an adversarial bottom/shape test.
5. The zero and successor probes must select the real generated rules, use
   their literal capture inventories and fixed bodies, and expose an
   informative result observation.  A `.bot`-only proof, empty-pattern path,
   or premise containing the final RHS relation fails the probe.
6. The successor probe must consume the predecessor relation from a strictly
   smaller constructor-field branch.  Supplying it as an unconstrained
   callback, same-depth hypothesis, normalization theorem, or exported
   inversion result fails the probe.
7. A failed proof search is not a counterexample.  A negative result must be
   a checked derivation of `Not P`, an explicit inhabitant whose required
   conclusion reduces to `False`, a kernel differential mismatch, or a
   signature/axiom dependency that violates a stated gate.
8. Do not repair a refuted statement in place until its smallest
   counterexample and the exact consumer requirement are recorded.  The
   repaired interface must be strictly weaker or carry strictly more local
   evidence in a way the counterexample cannot inhabit.

##### Evidence ladder

The campaign proceeds through the following increasingly quantified claims.
The first failing edge is the primary localization result; do not skip a rung
by proving a stronger conditional theorem.

| Rung | Claim | Current state | Required evidence |
|---|---|---|---|
| **T0 — local computation** | Exact beta and the selected Nat zero/successor contractions are locally typed and path-typed | landed | the existing `TypedWHRedS.beta`, registered actions, exact multi-beta paths, and their standard axiom closures |
| **T1 — generated RHS** | Each concrete generated Nat RHS preserves the guarded relation from exactly its live captures | landed | zero/successor `LRD.IotaRHSDefEq` contracts; successor exposes exactly one predecessor upgrade; neither accepts its conclusion |
| **T2 — exact redex** | One explicit zero redex and one explicit successor redex are self-adequate at an informative fixed shape at shape level one in the empty target context | landed | `zeroT2Redex_directSelf` and `succT2Redex_directSelf` are premise-free guarded self-relations with pinned no-`sorryAx` closures; `succT2Shapes_nonbottom` records the successor witness's nonvacuity |
| **T3 — exact derivation** | The complete self-adequacy induction handles the exact strong derivations of those two redexes at their actual stratification depths | zero framed branch and conditional successor framed branch landed; strict predecessor producer/coherent induction open | `zeroT2RedexStrong`, `succT2RedexStrong`, their concrete stratifications, and `succT2StrictDepths` provide clean exact derivations; `natZeroRegisteredIotaMajorLinkStepAt_of_selfAdequate` closes every framed zero link, while `natSuccRegisteredIotaMajorLinkStepAt_of_selfAdequate` closes every framed successor link from the exact residual `NatSuccFramedPredStep`; `natRegisteredIotaMajorLinkStepAt_of_selfAdequate` combines them, but T3 still requires deriving that producer from the genuine strict coherent predecessor and then constructing `LRD.CoherentTypedIotaLeafStep []` |
| **T4 — shape polymorphism** | T3 survives arbitrary caller-selected semantic levels and observations satisfying the actual typing relation | open | a theorem quantifying over shapes but still fixed to empty target context and identity direct substitution |
| **T5 — direct substitutions** | T4 survives every `LR.DirectSubstWF` in a fixed well-formed target context | open | the exact direct-substitution theorem; no erasure to legacy `SubstWF` is claimed |
| **T6 — contextual level one** | Guarded Nat adequacy holds uniformly over well-formed target contexts at shape level one, while quantifying over the stratification depths supplied by the derivations | open | the intended direct `natContextualAdequacyAtOne` or its exact accepted spelling |
| **T7 — inversion extraction** | Nat contextual adequacy yields path-valued sort/Pi inversion and the direct Nat `PiPathInv` consequence | open | premise-free `natPiPathInvDirect` and nonvacuous sort/Pi witnesses |

T0 and T1 are prerequisites, not substitutes for T2.  T6 is not claimed from
an unguarded adequacy theorem: `LRD.Adequate` ranges over
`DirectSubstWF`, whereas legacy adequacy ranges over all `SubstWF`.  Any proof
that silently erases this quantifier difference is rejected.

##### F0 — freeze the question and the trust baseline

Before attempting another producer, record one working-copy snapshot and the
exact signatures of the claims being tested.

1. Record the revision/snapshot, dirty-file inventory, focused build counts,
   and current direct-route diff.  The record must make clear whether it is a
   published Git checkpoint or only a working-copy snapshot.
2. Pin `#check @...`, `#print ...`, and `#print axioms ...` for:
   `TypedWHRedS.beta`, `LRD.constDefEq`, `LRD.constDefEqRootLam`,
   `LRD.iotaDefEq_of_ctorExactAt`, both native Nat exact leaves,
   `natSelfAdequateConstStep_of_leaf`, `LRD.CoherentIotaLeafStep`, and the
   strongest assembled self-adequacy theorem.
3. Record the exact missing names `natContextualAdequacyAtOne` and
   `natPiPathInvDirect`; an older conditional theorem with a similar result
   does not count.
4. Pin negative dependency scans over each direct theorem body for
   `WHRedS.defeq_of_piPathInv`, `SortEdgeData`, `BetaFire`, `PiPathInv`, and
   `MajorLinkRect`.  Legacy comparison sections may retain those names, but no
   direct root may reach them transitively.
5. Create machine-checked probes in one additive Experimental module until
   their truth status is decided.  Small negative artifacts may live under
   `plans/probes/`, but roadmap status remains here and the probe must be
   imported by an explicit focused build target while active.

F0 exits with a reproducible baseline and no semantic changes.  If an alleged
direct endpoint already reaches an admitted or legacy producer, classify the
result as H-TRUST and repair the dependency before any truth-status inference.

##### F1 — close or refute the two smallest concrete Nat redexes

Build zero first and successor second.  Each probe fixes `natParams`,
`natSemantic`, the empty target context, a nil valuation or another explicit
valuation justified by the syntax, identity direct substitution, the literal
generated rule, and an informative shape chosen before proof search.

For the zero probe:

1. Write the exact `Nat.rec`/`Nat.zero` redex and its generated contractum;
   prove they are syntactically distinct so reflexivity cannot close the
   advertised reduction path.
2. Construct its ordinary and strong typing derivations, extract the concrete
   inhabited `HasTypeStratifiedS` depth supplied by `IsDefEqStrong.stratify`,
   and record that depth rather than forcing it to one.
3. Exhibit the recursor-prefix captures at their literal paths and prove the
   selected descriptor is `natZeroDirectIotaRule`, not merely an existential
   registered pattern.
4. Choose a non-bottom semantic observation that forces the fixed-head and
   generated-RHS branches to run.  Prove its `LE_Interp` and `HasType`
   hypotheses directly.
5. Invoke the existing zero native exact leaf and close the full redex-level
   guarded relation without a leaf callback or a premise equal to the goal.

For the successor probe:

1. Write the exact `Nat.rec`/`Nat.succ pred` redex and generated recursive
   contractum, again proving syntactic nonidentity.
2. Materialize all four literal captures and show the only constructor-field
   capture is the predecessor.
3. Build the predecessor's guarded term upgrade from a genuinely strict
   predecessor branch at the witness's exact element/type shapes.  Do not
   assume that predecessor has depth zero, and do not reselect those shapes
   existentially after the native leaf has fixed them.
4. Show the recursive-result relation is produced by semantic evaluation of
   the fixed RHS body, rather than assumed as an input or obtained from global
   normalization.
5. Invoke the successor native exact leaf and close the full redex-level
   guarded relation at the same informative result observation as its typing
   witness.

Each probe must additionally have a companion nonvacuity theorem exposing:

- the concrete `Ctx.WF []` and direct identity substitution;
- the selected zero/successor descriptor and successful match;
- the informative, non-bottom term and type observations;
- the actual registered contraction edge; and
- for successor, use of the predecessor upgrade in the final RHS relation.

If zero fails, stop before successor and minimize the failure.  If zero passes
but successor fails, reduce the gap in this order: predecessor exact-shape
upgrade, recursive fixed-body application, strict-depth availability, then
path conversion.  Do not generalize any of those pieces until the concrete
failure is classified.

##### F2 — adversarial vacuity and shape probes

Every producer used by F1 is attacked using the same patterns that refuted
the earlier terminal-link and exact-retarget interfaces.

| Probe | Construction | Failure detected |
|---|---|---|
| **bottom witness** | instantiate every universally quantified semantic observation with `LE_Interp.Witness.bot` where permitted | a supposed result law forces a non-bottom output below bottom |
| **two sort bits** | type the same bottom observation at `TShape.sort true` and `TShape.sort false` | hidden `TShape.HasType` functionality or illicit exact retargeting |
| **heterogeneous universes** | compose a `TypeDefEqPath` whose adjacent edges retain different universe witnesses | homogeneous path collapse or universe equality smuggled into conversion |
| **shape lift/lower** | run the same concrete term at its originating level and at one lifted level, then compare only through the proved lift equivalence | projection from an arbitrary higher refinement or loss of the strict predecessor index |
| **pattern nonselection** | instantiate a nonmatching constructor, wrong arity, or wrong recursor head | a leaf that closes through empty pattern evidence or ignores the selected descriptor |
| **unused predecessor** | replace the successor predecessor payload by an otherwise inhabited bottom relation | a successor certificate whose advertised recursive dependency is semantically dead |
| **goal-as-field** | normalize every record/callback signature and compare it with the final adequacy conclusion | a certificate that simply assumes the theorem under a renamed field |

For each new `Prop P`, provide one of:

- a concrete inhabitant at the intended Nat site plus a negative theorem for
  the adversarial instance;
- a proof that the adversarial instance cannot satisfy a documented premise;
  or
- a checked refutation of `P`, followed by removal or replacement of `P`.

F2 exits only when bottom cannot make a positive probe vacuous, informative
shape distinctions survive, and every exact retarget is justified by local
data rather than type-shape functionality.

##### F3 — slice the quantifiers and locate the first false generalization

After F1, generalize one axis at a time.  Maintain an explicit theorem matrix
rather than editing one large theorem repeatedly.

1. **Term axis:** fixed zero redex, then fixed successor redex, then either
   concrete Nat redex.
2. **Shape axis:** one informative witness, all observations at its semantic
   level, then all levels via the proved originating-shape lift equivalence.
3. **Substitution axis:** identity direct substitution, closed direct
   substitutions, arbitrary `DirectSubstWF`.
4. **Target-context axis:** `[]`, one explicit well-formed binder, arbitrary
   `Ctx.WF Γ₀`.
5. **Source-context axis:** closed redex, literal generated telescope context,
   arbitrary source context admitted by the exact strong derivation.
6. **Derivation axis:** the explicit self-typing derivation, all constructors
   used by the Nat redex, then arbitrary `IsDefEqStrong` at the fixed depth.
7. **Depth axis:** constructor-specific base leaves, the actual depths
   extracted from the Nat derivations, then the strict predecessor family
   needed by the contextual bootstrap.

At every edge record the newly introduced quantifier and the exact missing
datum.  The accepted repair depends on the first failing edge:

- shape failure means `LRD` has the wrong level variance or lift law;
- substitution failure means `DirectSubstWF` or its binder extension loses a
  proof-relevant action;
- target-context failure means contextual closure or weakening is missing;
- source-context failure means the generated rule certificate is not stable
  under its actual telescope;
- derivation failure means a constructor of `IsDefEqStrong` lacks a direct
  semantic clause;
- depth failure means the bootstrap induction unit is wrong or the requested
  same-depth fact is false.

No edge is repaired with a global callback.  The datum must be produced at
the edge where it is lost, or the theorem must retain the smaller
quantification under which it is true.

##### F4 — test the generic environment assumptions with hostile instances

The concrete Nat instance can be sound even if the generic theorem is false.
Test three boundaries separately:

1. `[Params]` with only its syntactic pattern uniqueness/well-formedness
   laws;
2. `[Params] [Params.Semantic]`, including proof-carrying local actions and
   registered strong equalities; and
3. instances actually produced from `natSemantic`, `d0Semantic`, or a
   `VEnv.WF` declaration history.

Attempt the following smallest hostile constructions at each boundary:

- an eta-sensitive rule schematically equivalent to
  `drop ctor ↦ zero`, where `fun x => ctor x` is definitionally eta-equal to
  the matched argument but is not syntactically matched;
- coexistence of registered structure eta with an iota rule whose matching
  behavior changes across the structure expansion;
- a registered equation at a universe-valued type whose endpoints expose
  different sort/Pi heads;
- two applications of the same classified inductive head with different
  universe or parameter arguments but a derivable untyped equality;
- a rule whose universe list is merely semantically equivalent where a
  consumer incorrectly demands literal list equality; and
- overlapping or extension-added rules that satisfy local lookup facts but
  invalidate a global uniqueness or join claim.

For eta/iota, distinguish three propositions explicitly:

1. the two branches are definitionally equal because they share a source;
2. the operational reduction relation has a common reduct; and
3. the checker algorithm returns the same result on both presentations.

Failure of (2) is a Church–Rosser/interface defect, not by itself a proof of
logical inconsistency.  Failure of sort/Pi discrimination or same-head
injectivity under a concrete `VEnv.WF` is a direct NORM-DI soundness blocker.

Interpret hostile-instance results as follows:

- a counterexample under `[Params]` that cannot inhabit `Params.Semantic`
  narrows the generic theorem's required premise but does not refute the
  concrete Nat route;
- a counterexample under `Params.Semantic` requires strengthening or scoping
  that interface before M3 extraction;
- a counterexample under `natSemantic`/`d0Semantic` refutes M2 as stated;
- a counterexample from an actual `VEnv.WF` history is H-MODEL and stops all
  downstream injectivity work until the environment/equality rules are fixed.

F4 must also classify the already known eta/registered-rule critical pair in
the direct route.  Either prove that real generated Nat rules exclude it by a
specific saturation/match-stability fact, or carry a named admissibility
certificate into the eventual M3 interface.  Do not assume global confluence
to discharge this classification.

##### F5 — attack the core inversion conclusions directly

Search for counterexamples before using adequacy to prove the public results.
The probes must avoid the sorried declarations in
`Theory/Typing/Injectivity.lean`.

1. Try to construct `VEnv.WF env`, `OnCtx Γ (env.IsType U)`, and
   `env.IsDefEqU U Γ (.sort u) (.forallE A B)`.
2. Try to equate two sorts whose levels are not semantically equivalent.
3. Try to equate two Pi types while making either their domains or codomains
   nonconvertible in the required context.
4. Try to equate two applications of the same Nat/inductive/Quot head while
   choosing distinguishable universe, carrier, parameter, index, or relation
   arguments.
5. Repeat the search first in a hand-built minimal Theory environment, then
   in the concrete Nat/D0 generated environments, and finally through an
   executable-checker-produced environment certificate.

Use constructors of `IsDefEq` and `IsDefEqStrong` to enumerate the possible
last steps for the smallest syntax sizes.  The search need not be globally
decidable: bounded enumeration is useful only to produce a concrete witness
or to identify the first constructor whose invariant is not represented.
Surviving a bound is not a proof and must be reported as such.

If a candidate counterexample uses `extra`, expand it through
`Params.Semantic.registered` and the exact `Pattern.Action`.  If it uses
`defeqDF`, retain the full heterogeneous type path rather than assuming the
endpoint universes agree.  If it uses transitivity, show every intermediate
type and registered rule explicitly; do not collapse the chain into an
uninspectable existential.

##### F6 — run targeted Theory/checker/kernel differentials

Internal consistency is distinct from faithfulness to Lean.  Extend the
existing differential harness only with cases that distinguish a live
falsification hypothesis:

- eta-expanded versus syntactically matched recursor arguments;
- structure expansion immediately adjacent to registered iota reduction;
- universe-equivalent but syntactically different level lists;
- a recursive Nat successor contractum requiring the predecessor and
  recursive result at their dependent types;
- malformed recursor universes, major arity, computed indices, or constructor
  fields near the accepted boundary; and
- the smallest same-head application whose parameter equality is exactly the
  future `IndTyAppInj` conclusion.

For each case record four results independently: Lean source elaboration,
Lean kernel acceptance, executable Lean4Lean phase/result, and Theory replay.
An expected rejection must identify the same semantic reason, not merely fail
at any earlier parser or lookup phase.  An acceptance mismatch or a successful
checker result with no Theory certificate is H-REFINE and blocks release work
even if the direct logical relation remains internally consistent.

F6 does not require exhaustive fuzzing.  If randomized generation is later
used, every retained failure must be minimized to a deterministic source and
raw declaration fixture before it affects the roadmap decision.

##### F7 — trust, dependency, and reproducibility audit

Every surviving positive root receives:

- a pinned full signature and transitive `#print axioms` result;
- a source and compiled-environment check for `sorryAx`;
- a negative dependency scan for the legacy inversion/normalization
  producers;
- a note identifying each compiler-decision leaf and the closed finite fact
  it proves;
- a nonvacuity theorem for its principal hypothesis; and
- a focused build command reproducible from the recorded snapshot.

The minimum focused commands are:

```text
nix develop --command lake build Lean4Lean.Experimental.SExprParamsD0
nix develop --command lake build Lean4Lean.Experimental.ShapeLogRelAdequacy
```

A truth-status decision that changes the NORM-DI interface or permits M2a to
resume additionally runs the full Experimental gate.  A result touching
Theory rules, `VEnv.WF`, checker refinement, or a release assumption runs the
complete Section 8 checkpoint gate and the relevant kernel differentials.
`git diff --check` is required for every retained probe change.

##### Decision matrix and required response

| Finding | Classification | Required action |
|---|---|---|
| Exact zero or successor target has a checked counterexample | M2 false as stated | stop M2; retain the minimized witness; identify whether the equality rule, guarded semantics, or target conclusion must change |
| Concrete redexes pass, but a candidate producer is refuted | H-LOCAL | delete or quarantine the producer; replace it with local data or a weaker comparison; rerun F1/F2 before generalizing |
| First failure is shape, substitution, context, derivation, or depth generalization | H-ARCH | keep the last true rung as the specification; redesign only the failing induction unit; do not broaden assumptions |
| Hostile `[Params]` instance fails, but `Params.Semantic` excludes it | syntactic interface intentionally weak | require `Params.Semantic` at the theorem boundary and document the exclusion; concrete M2 may continue |
| Hostile `Params.Semantic` instance refutes the target | H-ADM | strengthen the semantic interface with the smallest witnessed admissibility fact, then reconstruct Nat/D0 instances |
| Concrete `VEnv.WF` breaks sort/Pi discrimination or head injectivity | H-MODEL | declare a soundness blocker; stop downstream REC/D2/Quot use; minimize and repair Theory/environment rules before proof search |
| Checker/kernel/Theory differential disagrees | H-REFINE | declare a release blocker; fix the accepting phase or translation and preserve the differential as a permanent regression |
| Positive theorem reaches an admission, bridge, compiler semantic oracle, or legacy producer | H-TRUST | revoke the positive result; remove the dependency or classify it explicitly before reconsidering the theorem |
| T0–T6 survive with clean trust and nonvacuity evidence | falsification checkpoint passes | resume M2 extraction at T7; this raises confidence but is not a consistency proof |

##### Exit report

This checkpoint is complete only when the roadmap records one of two outcomes:

1. **Refuted:** a minimized, machine-checked counterexample; the first false
   evidence-ladder rung; its classification; affected public claims; and the
   redesign or scope reduction required before work resumes.
2. **Survived:** premise-free informative zero and successor redex theorems;
   the first six evidence rungs through contextual shape-level-one adequacy; hostile
   instance and eta/registered-rule classifications; clean trust/dependency
   results; and the exact revision on which the focused and required broader
   gates passed.

An inconclusive proof search is neither outcome.  If a rung remains open, the
report names its smallest signature, its inhabited hypotheses, the exact
missing datum, and which falsification attempt ruled out each obvious
counterexample.  M2a remains open until the rung is proved or refuted.

##### Active falsification result — 2026-08-24 working-copy snapshot

This is an interim localization result, not either FALSIFY exit outcome.  It
is pinned to Git `03681c3a2dd9607b645990f956961847b1745f22` plus the live dirty
working copy; concurrent M2 edits mean the source hashes and line numbers are
time-sensitive.  The additive harness is
`Lean4Lean.Experimental.SExprFalsification` and is not imported by the
production route.

1. **F0 trust scan:** the direct beta/iota/constant roots and the four Nat
   native/self leaves have no source dependency on
   `WHRedS.defeq_of_piPathInv`, `SortEdgeData`, `BetaFire`, `PiPathInv`, or
   the exact legacy `LR.MajorLinkRect`.  Their recorded axiom closures are the
   standard logical closure; the Nat leaves additionally use only the three
   permitted closed metadata decisions for generated zero lookup, successor
   lookup, and RHS disjointness.  This does not yet establish end-to-end
   trust: `LRD.coherentRetainedResult_of_steps` still takes an opaque
   `LR.CoherentRetainedNatStep`, for which no concrete Nat producer exists,
   and the direct endpoint names `natContextualAdequacyAtOne` and
   `natPiPathInvDirect` remain absent.
2. **Concrete zero syntax survives:** the harness fixes
   `natZeroDirectIotaRule`, its real generated body, and its three literal
   captures; proves the redex differs syntactically from its contractum;
   exposes both the registered contraction and generated multi-beta path;
   constructs the RHS strong self-typing from `natSemantic`; proves the rule
   type premise is inhabited; constructs the literal redex's strong
   self-typing; and extracts its actual `HasTypeStratifiedS` depth.  This
   closes the zero syntax/nonvacuity half of F1 and prevents the older
   `hRuleType` premise from hiding an empty theorem.
3. **The T2 observation is now fixed before proof search:** use object levels
   `u0 = 0`, `u1 = 1`, and `u2 = 2`; motive
   `fun _ : Nat => Sort u1`; zero minor `Sort u0`; constant successor minor;
   and major `Nat.zero`.  The term observation is `WShape.sort false` and its
   type observation is `WShape.sort true`, both literally at shape level one.
   The harness records their typing, non-bottomness, interpretation of the
   reduced endpoints, and the locally path-typed dynamic beta contraction
   `motive Nat.zero` to `Sort u1`.  A Nat-valued motive is deliberately
   rejected as the smallest probe because its body action would occur at
   shape level zero, which cannot display an inductive-type observation.
4. **Both native T2 leaves landed:** the complete concrete zero generated-RHS
   tower is packaged by `zeroT2GeneratedApplication_typedBeta`: three typed
   beta edges under fixed applications, all at the literal unreduced result
   type and with a pinned no-`sorryAx` closure.  The first attempt to connect
   the actual redex through `natZeroRuleActionSound` was rejected because its
   environment reconstruction imported `sorryAx` and persistent-map axioms.
   The accepted route reconstructs the literal telescope in
   `zeroT2RuleTypeStrong`, types and beta-collapses the generated LHS locally
   in `zeroT2RegisteredDefEq`, packages the exact match as
   `zeroT2Registered_typedWHRedS`, and transports the guarded generated-RHS
   relation to the redex in `zeroT2Redex_directSelf`.  Exact axiom guards rule
   out both rejected dependency classes.  Thus the formerly global
   `LRD.FixedHeadConvertStep []` blocker is not needed for this closed zero
   witness.  The successor witness uses major `Nat.succ Nat.zero` and does not
   copy the zero proof: `succT2RuleTypeStrong` reconstructs its five-field
   telescope, `succT2RegisteredDefEq` validates all four captured arguments,
   and `succT2GeneratedApplication_typedBeta` preserves the recursive call
   through four outer beta steps before two minor-function beta steps reach the
   contractum.  The recursive application is typed from the zero certificate
   and `natRecStrongOfZeroRuleType`; `succT2Registered_typedWHRedS` packages the
   exact match, and `succT2Redex_directSelf` supplies the premise-free
   informative result.  Its exact guard is likewise free of `sorryAx` and
   persistent-map axioms.  T2 is therefore complete.
5. **T3 syntax/provenance landed:** `zeroT2RecursorPrefixStrong` rebuilds the
   dependent recursor spine without the trust-unclean generic bridge;
   `zeroT2RedexStrong` and `succT2RedexStrong` give the two concrete strong
   derivations, and their stratified forms expose real existential depths.
   `succT2StrictDepths` extracts the literal predecessor below its constructor
   major below the redex, with both inequalities strict and no monotonicity
   padding.  Their exact guards contain neither `sorryAx` nor persistent-map
   axioms. The exact registered zero leaf is now closed by
   `natZeroIotaDefEq_of_registeredCtorExactAt_selfAdequate`: its listed trace
   readbacks, common-level releveling, semantic rule-type witness, and
   recursive self-adequacy construct the result without `makeAlignment` or a
   completed-RHS premise. The zero leaf is now also frame-complete:
   `natZeroRegisteredIotaMajorLinkStepAt_of_selfAdequate` normalizes every
   `CtorFrame` link, rebuilds its path-valued recursor spines, and closes the
   synchronized rectangle; `natRegisteredIotaMajorLinkStepAt_of_zeroSelfAdequate`
   installs that branch in the registered dispatcher. The remaining T3 test
   is the successor branch and then the actual complete induction using a
   concrete Nat `LRD.CoherentTypedIotaLeafStep []`. An arbitrary callback is
   not evidence for this rung.
6. **F2 bottom/two-sort audit:** the repaired
   `DirectFixedHeadProducer` does not recreate either refuted terminal law.
   It packages one telescope and witness; the nil case retains an order edge,
   not type-shape equality; and informative consumption requires a non-bottom
   result. The harness now proves
   `directFixedHeadTelescopeLE_headTy_nonbot`: an informative terminal
   observation forces the packaged head-type observation to be non-bottom.
   The two-sort cross-package rejection is now concrete as
   `nonbottom_lambda_has_incompatible_type_shapes`: one informative singleton
   lambda has two valid Pi-type observations whose domains are respectively
   `sort false` and `sort true`, hence incompatible. Therefore a semantic
   registered-type witness cannot be synchronized with a capture-built
   telescope from shared non-bottomness and two shape typings alone. The
   former `makeProducer` callbacks have also landed their accepted H-LOCAL
   tightening: all four now receive the non-bottom fact already known at
   their call sites. They have since been renamed `makeAlignment` and return
   `DirectFixedHeadAlignedTyping`, which exposes the semantic typing package,
   concrete dominance spine, and precise tower-to-registered-type comparison;
   the generic `.producer` consumer performs the weakening. The registered
   zero leaf now constructs that comparison by lifting both semantic and
   exact capture layers to one common level, and its nullary framed rectangle
   is closed without transporting arbitrary field evidence. The remaining
   architectural work is the corresponding successor treatment.
7. **F4 eta boundary:** bare syntactic `Params` still lacks eta/match
   stability, so the hostile `drop ctor` versus `fun x => ctor x` critical
   pair remains a generic Church–Rosser risk.  It has not produced an M2
   counterexample.  The next discriminator is a semantic
   `PatternArgumentNonFunction` theorem retaining the exact saturated
   constructor observation and contradicting Pi typing.  If derivable from
   `Params.Semantic.ctor`, the hostile instance is excluded at the intended
   boundary; otherwise this is H-ADM.  Concrete Nat remains quarantined by
   its exact zero/successor inventory and empty structure-eta registry.

The evidence therefore currently favors H-ARCH, with the completed callback
tightening classified as H-LOCAL, over model unsoundness. T2 is closed by the
two fixed premise-free non-bottom redex witnesses, and T3's concrete strong
derivations plus strict successor-predecessor provenance are now clean. F2
additionally proves that fixed-head alignment cannot be recovered from
non-bottom shape typing alone, while the registered zero trace now supplies
the stronger local data needed to construct it. The framed zero major-link
rectangle is now complete and installed in the registered dispatcher. The
remaining T3 separating test is to complete the successor treatment and run
the complete self-adequacy induction using the concrete Nat coherent
typed-iota leaf rather than an arbitrary callback. Neither the successful
local witnesses nor failure to
synthesize the eventual global `LRD.Adequate [] [] .nil` theorem counts as
the FALSIFY exit decision by itself.

#### M2 — concrete Nat/D0 direct adequacy

Start with `natParams`, not `d0Params`. This isolates generated iota from
delta and forces the critical recursive successor branch to be real.

1. Build the zero certificate from the exact generated rule, match, captures,
   typing, and zero-branch semantic relation.
2. Build the successor certificate from the exact generated rule and the
   retained semantic relation for both the predecessor and recursive-result
   arguments. The recursive result must come from the semantic RHS induction,
   not from a global theorem about the instantiated contractum.
3. Feed those certificates to a direct variant of the adequacy induction and
   prove contextual adequacy at depth 1.
4. Derive, with no external inversion premise, working theorems of the form
   `natContextualAdequacyAtOne`, `natPiPathInvDirect`, and
   `natJointStratifiedInversionDirect`.
5. Instantiate the zero and successor redexes explicitly so the certificate
   cannot pass vacuously through an empty-pattern or bottom-shape case.
6. Only after that succeeds, add the `d0def` constant and prove the D0 delta
   case without changing the Nat rule contract.

The names are provisional, but each final M2 theorem must be premise-free
apart from its ordinary context/environment WF hypotheses. Its dependency
closure must contain no `sorryAx`, custom axiom, `SortEdgeData`, `BetaFire`,
`PiPathInv`, or `MajorLinkRect`. Existing logical axioms and already audited
container/native decision leaves remain governed by the normal root policy.

M2 fails the route if the successor proof needs normalization of the
substituted RHS, if the branch certificate assumes the desired `LR.DefEq`
instead of deriving it from the recursive semantic hypothesis, or if the
direct adequacy theorem still reaches `WHRedS.defeq_of_piPathInv`.

#### M3 — extract the registered-rule adequacy interface

Do not design this interface before M2. After the Nat proof compiles,
lambda-lift exactly the data it used into an adequacy-layer proposition or
structure, provisionally `LR.RegisteredAdequacy`.

The interface may retain:

- the exact `Pattern.IotaRule` selected by `Params.Semantic.iotaRule`;
- `Pattern.IotaReductionSite` and its redex/contractum typing equality;
- typed captures and the existing `PatternLeafSpine` alignment;
- the semantic interpretation of the selected RHS branch; and
- recursive branch adequacy at strictly smaller semantic structure/depth.

It may not contain:

- `LR.ContextualAdequacyAt`, `LRS.PiPathInv`, `IndTyAppInj`,
  `QuotAppInj`, `SortEdgeData`, or an equivalent theorem under a new name;
- a field asserting the final redex/contractum `LR.DefEq` without exposing
  the branch construction; or
- normalization/subject reduction for arbitrary untyped `WHRedS`.

Place this contract in `ShapeLogRelAdequacy.lean`, not `SExpr.lean`. Prove
weakening/environment-extension transport so an already certified Nat prefix
can be reused in D2. Introduce the new generic adequacy entry point alongside
`adequacy_of_iotaWitnessStep`; remove the latter only in M7.

M3 exits when Nat and D0 instantiate the extracted interface with no extra
premise compared with M2, and the generic theorem returns direct contextual
adequacy plus its `LR.ContextualAdequacyAt 1` projection without accepting
`piInv` or `linkRect`.

#### M4 — paired classified-head observation

The current `ShapeS.indTy` is atomic and `LRS.IndTyHead` observes each
endpoint independently. That proves head classification but forgets the
relationship between application arguments, so it cannot imply
`IndTyAppInj`.

Use a discriminating probe for

```text
Γ ⊢ I p ≡ I a : sort u  ->  Γ ⊢ p ≡ a : P
```

where `I` is stuck, universe-polymorphic, and its parameter type is
dependent enough to exercise spine transport. Try the least invasive design
first: replace the direct `.indTy` clause with a paired observation carrying
one classified head, both level instantiations, both typed application
spines, and the existing logical/raw relation for corresponding arguments.
Reuse `SpineWF`, `TypeDefEqPath`, and the normalized constructor-spine
machinery rather than inventing an untyped `List.Forall₂` relation.

If the fundamental theorem cannot preserve that sidecar through
monotonicity, joins, lifting, and constant application because the semantic
shape has erased the arguments, prototype a dedicated observable head shape
(`typeHead`/`indApp`) in isolation. It must define order, compatibility, join,
lift, typing, and application behavior and must preserve the existing eta and
proof-irrelevance cases. Keep the old atomic `indTy` as an erasure boundary
during migration.

The design decision is settled by machine-checked evidence:

- choose the sidecar if it proves the same-head, pointwise-argument theorem
  and survives all direct fundamental cases;
- choose a new shape only if the failed proof identifies an operation that
  necessarily erases the sidecar; and
- if a new shape breaks joins/lifts or forces unrelated constructor semantics
  to change, split out a target-specific head observation instead of
  rewriting the whole domain.

M4 exits with direct `IndTyAppInj` derived from adequacy and a nonvacuous
same-head application test. It does not exit with merely two independent
`IndTyHead` witnesses.

#### M5 — D2 generated-rule closure

D2 must consume the paired observation *locally* while constructing its five
Tree/TreeList rule certificates. It must not call the exported
`IndTyAppInj`, because that theorem is downstream of D2 adequacy.

1. Transport the inherited Nat rule certificates across the D0-to-D2
   environment extension.
2. Add a direct adequacy-side companion to `PatternLeafSpine` carrying the
   major type's paired head observation. At each Tree leaf, project parameter
   relations from that observation and feed them directly to
   `Pattern.Check.OK`; leave the operational `PatternLeafSpine` reusable by
   the legacy path.
3. Treat constructor level alignment separately. Prefer a certificate from
   the exact registered generation metadata and actual match levels. If the
   current literal equality in `D2TreeLevelAlignmentStep` is stronger than
   the proof needs, replace it with a typed level-instantiation transport; do
   not derive syntactic list equality from type injectivity by fiat.
4. Reuse the landed eight-common-argument prefix, exact field suffix,
   `D2TreeReplayStep`, and `D2RegisteredBodyStep` for the finite RHS work.
5. Assemble D2 `RegisteredAdequacy`, prove direct contextual adequacy, and
   only then export D2 `PiPathInv` and `IndTyAppInj`.

M5 acceptance requires all five Tree rules plus the two inherited Nat rules,
including the successor recursive-result path. `D2BlockStepExact` and the
rule-certificate constructors must not take global `IndTyAppInj`,
`D2TreeCheckedStep`, or a raw source-level equality that is used only to hide
the missing semantic transport. The concrete replay may retain a smaller
engineering lemma after its semantic premises are discharged.

#### M6 — Quot, public reflection, and downstream consumers

After D2 decides the head-observation representation, reuse it for Quot only
to the extent justified by the compiled proof. If inductive and Quot heads
share all operations, generalize to a classified `typeHead`; otherwise keep a
small Quot-specific observation rather than prematurely redesigning the
domain.

Then derive:

- `QuotAppInj` from direct adequacy;
- `JointStratifiedPathInversion` and `LRS.PiPathInv.of_adequacy` from the same
  direct contextual theorem;
- `IsDefEqU.sort_inv`, `IsDefEqU.forallE_inv_stratified`, and
  `IsDefEqU.sort_forallE_inv` at the explicit registered/admissible environment
  premise accepted by the release contract; and
- the D2 and REC parameter transports from exported `IndTyAppInj`.

The [conversion-checker formalization][conversion-paper] is relevant here:
injectivity, rather than global normalization, is the property needed by most
checker correctness consumers. Full normalization remains valuable for a
termination theorem, but it is not a prerequisite for closing R1-R3 or V5.

[conversion-paper]: https://arxiv.org/abs/2502.15500

#### M7 — migration, retirement, and gates

Migrate one consumer family at a time: D2, REC/V5, projection-head inversion,
public Injectivity, then any remaining Experimental wrappers. For each family,
pin its theorem's axiom closure before removing the compatibility route.

Only after every consumer is on the direct route:

- delete or deprecate the `piInv`/`linkRect` parameters on the old adequacy
  wrappers;
- remove `SortEdgeData`, `BetaFire`, and `MajorLinkRect` from supported-root
  dependency closures; retain a historical probe only when it still guards a
  false shortcut;
- promote the stable syntax/relation/adequacy modules according to PROMOTE;
- update the sorry frontier and exact axiom manifests; and
- run the complete Section 8 gate on the same revision.

The retirement grep is semantic, not just textual: `#print axioms` for every
new public root must confirm that a legacy theorem was not hidden behind an
adapter or an instance.

#### Validation and global kill criteria

Every milestone runs the smallest affected Lake targets first, then the full
Experimental target. M2, M5, M6, and M7 additionally run the complete
checkpoint gate. The focused build matrix is:

| Milestone | Minimum focused command before the broader gate |
|---|---|
| M0/M2 | `nix develop --command lake build Lean4Lean.Experimental.SExprParamsD0` |
| M1/M3 | `nix develop --command lake build Lean4Lean.Experimental.ShapeLogRelAdequacy` |
| M4/M5 | `nix develop --command lake build Lean4Lean.Experimental.SExprParamsD2Registered` |
| M6 | `nix develop --command lake build Lean4Lean.Experimental.SExprParamsD1 Lean4Lean.Quot` |
| M7 | all commands in Section 8, on the same revision |

Each new endpoint receives:

- its full explicit signature pinned with `#check @name`/`#print name` and its
  `#print axioms` output pinned in a source guard or audit module;
- explicit zero/successor or generated-rule witnesses to prevent vacuity;
- negative dependency scans over each new direct theorem body/module for
  `WHRedS.defeq_of_piPathInv`, `SortEdgeData`, `BetaFire`, and
  `MajorLinkRect`, while the legacy comparison module still exists; and
- a clean `git diff --check` plus the import-boundary audit.

Reject the direct route or its current interface—not merely its proof
script—if any of the following occurs:

- an arbitrary raw weak-head reduction is upgraded to a typing equality;
- a registered-rule field is propositionally equivalent to the adequacy goal;
- the Nat successor branch requires full normalization or an exported
  inversion theorem;
- D2 uses global `IndTyAppInj` while constructing the adequacy from which that
  theorem is extracted;
- universe-list equality is assumed where only typed instantiation transport
  is justified; or
- a head-observation extension collapses the arguments it was introduced to
  distinguish.

The closed routes remain closed: syntactic `(rank, size, depth)` and
family-ordinal measures; uniform/same-depth beta stratification; CR/Pi
inversion as a producer; registered-head narrowing; body-blind lambda
classification; deleting `hu0`; and treating pattern membership as semantic
soundness.

#### Optional NORM-WHN track

Full weak-head normalization is a separate, non-release-critical project. If
funded, its starting specification is a substitution-closed reducibility
predicate with a dynamic-beta closure theorem, modeled on the
[Martin-Löf-style Coq development][coq-logrel], not another bounded syntax
measure. It receives a separate budget and must not be used to weaken M2's
direct acceptance test.

[coq-logrel]: https://github.com/CoqHott/logrel-coq

The unrestricted P2/P3 large-elimination theorem is likewise not the
baseline. If pursued, it receives its own truth-status probe and explicit
environment premise.

### 5.4 CR and SST — remaining core metatheory

**CR engineering:** the exact proof-irrelevance boundary is now present as
`Params.pat_arg_prop`, and `NormalEq.parRed_extra_propArg` machine-checks the
corresponding appDF-by-`.extra` subcase. The classified semantic development
already derives this boundary through
`SExpr.Params.Classified.theoryPatArgProp`.

That condition did **not** close R5 as previously claimed. If the matched
argument is a constant-headed function `ctor` and the left argument is its
eta expansion `fun x => ctor x`, `NormalEq.etaL` relates the arguments while
the left application need not match the rule. A schematic rule
`drop ctor ↦ zero`, with `drop : (Nat → Nat) → Nat`, makes `PatArgProp`
vacuous because the argument type is not `Prop`; the right side contracts and
the left side can be stuck. A `StructEq` argument creates the analogous
critical pair once registered structure eta and iota coexist. The existing
probe had noted the eta branch but proved only the proof-irrelevance branch.

The R5 signature is now repaired without assuming global confluence.
`Params.PatternArgumentNonFunction` records that the immediate constructor
major of a registered application pattern is saturated and hence has no Pi
typing; this excludes the hostile eta instance. Separately,
`Params.StructurePatternCompatibility` supplies only the local
`NormalEq.appDF`/`ParRed.extra` join whose argument carries a retained
`StructEq` seed. `NormalEq.parRed` requires both, and `Params.Extension`
inherits them before adding whole-equation `CRDefEq` coverage.

Next prove the non-function producer from exact generated constructor
metadata, construct the structure compatibility producer with D4, and then
finish the remaining match/spine inversion using the landed `Check.OK`
transport, level-list congruence, and closed-template RHS congruence.

The whole-live-environment `Params.Extension.join` instance comes later. It
must prove a typed join for every registered raw equation; registration or
syntactic coverage alone is never enough.

**SST strengthening:** W0-W3 are probe-proved. Remaining work is:

- W4: repackage `.extra` action certificates at the lifted base context
  (thread certificates as data; do not search for a syntax-size measure);
- W5: clean `NormalEq.weakN_inv` by a new mutual induction;
- W6: re-found `NormalEq.trans`, Church--Rosser, and standardization per depth;
- W7: assemble the already sketched staged inverse; and
- W8: instantiate it at the accepted generic environment surface.

The `registeredStructureHeadInversion` statement repair is landed. Its
`constructor_name_inv` and `constructor_inv` fields now require
`VEnv.ConstructorHead`: an exact source-constructor membership and completed
`VDecl.WF.induct` transaction below the current environment. Consequently an
axiom-headed major and a definition alias cannot satisfy the premise. Verify's
`ProjectionReady.constructorHead` connects each successful host `ctorInfo`
lookup to that Theory certificate; singleton, mutual, and nested transaction
helpers construct it, and ordinary/family-only readiness transports preserve
it monotonically. After `weakN_iff`, the remaining proof uses strengthening,
`TrProj.result_eq`, uniqueness, and `IndTyAppInj`.

### 5.5 ENV and REC — checker closure

Three checker sorries remain:

- **V3 — `addDecl.WF`, inductive case.** Generalize what the concrete replay
  matrix already performs: checker run → normalization candidate → generation
  certificate → certified block/nested transaction → `TrEnv'`. This is a
  multi-session engineering proof and the final removal of the semantic
  placeholder in environment construction. The arbitrary-block candidate now
  has one total executable generation-shape gate (including exact family and
  constructor list consumption), a proof-carrying producer, and a transparent
  `checkConstructors` decomposition projected directly from
  `NormalizationCandidateExecution.constructorRun`. The strengthened block
  producer now retains that detailed execution instead of rerunning the
  erased candidate producer. An exact inner/outer CPS
  factorization now also proves that a successful
  `buildNormalizationCandidateExecution` owns the family validator's selected
  statistics, common result level, and terminal reader context. Its terminal
  parameter/index/constant-count assertions are now proved from that same run
  and packaged as an execution-owned `FamilyValidationBlockRun`; both ordinary
  and indexed Tree/TreeList fixtures consume these real-run projections. A
  generic `BlockGenerationRun` assembles `BlockGenerationChecked.WF` from
  exact compositional family and flattened-constructor records. The ordinary
  and indexed Tree/TreeList fixtures now populate those dependent records from
  the retained block semantic hierarchy and validator-owned checked facts,
  build exact produced-generation runs, and recover each fixture generation
  `WF` without fixture-selected family or constructor lists. The indexed
  family stage preserves the pre-existing Nat projection/eta capabilities via
  a generic multi-constructor declaration-trace transport. The executable
  producer now also retains actual recursor synthesis and declaration with a
  producer-owned common-K invariant. Generated family, constructor, and
  recursor metadata feed a rule-completable exact Theory prefix, and the
  ordinary and indexed fixtures use their actual synthesized kernel maps. The
  complete outer execution now retains nested elimination, ordinary flattening,
  recursor generation, and mixed restoration; a concrete RoseTree run proves
  the public `addDecl` equation and exact `TrEnv'` nested transaction over its
  actual restored map. Operational completeness of every downstream and outer
  phase is now generic. The attempted residual nonprimitive observer contract
  is not derivable from the former public run: the executable
  `plans/probes/deep_alias_candidate_gap.lean` builds 100,051 safe
  abbreviations for which public family/constructor validation succeeds while
  candidate-only parameter-domain WHNF exhausts its deterministic fuel. The
  public `AddInductive.run` therefore consumes
  `buildNormalizationCandidateExecution` as its real prefix. That producer
  preserves validation, family declaration, and constructor validation order,
  then retains the exact pre-family and post-family candidate traversals.
  Successful public ordinary and nested calls now derive
  `NormalizationCandidateExecution.completeForRun` and
  `EnvironmentInductiveExecution.complete` with no observer callback, and the
  `addDecl` component/transaction APIs expose only the remaining semantic and
  readiness premises. Candidate traversal also uses the configured
  recursion-depth budget rather than the smaller inductive-analysis budget.
  The 1100-binder `plans/probes/deep_candidate_gap.lean` regression remains
  accepted by both paths, while the deep-alias regression is rejected by both
  with the same deterministic timeout. Generic
  ordinary/nested semantic transactions
  preserve quotient initialization and supply translation plus model
  extension to a decomposed `VEnvs.WF` assembler. On the non-primitive path,
  a coherent family of exact name-avoiding traces additionally derives Theory
  primitive reflection, host primitive safety, and cross-safety monotonicity.
  Exact replay can
  now be followed by a coherent checked list of Theory-only structure-eta
  registrations; this completion preserves translation, primitives,
  projection artifacts, and cross-safety ordering. A per-structure
  registration artifact is now constructed unconditionally from a projection
  artifact and the base model's `WF` proof; after the shared registration it
  constructs the final `StructureEtaArtifact`. A global coverage object now
  classifies every accepted host structure as already registered or backed by
  an exact artifact in that shared list and derives `StructureEtaReady`; no
  final readiness oracle remains in the completion package. Checked generation
  derives constructor-prefix typing, the exact canonical capture spine for
  every generated iota rule, and current-model rebuild typing. The common
  parameter/motive/minor recursor spine is normalized once and reused by both
  projector typing and rule capture; shared `instRevAt` algebra cancels the
  two lifted common binders before appending the complete canonical field
  spine. Consequently registered generated-iota evidence derives exact
  earlier-projector equations internally, the dependent source-order prefix
  induction iterates to all selecting minors, and the public `toMinorsWF`,
  `toProgramsWF`, and `toRebuildWF` theorems require no external minor or
  capture contract. The persistent eta obligation is now closed through an
  explicit `VEnv.ConversionRegular` capability. Raw `VEnv.LE` remains the
  correct inventory-only relation; each actual typing target supplies the
  conversion laws derived from its own `VEnv.WF`, while environment history
  recovers the full certificate for every registered rule. Checked generation
  consequently derives `VStructureView.WF.toStructEtaWF` and
  `StructureEtaRegistrationArtifact.ofProjection` without a caller-supplied
  future-model reconstruction oracle. The primitive
  recognizer itself is proved and the declaration bridge splits its canonical
  Bool/Nat branch from nonprimitive replay. The recognizer's concrete host
  syntax now selects the complete canonical Theory declaration directly, so
  producers supply neither a parallel raw source nor a semantic normalization
  run. Checked generation
  derives the canonical recursor name internally, and that inventory turns
  coherent ordinary traces into the complete primitive transaction. The
  recognizer shape and retained public nested-elimination run now prove that
  canonical Bool/Nat sources are unchanged and generate no auxiliary family;
  the primitive transaction package no longer asks producers for either fact.
  A primitive-specific replay now consumes the family, constructor, and
  recursor insertion folds indexed by that retained execution, constructs the
  exact public `AddInductBlockTrace`, and uses the fixed canonical generation at
  every safety level. The public primitive transaction package contains this replay
  rather than accepting arbitrary traces. Keeping the replay at the exact fold
  boundary bypasses both the intentionally unavailable `HasPrimitives` invariant
  between insertion of a primitive family and its constructors and the generic
  staging records' final `TrEnv' .safe` postcondition, which would exclude valid
  partial and unsafe input models with additional visible constants. Lightweight
  family, constructor, and recursor interpreters now construct those exact folds
  from the retained declaration equations, semantic list translations, and the
  weaker `Aligned` name-domain invariant; a primitive assembler connects their
  endpoints directly to the public replay. The family, constructor, and
  generated-recursor translation lists, complete Bool/Nat generation `WF`,
  exact recursor K target, and generated-rule fold are now derived from the
  retained execution. A safety-indexed assembler constructs the coherent
  canonical replay directly from the input `VEnvs.WF`, so the primitive
  transaction boundary has no separate metadata, semantic-WF, or replay input.
  Primitive readiness derives exact final-constructor classification,
  completed Theory constructor heads, both current and future-model cached
  parameter-count agreement, and final projection/structure-eta readiness.
  Primitive candidate normalization is likewise closed. Operational
  completeness and the persistent eta-rule certificate are now unconditional.
  Exact host family/constructor/recursor observations and final projection
  readiness construct each nonprimitive singleton-structure registration
  artifact; a common checked rule list now deterministically computes every
  safety-indexed completion endpoint. The plan is certified once in the
  smallest `.safe` model and transported coherently, including exact rule
  identity, to `.partial` and `.unsafe`. Retained ordinary family,
  constructor, and recursor declaration traces now classify every final host
  lookup; every flattened source family owns a generated recursor; and the
  coherent ordinary transaction derives its finite source-name scan and exact
  readiness coverage without a caller-supplied inventory. The mixed nested
  restoration fold now likewise preserves map well-formedness, proves every
  restored name fresh in the input map, and classifies final family,
  constructor, and recursor observations as old or exact inventory members.
  Its pure source-family chunks retain exact family names, constructor owners,
  and canonical main recursors, so the coherent nested transaction derives
  its original-source scan and readiness coverage automatically as well. A
  single readiness constructor now selects the ordinary or nested plan from
  the retained execution. One exact `.safe` ordinary or nested trace now
  replays into `.partial` and `.unsafe` automatically, preserving the original
  safe endpoint and one shared generation/restoration artifact. Next construct
  that safe trace and safe projection readiness from the retained execution,
  then close `addDecl.WF`. The remaining projection proof must account for the
  current interface mismatch in which host projection readiness admits
  recursive singleton structures while `VStructureView` records only a
  nonrecursive structure view.
- **V4 — `checkPrimitiveDef.WF`.** Recheck upstream PR #32 before editing its
  file surface. If it is not merged by the next CR checkpoint, prove the
  recognizer locally with an `M.WF`-style run certificate.
- **V5 — `reduceRecursor.WF`.** Exact local σ̂-to-`restoreExpr` alignment is
  proved for complete auxiliary-family and auxiliary-constructor application
  spines, including zero parameters and arbitrary trailing arguments under
  explicit restored-head inertness, and for full recursor-rename spines.
  `NestedStagedCertificate` now retains an exact flattened transaction beside
  the restored one and derives its rule typing, `RuleClosure`, and exact
  `IotaPat` facts, paired by position with the final registered restored rule.
  `ExactProducedBlockMetadataPrefixRun` constructs that package without an
  alignment equality. The RoseTree outer execution now supplies exact source
  family/constructor inventories, checked analyzer semantics, the flattened
  semantic generation, synthesized recursor metadata, and its deterministic
  rule fold under `RoseFlatCandidateReadiness09`. It instantiates the generic
  staged bridge and derives paired flat/restored facts for all three flattened
  constructor positions. All three corresponding host selectors now have
  exact reducer/generator arity and field-count equations, deterministic plus
  semantic RHS translations to the paired restored rules, and concrete
  complete-redex restoration theorems for the main, nil, and cons cases. A
  stable generic lemma constructs generated-pattern matches from completed
  spine lengths, while a Verify-side certificate consumer removes every
  certificate-owned premise from `pat_wf`. A generic check constructor reduces
  the folded `Pattern.Check.OK` obligation to pointwise parameter agreement
  and explicit-index/computed-index agreement, while `AppStack.splitAt` and
  the generalized `AppStack.toSpineWF` isolate and type the translated redex
  prefix below the WHNF import boundary. All three concrete Rose rules are
  unindexed, so only parameter agreement remains from their check relation.
  The completed transaction now exports its full generation environment and
  derives the selected constructor owner, exact runtime recursor/constructor
  head types, and both explicit owner-family types of the major. Unique typing
  reduces parameter agreement to a same-head family-application equality;
  consuming it is exactly the NORM-DI-owned `IndTyAppInj` consequence.
  Canonical captures equal the exact reducer prefix/field slices, pointwise
  translation is preserved by those slices, and the factored pure reducer
  tail has an exact prefix/field/trailing list normal form. Strict and weak
  application builders now turn a typed capture spine directly into output
  translation. A generator-aligned output theorem performs the complete host
  slice translation, appends the post-major spine, and rebuilds the exact
  runtime reduct. Generic prefix replay plus prefix/field spine assembly
  isolates capture typing to the constructor-field continuation. Exact
  constructor spines now expose their post-parameter field suffix. Generic
  one-parameter `instRevAt` algebra identifies the generated lifted suffix
  with ordinary dependent substitution; whole-Pi inversion extracts
  structural telescope equality, and `TelDefEq.spine_sort` transports every
  field argument. The selected main and cons rules are certified at that
  boundary, while a zero-field specialization closes flattened `List.nil`
  reflexively. The
  unindexed certificate consumer removes the vacuous index premise and returns
  its reduction at the exact capture-spine result type, ready for trailing
  application congruence. Generic `SpineWF` constant-interpretation transport,
  arbitrary-terminal telescope retargeting, and structural restored
  Pi/lambda-tower laws now carry a saturated flattened capture spine to the
  final environment under an explicit `ConstInterp` and whole restored-rule
  type alignment. The staged one-parameter consumer retains that flat spine,
  constructs the canonical restored capture spine, and applies the final
  registered restored equation. A separate WF-derived β-collapse reduces the
  restored LHS tower through those captures and any post-major arguments to
  the instantiated restored generated body. On the flat side, the certified
  reduction and registered generated rule now expose the exact instantiated
  generated-body/runtime-redex equality without replaying `pat_wf` internals.
  σ̂ commutes with both universe instantiation and `instRev`, so typed
  constant-interpretation transport carries that equality to the final
  environment. The concrete six-point `ConstInterp` now preserves the entire
  flattened declaration/equation inventory, and arbitrary-level whole-rule
  type and LHS alignment makes restored-body versus σ̂-image body a generic
  consequence of applying and β-collapsing both rule towers. Direct
  arbitrary-level main/nil/cons runtime normal forms close the second local
  redex alignment (syntactically for main and by typed β for the auxiliary
  constructors). A joint one-parameter consumer retains the flattened capture
  spine and generated-body/redex equality from the local inductive-head
  injectivity consequence. Each selected Rose rule instantiates that joint
  result directly through its final runtime redex, eliminating the former
  caller-supplied flattened body match. The generator-aligned reducer theorem
  and its matched-body adapter consume that equality through every post-major
  argument; the runtime recursor array uses the correct strict major-index
  bound and derives the canonical capture length through the pre-major `take`.
  Exact nonliteral and constructor-headed `inductiveReduceRec` equations now
  retain environment and rule lookup, major selection, WHNF, field/level
  guards, and the pure tail; exact constructor recognition discharges both
  literal exclusion and the structure-conversion callback. A composed theorem
  pairs that actual execution with the nested translated reduct. The public
  Rose output now has exact restored main/aux recursor lookups and exact
  restored-or-preserved node/nil/cons constructor lookups. Its concrete
  main/nil/cons equations additionally discharge K, rule selection, and
  universe metadata. The supported exhaustive ordinary theorem now invokes
  the live WHNF callback itself, covers all expression and literal cases, and
  closes rule/field/level failures. Concrete main and auxiliary wrappers
  remove the exact callback premise and expose only `SelectedBranchWF` when a
  rule is really selected. Exact K-conversion,
  Nat/String-literal, missing-head/metadata, rule/field/level failure, and all
  three quotient-gate equations factor the remaining operational paths. The
  concrete Rose executions lift through the actual pointwise
  `reduceRecursor`, preserving its state exactly. A quotient-disabled
  pure-result adapter now joins those operational equations to the live
  `RecM.WF` postcondition, and the nonconstant, non-recursor, and
  missing-major exits close with no callback or semantic premise. General
  live wrapper joins now cover both quotient-gate values: a declining quotient
  run threads its advanced state into an inductive proof valid at that state.
  Translated quotient-enabled environments project the complete canonical
  Quot constant/equation inventory. Typed eliminator and constructor spines
  feed a `QuotAppInj`-parameterized consumer: `Quot.lift` reduces through the
  registered quotient equation and `Quot.ind` through proof irrelevance. The
  resulting exhaustive `quotReduceRec.WF` proves Theory translation and
  `FVarsBelow` for both successes and every non-Quot `none` branch, and
  composes through the live wrapper with exact state threading. Only the
  NORM-M6 producer of `QuotAppInj`, not the quotient semantic consumer,
  remains open. Generic
  `applyRecursorRule` free-variable preservation factors the output into its
  closed instantiated rule head, original recursor arguments, and WHNF-major
  fields; strict input translation recovers the checked head levels, and
  syntactic level substitution preserves RHS closure. Strict input translation
  also projects the selected major argument. The exhaustive live consumer
  executes `whnf.WF` directly, derives the major's translation and
  `FVarsBelow`, transports Nat literals, executes String expansion, and
  analyzes every nonliteral host shape. The main/node and joint auxiliary
  nil/cons Rose wrappers instantiate that control-flow theorem; their
  successful selectors invert to exactly those three constructors, and named
  branch-certificate constructors discharge level, arity, and free-variable
  bookkeeping. The remaining local semantic boundary is exactly the three
  node/nil/cons output translations, supplied with both major-translation
  witnesses needed by `IndTyAppInj`. The
  completed-`List`
  readiness package now derives
  every primitive, safety, semantic-stage, and pre/post-family readiness field
  from one explicit premise: the open-world parameterized-constructor
  `numParams` invariant. Repair or justify that interface boundary before an
  unconditional Rose certificate. On the conditional path, lookup, structural
  matching, unindexed folded-check construction, translated-prefix typing,
  reducer-slice/capture alignment, exact typed canonical RHS application, RHS
  translation, output-tail translation, and flattened-to-restored redex
  alignment are landed. Next supply NORM-DI's inductive-head injection at each
  selected site, discharge those three semantic output functions (which now
  construct the main and auxiliary `SelectedBranchWF` contracts), and then
  prove semantic preservation across the
  factored K, structure-expansion, literal, and failure branches plus
  certified singleton/mutual/nested rules.

Once V3-V5 and the metatheory roots close, state the final executable-checker
soundness theorem over environments containing ordinary declarations, Quot,
single/mutual/nested inductives, literals, structures, and extension rules.
Re-run the fresh whole-core replay; fix or file any remaining loose-bound-
variable failure.

### 5.6 PROMOTE — stable API and audit boundary

Promotion is mechanical but not cosmetic. Conditional theorems may be
promoted if their premises are explicit and stable.

- Move the retained SExpr core and shape/adequacy modules to stable Theory
  paths; move fixture-dependent D modules to Verify/Tests, never Theory.
- Resolve the `UniqueTyping.lean` filename collision and preferably rename the
  generic SExpr `Params` namespace to avoid confusion with `VEnv.Params`.
- Regenerate `Lean4Lean/Audit/SorryFrontier.lean` imports and extend
  `surfacePrefixes`; otherwise moved modules can silently leave the audit.
- Replace probe-only evidence with in-source `#guard_msgs`/`#print axioms`
  pins. Keep a probe only when it remains the discriminating evidence for an
  open research decision.
- Recheck every import boundary and downstream public name; API changes are
  additive with a deprecation window.

Promotion itself does not delete a supported sorry. A frontier entry leaves
only when its actual proof lands.

### 5.7 TRUST, DIFF, and RELEASE

**Axiom reachability.** `Audit/SorryFrontier.lean` now generates the complete
transitive closure for every declaration in four release surfaces: Theory,
Verify, the shipped `Lean4Lean` library, and `Main` (the CLI). The exact union
contains 324 leaves: 3 logical-baseline axioms, `sorryAx`, 6 rejected-fixture
declarations, 27 custom project contracts, and 287 compiler-generated
`native_decide`/`bv_decide` certificates. The current per-root closures are
Theory 10, Verify 239, library 5, and CLI 3.
The audit pins each root's membership separately and rejects any new, removed,
moved, multiply classified, or root-forbidden leaf; compiler certificates are
Verify-only, and admitted proofs cannot enter the library or CLI. Transitional
bridges are now Verify-only; the library root admits only the logical baseline
and its two pointer contracts, while the CLI admits only the logical baseline.

The project manifest separately assigns stable ID, disposition, reason, and
owner to every custom axiom; pins the source inventory exactly; proves Theory
reaches none; rejects dead or forbidden contracts; and proves no manifest
axiom is globally registered as a simp theorem. Verify consumers now name the
precise bridge at each use. Initial retirement queue:

1. **Done:** delete dead `Level.mkLevelIMaxCore_eq`,
   `Expr.liftLooseBVars_eq`, `Expr.equal_eq`, `Level.mkMaxAux_eq`, and
   `Level.skipExplicit_eq` (34 project axioms reduced to 29);
2. **Done:** prove `TreeMap.all_eq_all_toList` from the pinned standard-library
   model equation and `TreeMap.any_eq_any_toList` from the corresponding
   traversal induction; continue with `Level.hasParam_eq`/`hasMVar_eq` when a
   sound route is available. Do not adopt PR #27's saturating `mkData'` model
   while lean4#8821 remains open: the PR's counterexample confirms that the
   current unconditional equations are refutable against the pinned finite
   cache model, and upstream identifies opacification as the prerequisite;
3. **Done:** remove every project axiom from the global simp set, migrate
   Verify consumers to explicit bridge dependencies, and enforce the boundary
   in the compiled audit;
4. **Done:** classify the logical and compiler-generated leaves, import the
   actual library/CLI roots into the audit, and pin all four transitive closures;
5. **Done:** move the persistent-map proof helpers under Verify, retain their
   former `Std` paths as compatibility imports, and make transitional bridges
   forbidden at the library and CLI roots;
6. reduce the final platform budget to explicitly tested pointer/layout or
   lawful equality contracts, absent from Theory roots.

**Differential corpus.** Automate elaboration, raw-environment translation,
justified normalization, Theory generation, and comparison. Compare both
success and failure as data: phase, metadata, generated constants, universe
lists, field/recursive positions, K flag, rule count, and every RHS. Check the
upstream `differential` branch before duplicating its harness.

The reusable harness is being built on the single-declaration slice ported
from that branch:
`lean4lean --decl=<Name> <Module>` replays one exact declaration plus its
dependencies, requires an unambiguous module, and rejects missing or
non-replayable targets instead of reporting a misleading zero-declaration
success. `--json` emits a versioned result for acceptance and rejection, with
exact structural names/levels/expressions, generated constants, constructor
field positions, K and rule counts, and every recursor RHS. Its sole
normalization strips kernel-irrelevant `Expr.mdata`, matching Lean's debugger
codec boundary. For a selected ordinary inductive block, the harness now uses
a CLI-local closed fragment equivalent to Verify's deterministic `trExprS?`
translation without importing Verify's axiom closure, runs the port's real
normalization candidate, feeds the resulting source/view pair to the Theory
block analyzer and generator, and compares recursor types, flags, counts, and
every translated RHS against Lean's stored metadata. The analyzer's recursive
field positions are copied back into constructor snapshots. Compiled guards
pin the CLI translator to `trExprS?` across binders, lets, metadata, literals,
and its rejection boundaries. The pre-inductive environment is retained
explicitly, so the same path works for `--fresh`.
`--case=<FILE>` adds versioned expected outcome/phase inputs, so negative cases
pass only at their declared rejection phase. Its optional `source` input is
copied to a private declared-module path and elaborated by the pinned compiler
before entering the same versioned pipeline; both acceptance and elaboration
rejection are corpus data. For nested declarations, the harness
discovers the referenced earlier inductive families, compares the port and
Theory flattened blocks exactly, normalizes and analyzes that flattened view,
then compares the restored recursor inventory and every restored rule RHS with
Lean's stored metadata. The packaged corpus pins an ordinary structure, a
genuinely normalization-changing structure, a recursive dependent family, a
standalone source-elaborated mutual Tree/TreeList block, a source-elaborated
normalization-changing recursive alias, a fresh `Lean.Syntax`
nested-restoration case, and phase-specific ambiguous-selection,
source-elaboration, missing-module, and missing-declaration
rejections; expectation mismatch is also required to fail. Remaining DIFF work
is broader positive and negative golden coverage.

**Durable divergences.** Two implemented fork decisions must travel with the
release work:

- **D019, registered structure eta:** Theory uses a registered descriptor,
  deterministic recursor-encoded projectors, subject-reduction certificate,
  and explicit equality constructor. Remove it if upstream adopts an
  equivalent; if upstream rejects Theory-level eta, disable the executable
  eta paths rather than certify them against a weaker relation.
- **D020, proof-carrying extensions:** pattern membership is combinatorial;
  each contraction carries its local equality; global raw equations require
  `Params.Extension.join`; beta-collapsed coverage is syntactic only. Remove
  it if upstream adopts an equivalent shape/soundness/join separation.

**Upstream series.** Extract fresh review branches rather than rewriting the
published development line. Proposed order: generic level/syntax lemmas;
Theory API extraction; certified inductive vertical slice; broader inductive
coverage; pattern and Verify environment alignment; projection/eta;
metatheory closure; remaining checker proofs; trust minimization. Coordinate
the pattern/iota series with PR #43 rather than submitting a competing design
blindly. Keep Nix/infrastructure and the replay teardown fix separate unless
upstream asks otherwise.

### 5.8 RENAME — deferred Lean4Ix identity migration

**Status:** accepted and deferred. `Lean4Ix` means the Lean 4 formalization,
kernel model, checker, and verification infrastructure used by Ix. This is a
project-identity migration, not theorem work, and it must not begin while the
current proof-critical working copy is active.

The rename is intentionally split into public identity, downstream adoption,
and an optional internal module-namespace migration. Renaming the repository
does not by itself justify changing thousands of stable Lean declaration
names. The recommended default is to establish `Lean4Ix` as the canonical
project, Lake-package, Nix, documentation, and CLI identity while preserving
the `Lean4Lean` Lean module/namespace surface through the first Ix adoption.
Only then decide whether an internal breaking rename has enough concrete value
to pay for its proof, audit, and downstream churn.

#### Entry gate — no rename work before this point

Start RENAME only after all of the following are recorded in this roadmap:

1. The theorem-owning workstream has landed its accepted main theorem at a
   committed checkpoint, rather than merely producing a conditional theorem
   or working-copy witness. For the current NORM/INV route this means the
   accepted contextual adequacy/inversion endpoint, or an explicitly approved
   replacement or scope decision that closes that workstream.
2. The checkpoint passes the complete Section 8 gate on one revision,
   including the supported, default, Experimental, Nix, format, differential,
   and exact axiom-audit surfaces.
3. The theorem checkpoint has been published or otherwise made recoverable;
   the rename starts from a fresh descendant change with no proof edits mixed
   into it.
4. A revision of `~/projects/ix` is pinned as the downstream migration
   baseline, and its current Lean4Lean dependency, import, Nix, and CLI uses
   are inventoried read-only.
5. No other agent or branch is editing the Lake manifest, flake outputs, audit
   root prefixes, CLI contract, module tree, or Ix dependency integration.

Failure of any entry condition leaves this workstream deferred. A branding
deadline is not grounds for weakening the theorem or checkpoint gates.

#### Identity contract and decisions to freeze

Before editing, review every default below, record any accepted departure in
this section, and fill in the repository- and owner-specific decisions that
follow the table:

| Surface | Canonical target | Compatibility default |
|---|---|---|
| Project/display name | `Lean4Ix` | Mention “formerly Lean4Lean” for one tagged Ix integration cycle |
| Repository slug and local checkout | `lean4ix` | Preserve the hosting-service redirect from `lean4lean`; do not rewrite published history |
| Lake package name | `lean4ix` | Update dependency declarations explicitly; pin the last `lean4lean` package revision |
| Lean libraries/modules | initially `Lean4Lean`, optionally later `Lean4Ix` | Keep the existing namespace during public adoption unless the namespace gate below selects a breaking migration |
| Primary executable | `lean4ix` | Ship `lean4lean` as an equivalent deprecated wrapper during the compatibility window |
| Nix default package/app | `lean4ix` | Retain a `lean4lean` alias with the identical derivation and output during the window |
| Downstream library artifact | Lean4Ix-branded artifact | Preserve or explicitly migrate `lake-dependency` and `depOverrideDeriv.lean4lean` consumers |
| Differential JSON contract | versioned Lean4Ix contract | Continue accepting and emitting the existing `lean4lean.differential` v1 schema until a deliberate v2 migration; never silently rename its identifier |
| Documentation tagline | “Lean 4 metatheory and verification infrastructure for Ix” | Keep historical attribution and old-name search terms |

The decision record must also name:

- the canonical Git host, organization, and repository URL;
- the exact casing used by Git, Lake, Lean modules, Nix attributes, binaries,
  artifact filenames, and prose;
- the compatibility duration as an observable release or checkpoint event,
  not an unbounded promise or calendar guess;
- whether `Lean4Lean` remains the permanent internal namespace or is only a
  compatibility surface;
- the owner of this repository's migration and the owner of the paired Ix
  change.

No mechanical edit begins while any identity cell or owner is undecided.

#### R0 — freeze the complete rename inventory

Search both this repository and the pinned `~/projects/ix` revision. Classify
every old-name occurrence into exactly one of these surfaces:

1. project branding, repository remotes, links, badges, and historical prose;
2. Lake package, library, module, executable, and default-target names;
3. Lean paths, imports, namespaces, declaration names, generated names, and
   user-visible pretty-printer or diagnostic output;
4. Nix derivations, flake packages/apps/checks, dependency overrides, wrappers,
   artifact names, and downstream fixture wiring;
5. CI jobs, caches, release scripts, tarballs, synchronization scripts, and
   build-status references;
6. CLI help, executable discovery, diagnostics, exit behavior, paths, and the
   differential JSON schema;
7. audit prefixes, sorry-frontier imports, axiom manifests, guard messages,
   golden files, generated fixtures, and snapshot expectations;
8. documentation, comments, plans, divergence records, and historical names;
9. Ix dependency declarations, imports, build expressions, scripts, caches,
   documentation, and user-facing references.

Mark each occurrence `rename`, `compatibility alias`, or
`historical/intentional`, with a short reason for the latter two. Do not use a
raw repository-wide replacement: `Lean4Lean`, `lean4lean`, package names,
schema identifiers, and historical prose have different compatibility rules.

Capture the pre-rename baseline in the checkpoint report:

- source revision, remote URL, Lake and flake lock state;
- hashes of the package manifest, flake, audit manifest, and CLI JSON schema;
- the complete Section 8 results and the exact four release-root axiom
  closures;
- `--help`, one successful differential result, and one expected rejection;
- the downstream library fixture result; and
- the pinned Ix revision plus its complete build, test, and end-to-end command.

**R0 exit:** the inventory has no unclassified occurrence, the baseline is
reproducible, and every planned change maps to a later migration phase.

#### R1 — add dual-name compatibility without moving Lean modules

1. Add `lean4ix` as the primary executable over the existing `Main` root.
   Retain `lean4lean` as a thin deprecated wrapper or equivalent Lake target;
   it must not fork command parsing or semantic code.
2. Add canonical `lean4ix` Nix package/app attributes. Keep old `lean4lean`
   attributes as aliases to the same derivations rather than separately built
   artifacts.
3. Introduce the canonical downstream library artifact and override key while
   retaining the existing `lake-dependency` and
   `depOverrideDeriv.lean4lean` route until Ix has migrated.
4. Leave all `Lean4Lean.*` imports, namespaces, source paths, theorem names,
   audit prefixes, and root declarations unchanged in this phase.
5. Add regressions proving that both executable names have the same help,
   exit status, diagnostics, JSON v1 behavior, successful replay, rejection
   behavior, and selected declaration output.
6. Build both old and new Nix attributes and run the downstream fixture through
   both dependency spellings.

Reject R1 if it duplicates semantic implementation, changes an axiom closure,
or makes the old and new entry points resolve different roots.

**R1 exit:** the new public entry points work, the old ones are mechanically
equivalent compatibility aliases, and the Lean theorem surface is untouched.

#### R2 — switch public identity and repository metadata

1. Rename the hosted repository and the canonical local checkout; retain the
   hosting provider's old-URL redirect. Do not rewrite published history.
2. Update the README, documentation titles, badges, canonical links, build
   examples, CLI examples, Nix examples, issue templates, and release metadata.
   State explicitly that Lean4Ix is the formalization and verified-kernel
   infrastructure used by Ix.
3. Change the Lake package identity and flake description to Lean4Ix while
   continuing to expose the unchanged `Lean4Lean` library/module targets.
4. Update CI job names, cache namespaces, release artifacts, synchronization
   scripts, and any repository-name-derived paths. Either bridge old caches or
   accept a documented one-time cold build; never silently share incompatible
   cache keys.
5. Replace current-identity prose but retain old names in quotations, git
   history, schema v1 identifiers, compatibility code, and divergence IDs
   where changing them would destroy traceability.
6. Publish a migration note containing the new URL, commands, compatibility
   duration, last old-name checkpoint, and Ix integration status.

**R2 exit:** a fresh clone from the new URL passes Section 8, the old URL
redirect reaches the same history, and all advertised commands work exactly as
documented.

#### R3 — migrate `~/projects/ix` atomically

1. Create an Ix migration change from the pinned R0 revision; do not update a
   moving, unrecorded working copy.
2. Update the repository input, Lake dependency key, Nix override, executable
   calls, scripts, CI configuration, cache names, documentation, and any
   generated lock material as one reviewable series.
3. Continue importing `Lean4Lean.*` while the internal namespace is stable.
   This separates dependency adoption from a possible source-wide API break.
4. Run the full Ix build and tests plus at least one end-to-end path that
   exercises the Lean4Ix-produced or verified kernel artifact, not merely
   dependency resolution.
5. Record the paired Lean4Ix and Ix revisions in both roadmaps or release
   notes so the integration can be reproduced.
6. Verify the old compatibility route once, then make the canonical Lean4Ix
   route Ix's default and ensure no undocumented old package or binary use
   remains.

Stop rather than land an Ix change that depends on a mutable checkout,
uncommitted sibling state, an unpinned remote, or a private compatibility
workaround.

**R3 exit:** the pinned Ix revision consumes Lean4Ix canonically and passes its
full build, tests, and end-to-end kernel integration.

#### R4 — make an explicit internal namespace decision

Choose one route only after R3:

- **Route A — retain `Lean4Lean` internally (recommended).** Treat it as the
  stable formalization namespace under the Lean4Ix project identity. Document
  the distinction, whitelist intentional old-name hits, and avoid a broad
  proof diff with no semantic benefit.
- **Route B — migrate modules and namespaces to `Lean4Ix`.** Approve this only
  if a concrete consumer or maintenance benefit outweighs the proof, audit,
  and downstream cost. Treat it as a separate breaking API migration, not
  cleanup bundled into R2 or R3.

If Route B is selected:

1. Move the source tree and root aggregators in dependency order, updating
   imports before declarations and leaves before release roots.
2. Update namespaces, qualified declarations, generated names, string-based
   fixtures, pretty-printer expectations, tests, Lake roots, and Nix module
   discovery. Do not create a second implementation under the new namespace.
3. Regenerate and semantically review audit prefixes, sorry-frontier imports,
   axiom manifests, root-closure snapshots, `#guard_msgs`, and golden files.
   A large name-only diff must not hide a changed trust dependency.
4. Use compatibility import modules only where they are truthful. An import
   shim does not preserve every fully qualified declaration name; document
   unavoidable source changes instead of claiming transparent compatibility.
5. Update Ix imports in a paired change and run both repositories' complete
   gates at each mechanically reviewable slice.

Route B is a major API event. Revert to Route A if it obscures proof changes,
changes axiom reachability beyond the approved name map, requires duplicate
module trees, or cannot be reviewed in dependency-ordered pieces.

**R4 exit:** the chosen namespace policy is explicit, tested by Ix, reflected
in the old-name whitelist, and has no ambiguous half-migrated module surface.

#### R5 — remove compatibility names

Remove old public aliases only after all of these hold:

1. at least one published Ix integration uses only the canonical repository,
   package, Nix, and executable names;
2. two consecutive Lean4Ix checkpoints pass the complete Section 8 gate;
3. the old repository redirect, last compatible tag, and migration note are
   durable and tested;
4. the R0 inventory rerun contains no unclassified old public-name use; and
5. the user explicitly approves compatibility removal.

Delete compatibility aliases in their own change. Preserve historical prose,
schema v1 identifiers, tags, and—if Route A was chosen—the intentional
`Lean4Lean` module namespace.

**R5 exit:** every removed alias has a documented replacement and last
compatible revision, while old published artifacts and links remain
understandable.

#### Rename validation matrix

Run the ordinary Section 8 gate at every phase and add the following identity
checks while the internal namespace remains unchanged:

```text
lake build Lean4Lean Lean4Lean.Theory Lean4Lean.Verify Lean4Lean.Tests
lake build lean4ix lean4lean
lake build Lean4Lean.Experimental
nix build .#lean4ix .#lean4lean .#lake-dependency
nix flake check --accept-flake-config --print-build-logs
git diff --check
```

If Route B is selected, replace canonical library targets with `Lean4Ix.*` and
also build every promised compatibility import. In all routes:

- compare the exact four release-root axiom closures against the baseline
  through the approved declaration-name map;
- run successful and rejected CLI cases through both executable names and
  compare stdout, stderr, exit status, and JSON structurally;
- test the downstream library fixture without relying on the sibling checkout;
- run the pinned Ix build, tests, and end-to-end kernel integration;
- test the canonical URL and old-URL redirect from a clean clone;
- rerun the classified old-name search; and
- inspect produced binary, library, artifact, module, and documentation names
  for phase-consistent identity.

#### Commit sequence, rollback, and kill criteria

Keep the migration reviewable in this order:

1. document and freeze the identity contract, R0 inventory, and baseline;
2. add the dual CLI, package, and Nix compatibility surface;
3. switch repository metadata and public branding;
4. land the paired Ix migration;
5. if approved, land the breaking internal module migration as its own series;
6. after the explicit gate, remove obsolete compatibility aliases.

Preserve the pre-rename theorem checkpoint as a published revision or tag.
When a phase fails, roll back only that phase's identity changes and return to
the last green checkpoint; do not repair rename fallout by altering theorem
statements, proof assumptions, semantics, or trust policy.

Stop and reassess the rename if any phase:

- changes an axiom closure except for the approved declaration-name mapping;
- lets files escape the sorry-frontier or audit-prefix coverage;
- duplicates module implementations or semantic CLI code;
- changes CLI semantics, diagnostics, exit behavior, or JSON without a
  separately versioned contract;
- requires an unpinned or unreproducible Ix dependency;
- cannot provide reliable redirects or truthful compatibility aliases; or
- collides with renewed main-theorem work on the same manifests, modules,
  audit roots, or consumer integration.

The correct response to a kill criterion is to pause or narrow the rename,
never to block or weaken the theorem work.

#### Exit report

Before marking RENAME complete, record in this roadmap:

- the first canonical Lean4Ix revision and release tag;
- the paired Ix revision and its passing integration command;
- the chosen internal namespace route and any alias-removal revision;
- the complete validation-matrix results and exact root-closure comparison;
- the final intentional old-name whitelist; and
- confirmation that the migration changed no theorem meaning, proof premise,
  executable semantics, or trust classification.

## 6. Exact sorry-closure map

| ID | Declaration | Closure route | Class |
|---|---|---|---|
| R1 | `IsDefEqU.sort_inv` | NORM-DI M2/M5/M6 direct adequacy → reflection → accepted public premise | research-dependent |
| R2 | `IsDefEqU.forallE_inv_stratified` | `LRS.PiPathInv.of_adequacy` from the NORM-DI direct contextual theorem | research |
| R3 | `IsDefEqU.sort_forallE_inv` | existing disjointness/reflection after R2 | engineering after research |
| R4 | `IsDefEqU.weakN_iff` forward | SST W4-W8 | research |
| R5 | `NormalEq.parRed` appDF × `.extra` | statement repaired with `PatternArgumentNonFunction` plus local `StructurePatternCompatibility`; prove their generated producers, then use the known transports | engineering; structure producer depends on D4 |
| R6 | `WF.registeredStructureHeadInversion` | statement repaired with `ConstructorHead`; then R4 + `IndTyAppInj` + projection uniqueness | engineering after research |
| V3 | `addDecl.WF`, inductive case | certified checker-run-to-transaction pipeline | engineering, multi-session |
| V4 | `checkPrimitiveDef.WF` | absorb PR #32 or local run certificate | engineering, external watch |
| V5 | `reduceRecursor.WF` | landed exact generated heads/owner recovery/same-head major equality, generic matching and typed unindexed consumer, one-parameter dependent-field transport, concrete six-point σ̂ `ConstInterp`, arbitrary-level whole-rule type/LHS/body/runtime alignment, joint capture/body production from local major injectivity for all three Rose rules, matched-body output translation through trailing arguments, generic nonliteral/constructor-headed `inductiveReduceRec` execution/translation composition, exact public Rose recursor/constructor lookups, concrete main/nil/cons pointwise `reduceRecursor` executions, live `RecM.WF` joins for both Quot gates with early exits closed and fallback state threaded, canonical quotient-inventory recovery, typed `Quot.lift` registered-equation reduction, proof-irrelevant `Quot.ind` reduction, exhaustive quotient translation/`FVarsBelow` semantics conditional on `QuotAppInj`, generic checked-level RHS/FVars preservation, strict selected-major projection, exhaustive live `k = false`/non-structure callback analysis across every expression and literal shape, concrete main and joint auxiliary Rose wrappers with no exact WHNF premise, executable successful-selector inversion into node/nil/cons, branch constructors which discharge all nonsemantic `SelectedBranchWF` fields, and operational factorization of K, Nat/String literal, Quot-gate, and early/late failure branches → supply NORM-DI M4/M5 `IndTyAppInj` at the three live semantic outputs and NORM-M6's `QuotAppInj` producer → compose the resulting node/nil/cons translations through the constructed main and auxiliary success contracts and the factored remaining branches → repair/justify sole open-world constructor-parameter premise | engineering plus NORM-DI, multi-session |

The six Tier F audit entries are deliberate kernel-rejection recoveries and
are not proof debt. The zero-sorry gate reduces the allowlist to exactly those
six and makes any newly sorried supported declaration fail the build.

## 7. Trust and process rules

- No custom axiom may enter Theory. Standard logical axioms are accepted only
  when an exact root closure justifies them.
- Compiler-generated decision certificates are exact-manifested and Verify-only;
  `sorryAx` is confined to the two proof surfaces and governed by the direct
  frontier allowlist. Neither class may enter the shipped library or CLI.
- Error-recovered axiom declarations are allowed only as the six pinned,
  kernel-rejected Theory fixtures and may not justify another release surface.
- Verify-specific implementation equations require a manifest, a pinned Lean
  revision, tests, and absence from Theory roots. Known-false cached-field
  equations are forbidden until replaced by theorems.
- Do not add `[simp]` to a project axiom. The compiled manifest audit rejects
  any globally registered occurrence; consumers name the exact bridge they
  use.
- A runtime success trace may establish computation, never semantic authority.
  Normalized views require `Normalization.WF`; pattern registration requires
  explicit local or global equality evidence.
- No supported root imports `Lean4Lean.Experimental` at a checkpoint.
- Reconcile upstream only at an explicit integration checkpoint. Re-run the
  PR #43/#32/#27 overlap watch at each boundary.
- Preserve exported Theory names additively and keep consumer migrations out
  of this repository.

## 8. Checkpoint gates

Every semantic checkpoint runs, from the pinned Nix development shell:

```text
lake build Lean4Lean.Theory Lean4Lean.Verify
lake build Main Lean4Lean.Audit.SorryFrontier
lake build
lake build Lean4Lean.Experimental
nix build --accept-flake-config .#lean4lean .#lake-dependency
nix flake check --accept-flake-config --print-build-logs
nix fmt --accept-flake-config -- --check flake.nix
git diff --check
```

Additionally:

- new theorem roots have checked `#print axioms` output;
- `rg '^import Lean4Lean.Verify' Lean4Lean/Theory` is empty;
- `rg '^import Lean4Lean.Experimental' Lean4Lean/Theory Lean4Lean/Verify` is
  empty at a supported checkpoint;
- the frontier audit is exact in both directions;
- changed inductive/projection behavior passes the relevant kernel
  differential fixtures;
- no temporary source/view path remains semantically live beside its
  replacement; and
- the committed checkpoint, not an earlier intermediate tree, is the revision
  whose gates and publication hash are recorded.

Publish only a committed green checkpoint. The active publication bookmark is
`jcb/formalization3`; if it is replaced, update the status table and keep the
old checkpoint recoverable.

## 9. Planning hygiene

`plans/roadmap.md` is the sole tracked plan. Keep it forward-looking:

- completed work is reduced to the status/foundation summary;
- failed routes become short constraints in the owning open work package;
- detailed execution transcripts live in commit messages and git history;
- durable semantic divergences live in `upstream-divergence.md` plus the
  compact removal conditions above; and
- local probes may remain under `plans/probes/`, but they do not define
  roadmap status.

When an active work package changes dependencies, update this file in the
same checkpoint. Do not create another permanent side-plan; put temporary
notes under ignored `plans/` paths and delete them when the decision lands.
