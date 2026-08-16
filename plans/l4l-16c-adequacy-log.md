# L4L-16C adequacy attempt log

This file preserves the working-notes narrative that accumulated in
`plans/roadmap.md`'s L4L-16 ladder entry between 2026-08-12 and
2026-08-13, moved here when the 2026-08-13 audit re-cut the milestone
(`plans/l4l-16-completion-plan.md`). It is a historical record of the
repair sequence at the adequacy iota leaf — valuable precisely because it
documents the repeated erased-type-alignment discoveries that motivated
the O1/O2/O3 decomposition — and is not status-bearing.

## Original L4L-16A bullet (roadmap, as of 2026-08-13 04:32)

*L4L-16A — bridge interface and judgment translation.* Largely
implemented in the uncommitted working copy (audited 2026-08-12): the
SExpr `Params` class is proof-carrying (`extra_pat` deleted), the
five-field `Params.Semantic` bridge interface
(`structureEta`/`ctor`/`defn`/`registered`/`iotaSite`) packages the
environment-specific obligations, `VEnv.IsDefEqStrong.mkS` translates
the current Theory judgment — including `IsDefEq.structEta` — at
`[propext, Quot.sound]`, `IsDefEqStrong.defeq` and `Params.ctor_ty` are
proved, and `VEnv.IsDefEqU.sort_invS` states the endpoint with no
project axiom. The remaining L4L-16A cleanup is complete in the working
copy: `Experimental/UniqueTyping.lean` now exposes only the valid strong
sort-uniqueness compatibility theorem, while the four pre-broken,
unreferenced prototypes are explicit import-compatible parked stubs.

(Correction recorded at the 16B′ checkpoint: `Params.Semantic` has six
fields — the bullet above omitted `iotaRule`.)

## Original L4L-16B bullet

*L4L-16B — SExpr infrastructure closure.* Discharge the remaining
SExpr-side admissions, which are no longer
`strong`/`defeq`/`ctor_ty` but: substitution (`IsDefEqLift.subst`),
reduction/typing soundness (`WHRedS.defeq`,
`InferType.hasType`/`whRed`, `InferTypeS.hasType`, the `.extra` cases
of `WHRed.subst`/`weakU_inv`), `CRDefEq.trans`, and `ShapeLogRel`'s
`Shape.WF.plift`, whose `stop` tactic must become a proof or an
explicit sorry. The generic substitution-container repair is
kernel-checked in the working copy: `Ctx.Subst.lift_r`, `lift`, `id`, and
`one` now take the weakening/variable operations they actually require,
and `Ctx.SubstEq.ofLift` supplies the binder-stable equality embedding.
The under-specified `NormalEq.appDF` constructor now carries equality of
its two instantiated codomains; this makes the application cases of
`NormalEq.symm` and `NormalEq.weak'` kernel-checked rather than opaque
transports. `CRDefEq.trans` and the remaining reduction/typing admissions
are still open.
The live stratified-S `mono`, `to_core`, and `isType` admissions are also
discharged. Same-substitution `IsDefEq.subst`, heterogeneous
`IsDefEqStrong.substCongr`/`subst`, and context conversion
`Lookup.defeqDF_l'`/`IsDefEq.defeqDF_l'` are now kernel-checked. The
three-way substitution interface is `Ctx.SubstEq`, and `LRS.PiInstDefEq`
retains both the semantic codomain edge and its raw SExpr congruence.
`Ctx.Subst.imp` now transports substitution evidence, and a genuinely
typed substitution transports an entire proof-carrying
`Pattern.Action`; consequently `WHRed.subst` and `WHRedS.subst`, including
the generated-rule `.extra` branch, are kernel-checked under the narrowed
SExpr-typing premise. `SExpr.SpineDefEq` now records a dependently typed
pointwise equality between two application spines, with checked head
congruence, left-spine projection, and reflexive construction from
`SpineWF`; this is the raw alignment layer needed by the paired generated
RHS certificate.
`IsDefEqLift.subst` remains open because its old polymorphic
`Ctx.Subst HasType` premise permits an arbitrary `HasType` relation and is
therefore not a sound theorem statement; narrow that interface to lifted
SExpr typings before proving it.

(Corrections recorded at the 16B′ checkpoint: the `Shape.WF.plift`
"`stop` tactic" claim was stale — the whole prototype was inside a block
comment, never elaborated, with zero consumers; and `WHRed.subst`'s
`.extra` case was already kernel-checked, only `weakU_inv`'s remained.)

## Original L4L-16C bullet — the attempt history

*L4L-16C — constant adequacy.* Close the `LR.adequacy` constant
branch: the definition-body evaluation route is token-closed but leans
on the circular `hDef` premise noted below, and one admission remains
at the reached pattern leaf. The structural `Const.lam` recursion is
now kernel-checked: it transports the related application spine and Pi
edge into `LR.constDefEq`, which discharges every semantic
`bot`/`lam`/`ctor`/`indTy` case and follows the well-founded `R` child.
The working copy now
makes the local evidence boundary finite and uniform: `Pattern.Action`
bundles membership, the exact match/captures, discharged checks, and the
concrete local equality; `IsDefEqStrong.extra`, `WHRed.extra`, and
`ParRed.extra` all consume that one certificate, its weakening transport
is proved once, and both semantic soundness and adequacy consume it without
recovering soundness from membership. The zero-arity definition bridge
constructs an `Action` explicitly. The first half of the nonzero leaf
contract is also kernel-checked: `LRS.CaptureDefEq`,
`LE_Interp.Matches.varN_materialize`, and
`LE_Interp.Matches.iota_materialize_exact` turn exact related recursor and
constructor spines into the two concrete `MatchesS` witnesses, retain a
typed logical-relation witness for every capture, and lift major-premise
reductions under the recursor spine. The iota lemma deliberately keeps
recursor captures at depth `n+1` and constructor fields at depth `n`.
The transport-aware closure API is now kernel-checked as
`LRS.CtorDefEq.Algebra`/`fold`: its `.unlift` handler receives the already
folded high-level result, making pointwise projection of arbitrary refined
fields unavailable by construction. The evaluator now also carries the
invariant that its accumulated related spine is nonempty. The checked
`LE_Interp.Matches.iota_of_pat_nonempty` inversion excludes definition
patterns at the leaf, and `LR.PatternLeafDefEq`/`LR.IotaLeafDefEq` name the
exact boundary with a checked adapter between them. `LR.DefEq.ctor'_inv`
now uses the iota constructor's `.ctor` classification to rule out the
eta-collapse branch of `WShape.ctor'` and exposes the exact
`LRS.CtorDefEq` witness needed by the fold. Thus the remaining admission is
no longer polymorphic over definitions and iota rules: it is exactly the
iota leaf, whose finite contraction and generated-RHS congruence are now
separate obligations. A subsequent interface audit found that the former four
`Params.Semantic` fields could not recover a certified nonzero rule, its
checks, or a typed local action from an arbitrary `Params.Pat` witness.
The former provisional `iotaAction` obligation has now been replaced in
the working copy by the evidence-rich `iotaSite` contract.  Its
`Pattern.IotaTyping` input retains the typed recursor and constructor
spines (with the exact constructor levels), while
`Pattern.IotaReductionSite` exposes the registered tower, typed capture
spine, beta collapse, checks, and RHS computation.  The generic
`IotaReductionSite.action` construction applies the registered equation
along that spine, so the bridge no longer returns a contraction oracle or
any logical-relation conclusion. Every
SExpr now also has a chosen well-formed Theory representative
(`SExpr.reify`), semantic pattern matches reify to exact Theory matches, and
RHS application commutes with that representation. `LR.constDefEq` carries
the accumulated raw equality and result-type validity down to the leaf.
Finally, `LR.iotaActions_of_exact` conditionally combines exact related recursor and
constructor spines with that bridge to construct both concrete actions,
pointwise capture relations, and both full weak-head reduction paths to the
instantiated RHSs.  The fold-facing form is now kernel-checked without a
canonical-relation assumption: `LRS.CaptureDefEqAt`,
`LE_Interp.Matches.varN_materializeAt`,
`LE_Interp.Matches.iota_materialize_exactAt`, and
`LR.iotaActions_of_exactAt` keep constructor captures in an arbitrary `IH`
and recursor captures in `LRS IH`; the older existential-depth theorems are
wrappers over that adjacent-level API.  `LRS.IotaRHSDefEq` names the
intended evidence-only congruence boundary for the fold. A second
interface audit pins the missing live premise:
semantic `MatchesS` erases the constructor levels, while
`BlockGenerationChecked.pat_wf` requires the rule-instantiated constructor
levels and typed recursor, constructor, and capture spines. Bare SExpr
self-typing cannot recover those data without application/type inversion.
The accumulator now carries `SExpr.SpineWF` certificates for both recursor
applications, and `LRS.CtorDefEq.exact` retains both typed constructor
spines and their head typings through the transport-aware fold. A leaf
audit now shows that the provisional `LRS.IotaRHSDefEq` statement still
erases one essential fact: at a variable RHS leaf the capture witness has
its own existential SExpr type, but the contract supplies no alignment
between that type and the whole RHS equality's type. Weak type uniqueness
cannot manufacture that alignment before L4L-17. The next local boundary
is therefore to retain a typed RHS/capture alignment witness in the
reduction site (or equivalently narrow the congruence contract). The raw
dependent-spine half of that boundary is now `SExpr.SpineDefEq`; the next
step is to retain the ordered generated capture paths and their exact
codomain/semantic alignment.  The transport core for that continuation is
now kernel-checked: `LRS.DefEq.app` is polymorphic in the predecessor
relation, `LogRel.LiftEquiv` packages the two fold transport laws, its
`trans` and base-origin-only `cancelRight` operations compose/cancel those
laws without projecting arbitrary high refinements, and `succ` transports
the package through one `LRS` layer.  Capture and constructor-argument
witnesses rebase through the same package.  The accumulator now packages
its final application as `LR.PatternLeafSpine`: the raw last-Pi
certificate, the major's logical relation at that exact domain, the
remaining recursor arguments, and the semantic Pi edge are one dependent
witness.  This package is threaded through every recursive
`LR.constDefEq` lambda layer, and the focused adequacy target is green with
that stronger invariant.  A fold audit then exposed the remaining
non-root gap: `LRS.CtorDefEq.trans` deliberately erases the SExpr type of
its midpoint, so two exact constructor leaves can carry unrelated
existential field types even when their shared midpoint syntax agrees.
Neither the aligned capture relation nor the generated-RHS application
chain can compose those leaves without a type alignment, and the current
coarse `LRS.TyDefEq.indTy` supplies only two `IndTyHead` witnesses.
Retrying the rejected type-indexed `CtorDefEq` encoding merely moves the
same issue to untyped weak-head subject expansion.  The next repair must
therefore retain a composable canonical field-type alignment in exact
constructor observations (derived from the live constructor certificate),
or explicitly promote the required limited uniqueness lemma from L4L-17;
it must not manufacture the midpoint type.  Once that boundary is
kernel-checked, construct the repaired contract over `LE_Interp.recR`,
instantiate `LRS.CtorDefEq.fold`, close the leaf, and replace the circular
constant `hDef` premise with its live-environment construction. The
accumulator typing currently inherits the
open L4L-16B `WHRedS.defeq` obligation; `IsDefEq.subst` itself is now
kernel-checked. The
continuation's `.unlift` case must
lower the whole result; arbitrary high-level field refinements cannot be
projected pointwise without reviving the rejected `Shape.WF.plift`
principle.

(Correction recorded at the 16B′ checkpoint: the `hDef` premise is a
field of `IsDefEqStrong.const` discharged by `mkS` from
`Params.Semantic.defn`; its live construction is the 16D `defn` field,
not separate 16C work.)

**Joint normalization audit, 2026-08-13.** The limited-uniqueness
implementation split cleanly into global `RawTypeUniq` plus the one
successor-only, term-indexed `LimitedUniq.LamRetype` case; the earlier claim
that a generic assumption-free `Retype` handled lambdas was false.
`PiTypeAlign` remains only an optional sufficient adapter, not a builder
assumption, and `JointBuilder.succ` explicitly consumes lower adequacy. The exact-leaf
audit also found that `CtorExact` had not related its two universe-level
lists. Both construction sites already pass one list, so the certificate now
stores `ls = ls'`. A native leaf can therefore export an ordinary typed
equality. `CtorPath.foldRaw` retypes every link at one externally chosen
domain and threads the right endpoint typing through the path;
`CtorChain.foldRaw` and `CtorDefEq.foldRaw` add exactly two root-view typing
callbacks. Their measured closure is
`[propext, Classical.choice, Quot.sound]`, as is the native exact iota
handler. Thus intermediate links are no longer implicated in
`WHRedS.defeq`; only arbitrary weak-head expansion at the two roots remains.

A later consumer audit found one further separation: a framed exact iota
handler runs at its native relation, while the recursor prefix and result
typing remain at the canonical root relation. Arbitrary high extensions of a
common lower relation agree only on lifted lower shapes, so the root prefix
cannot be projected through a general `unlift` frame. Constant evaluation now
returns a synchronized `LogRel.DefEqRect` containing both endpoint
self-relations and the cross-relation. The open semantic consumer is
therefore the generated fixed-head application chain at the canonical root;
native normalization remains responsible for raw constructor/capture
materialization, not for transporting that root prefix.

The same audit invalidated the claim that O3 could be built independently
from `LE_Interp.recR`. The existing `IotaRHSDefEq` inputs do not contain the
fixed RHS head's logical validity or the intermediate semantic Pi telescope.
Those facts must be carried by the surrounding semantic-`R` induction; they
cannot be reconstructed from raw `PathSpineWF` and final result validity.
The syntactic half is now discharged without a new bridge field:
`Params.Semantic.closedHasTypeStrong` reifies any semantic level list,
instantiates and weakens an ordered-environment closed Theory typing, and
translates it back to SExpr. `Pattern.IotaRule.rhsStrong` applies it to the
registered fixed RHS. Both declarations measure at
`[propext, Classical.choice, Quot.sound]`; only logical head adequacy and the
semantic Pi application chain remain for the repaired O3 contract.

**Heterogeneous-transitivity retirement, 2026-08-13.** The raw and strong
SExpr `trans'` constructors are now gone. `SpineWF` and `SpineDefEq`
concatenate conversion-aware spines without composing conversions whose sort
indices may differ. The only downstream semantic use was successor
`TyDefEq.trans` at Pi shape; its domain and codomain equalities now use
nonempty `TypeDefEqPath`s. Paths reverse, concatenate, transport judgments,
and convert binder contexts one individually typed edge at a time. Once
`RawTypeUniq` is available, `TypeDefEqPath.collapse` aligns each shared
endpoint's two universe assignments and recovers one ordinary equality.
`ContextualRawTypeUniq` and `LR.ContextualJointBuilder` expose exactly the
well-formed-context package needed to repeat that collapse under a Pi binder;
`forallE_whRed_l_of_adequacy_collapsed` and
`forallE_inv_of_adequacy_collapsed` check the complete handoff. The full
`ShapeLogRelAdequacy` target is green. Path operations and collapse audit at
`[propext, Quot.sound]`; path-valued/collapsed adequacy inversion and the new
weak-to-strong reflection bridge stay within
`[propext, Classical.choice, Quot.sound]`. No `sorryAx` is introduced by this
retirement. The sole adequacy admission remains the iota leaf and now has a
sharper implementation constraint: its constant evaluator must retain the
abstract semantic `R` proof so `LE_Interp.recR` can supply fixed-head logical
adequacy, rather than first erasing provenance through `Const.mono`.

**Proof-relevant recursion refinement (2026-08-13).** Fixed-head
self-validity has two semantic inputs, but pairing two proof-indexed
`LE_Interp` recursors does not retain evaluator provenance: `LE_Interp` is a
`Prop`, so proof irrelevance identifies derivations that selected different
constant relations. Focused elaboration probes additionally showed the
binary homogeneous predicate cannot simultaneously support conversion to an
arbitrary displayed type and the term/type role swap at application. Thus
`recRDeep₂` remains correct only for proof-independent consumers and is not
the leaf's evaluator recursion principle.

The repaired boundary is `LE_Interp.Witness`, a proof-relevant mirror chosen
from every public interpretation. Its constant case stores one relation and
the matching `R → Witness` callback; `Witness.recR` follows exactly those
edges, `Witness.mono` preserves the chosen tree, and
`Lower.realizeWitness` converts a lower evaluator result back through the
same callback. The complete witness/forgetful layer kernel-checks and audits
at `[propext, Classical.choice, Quot.sound]`. The adequacy constant branch now
destructs the chosen witness directly. Fixed RHS selection is packaged by
`RHS.fixedWitness` and `fixedLowerWitness`; `Witness.closed` preserves the
chosen tree while changing valuations for closed registered heads;
`Witness.mono_l` preserves it under valuation growth; `Witness.recDeep`
supplies exact hypotheses for every ordinary/type/registered child;
`Witness.recDeep₂` nests two such trees while keeping first-side hypotheses
polymorphic in the second, which covers the application term/type role swap;
and
`IotaRHSDefEq.of_nonbotWitness` delivers that exact head witness to the
nonbottom generated-chain callback. These additions also audit at the clean
baseline. The retained proof tree now also has a kernel-checked compatible
merge: `RDeepChildren.JoinLaws` makes bottom, root lowering, valuation growth,
and exact recursive-result join explicit, and proof-relevant `compat_join`
keeps the chosen joined constant callback synchronized with its retained
tree. Binder saturation and generic self-typing are now closed as well:
`RDeepChildren.Laws`, `TypedRDeep.lam`, and `TypedRDeep.forallE` retain the
package under binders; Nat-first `recNatRDeep`/`recNatRDeep₂` make conversion
restart only after a strict stratification-depth decrease; and
`FitsRDeep`/`SoundRDeepAt`/`soundRDeepRestart`/`recNatRDeepSound` compile the
full application, lambda, Pi, and conversion induction. The next leaf step
is therefore only the consumer-specific fixed-head `buildP` application-chain
algebra; `DefEqRect` continues to provide the structural transports for its
proof-independent result.

## Roadmap 16C′ narrative moved here (2026-08-14 cleanup)

Moved verbatim from the roadmap ladder bullet per completion-plan
guardrail #4 (roadmap is status, not lab notebook). This is the
chronological continuation of the entries above; overlap with the
completion plan's design sections is intentional.

**Progress, 2026-08-13:** step (1)'s
interfaces are kernel-checked: `LR.AdequacyAt`, `LR.JointStage`, and
the corrected offset `LR.JointBuilder` validate the level dependency;
the initial same-level `uniqOfAdequacy` draft was rejected because bottom
shapes erase typing evidence and it omitted target-context validity. The
public Pi/sort
inversions factor through level-indexed adequacy; and `mk` reflection
is fixed at `VEnv.EqUpToLevels` (not false syntactic injectivity).
Step (2) is also kernel-checked: native exact `CtorLink`s carry unary
root frames, nonempty `CtorPath`s concatenate through classified-spine
determinism, and `CtorDefEq.toChain` covers every free-closure
constructor with a proved round trip. A three-operation
`CtorChain.Algebra` now exposes only native exact leaves, composition,
and root anchoring to the eventual uniqueness-aware consumer;
`CtorChain.NativeAlgebra` makes the well-founded order explicit by
completing each native leaf, folding its transport frame back to the
root, and only then composing at the root with predecessor uniqueness.
Thus `unlift` never requests uniqueness for arbitrary high-level fields.
A later consumer audit clarified that this order normalizes constructor
evidence but does not alone close iota: the exact handler's native relation
cannot consume the canonical-root recursor prefix through an arbitrary
lift/unlift zigzag. Such a zigzag agrees only on lifted lower shapes, not on
unrelated high refinements.
The subsequent raw audit found and fixed one omitted invariant:
`CtorExact` now records equality of the two constructor universe-level
lists (both live producers already supplied the same list). Native leaves
therefore expose an ordinary typed equality. `CtorPath.foldRaw`,
`CtorChain.foldRaw`, and the `CtorDefEq.foldRaw` adapter retype and compose
every native edge at one recursor domain using `RawTypeUniq`; their axiom
closures are exactly `[propext, Classical.choice, Quot.sound]`. The two
root `CtorView`s are explicit subject-reduction callbacks, not hidden in
normalization. The native exact iota theorem is independently measured
clean. The callbacks were subsequently discharged from
`JointStratifiedInversion`, as recorded below.
The step
(3) spike resolved its
open q1 negatively: `InferType.app` needs an actual weak-head reduction
from the inferred function type to a Pi, while a weak conversion supplies
only definitional equality; deriving the former is Church–Rosser-strength.
The same audit rejected treating `IotaRHSDefEq` as route-independent:
`PathSpineWF` alone does not provide the fixed RHS head's logical validity
or the intermediate semantic Pi telescope. That evidence must be an
induction hypothesis of the surrounding `LE_Interp.recR` construction.
Its syntactic typing is no longer missing:
`Params.Semantic.closedHasTypeStrong` reifies the semantic level list,
strengthens the ordered-environment Theory typing, and translates it back;
`Pattern.IotaRule.rhsStrong` specializes this to the registered RHS, with
the clean standard axiom closure.
The heterogeneous raw/strong `trans'` constructors have also been removed
rather than treated as an interim oracle. Conversion-aware spines now
append structurally, and successor Pi type validity retains a nonempty
`TypeDefEqPath` of ordinary typed equalities. `TyDefEq.trans` concatenates
those paths; `TypeDefEqPath.collapse` consumes `RawTypeUniq` only at the
promotion boundary. `LogRel.ContextualRawTypeUniq` plus
`LR.ContextualJointBuilder` provide the well-formed extended-context form,
and the level-indexed `_collapsed` Pi-inversion adapters kernel-check the
domain/codomain handoff. The full adequacy target remains green; path
operations/collapse audit at `[propext, Quot.sound]`, while reflection and
adequacy inversion remain at the standard
`[propext, Classical.choice, Quot.sound]` baseline.
A subsequent recursion-boundary probe rejected the shallow `RChildren`
contract: symmetry and transitivity transport the current semantic proof
but not its `R`-child induction hypotheses.  `LE_Interp.RDeepChildren` and
`LE_Interp.recRDeep` now kernel-check the corrected lexicographic interface:
ordinary semantic children retain provenance, while abstract constant
edges additionally receive the full recursive hypothesis.  The matching
`HasTypeStratifiedS.forallE_inv` exposes strictly shallower domain/codomain
typings.  This also found and fixed a context-order bug in the joint tower:
contextuality now lives inside every `JointStage`; it is no longer a wrapper
around fixed-context builders, which could not enter `A :: Γ` while proving
uniqueness.  These declarations audit at the standard clean baseline.
The full syntactic consumer is now complete too:
`JointStratifiedInversion` packages the exact sort/Pi observations and
`IsDefEq.uniq_of_stratified_inversion` derives contextual raw uniqueness by
well-founded induction on stratified typing depth.  It then proves
`WHRed(S).defeq_of_stratified_inversion`; the beta and registered-step cases
are no longer open.  `CtorDefEq.foldRaw_of_jointBuilder` supplies both root
callbacks and derived uniqueness to the normalized chain.  All audit at
`[propext, Classical.choice, Quot.sound]`.  The base bootstrap is complete:
positive adequacy transports sort/Pi observations across heterogeneous
`TypeDefEqPath`s, derives stratified path uniqueness, and only then collapses
the paths.  Contextual raw uniqueness and direct stratified inversion now
follow from level-one adequacy, so `JointBuilder.invZero` has been deleted.
The merged milestone has also replaced the over-strong successor
`PiTypeAlign` requirement with exact, term-indexed `LamRetype`, made lower
adequacy an explicit input to `JointBuilder.succ`, and changed constant
evaluation to return synchronized `LogRel.DefEqRect`s (both endpoint
self-relations plus the cross-relation). The remaining step is the
canonical-root application-chain proof for the fixed iota head, followed
by the semantic leaf fold. A focused probe rejected the initially paired
proof-indexed recursion boundary: because `LE_Interp` is a proposition,
proof irrelevance erases which abstract constant relation an evaluator
chose, and the homogeneous pair also cannot cover both conversion and the
application term/type role swap. `LE_Interp.Witness` now supplies the
proof-relevant internal tree, with exact constant callbacks, monotonicity,
index-only recursion, and lower-result realization; forgetting it recovers
the public interpretation. The layer kernel-checks at
`[propext, Classical.choice, Quot.sound]`. `recRDeep₂` is retained only for
proof-independent consumers. The chosen witness is now threaded through
the live adequacy constant case: downward-closed fixed RHS selection,
valuation/closed transport, unary and binary proof-relevant child
recursion (including term/type role swaps), and the witness-aware
nonbottom iota adapter all kernel-check at the same
baseline. The retained-tree transport layer now also covers predicate
mapping, syntactic lift/weakening, substitution/instantiation, and exact
Pi/lambda inversion.  A proof-relevant `TypedRDeep` package has been
kernel-checked through dependent application and forgets back to the
existing `InterpTyped`; this proves that application introduces no fresh
semantic recursion edge.  The finite compatible join used by
lambda/forall saturation is now kernel-checked as well:
`RDeepChildren.JoinLaws` exposes bottom, root lowering, valuation growth,
and exact recursive-result join, while proof-relevant `compat_join`
synchronizes the selected joined witness with its retained tree (including
the constant evaluator callback).  These declarations audit at
`[propext, Classical.choice, Quot.sound]`. Binder-compatible saturation is
now complete too: `RDeepChildren.Laws`, `TypedRDeep.lam`, and
`TypedRDeep.forallE` retain exact trees through weakening and both binders.
Conversion forced the correct lexicographic order; the new Nat-first
`recNatRDeep`/`recNatRDeep₂` permit an arbitrary witness restart only after
the stratification depth falls. `FitsRDeep`, `SoundRDeepAt`,
`soundRDeepRestart`, and `recNatRDeepSound` then kernel-check the entire
syntax-directed retained-typing induction, including conversion, at the
same baseline. The remaining proof body is the consumer-specific `buildP`
algebra that produces the fixed-head logical application chain. Its core
dependent-application handoff is now factored as the admission-free
`LR.adequateApp`: exact function, argument, and instantiated-result
callbacks close the full shape join at
`[propext, Classical.choice, Quot.sound]`, and the retained self-typing
probe reuses it without another evaluator assumption. The remaining
consumer work is the conversion/type-relation handoff and constant case,
followed by `of_nonbotWitnessResult` and the semantic leaf fold. The sole
adequacy admission remains open until that fold lands.
