# L4L-16 sort-inversion route decision

Date: 2026-08-12

Status: route selected and prerequisite interface landed. The post-v4.33
spike selected the semantic route; L4L-18B completed its prerequisite
proof-carrying extension interface on 2026-08-12, so L4L-16 is now active.
This note does not weaken the theorem, add an assumption, or change the
accepted trust closure.

## Gate theorem

The only proof gate for this milestone is the existing live statement in
`Theory/Typing/Injectivity.lean`:

```lean
theorem VEnv.IsDefEqU.sort_inv
    (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v
```

The current declaration is still admitted.  It is one of the 16 proof-debt
declarations in `Audit/SorryFrontier.lean`; therefore the compiled allowlist
remains at 22 entries (16 proof declarations plus six deliberately rejected
kernel fixtures).

The accepted exit closure is the ordinary Theory baseline only: any subset
of `propext`, `Classical.choice`, and `Quot.sound`.  In particular,
`sorryAx`, a generated environment oracle, or a project-specific pattern
axiom is not an acceptable bridge.

## Route 1: shape logical relation

Decision: retain this as the technically credible long-term route, but do
not merge the fetched experimental branch as an L4L-16 proof.

The semantic idea is validated by the completed companion development
`domain-semantics-lean`: finite shape approximations prove definitional
inversion in the presence of non-normalizing fixed points and eta.  The
lean4lean `logrel` branch is an earlier version extended with constants and
rewrite patterns.  Its endpoint theorem is the right shape, but its live
closure is not acceptable:

```text
Lean4Lean.SExpr.sort_inv
  [propext, sorryAx, Classical.choice, Quot.sound,
   Lean4Lean.SExpr.Params.extra_pat]
```

The post-sync closure was reproduced by building
`Lean4Lean.Experimental.UniqueTyping` and printing the dependencies.  The
remaining assumptions on the path are concrete:

1. `SExpr.IsDefEq.strong` is admitted.  Its constructor case needs the
   classification/type bridge below.
2. `SExpr.IsDefEqStrong.defeq` is admitted.
3. `Params.ctor_ty` is admitted; the current `Params` classification has no
   proved connection from a constructor classification to the translated
   constant type required by `CtorBundle`.
4. `LR.adequacy` has one live admitted branch: constant adequacy.
5. `Params.extra_pat` is a project axiom rather than a class field or a
   derived environment theorem.
6. The unmerged VExpr-to-SExpr bridge from PR 37 translates the pre-eta
   equality judgment only.  It predates the live `IsDefEq.structEta`
   constructor and therefore is not exhaustive for the current Theory
   judgment.
7. The current pattern contract cannot be instantiated by a live `VEnv.WF`.
   `extra_pat` asks for a syntactic `Matches` proof for `df.lhs`, while
   generated iota and quotient equations are registered as closed lambda
   towers.  Their useful pattern appears only after a typed beta collapse.
   `CertifiedExtension.covers` and `IsDefEq.appN_lamN` record the needed
   spine-level fact, but they intentionally do not manufacture a global
   `Params` instance.
8. A global environment bridge must cover definitions, mutual definitions,
   quotient rules, ordinary and block inductives, nested inductives, and the
   registered structure-eta capability.  The current block-local assembler
   covers one certified block plus explicitly certified extensions; it is
   not that global bridge.

Items 5 and 7 are exactly the interface decision assigned to L4L-18B.
Nested-rule transport and the missing current-judgment coverage overlap the
later L4L-19 work.  Pulling them into L4L-16 would not be a focused promotion
of a completed experimental proof; it would be the extension-interface and
consumer-bridge redesign themselves.

## Route 2: live stratified derivations

Decision: discard this as the L4L-16 implementation route.

The live `Strong.lean` development is complete through strong translation,
stratification, weakening, substitution, and type-shape recovery.  The
remaining obstruction is not bookkeeping in the final sort case:

1. A converted typing of a sort can have an arbitrary syntactic intermediate
   type (for example, an application reducing to a sort).  A proof specialized
   only to sort syntax must therefore establish uniqueness for that arbitrary
   middle term.
2. In the application case, the same function can be typed at two candidate
   Pi types.  Aligning the result universes requires Pi--Pi injectivity for
   those function types; equality of their outer `imax` levels is not enough
   to recover the codomain levels.
3. The live stratified uniqueness proof consequently calls
   `forallE_inv_stratified` in its application case and `sort_inv` throughout
   its conversion cases.  Those are the first two public admissions in
   `Injectivity.lean`, not smaller lemmas hidden behind the current theorem.
4. The explicit level-indexed prototype reaches the same boundary at
   `Experimental/Stronger.lean`: `IsDefEqStrong.sort_invL` is proved, but
   `IsDefEqStrong.uniqL'` stops in its application case with the note that it
   needs unique typing.

A bounded mutual induction does not remove this dependency.  It must prove
sort inversion, Pi--Pi injectivity, and type uniqueness together.  That
absorbs the central L4L-17 theorem into L4L-16 rather than completing the
advertised sort-only route.  The current ordering, in which L4L-17 builds on
`sort_inv`, is therefore circular for route 2.

## Checked non-routes

- The current Church--Rosser development is not an independent escape hatch.
  It imports `UniqueTyping`, consumes the same sort/Pi inversion frontier,
  and still has the two `NormalEq.parRed` admissions assigned to L4L-18A.
- No completed proof exists on the fetched upstream `logrel` branch, the
  current public upstream branches, or the argumentcomputer development
  branch.  The VExpr translation branch deliberately leaves construction of
  `Params` and constant adequacy open.
- The completed companion semantic formalization validates the mathematical
  route, but its calculus has fixed points and closed type formers rather
  than lean4lean's declaration-indexed constants, generated equations, and
  registered structure eta.  It is not a theorem that can be imported as the
  missing environment bridge.

## Required decision to resume

One prerequisite ordering must change before implementation can resume:

1. **Semantic route (recommended):** move the `Params`/beta-collapsed
   extension contract and the live-environment semantic bridge ahead of the
   L4L-16 exit, including a current `structEta` soundness case; then finish
   constant adequacy and promote only the resulting accepted-closure proof.
2. **Joint inversion route:** explicitly merge the L4L-16 and L4L-17 research
   gates and implement sort inversion, Pi injectivity/discrimination, and
   unique typing as one mutually founded development.

Until one of those scopes is approved, the honest repository state is the
unchanged public `sorry`, unchanged exact allowlist, and this blocked route
decision.  Replacing the gap with `Params.extra_pat`, another generated
oracle, or a theorem whose closure still contains `sorryAx` is forbidden.

## Resolution (2026-08-12)

Option 1 is adopted, with an independence rider: the metatheory ladder is
reordered to land L4L-18B first, and every upstream-coordination gate is
removed from the roadmap.  The `Params`/beta-collapsed extension interface
is a fork-owned decision; it ships with a design note plus a
divergence-ledger row when implemented, and upstream engagement
consolidates in the L4L-20C PR series.  The new execution order is
L4L-18B (extension contract and pattern interface), then the re-scoped
L4L-16 (live-environment semantic bridge with registered structure eta,
current-judgment VExpr-to-SExpr translation, the SExpr admissions and
constant adequacy, and promotion of the public `sort_inv` closure out of
`Experimental/`), then L4L-17 (remaining inversion/uniqueness statements,
now including `registeredStructureHeadInversion`), then L4L-18A against
the redesigned interface.  The joint L4L-16/L4L-17 merge was declined: on
the semantic route the inversion statements arrive from one adequacy
development, so the milestone split is no longer circular.

L4L-18B subsequently removed `pat_wf` and `extra_pat` from Theory's `Params`,
made each operational pattern step carry its exact local equality, introduced
the explicit `Params.Extension.join` Church--Rosser obligation, and proved
beta-collapsed coverage for generated iota rules and `quotDefEq` (design note
`plans/l4l-18b-extension-interface-design.md`, ledger D020). The remaining
work in this record is therefore the live semantic environment instance,
current-judgment translation, adequacy, and public theorem promotion assigned
to L4L-16.

## Second resolution (2026-08-13): joint L4L-16/17 route adopted

The L4L-16C leaf work produced a complete impossibility map
(`plans/l4l-16-completion-plan.md`): eliminating the
constructor-observation free closure for higher-order (lam-shaped)
constructor fields requires typed-equality transport across a shared
endpoint — weak heterogeneous transitivity, i.e. exactly the
uniqueness-strength frontier — in every branch (semantic composition,
raw composition, per-link typed sites, telescope descent), while
first-order fields compose with machinery available today. Two exits
were presented: stage the claim to first-order-constructor
environments (lifting at L4L-17), or adopt this note's previously
declined Option 2 and merge the L4L-16/L4L-17 research gates into one
mutually founded development.

John chose the joint route (2026-08-13). Consequences:

- The ladder keeps the L4L-16 identifier; L4L-17's statements
  (`forallE_inv_stratified`, `sort_forallE_inv`, `weakN_iff`,
  `registeredStructureHeadInversion`, the reflection decision, and the
  weak-judgment uniqueness scope retired from
  `Experimental/UniqueTyping.lean`) become co-deliverables of the
  joint development rather than a successor milestone.
- The circularity objection that rejected Option 2 in the original
  spike applied to the *live stratified* route (Route 2), where
  uniqueness had to be assumed to prove sort inversion syntactically.
  On the semantic route the shape-level stratification gives the
  candidate well-founded structure: the joint induction co-proves
  adequacy and a level-indexed limited uniqueness, each level's
  uniqueness derived from adequacy at that level and consumed by
  adequacy one level up (the lam-field composition). Designing that
  mutual induction precisely — including the level-indexed statements
  of the SExpr-side inversion lemmas, which are currently stated only
  at the top — is the first task of the joint development.
- Work that is route-independent proceeds unchanged: the chain
  normalization (`CtorLink`/`CtorChain`/`toChain`), the InferType
  principal-types bootstrap for the root sites, O3's `LE_Interp.recR`
  argument, and the 16D instance ladder.
- Publication holds until the joint leaf closes (John, same date).

### Joint-interface checkpoint (2026-08-13)

The first two implementation dependencies are now kernel-checked.
`LR.AdequacyAt`, `LR.JointStage`, and `LR.JointBuilder` make the corrected
offset recursion explicit, while `LogRel.LimitedUniq` states the exact
same-term/same-shape retyping contract consumed by constructor-field
composition. The first interface draft incorrectly claimed that arbitrary
same-level adequacy implied this weak-judgment contract: bottom shapes erase
typing evidence, and the target context was not required to be well formed.
The checked replacement carries target-context validity, proves levels zero
and one by specialized base arguments, derives level-zero alignment from the
positive level-one observations, and only then iterates uniqueness at `n`
into adequacy at `n + 2`. SExpr Pi/sort inversions accept adequacy at an
explicit positive shape level.

The reflection choice is conservativity modulo source level equivalence:
well-formed `SLevel.mk` equality reflects to `VLevel` equivalence, and
well-formed `SExpr.mk` equality reflects to `VEnv.EqUpToLevels`; literal
syntactic injectivity is intentionally not claimed. The route-independent
constructor normalization is also complete in the working tree:
`CtorDefEq.toChain` produces root-anchored chains of native exact links,
retaining lift/unlift evidence in per-link frames and using classified
constructor-spine determinism to join transitive midpoints. The normalized
consumer API is the three-operation `CtorChain.Algebra` (native exact leaf,
composition, root anchoring), refined by `CtorChain.NativeAlgebra`: native
completion precedes frame transport, and predecessor uniqueness is consumed
only by root composition. A later raw audit strengthened exact leaves with
equality of their constructor universe-level lists and added
`CtorPath.foldRaw`/`CtorChain.foldRaw`/`CtorDefEq.foldRaw`. These retype every
native edge at one common domain via `RawTypeUniq`; only the two root views
remain explicit subject-reduction callbacks, and the normalized route is
measured free of `sorryAx`. The generic stratified proof is now
kernel-checked: `JointStratifiedInversion` implies contextual weak type
uniqueness, which in turn proves both weak-head root callbacks (including beta
and registered steps). `CtorDefEq.foldRaw_of_jointBuilder` consumes those
callbacks and the derived uniqueness, so normalized-chain root subject
reduction is complete conditional on a builder. The positive bootstrap is now
also complete: non-bottom sort/Pi observations are transported across whole
`TypeDefEqPath`s, yielding path-level inversion and stratified path uniqueness
before any path is collapsed. Consequently level-one adequacy derives
contextual raw uniqueness and direct `JointStratifiedInversion`; the former
`JointBuilder.invZero` callback has been deleted. `uniqSucc` now consumes the
exact term-indexed `LamRetype` callback (with `PiTypeAlign` only an optional
adapter), and `JointBuilder.succ` explicitly receives lower adequacy. The
remaining semantic obligation is the canonical-root application chain for
the fixed iota RHS head. A native framed leaf cannot consume the root
recursor prefix through arbitrary `unlift` refinements; synchronized endpoint
relations are now retained as `LogRel.DefEqRect`. A spike
resolved
the proposed generic InferType-completeness
shortcut negatively: weak definitional equality of an inferred function
type with a Pi does not provide the weak-head reduction demanded by
`InferType.app` without the very Church–Rosser/inversion result being built.
