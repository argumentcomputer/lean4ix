# L4L-16 sort-inversion route decision

Date: 2026-08-12

Status: route selected and prerequisite interface landed. The post-v4.33
spike selected the semantic route; L4L-18B completed its prerequisite
proof-carrying extension interface on 2026-08-12, so L4L-16 is now active.
This note does not weaken the theorem, add an assumption, or change the
accepted trust closure.

> **Trimmed 2026-08-20:** the route enumerations, the "Checked non-routes"
> section, the resolved "Required decision to resume" section, and the
> 2026-08-13 joint-interface checkpoint narrative were deleted; the
> checkpoint's artifacts (`LR.AdequacyAt`, `LR.JointStage`,
> `LR.JointBuilder`, `CtorChain`, `foldRaw`) are all landed in
> `Experimental/ShapeLogRel.lean`, and landed status lives in
> `plans/roadmap.md`. This file retains the gate theorem and the two dated
> resolutions as the constitutional record. (The deleted decision section's
> Option 1 = semantic route and Option 2 = joint inversion route — both are
> restated inside the resolutions below.)

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

## Route 2: live stratified derivations

Decision: discard this as the L4L-16 implementation route.  Route 2 is
refuted by the circularity result: on this route uniqueness must be assumed
to prove sort inversion while L4L-17's uniqueness builds on `sort_inv` —
see the second resolution below.

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
