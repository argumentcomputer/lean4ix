# L4L-16C′ pre-mortem residue

This document began as a pre-mortem gap map for the final adequacy-leaf step
(`buildP`) and grew into the session journal of the 13 subagent sessions that
ran the 16C′ campaign (2026-08-14/15). Trimmed 2026-08-20: the header G1–G5
worker resolution, the file:line snapshot/machinery-signature/gap-map/checklist
sections, and subagent entries 1–11 were superseded by their successors and
digested into `plans/roadmap.md` §5; the full text lives in this file's git
history. What survives here is exactly what other documents still cite as
binding: the N2 decision, the vacuity-discipline process rule, and the banked
consumers from the final two sessions.

## N2 decision — retain one ordered term/type telescope (2026-08-14)

**Decision: take the joint two-telescope route, not a pointwise widening of
`CaptureDefEqAligned`.**  A standalone field for each path cannot certify
that its alleged domain is the domain selected by the *same* registered-type
observation after all earlier dependent applications.  It would also leave
`PathSpineWF.conv`/`.ret` free to switch the syntax telescope without moving
the semantic type witness.  Both are erasure #7 in a new wrapper.

The producer will therefore recurse in `rule.capturePaths` order while the
outer recursor evaluator and its registered-type evidence are still in
scope.  One layer retains, at a common shape level:

- the RHS-spine argument `aSp` and a capture cap `argCap` with
  `aSp ≤ argCap`;
- `argCap.HasType tyDom`, where `tyDom` is the domain of the current peeled
  registered-type observation;
- the recursive result below `g.app aSp`, re-anchored at
  `tyFun.app argCap` on the type side.

The consumer for exactly this layer is now kernel-checked as
`LE_Interp.RHS.ShapeSpine.peelTypedLayer` in `ShapeLogRel.lean`.  Its proof
needs no ambient upper function or downward typing transport: the three
fields above plus the recursive term/type bounds construct the singleton
lambda/Pi layer and prove both lower inequalities.

The completed ordered certificate must expose the fixed-head consumer's
actual endpoint, not merely another synthetic typing pair:

```text
∃ headElem headTy,
  headElem ≤ head ∧ headElem.HasType headTy ∧
  Nonempty (LE_Interp.Witness ρ headTy
    (SExpr.mkInst recLs rule.df.type))
```

`FixedHeadResultAt` will consume that synchronized endpoint.  The current
context-free `typedLowerHead` input remains useful only as the shape fallback
and must not be used to manufacture the final witness.  The ordered producer
belongs at the outer `constDefEq`/`Matches` materialization boundary, where
the recursor's type evidence and the accumulated semantic-to-logical
argument caps coexist; the leaf-local `hcap` map is already too late.

Two invariants are part of this decision:

1. A raw `PathSpineWF.conv`/`.ret` edge may be crossed only by the strictly
   smaller typing-depth inversion package.  A same-depth conversion call is
   the standing circularity tripwire.
2. Valuation changes are explicit.  Closed registered roots may use
   `Witness.closedAt`, but an ambient-`ρ` capture certificate is never
   silently combined with a `.nil` head witness; the joint producer performs
   and records the transport before the leaf boundary.

## Vacuity discipline — standing process rule

Adopted 2026-08-15, after two named `Prop`s (`LR.FixedHeadTerminalRetarget`
and `LR.FixedHeadTerminalLink`) were found FALSE in one day: **every new named
`Prop` interface gets a nonvacuity witness before it is consumed** — an
explicit, named, non-degenerate inhabitant (or an outright proof of the
`Prop`), landed in-file beside it; a refutation additionally shows the
judgment it refutes is nonempty; environment-conditional witnesses are
recorded as such (e.g. `LRS.indTyHead_nonvacuous`, inhabited as soon as any
nullary inductive type is declared). A session closes only with "no new
`Prop` was left unwitnessed and no derivation of `False` succeeded". The
pattern behind both refutations, stated so it is not repeated: the
observation lattice has a bottom that *every* syntax is witnessed at and that
*every* type of type-kind types, therefore no terminal fact about the peel
may be stated as a law quantified over observations — a terminal fact must be
a *datum at the observation actually reached*, i.e. existential /
continuation-passing in that index. The cheap vacuity test on the next such
`Prop`: instantiate at `TShape.bot` and see whether the statement survives.

## Banked consumers (session-C subagents 12/13, 2026-08-15)

The final two sessions banked the downstream-consumer direction of the leaf.
Names and one-line meanings, as recorded there:

- **`ParRed.defeq_of_piPathInv` / `ParRedS.defeq_of_piPathInv`** (with
  `LRS.parRedSDefeq_of_piPathInv` and the headline
  `LRS.piPathInv_iff_parRedSDefeq`) — banks the whole CR ladder as a
  *consumer* of the leaf: probeR13-loop proved the ladder rung
  `LRS.ParRedSDefeq` and the 16C′ leaf `LRS.PiPathInv` interderivable, so the
  moment 16C′ lands, the ladder is free — `LRS.ParRedSDefeq` outright,
  `LRS.SubjectRedS` (already landed as `WHRedS.defeq_of_piPathInv`), the
  single-edge `LRS.PiEdgeInv` — and it retires the `sorryAx` that Theory's
  `VEnv.ParRed.defeq` and `VEnv.StRed.triangle` carry.
- **`LRS.PatStep`** — the second, independent uniqueness site:
  `.of_typeUniq` proves it from raw type uniqueness and from nothing about
  Pi shapes. It is not an extra residual on top of the leaf: every redex a
  `Pattern.Action` can match is a constant-headed spine, so
  `.of_piPathInv` (via `LRS.constSpineTypeUniqPath`) discharges it from
  `LRS.PiPathInv` as well.
- **`LRS.BetaFire`** (+ `.of_piPathInv`) — the β *contraction* is where the
  leaf is charged; `beta_congr_no_piInv` shows the β congruence needs no
  Π-inversion at all, and `betaSort_domain_unconstrained` shows sort-typedness
  constrains the result type, never the domain — the sort restriction is not
  an escape.
- **`LRS.ChainAnchorAt`** (+ `.uniformDepthBound` / `.of_uniformDepthBound`)
  — the stratification escape's consumer-side obstruction, provably
  equivalent to a uniform stratification bound (the same fatal proposition
  probeS identified). **Now known FALSE** — kept on this list as refuted so
  the dead route is not re-attempted (refutation in the design docs below).
- **The inversion suite `IsDefEqStrong.app_inv'` / `.lam_inv'` /
  `.forallE_inv_path`** (`SExpr.lean` :3705/:3753/:3804) — ~145 lines of pure
  structural case analysis on `IsDefEqStrong`; reaches neither
  `IsDefEq.strong` nor `LRS.PiPathInv`. Each also returns the
  `TypeDefEqPath` from the subject's **own** type to the declared type `V` —
  the whole novelty over Theory's `VEnv.HasType.app_inv` / `.lam_inv`, and
  what removes every `IsDefEq.trans_l` / `uniqU` fixup the Theory proofs
  spend. Structural, worth landing on its own.
- **The `TypeDefEqPath` relocation** — `TypeDefEqPath` and its whole
  conversion API (`single`, `trans`, `leftType`, `rightType`, `left`,
  `right`, `symm`, `defeqDF`, `defeqDF_l`, `defeqDF_l_path`, `subst`) moved
  out of `ShapeLogRel.lean` to `SExpr.lean:3613`: every input is SExpr-level,
  zero consumer fixups. `TypeDefEqPath.collapse` deliberately stayed in
  `ShapeLogRel.lean` — it has the extra input `LogRel.RawTypeUniq`, declared
  there.
- **The `PiComponentTransport` dissolution** — `LR.PiComponentTransport` is
  not a residual and not new data: it is the inductive step of an induction
  on the SHAPE level (the convert step at `n+1` consumes the convert step at
  `n`), and the two-reduct form is illusory (`WHRedS.determ` collapses it —
  `.of_diag`/`.diag`). The one genuinely new obligation the induction
  exposes is `LRS.IndTyHeadNorm`, which has no upstream analogue.

## Where the program ended

The machine-checked refutations that ended 16C′-as-scoped live in
`plans/l4l-16-stratified-observation-design.md`,
`plans/l4l-16-registered-pi-design.md`, `plans/l4l-16-typedview-design.md`,
and `plans/roadmap.md` §5.
