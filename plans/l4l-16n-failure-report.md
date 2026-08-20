# L4L-16N failure report

Date: 2026-08-20

Status: **halted at N2 by the roadmap's second and final kill criterion.**
The conditional L4L-16C′w regime remains in force. This report is an
execution outcome, not a claim that weak-head normalization is false.

## Outcome

N0 and N1 produced useful, sorry-free infrastructure:

- `Params.Classified` and proof-carrying generated-iota provenance,
  including the non-Prop firing law and `PatArgProp` consequence;
- proof-carrying weak-head steps, Kripke normalization bases,
  step-indexed PER candidates, neutral/sort/Pi/lambda constructors, logical
  substitutions, the structural application/Pi fundamental cases, and a
  candidate-to-`LRS.PiPathInv` escape;
- a machine-checked circularity boundary:
  `SubjectPreservingWHNormalization.betaFire` proves that demanding a typed
  normalization trace already supplies `LRS.BetaFire`, the leaf that N2 was
  meant to derive. The usable N2 interface therefore retains only an untyped
  operational trace.

N2 did not close. The exact Tree recursion-under-Pi transition defeats the
authorized primary measure, and the only authorized fallback is inconsistent
with the checked mutual-recursion graph. Both facts are proved in
`Experimental/SExprNormalizationFailure.lean`.

## Primary measure failure

The production `Tree.branch` iota rule grows from 123 syntax nodes on its LHS
to 127 on its RHS. Its descriptor has owner family `0`, target family `1`,
and one Pi binder; the new subterm responsible for the growth is exactly the
captured field applied to the fresh variable:

```text
bvar 0                         -- captured recursive field, size 1
app (bvar 1) (bvar 0)          -- generated recursive major, size 3
```

An iota contraction is not a delta step, so its definition-rank component is
unchanged. Since the complete RHS is larger than the complete LHS, the
roadmap's `(definition rank, syntax size, typing depth)` lexicographic order
cannot decrease, regardless of the two typing-depth values. This is
`treeBranch_primaryMeasure_fails`; `treeBranch_rule_lhs_nodes` and
`treeBranch_rule_rhs_nodes` pin the two computed sizes.

## Family-ordinal fallback failure

For a leading family rank to repair the failed transition, it must be
non-increasing on every recursive edge and strictly decrease on the
under-Pi `Tree -> TreeList` edge. The checked artifact contains the reverse
`TreeList -> Tree` edge:

```text
Tree -> TreeList       requires rank(TreeList) < rank(Tree)
TreeList -> Tree       requires rank(Tree) <= rank(TreeList)
```

These inequalities contradict each other. The theorem
`tree_familyOrdinalFallback_false` quantifies over every `Nat -> Nat` rank,
so changing or reversing the stored source ordinals cannot help. The graph
also contains `TreeList -> TreeList`; the stronger
`tree_strictFamilyRanking_false` records that no rank can strictly decrease
on all edges.

## Scope and consequence

The N2 row says: if the primary Tree measure fails, try the block-family
ordinal measure; if that fails, halt and report, with no third fallback. That
condition is now met. Consequently:

- N3–N5 were not attempted past their compiled interfaces;
- `LRS.PiPathInv` and `LR.MajorLinkRect` remain the two explicit conditional
  inputs established at L4L-16C′w;
- the D2 and injectivity consumers gated by those inputs remain conditional;
- no axiom, `sorry`, or hidden `stop` admission was added.

This does not rule out a different normalization proof. A future attempt
would need a newly approved measure or relation, for example a genuine
block-level semantic subterm/accessibility relation capable of treating
functional recursive fields. That is a third route and therefore requires a
new roadmap milestone rather than silently extending L4L-16N.

## Verification

The failure record is pinned to the accepted Experimental baseline
`[propext, Classical.choice, Quot.sound]` (the family-rank contradiction
itself needs only `[propext, Quot.sound]`) and compiles with:

```sh
nix develop --command lake env lean \
  Lean4Lean/Experimental/SExprNormalizationFailure.lean
```

The candidate development remains separately compilable with:

```sh
nix develop --command lake env lean \
  Lean4Lean/Experimental/SExprReducibility.lean
```
