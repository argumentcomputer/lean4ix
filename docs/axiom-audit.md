<!--
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-->

# Lean4Ix implementation-contract audit

This note records the human validity review behind the compiled policy in
[`Lean4Lean/Audit/SorryFrontier.lean`](../Lean4Lean/Audit/SorryFrontier.lean).
The compiled audit is the source of truth for declaration inventory and
reachability; this document explains why each custom contract has its present
shape and what would allow it to be removed.

Audit baseline: 2026-08-25, after adapting the trust findings and repairs from
lean4lean PRs [#44](https://github.com/digama0/lean4lean/pull/44),
[#45](https://github.com/digama0/lean4lean/pull/45), and
[#46](https://github.com/digama0/lean4lean/pull/46) to this fork's larger
verification surface.

## Result

The known inconsistent or over-general contracts have been removed. In
particular, the former unconditional `Expr.looseBVarRange_eq` could derive
`False` from a bvar whose structural range is `2^20` but whose packed cache has
only 20 bits. The repaired theorem requires hereditary `Expr.BVarBounded`,
which that expression cannot satisfy. Its exact signature is pinned by the
compiled audit, so a same-name widening also fails the gate.

This is a repair of the Verify trust boundary, not an elimination of all trust.
There are 28 custom contracts: 22 transitional implementation bridges and 6
narrow platform contracts. They describe opaque or externally implemented
operations on their real domains. Theory reaches none of them.

The governing rules are:

1. An aborting C/C++ operation has no Lean result outside its runtime domain.
2. Packed metadata is an optimization, not semantic evidence, unless a
   cache-validity invariant is present.
3. A model equality is stated only where the executable and model operations
   agree. Callers outside that domain use a weaker truthful relation or a
   faithful model.
4. Custom axioms are never global simp rules; consumers name the exact bridge
   they use.
5. Every custom axiom must be live, uniquely classified, and allowed at every
   release root that reaches it.

## Repaired suspect contracts

| Contract from the pre-repair audit | Repaired disposition |
|---|---|
| `PersistentArray.toList'_push` | Replaced by `PersistentArray.WF.toList'_push`. Malformed records are outside the generated `empty`/`push` fragment. |
| `Level.mkData_eq` | Requires `depth < 2^24`, the domain before the runtime constructor aborts. |
| `Level.hasParam_eq` | Retained as a separate opaque cache contract. It was not independently refuted; the unbounded `mkData_eq` route that made the set jointly inconsistent is gone. |
| `Level.hasMVar_eq` | Same disposition as `hasParam_eq`; no out-of-domain `mkData` equation may justify it. |
| `Expr.mkData_eq` | Requires `looseBVarRange <= 2^20 - 1`, the packed-field domain. |
| `Expr.looseBVarRange_eq` | Requires hereditary `Expr.BVarBounded`; the old overflow witness fails this premise. |
| `Expr.instantiate_eq` | Requires either a closed source or closed substituends. The runtime operation is simultaneous, while `instantiateList` is sequential. |
| `Expr.instantiateRange_eq` | Requires `start <= stop <= subst.size`, matching the runtime checks. |
| `Expr.instantiateRevRange_eq` | Requires the same checked range. |
| `Expr.abstract_eq` | Requires an empty target list or a loose-bvar-free source, and always requires duplicate-free targets. |

`Expr.abstract_fvars_shape` is the new, weaker bridge used where callers need
only recursive skeleton preservation and cannot establish the exact equality
domain. It permits an abstracted fvar to become a bvar but exposes no claim
about the index, so neither abstraction counterexample inhabits a false
equality.

## Complete custom-axiom ledger

`platform` entries are deliberately narrow contracts for pointer behavior,
packed layouts, or an externally implemented lawful equality. `bridge` entries
are owned by `TRUST/retire`: replace them with proved wrappers,
`@[implemented_by]`, verified generated code, or a smaller consumer interface
when practical.

### Pointer and expression contracts

| ID | Declaration | Class | Actual scope and removal condition |
|---|---|---|---|
| L4L-PTR-001 | `Lean4Lean.ptrEqConstantInfo_eq` | platform | Pointer equality implies equality for constant metadata. Remove when the relevant pointer fast path is proved or absent from the shipped implementation. |
| L4L-PTR-002 | `Lean4Lean.ptrEqExpr_eq` | platform | Pointer equality implies expression equality. Same removal condition. |
| L4L-EXPR-001 | `Lean.Expr.abstractRange_eq` | bridge | Relates the opaque range wrapper to abstraction over the extracted in-bounds array fragment. Replace with a proved/implemented wrapper. |
| L4L-EXPR-002 | `Lean.Expr.abstract_eq` | bridge | Exact abstraction model only for empty targets or a structurally closed source, with duplicate-free fvars. Remove after verifying a faithful simultaneous abstraction model. |
| L4L-EXPR-003 | `Lean.Expr.eqv_eq` | bridge | Opaque cached expression equality agrees with structural `eqv'`. Replace with verified implementation or generated-code equivalence. |
| L4L-EXPR-004 | `Lean.Expr.hasLooseBVar_eq` | bridge | Opaque loose-bvar query agrees with structural recursion for a requested index. Replace with verified implementation. |
| L4L-EXPR-005 | `Lean.Expr.instantiate1_eq` | bridge | One-variable runtime instantiation agrees with the structural model. Replace with verified implementation. |
| L4L-EXPR-006 | `Lean.Expr.instantiateRange_eq` | bridge | Requires `start <= stop <= subst.size`; no result is assigned to the abort path. Replace with a proved checked wrapper. |
| L4L-EXPR-007 | `Lean.Expr.instantiateRevRange_eq` | bridge | Same checked range, for reverse instantiation. Replace with a proved checked wrapper. |
| L4L-EXPR-008 | `Lean.Expr.instantiateRev_eq` | bridge | Reverse instantiation equals simultaneous instantiation over the reversed array. Replace with verified implementation. |
| L4L-EXPR-009 | `Lean.Expr.instantiate_eq` | bridge | Sequential model equality only for a closed source or all-closed substituends. Remove after introducing and verifying a faithful simultaneous model. |
| L4L-EXPR-010 | `Lean.Expr.looseBVarRange_eq` | bridge | Cache/structure equality only under hereditary `BVarBounded`. Remove after proving cache validity for every supported expression ingress. |
| L4L-EXPR-011 | `Lean.Expr.lowerLooseBVars_eq` | bridge | Opaque lowering agrees with the structural model. Replace with verified implementation. |
| L4L-EXPR-012 | `Lean.Expr.mkAppData_eq` | platform | Pins the expression application-cache layout; its range field is already a packed value. Remove when cache construction is implemented in verified Lean/Ix code. |
| L4L-EXPR-013 | `Lean.Expr.mkData_eq` | platform | Pins cache layout only for `looseBVarRange <= 2^20 - 1`. Remove when the runtime constructor is verified or replaced. |
| L4L-EXPR-014 | `Lean.Expr.replace_eq` | bridge | Opaque replacement agrees with the no-cache structural copy. Replace with verified implementation. |
| L4L-EXPR-015 | `Lean.Expr.abstract_fvars_shape` | bridge | Unconditional skeleton preservation for fvar abstraction, intentionally weaker than equality. Remove with a verified faithful abstraction implementation. |

### Level contracts

| ID | Declaration | Class | Actual scope and removal condition |
|---|---|---|---|
| L4L-LEVEL-001 | `Lean.Level.hasMVar_eq` | bridge | Opaque cached mvar bit agrees with structural recursion. Retire after verified cache construction; do not derive it through an out-of-domain `mkData` equation. |
| L4L-LEVEL-002 | `Lean.Level.hasParam_eq` | bridge | Opaque cached parameter bit agrees with structural recursion, under the same policy. |
| L4L-LEVEL-003 | `Lean.Level.instLawfulBEqLevel` | platform | Lawfulness contract for the C++ level equality instance. Remove when equality is verified or replaced by a proved implementation. |
| L4L-LEVEL-004 | `Lean.Level.isExplicitSubsumedAux_eq` | bridge | Relates a partial/opaque helper to its terminating copy. Remove after the implementation is total and transparent or verified separately. |
| L4L-LEVEL-005 | `Lean.Level.mkData_eq` | platform | Pins the level-cache layout only for `depth < 2^24`; no value is assigned to the abort path. |
| L4L-LEVEL-006 | `Lean.Level.normalize_eq` | bridge | Relates opaque normalization to the terminating clause-for-clause copy, with finite differential coverage. Remove after verified implementation equivalence. |

### Persistent containers and syntax

| ID | Declaration | Class | Actual scope and removal condition |
|---|---|---|---|
| L4L-PARRAY-001 | `Lean.PersistentArray.WF.toList'_push` | bridge | List/push equation only for arrays generated from `empty` and `push`. Remove when `insertNewLeaf` is total/proved or a verified container replaces it. |
| L4L-PHMAP-001 | `Lean.PersistentHashMap.findAux_isSome` | bridge | Opaque node lookup and containment agree. Replace with verified implementation. |
| L4L-PHMAP-002 | `Lean.PersistentHashMap.WF.find?_eq` | bridge | Lookup agrees with the list model for well-formed maps. Replace with verified implementation. |
| L4L-PHMAP-003 | `Lean.PersistentHashMap.WF.toList'_insert` | bridge | Insert/list permutation for well-formed maps with lawful equality and hashing. Replace with verified implementation. |
| L4L-SYNTAX-001 | `Lean.Syntax.structEq_eq` | bridge | Partial syntax equality agrees with the structurally recursive copy. Replace with a proved implementation hook. |

## Executable hardening

The contract changes are paired with executable changes so cached metadata is
not silently trusted at semantic boundaries:

- `cheapBetaReduce` performs the trivial range instantiation even when a cache
  bit says no substitution is needed;
- `isDefEqLambda` and `isDefEqForall` always introduce a real fresh fvar for a
  binder instead of placing `default` in a delayed substitution; and
- `inferType'` rejects a loose bvar explicitly rather than continuing through
  an `unreachable!` default path.

For cache-correct, well-formed expressions these changes preserve results. A
future Lean4Ix fast path may recover the avoided work only behind a
proof-carrying cache-validity certificate and an observational-equivalence
proof.

## Regression evidence

[`Lean4Lean/Tests/TrustRepair.lean`](../Lean4Lean/Tests/TrustRepair.lean)
retains the concrete falsification families:

- simultaneous runtime substitution versus sequential open substitution;
- loose-bvar capture and duplicate-target abstraction mismatches;
- the first bvar outside the packed 20-bit range;
- reversed and out-of-bounds range premises;
- an arbitrary malformed persistent-array record;
- explicit checker rejection of a loose bvar; and
- ordinary closed-sort and beta-reduction behavior.

The tests execute only defined runtime inputs. They prove that invalid inputs
cannot supply the repaired hypotheses instead of invoking an operation that is
documented to abort.

## Exact release-root policy

At this audit baseline the compiled report is:

| Root | Declarations | Axiom leaves | Project contracts |
|---|---:|---:|---:|
| Theory | 8,969 | 10 | 0 |
| Verify | 23,046 | 319 | 28 |
| Shipped library | 5,165 | 5 | 2 pointer contracts |
| CLI | 60 | 3 | 0 |

The exact union has 325 leaves: 3 logical-baseline axioms, `sorryAx`, 6
deliberately rejected fixture declarations, 28 custom project contracts, and
287 compiler-generated `native_decide`/`bv_decide` certificates. The direct
sorry frontier remains exactly 15 declarations, including the six recovered
negative fixtures.

These counts are descriptive. The build does not merely compare counts: it
pins every name per root, each repaired high-risk signature, every custom
contract's liveness and classification, the absence of project contracts from
Theory, and the absence of custom contracts from the global simp set.

## Checkpoint validation

The repair was validated as one staged tree on top of parent
`65de52ff9d5e`. The pinned Nix development shell reported:

- strict Theory plus Verify build: 169 jobs;
- strict CLI plus exact frontier audit: 173 jobs;
- strict default build and tests: 240 jobs;
- Experimental build: 152 jobs, with its existing non-fatal WIP warnings;
- both package outputs (`lean4lean` and `lake-dependency`): successful; and
- all 11 Nix flake checks: successful.

Nix formatting, staged and unstaged `git diff --check`, the Theory/Verify and
Experimental import boundaries, the Experimental source-admission scan, and
the upstream-derived-file license audit also passed. The resulting commit ID
is recorded by the Git checkpoint carrying this document; no publication hash
is claimed until that checkpoint is pushed or bookmarked for recovery.

## Provenance and upstream disposition

The repairs were manually adapted rather than merged wholesale:

- PR #45 supplied the partial-runtime, substitution, abstraction, persistent
  array, and one-way cache analysis;
- PR #44 supplied hereditary loose-bvar boundedness and the simple sound
  checker path; and
- PR #46 supplied the falsification and audit methodology.

General repairs remain candidates for contribution back to lean4lean. The
Lean4Ix-specific consumer migrations and future cache certificates may remain
local when their operational detail is not appropriate for the more general
upstream model.
