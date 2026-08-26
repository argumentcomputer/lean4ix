<!--
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-->

# Universe-level representation and canonicalization

Lean4Ix deliberately separates the raw representation of a universe level from
its semantic meaning and canonical form. The C++-compatible helpers introduced
by UP5 refine the representation layer; they do not replace the Géran
canonicalization model.

## The three layers

| Layer | Main representation and API | Purpose |
|---|---|---|
| Raw executable representation | `Lean.Level`; `mkLevelMaxCpp`, `mkLevelIMaxCpp`, and `Level.substParamsCpp` in `Lean4Lean/Instantiate.lean` | Reproduce the exact tree constructed by Lean's C++ kernel where expression hashes and checker caches observe that tree. |
| Theory semantics | `Lean4Lean.VLevel`, `VLevel.eval`, and `VLevel.Equiv` in `Lean4Lean/Theory/VLevel.lean` | State the implementation-independent meaning of levels. Equivalence is equality under every valuation and ignores raw tree identity. |
| Canonical decision procedure | `Normalize.NormLevel`, `Level.normalize'`, `Level.isEquiv'`, and `Level.geq'` in `Lean4Lean/Level.lean` | Decide semantic equivalence and ordering using the canonical form based on Yoan Géran's construction. |

`Lean4Lean/Verify/Level.lean` proves soundness, canonicity, and completeness of
the canonical decision procedure. `Lean4Lean/Verify/Typing/Lemmas.lean` proves
that the C++-compatible raw constructors and substitution continue to denote
the same `VLevel` operations. Those proofs bridge the representation choice to
the existing semantic model; they do not establish that a raw C++ result is
itself canonical.

## Why raw shape still matters

Lean v4.33.0's public Lean helpers and C++ kernel constructors make different
local simplification choices in two pinned cases:

- after substituting `q` for `p`, C++ preserves the raw tree
  `max (succ q) 1`, while the public helper collapses it to `succ q`; and
- C++ collapses `imax 1 q` to `q`, while the public helper preserves an
  `imax` tree.

Each pair is semantically equivalent and has the same Géran canonical form.
It can nevertheless have a different structural hash before canonicalization.
That distinction is observable in expressions containing the level and in the
type checker's unfold and weak-head-normal-form caches. The executable checker
therefore needs C++-compatible raw construction for differential parity and for
faithfully transporting cache-sensitive behavior into Ix.

Full canonicalization at every construction site would erase that operational
information, allocate more than the C++ checker does, and model a different
execution strategy. Conversely, raw structural equality is not a substitute
for semantic equality. Sort comparison continues to use `Level.isEquiv'`,
whose complete fallback compares `NormLevel` canonical forms.

## Terminology and invariants

Use these terms consistently in code and documentation:

- **canonicalization** or **canonical form** means the complete Géran-based
  `NormLevel` procedure;
- **raw level construction** means building a `Lean.Level` node with the same
  observable structure as the C++ kernel; and
- **local simplification** or **constructor-time simplification** means the
  cheap, incomplete rewrites performed by `mkLevelMaxCpp` and
  `mkLevelIMaxCpp`.

The required invariants are:

1. C++-compatible construction matches the pinned kernel's raw result where
   structure, hashes, or cache entries are observed.
2. Every such construction preserves the intended `VLevel` semantics.
3. No caller treats a `*Cpp` result as canonical merely because local
   simplification occurred.
4. Semantic equality and ordering use `isEquiv'` and `geq'`, or an interface
   proved equivalent to them, rather than raw tree equality.

The exact raw parity fixtures live in
`Lean4Lean/Tests/DifferentialParity.lean`. The temporary compatibility layer,
its pinned Lean revision, and its removal condition are tracked as D024 in
`upstream-divergence.md`.
