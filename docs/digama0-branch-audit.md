<!--
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-->

# digama0/lean4lean branch audit

Snapshot: 2026-08-30. This is an implementer-facing inventory of every head
advertised by `https://github.com/digama0/lean4lean.git`, compared with the
active Lean4Ix working-copy line. It complements
[`remaining-proof-experiments.md`](remaining-proof-experiments.md): that file
tracks local proof experiments, while this file tracks upstream branch work.

The comparison fork point is `e0e3f6bcccb840cb0ea6f11c2b274ada93a12e00`.
The audited upstream master is `8223d223ed98`, and the active local change is
the mutable Jujutsu change `rtxutvuv`. Re-check hashes before integrating: the
change ID is stable, but its commit ID changes whenever the dirty working copy
is snapshotted.

The fetch also removed the stale local tracking bookmark `pr32@upstream`: that
branch is no longer advertised by the remote. Its primitive work is represented
by the later master series and the independently evolved Lean4Ix implementation.

## Bottom line

No upstream branch closes either current implementation frontier:

- upstream `addDecl.WF` still has its `inductDecl` `sorry`; and
- upstream `reduceRecursor.WF` is still entirely `sorry`-backed.

There are nevertheless four useful upstream artifacts:

| Priority | Artifact | Disposition |
|---|---|---|
| High, metatheory | `6ba54db`, simultaneous substitution (`IsDefEq.substDF`) | **Adapt, do not cherry-pick.** The replay is conflict-free and two of three modules compile, but Lean4Ix's later `structEta` constructor creates a genuine missing case. |
| Medium, runtime | `7eca770`, raise `FuelConfig.recDepth` from 10,000 to 50,000 | **Port with fixture isolation.** The production motivation is real; exact replay fixtures must retain explicit 10,000 fuel. |
| Medium, tooling | `bce3448`, Lean Kernel Arena NDJSON import runner | **Adapt.** The upstream branch builds. A replay onto Lean4Ix conflicts only in `Main.lean`; use the current CLI and a toolchain-matched `lean4export`. |
| Low, diagnostics | `4feb2a9`, `TypeChecker.Stats` and DEQ fingerprints | **Reimplement selectively.** Useful for differential/performance debugging, but six of seven changed files conflict with the current verified checker. |

The small documentation correction in `3adf6da` is also worth incorporating
into `upstream-divergence.md`: it explains the `isNeverZero` projection choice
using the strength of the generated recursor, not only a hypothetical
unsoundness example.

The primitive series on upstream master is substantial and constructive, but
it is an alternate organization of a boundary Lean4Ix has already closed with
the exhaustive live path and eighteen directly audited primitive declaration
certificates. Treat it as reference material, not as a replacement during the
current V3/V5 cleanup.

## Isolated audit workspace

The persistent workspace is:

```text
/home/jcb/projects/l4l-upstream-audit
workspace: upstream-audit
working change: uxmwommu
parent: 8223d223 master@upstream
status: clean
```

The following local changes are audit replays. They are deliberately not
ancestors of the active implementation line:

| Change ID | Upstream source | Result |
|---|---|---|
| `xlxrloly` | `6ba54db` (`substDF`) | Conflict-free replay onto `rtxutvuv`; focused build stops only at the absent `structEta` induction alternative. |
| `vlwuoqnm` | `7eca770` (50k `recDepth`) | Conflict-free replay; representative replay passes, fixture-heavy targets expose the exact migration work. |
| `mwoooslo` | `bce3448` (Arena) | Conflict only in `Main.lean`; `lakefile.toml` and `lake-manifest.json` apply mechanically. |
| `mvkzlppy` | `4feb2a9` (stats) | Conflicts in `TypeChecker.lean`, four Verify files, and `Main.lean`; only `Environment.lean` applies mechanically. |

Use the stable change IDs above rather than the audit commits' mutable hashes.
These changes are evidence and convenient diff bases, not integration-ready
commits.

## Validation performed

| Revision/change | Command or target | Outcome |
|---|---|---|
| `8223d223` upstream master | `lake build` | Passed, 161 jobs. It still reports the known upstream `sorry` declarations. |
| `bce3448` upstream Arena | `lake build` | Passed, 155 jobs, including `Export.Parse` and the `lean4lean` executable. |
| `xlxrloly` | `lake build Lean4Lean.Theory.Typing.Strong` | `VExpr` and `Typing.Lemmas` pass. `Typing.Strong` fails at the induction with `Alternative structEta has not been provided`. |
| `vlwuoqnm` | `lake build Lean4Lean.Verify.Environment.CandidateIdentityReplay` | Passed, 119 jobs. This shows that the many literal `10000`s are not all dependencies on the default. |
| `vlwuoqnm` | fixture-heavy replay targets | `InductiveFixtures` and `PrimitiveRecursors` fail. The first relevant failures are exact `recDepth = 10000` / `9999 + 1` definitional equalities; later failures cascade from changed traces and elaborator recursion depth. |

The 50k test included `ConstructorValidityReplay`, `InductiveFixtures`,
`PrimitiveRecursors`, `IndexedVecConstructors`, and
`IndexedVecSemanticReplay`. Do not interpret the large downstream error list as
independent proof breakage: the first exact-fuel failures invalidate the
fixture terms on which later definitions depend.

## Upstream master since the fork point

Upstream master has nine commits after the common base:

| Commit(s) | Content | Lean4Ix disposition |
|---|---|---|
| `7eca770` | Raises `recDepth` to 50,000 after an Arena church-numeral term required depth 14,520. | Port with an explicit 10k fixture configuration. This changes operational capacity, not logical soundness. |
| `3adf6da` | Explains the projection divergence via the generated recursor for `MaybeProp.{u}`. | Adapt the paragraph into `upstream-divergence.md`. No code dependency. |
| `71128e2`..`ac1498a` | Table-oriented primitive invariant, translation infrastructure, primitive clauses, condition/recursion/div/mod/gcd/bitwise proofs, and inductive guard. | Substantive constructive work, but the intermediate line temporarily contains copied substitution admissions; the final tree becomes source-sorry-free only after `6ba54db`/`8223d223`. It is superseded here by the directly audited exhaustive primitive path. |
| `6ba54db` | Adds substitution-monoid laws, `Ctx.SubstEq`, `IsDefEqStrong.substEq'`, and `IsDefEq.substDF`. | Valuable reusable metatheory; see the dedicated port note below. |
| `8223d223` | Replaces copied primitive substitution sorries with the new `substDF` API. | Relevant only if the upstream primitive module split is adopted. Do not take it independently. |

### `substDF`: exact port boundary

The upstream patch adds 369 lines across:

- `Lean4Lean/Theory/VExpr.lean` (mechanical substitution-monoid laws);
- `Lean4Lean/Theory/Typing/Lemmas.lean` (`Ctx.SubstEq`, lookup, skip, lift,
  and `lift_at`); and
- `Lean4Lean/Theory/Typing/Strong.lean` (the simultaneous strong-substitution
  induction and weak projection).

It replays with no textual conflict onto Lean4Ix. The first two files compile.
The sole reported compiler error is the new `IsDefEqStrong.structEta` case, but
that case is not just a missing constructor invocation. A complete adaptation
must supply both of these facts without circularly using `substDF` itself:

1. arbitrary simultaneous-substitution naturality for
   `VStructEta.projectors`, hence for `structureType` and `rebuild`; the current
   descriptor records `liftN`, `instN`, and `instL` naturality only; and
2. substitution of the registered parameter `SpineWF` premise. That premise is
   weak, nonrecursive data inside the strong `structEta` constructor, so the
   current strong induction does not provide an induction hypothesis for it.

Reasonable implementation choices are:

- strengthen `VStructEta` with a proved `projectors_subst` law and strengthen
  the strong eta premise to a substitution-friendly/strong spine judgment; or
- prove a noncircular simultaneous-substitution theorem for `SpineWF` from the
  existing single-instantiation lemmas, then add the corresponding
  `structureType_subst` and `rebuild_subst` laws.

After adding the case, rebuild `Lean4Lean.Theory.Typing.Strong` and print the
axioms of `IsDefEq.substDF`. The port must not acquire `sorryAx` through the
structure-eta bridge.

This theorem is infrastructure for SST/Church-Rosser work, especially clean
substitution packaging. It does **not** by itself prove R4
`IsDefEqU.weakN_iff`: inverse weakening still needs the missing unlifted
witness/normalization argument. It also does not directly close V3 or V5.

### 50k recursion depth: recommended migration

Do not mechanically change every literal `10000` to `50000`. Many are exact
trace fixtures, theorem parameters, or deliberately small boundary tests.
Instead:

1. change the production default in `FuelConfig` to 50,000;
2. introduce a named fixture value such as
   `fixtureFuel : FuelConfig := { recDepth := 10000 }`;
3. use that explicit value when constructing the exact contexts in
   `InductiveFixtures.lean` and `PrimitiveRecursors.lean`; and
4. rerun all replay modules plus the positive deep-recursion regression.

This preserves existing definitional certificates while giving ordinary
kernel replay the upstream capacity. The audit found 39 textual hypotheses of
the form `recDepth = 10000`; most need no change once their fixture context is
made explicit.

## Remote branch inventory

`patch-only` counts non-merge patches not equivalent to upstream master;
`equiv` counts patches already represented there. Ancestry-only merge commits
are omitted from these counts.

| Remote head | Patch-only / equiv | Audit result |
|---|---:|---|
| `master` (`8223d223`) | 9 commits since the fork | Four candidates described above; no V3/V5 closure. |
| `arena` (`bce3448`) | 1 / 0 | Current Arena runner; builds successfully. Adapt. |
| `arena-v4.26.0` (`56d4dc5`) | 3 / 2 | Old runner and `lean4export` pin experiments. Superseded by `arena`. |
| `arena-v4.27.0-rc1` (`8d950f5`) | 3 / 3 | Same old runner line on a retired toolchain. Superseded. |
| `arena-v4.29.0` (`742ecff`) | 8 / 1 | Historical runner, fuel experiments, and lean4#14577 repair. Current fuel values and the soundness repair are already present independently in Lean4Ix. |
| `bitvec_example` (`d3797bd`) | 2 / 0 | Unfinished packed-bitvector exploration with seven explicit sorries and `done` placeholders. Reject. |
| `cpp2025` (`6077c9d`) | 0 / 0 | Ancestor of master; no branch-only patch. |
| `cpp2026` (`143d58a`) | 0 / 0 | Ancestor of master; no branch-only patch. |
| `differential` (`4feb2a9`) | 10 / 0 | Almost all behavior fixes are already landed or superseded in Lean4Ix. Stats instrumentation remains optional; primitive bypass must never be integrated. |
| `itp2024` (`c534f13`) | 0 / 0 | Ancestor of master; no branch-only patch. |
| `logrel` (`e431dad`) | 0 / 40 | All non-merge patches are represented in master and therefore in the shared history. Archaeology only; the advertised injectivity endpoint still depends on numerous sorries/axioms. |
| `types2025` (`c01a114`) | 1 / 2 | Converts sorries into named axioms and adds an old ledger; does not prove them. Reject. |
| `v4.27.0-rc1` (`7ded588`) | 0 / 1 | Toolchain history already represented in master. |

### Arena branches

The current `arena` commit adds `--import <file.ndjson>`, parses a
`lean4export` stream, removes the three generated `Quot` names, disables the
ordinary Quot insertion, and replays the declarations into an empty
environment. The feature is useful for differential corpus testing.

Port it by adapting only the import mode to the current `Main.lean` option
parser and replay context. The isolated replay shows that dependency files are
mechanically compatible, but the branch pins `lean4export` v4.30 while Lean4Ix
uses Lean 4.33; select a compatible exporter revision and record the export
format version in corpus metadata.

The `arena-v4.29.0` lean4#14577 commit added `Result.lctx` and rechecked each
`aux2nested` expression. Lean4Ix already has `ElimNestedInductive.Result.lctx`,
the `aux2nested.forM ... checkType` pass, and kernel-hardening regressions for
the dropped-parameter attack. Do not port that commit again.

### Differential branch

| Commit | Disposition in Lean4Ix |
|---|---|
| `04411a3` single-declaration mode | Superseded by the richer exact `--decl=` and JSON-corpus path in `Main.lean`. |
| `65b5f96` module-region segfault repair | Obsolete relative to the current replay lifetime/ownership code. Review only if a fresh region bug appears. |
| `909b179` exact `--fresh` match | Already present in `matchesModuleTarget`. |
| `dbc01ec` lazy delta projection reduction | Already present and verified. |
| `d3dc43d` use `.const dontcare` for closed binders | Deliberately superseded: Lean4Ix opens a real local, avoiding dependence on packed loose-bvar cache correctness. Do not regress. |
| `4f6a089` compare application heads before arity | Already present with a differential regression. |
| `27a8f92` standard-library level fast path | Superseded by the complete verified `NormLevel` fast/fallback design. |
| `26f9838` C++ `max`/`imax` construction | Already present as `mkLevelMaxCpp`/`mkLevelIMaxCpp`, with verification and tests. |
| `1d2f186` bypass `checkPrimitiveDef` | Explicit parity hack; reject under every production configuration. |
| `4feb2a9` stats/fingerprint tracing | Useful optional diagnostics; reimplement against current state and proof APIs. |

For the stats port, keep counters observational: define one state-preservation
lemma for counter updates and use it at the verification boundary, rather than
threading ad hoc proof edits through every checker theorem. Retain environment
gating so normal replay has no trace-volume or hashing cost. The upstream patch
is a design sketch, not a conflict-resolution starting point.

### `logrel`, `types2025`, and `bitvec_example`

The `logrel` branch title “Finished injectivity!” is misleading as an
integration signal. Its final tree still contains the original Theory
injectivity/weakening sorries, many Experimental sorries, and the
`Params.extra_pat` axiom. Its useful design lineage is already represented by
the much newer local `Experimental` work and the NORM-DI inventory. Do not
transplant the branch.

`types2025` is provenance for an early axiom-accounting idea. Its unique commit
renames admissions as axioms; it neither reduces the trusted base nor matches
the current compiled `SorryFrontier` audit. Keep it out of the implementation
line.

`bitvec_example` is an incomplete representation experiment, not a hidden
proof. Its head contains seven explicit `sorry`s plus unfinished `done`
branches. Current bounded cache contracts and their trust repairs are the
supported replacement.

## Integration order

These candidates are independent of the immediate V3/V5 proof closure. A
low-risk order is:

1. copy the `3adf6da` rationale into the divergence ledger;
2. port the 50k default together with explicit 10k fixture fuel and rebuild the
   replay suite;
3. add the Arena import mode as a separate tooling change; and
4. adapt `substDF` only as a dedicated metatheory change with the structure-eta
   naturality design reviewed first.

Defer stats instrumentation until the active V3 checker interfaces settle.
Do not merge the upstream primitive rewrite, `types2025`, `bitvec_example`, or
the differential primitive-bypass commit as part of this cleanup.
