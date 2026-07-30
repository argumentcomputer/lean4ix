# Lean4Lean upstream divergence ledger

This file tracks every deliberate semantic, API, build, or verification delta
from `upstream/master` that must either be upstreamed or explicitly retained.
It is the tracked counterpart to `plans/roadmap.md`.

Audit baseline (2026-07-30):

- upstream: `0c38ab8`
- committed local checkpoint: `efb2a2b2eb95` (12 commits ahead)
- active worktree: green Stage-3 direct-indexed inductives, the current I2
  structural and semantic checked descriptor, the I1 Theory transaction API,
  E1 core Verify alignment, and replay-driven Nat/Eq/index-changing-`IndexedVec`
  environment fixtures; not yet committed or published

Status vocabulary: `local-committed`, `worktree`, `submitted`, `upstreamed`,
or `intentional-fork`. An entry is removed only after its removal condition is
met and every consumer has moved to the replacement.

## D001 — Nix packaging and downstream artifacts

- **Status:** local-committed
- **Commits:** `e4c46ec`, `29d017f`, `5ad48f9`, `ae43b7b`
- **Delta:** flake packaging, full Lake dependency artifacts, downstream
  consumer/CLI checks, lock deduplication, and Linux/Darwin CI.
- **Ix impact:** supplies the proof-bearing artifact needed by `IxTcVerify`
  and makes a pinned fork reproducible in Nix.
- **Tests:** `nix flake check --accept-flake-config --print-build-logs`;
  `downstream-consumer`, `cli-smoke`, `cli-smoke-external`, and `cli-noarg`.
- **Upstream issue/PR:** TBD; split packaging and CI into independently
  reviewable PRs.
- **Removal condition:** upstream publishes equivalent full dependency and
  consumer-test outputs and ix pins that upstream revision.

## D002 — replay teardown safety

- **Status:** local-committed
- **Commit:** `4a55f8d`
- **Delta:** avoid the `replayFromImports` teardown segfault.
- **Ix impact:** makes executable environment replay reliable when ix or its
  fixtures invoke the Lean4Lean CLI.
- **Tests:** `cli-smoke`, `cli-smoke-external`, and `cli-noarg` in the flake.
- **Upstream issue/PR:** TBD.
- **Removal condition:** equivalent fix lands upstream and all CLI regression
  checks pass against it.

## D003 — multi-part olean replay deduplication

- **Status:** local-committed
- **Commit:** `7c9ed2c`
- **Delta:** skip constants already imported while replaying multi-part oleans.
- **Ix impact:** prevents false duplicate-name failures when constructing an
  environment from compiled dependencies.
- **Tests:** external-environment CLI smoke test and full flake check.
- **Upstream issue/PR:** TBD.
- **Removal condition:** upstream replay is idempotent for the same fixture and
  the local special case can be deleted.

## D004 — case-insensitive current-module inference

- **Status:** local-committed
- **Commit:** `d81fd04`
- **Delta:** infer the current module without a case-sensitive path/name
  assumption.
- **Ix impact:** avoids host/filesystem-dependent replay failures in downstream
  builds.
- **Tests:** external-environment and no-argument CLI checks.
- **Upstream issue/PR:** TBD.
- **Removal condition:** upstream implements an equivalent portable inference
  rule and the cross-platform checks pass.

## D005 — exact sorry-frontier enforcement

- **Status:** local-committed, wording updated in worktree
- **Commit:** `c8a9ef8`
- **Delta:** token-aware, declaration-attributed allowlist excluding
  `Experimental/`, wired into Nix and CI.
- **Ix impact:** guarantees that upstream proof debt can only shrink at pin
  boundaries; currently records exactly 20 supported-tree sorries.
- **Tests:** `perl .github/scripts/check_sorry_frontier.pl` and the
  `sorry-frontier` flake check.
- **Upstream issue/PR:** TBD.
- **Removal condition:** upstream adopts an equal or stricter shrink-only gate;
  at zero debt, replace the allowlist with an unconditional rejection rule.

## D006 — staged computational inductive semantics

- **Status:** Stage 1/2 local-committed; Stage 3 worktree
- **Commits:** `71f2eae`, `06e904d`, `201c12f`, `efb2a2b`; Stage-3 delta is
  currently uncommitted.
- **Delta:** replace the three placeholder inductive declarations with a real
  `VInductDecl.WF`, computational `VEnv.addInduct`, generated recursor/iota
  rules, and a sorry-free `addInduct_WF`. Stage 3 supports one family with
  parameters, indices, direct recursive fields, never-zero or syntactically
  subsingleton large elimination, typed index spines, closed metadata, and
  pairwise-distinct generated names. Acceptance is now descriptor existence;
  see D009 for the shared analysis API.
- **Ix impact:** discharges ix gap A1's three upstream `sorryAx` origins and is
  the semantic basis for constructing `InductiveOracle`; current breadth is
  not yet enough for all ix blocks.
- **Tests:** exact Nat, Bool, List, Prod, Option, Eq, HEq, and index-changing
  `IndexedVec` recursor/iota fixtures; negative Or, duplicate-name, and
  loose-variable fixtures; Theory/Verify build; full flake check;
  `VEnv.addInduct_WF` axiom guard.
- **Upstream issue/PR:** TBD; submit in the staged PR sequence described in the
  roadmap rather than as one proof mega-diff.
- **Removal condition:** upstream exposes kernel-complete checked inductive
  semantics and preservation with the same fixture coverage, then ix pins it.

## D007 — consumer-facing inductive transaction API

- **Status:** worktree
- **Delta:** `VEnv.AddInductSuccess`, `addInduct_le`, generated
  type/constructor/recursor lookup theorems, rule-membership theorems,
  input-name freshness, atomic success/failure, and early-rejection lemmas.
  Generic `addConst_fresh` and absence-under-growth facts support the API.
- **Ix impact:** lets `InductiveOracle` consume checked block results without
  unfolding `Option` binds or `foldlM` implementation details.
- **Tests:** consumer-style `IndexedVec` fixture, type-name collision fixture,
  Theory/Verify build, full flake check, and a dedicated axiom guard for
  `addInduct_success` (`propext`, `Quot.sound`).
- **Upstream issue/PR:** TBD; submit after or with the Stage-3 preservation PR.
- **Removal condition:** equivalent stable postconditions are upstream and ix
  no longer imports the fork-only names.

## D008 — Verify inductive-environment alignment

- **Status:** worktree
- **Delta:** replace the empty `AddInduct` relation with typed witnesses for
  `inductInfo`, ordered `ctorInfo` insertions, `recInfo`, and the generated
  defeq-rule fold. Add fold realization, lookup, freshness, environment
  monotonicity, map-WF/value-preservation, real `Aligned.addInduct`, and the
  formerly impossible `TrEnv'.of_value` inductive case. Add `TrTypeExpr` to
  recover metadata translation typing premises from real Theory WF evidence,
  then quote and replay Lean's actual Nat, Eq, and index-changing `IndexedVec`
  metadata through `TrEnv'.induct`. The indexed replay is layered over the
  real Nat transaction and uses explicit `Nat.zero`/`Nat.succ` indices to keep
  its dependency claim semantic rather than notation-instance-driven.
  Replay an actual value-bearing `defnInfo` first and verify that
  `TrEnv'.of_value` recovers it through the subsequent Nat transaction. The
  trace carries the exact dependent `VInductDecl.Checked` value and derives
  its type/recursor/rules from that shared analysis rather than restating them.
- **Ix impact:** establishes the implementation-to-Theory environment bridge
  needed to translate checked inductive blocks and eventually construct
  `InductiveOracle`; later I2-I4 replay fixtures plus the I5 pattern package
  are still required before that oracle is constructible.
- **Tests:** `lake build Lean4Lean.Verify.Environment.InductiveFixtures`;
  concrete Nat, Eq, and `IndexedVec`
  final-WF/alignment/replay-equality/lookup-uniqueness checks and a pre-Nat
  definition value-preservation regression;
  full Theory/Verify and flake gates; compile-time axiom guards for
  `TrTypeExpr.to_trExprS`, `AddInduct.to_addInduct`, `Aligned.addInduct`, and
  the concrete `nat_trEnv'`, `eq_trEnv'`, and `indexedVec_trEnv'` witnesses.
- **Axiom note:** the guarded roots currently inherit `sorryAx` through
  `TrConstVal → TrExprS → TrProj`, plus the standard logical baseline. E1
  declares no new axiom. The concrete fixture additionally reaches the three
  existing persistent-map contracts while proving its `SMap` insertion
  freshness; Track P/T2 must remove or narrowly justify these inherited
  dependencies before release.
- **Upstream issue/PR:** TBD; submit with or immediately after the staged
  inductive-semantics series.
- **Removal condition:** upstream has a non-vacuous inductive alignment with
  concrete replay fixtures, ix uses it, and the guarded closure contains no
  `sorryAx`.

## D009 — shared checked inductive descriptor

- **Status:** worktree
- **Delta:** add dependent `VInductDecl.Checked`, normalized constructor and
  recursive-argument records, and the computational `checked?` analyzer.
  Define public Stage-3 acceptance as descriptor existence. Route recursor/rule
  access, `VEnv.addInduct`, its success/WF proof anatomy, Theory fixtures, and
  Verify's `AddInductTrace` through the descriptor. Add exact closed-metadata,
  all-annotation universe-range, family-telescope self-reference, direct
  result-shape, and generated-name `Nodup` checks plus a centralized proof API.
  Add `Checked.WF env` for normalized telescope/field/result-spine semantics,
  prove both compatibility directions and an iff with `VInductDecl.WF`, and
  make `addInduct_WF` consume it. Retain the exact analyzer result in
  `AddInductSuccess` and expose stable constructor/recursor collision rejection.
- **Ix impact:** creates the stable, consumer-neutral analysis object that E2
  can use to assemble `InductiveOracle` without duplicating raw declaration or
  de Bruijn analysis. The semantic certificate gives ix an environment-indexed
  proof boundary without importing Verify, while the transaction certificate
  lets it reuse the exact checked value. Reserved recursive binder telescope
  and target-family fields provide the extension point for Acc-like and mutual
  recursion.
- **Tests:** computed descriptor-shape checks for Nat, Eq, and `IndexedVec`;
  semantic bridge fixtures for `IndexedVec`; negative fixtures for loose data,
  internal/pre-existing name collisions, self-referential parameters, invalid
  levels, malformed results/spines, parameter counts, and universe-count
  mismatches; exact Theory/Verify build; 20-sorry audit; Theory import boundary;
  formatter; all nine flake checks.
- **Axiom note:** the analyzer and descriptor are computational and declare no
  axiom. Compile-time guards pin every exported structural fact, the three
  `Checked.WF` compatibility roots, transaction success/exact-analysis facts,
  and collision theorems to exactly `propext` and `Quot.sound`, a subset of the
  accepted Theory baseline. `addInduct_WF` retains the accepted
  `propext`/`Classical.choice`/`Quot.sound` closure.
- **Upstream issue/PR:** TBD; include as the architecture-first patch in the I2
  one-family-parity series.
- **Removal condition:** upstream generation, preservation, Verify alignment,
  and downstream consumers share an equivalent checked block result, and ix
  no longer imports the fork-only descriptor API.

## Review checklist

At each publish or ix pin boundary:

1. Refresh both baseline hashes and `git log upstream/master..HEAD`.
2. Add an entry before landing any new semantic/API delta.
3. Record the upstream issue or PR as soon as one exists.
4. Run the tests named by every touched entry.
5. Delete an entry only when its removal condition is demonstrably satisfied.
