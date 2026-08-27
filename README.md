<!--
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-->

# Lean4Ix

**Lean4Ix is a formal model of the Lean 4 kernel for the Ix zkPCC platform,
based on [lean4lean](https://github.com/digama0/lean4lean).**

> [!WARNING]
> Lean4Ix is work in progress and experimental. It is not yet a completed
> verification, a production security boundary, or a claim that every Lean
> kernel feature is covered. Proof obligations, trusted implementation bridges,
> and conditional research endpoints are tracked explicitly; consult the
> compiled trust audit and the
> [upstream divergence ledger](upstream-divergence.md) for the status of the
> exact revision you are using.

Lean4Ix contains an implementation of the Lean 4 kernel written in mostly pure
Lean 4, an implementation-independent Theory model of that kernel, and proofs
relating the executable implementation to the model. The executable port is
derived closely from Lean's C++ kernel. It therefore benefits from many of the
same algorithms and performance choices, but it is not an independent kernel
implementation and may share implementation bugs with Lean.

## Role in Ix

Lean4Ix is intended to be the formalization and verification layer between Lean
and the more specialized kernels used by Ix. The Ix project will transport
theorems established here into two settings:

- an out-of-circuit kernel, where compatibility and performance matter and
  proofs may need to account for implementation details such as cached metadata,
  persistent containers, and normalization behavior; and
- kernels represented inside cryptographic circuits for the zero-knowledge
  proof backend, where representations and algorithms are specialized further
  for circuit constraints and proof cost.

Lean4Ix is not itself the final in-circuit kernel. Its job is to provide a
precise semantic reference, verified executable behavior where applicable, and
the theorem interfaces needed to justify those later specializations.

## Relationship to lean4lean

[lean4lean](https://github.com/digama0/lean4lean) remains the upstream project
and the source of the general Lean kernel model. We expect work to flow from
lean4lean into Lean4Ix more often than in the opposite direction. A general
formal model can usually keep interfaces and metatheory more theoretically
elegant, while Lean4Ix may need Ix-specific environment classes, operational
details, performance contracts, or theorem shapes that would not be desirable
upstream.

That specialization is not meant to create a one-way boundary. If a proof,
interface repair, bug fix, fixture, or tool developed here is useful to
lean4lean, we are entirely open to it being reused or contributed upstream.
General results should be upstreamed when doing so is useful and does not force
Ix-specific policy into the upstream design. Durable differences are recorded
in the [upstream divergence ledger](upstream-divergence.md) so that updates in
either direction remain reviewable.

## Architecture

| Path | Role |
|---|---|
| `Lean4Lean/` | Executable kernel port and public library surface. |
| `Lean4Lean/Inductive/` | Inductive validation, generation, recursors, and iota reduction. |
| `Lean4Lean/Theory/` | Implementation-independent syntax, environments, typing, definitional equality, and metatheory. |
| `Lean4Lean/Verify/` | Refinement proofs connecting Lean kernel data and executable checker paths to Theory. |
| `Lean4Lean/Experimental/` | Active semantic and metatheoretic research. These modules are not part of the supported default surface and may expose conditional endpoints. |
| `Lean4Lean/Audit/` | Machine-checked sorry and axiom-frontier policy. |
| `Lean4Lean/Tests/` | Regression, consumer-surface, replay, and differential fixtures. |
| `docs/universe-levels.md` | Boundary between raw C++ level construction, Theory semantics, and Géran canonicalization. |
| `docs/remaining-proof-experiments.md` | Implementer inventory of the workspaces, probes, refuted routes, and reusable results behind the eight supported proof obligations. |
| `docs/digama0-branch-audit.md` | Branch-by-branch audit of upstream lean4lean work, including isolated replay results and port/reject guidance. |
| `Main.lean` | Differential replay and kernel-checking command-line application. |
| `plans/` | Untracked local planning workspace (see `.gitignore`); maintainer status notes are deliberately not shipped with the repository. |
| `upstream-divergence.md` | Durable differences between Lean4Ix and lean4lean, including removal conditions. |

The central proof boundary is:

```text
Lean kernel data and execution
              |
              v
    Lean4Lean/Verify
              |
              v
     Lean4Lean/Theory
              |
              v
  Ix-specific theorem transport
```

## Design emphasis

Compared with the general upstream project, Lean4Ix currently puts additional
emphasis on:

- proof-carrying reconstruction of inductive declarations, generated recursors,
  registered reductions, projections, and structure eta from actual kernel
  execution and metadata;
- explicit environment capabilities and readiness conditions rather than
  silently assuming that every well-formed abstract environment corresponds to
  one accepted by the executable checker;
- exact accounting for opaque operations, caches, container behavior, and other
  runtime contracts that can matter to the out-of-circuit Ix kernel;
- differential fixtures that compare accepted and rejected Lean declarations,
  normalized metadata, generated rules, and nested restoration; and
- theorem interfaces designed to be transported into still more specialized
  out-of-circuit and in-circuit kernels.

This is only an overview. The divergence ledger is the authoritative record of
intentional differences, and the compiled audit
([Lean4Lean/Audit/SorryFrontier.lean](Lean4Lean/Audit/SorryFrontier.lean)) is
the authoritative machine-checked statement of the current proof and trust
frontier.

Universe levels deliberately have separate representation and semantic layers.
The executable checker reproduces the C++ kernel's cheap constructor-time
simplifications when exact expression hashes and cache entries matter, while
semantic equality and ordering continue to use the verified Géran canonical
form. The C++ compatibility functions are not a competing normalizer; see the
[universe-level design note](docs/universe-levels.md) for the precise boundary.

### Naming during the migration

The repository identity is Lean4Ix, but the Lean namespace, Lake package,
library targets, and command-line executable currently retain the historical
`Lean4Lean` / `lean4lean` names. This compatibility window is intentional while
the main theorem work and the downstream Ix consumer are stabilized.

## Building

To compile the code, install
[elan](https://lean-lang.org/lean4/doc/quickstart.html), the Lean version
manager. It will select the version pinned in [lean-toolchain](lean-toolchain).
The default supported targets can then be built with:

```
lake build
```

Individual targets include:

- `lake build Lean4Lean` builds the executable library interface without the
  proof libraries.
- `lake build lean4lean` builds the compatibility-named command-line tool.
- `lake build Lean4Lean.Theory` builds the abstract model and metatheory.
- `lake build Lean4Lean.Verify` builds the implementation-to-Theory refinement
  proofs.
- `lake build Lean4Lean.Tests` builds the supported regression modules.
- `lake build Lean4Lean.Experimental` builds the off-default research surface.

### Building with Nix

Alternatively, if you use [Nix](https://nixos.org/) with flakes enabled, you can
build the `lean4lean` CLI (including the Lean toolchain pinned by
[lean-toolchain](lean-toolchain), via [lean4-nix](https://github.com/lenianiva/lean4-nix))
with:

```
nix build .#
```

The wrapped binary in `./result/bin/lean4lean` (also `nix run .# -- <args>`)
pins its own Lean sysroot and prepends this package's search path to
`LEAN_PATH`, so it works standalone while still honoring the target project's
paths under `lake env` (see below). Other outputs:

- `nix build .#lake-dependency` builds the `Lean4Lean` library artifact
  (oleans, `.export` files, static/shared libraries — no CLI or proofs) that
  downstream Lake packages can consume via lean4-nix's
  `depOverrideDeriv.lean4lean`.
- `nix flake check` builds the `Lean4Lean.Theory` and `Lean4Lean.Verify`
  proof libraries plus the sorry audit
  ([Lean4Lean/Audit/SorryFrontier.lean](Lean4Lean/Audit/SorryFrontier.lean),
  which fails if any `Theory`/`Verify` declaration gains, loses, or renames
  a `sorry` versus its exact allowlist, pins the custom-project and generated
  decision-axiom manifests, rejects dead/forbidden or globally-simp-registered
  entries, pins and emits the exact classified closure of each of Theory,
  Verify, the shipped library, and the CLI, and rejects transitional bridges at
  the library/CLI roots) under `checks.proofs`, builds the
  `Lean4Lean.Tests` regression modules (`checks.tests`), and builds and
  runs a minimal downstream consumer of the library artifact
  (`checks.downstream-consumer`).
- `nix develop` provides a shell with the pinned `lean`/`lake` toolchain, and
  the checked-in [.envrc](.envrc) loads it automatically for
  [direnv](https://direnv.net/) users (run `direnv allow` once).

## Running

After `lake build lean4lean`, the executable is at
`.lake/build/bin/lean4lean`. Run it through `lake env` so that Lean search paths
are configured:

```sh
lake env .lake/build/bin/lean4lean
```

With no arguments, the executable checks every `.olean` on the package search
path. To check another Lean package, change to that package and run the Lean4Ix
binary in the target package's Lake environment, for example:

```sh
lake env /path/to/lean4ix/.lake/build/bin/lean4lean <args>
```

The command-line interface is:

> `lean4lean [--fresh] [-v|--verbose] [--compare] [--decl=DECL [--json] | --case=FILE] [MOD]`

* `MOD`: an optional lean module name, like `Lean4Lean.Verify`. If provided, the specified module will be checked (single-threaded); otherwise, all modules on the Lean search path will be checked (multithreaded).
* `--fresh`: Only valid when a `MOD` is provided. In this mode, the module and all its imports will be rebuilt from scratch, checking all dependencies of the module. The behavior without the flag is to only check the module itself, assuming all imports are correct.
* `--verbose`: shows the name of each declaration before adding it to the environment. Useful to know if the kernel got stuck on something.
* `--compare`: If lean4lean takes more than a second on a given definition, we also check the C++ kernel performance to see if it is also slow on the same definition and report if lean4lean is abnormally slow in comparison.
* `--decl=DECL`: Replays only the named declaration and the dependencies needed to check it. The module selection must resolve to exactly one module, and a missing, unsafe, or partial declaration is an error. This mode is useful for deterministic differential-corpus cases.
* `--json`: With `--decl`, emits one compact `lean4lean.differential` version-1 JSON result, including on rejection. Successful results compare normalized raw-source and replayed metadata for every generated constant. For a selected inductive block, they also translate closed metadata to the binder-name-free Theory syntax, run the kernel port's normalization candidate and the Theory analyzer/generator, populate analyzer-owned recursive field positions, and compare generated recursor types, flags, counts, and every rule RHS with Lean's stored metadata. Nested blocks additionally discover their previously declared target metadata, compare the port and Theory flattening results, normalize the flattened block, and compare the complete restored recursor inventory. Names, universes, and raw expressions are structural JSON; the raw codec strips only kernel-irrelevant `Expr.mdata`. The Theory translation additionally erases binder annotations, substitutes lets, and expands literals, matching Verify's deterministic strict translation. Unsupported strict-translation or normalization inputs are reported at their named phase rather than folded into a kernel-replay error.
* `--case=FILE`: Reads a versioned JSON corpus case containing `id`, optional `source`, `module`, `declaration`, `fresh`, `expectedOutcome`, and `expectedPhase`. With `source`, the runner copies the file to its declared module path in a private temporary root and invokes the pinned Lean compiler before replay. The process succeeds when the observed outcome and phase match, so expected rejection cases are first-class tests. Selection, elaboration, module loading, and kernel replay are tracked separately even when failure occurs before the replay branch. This flag supplies its own module/declaration/fresh settings and cannot be combined with positional modules, `--decl`, or `--fresh`.

The packaged differential check runs both an accepted and a rejected case from
standalone `.lean` source. The accepted module continues through the same
translation/generation comparison; the type-incorrect source is retained as
an expected rejection at the `elaboration` phase.

## Documentation and project status

- Open milestones and release planning live in a maintainer-local roadmap
  (`plans/roadmap.md`, deliberately untracked — see `.gitignore`). The
  repository-visible status record is the commit history plus the documents
  below.
- [upstream-divergence.md](upstream-divergence.md) records intentional Lean4Ix
  differences from lean4lean and the conditions under which they can disappear.
- [Lean4Lean/Audit/SorryFrontier.lean](Lean4Lean/Audit/SorryFrontier.lean)
  machine-checks the admitted-proof and axiom frontier.
- [docs/axiom-audit.md](docs/axiom-audit.md) explains the validity review,
  repaired runtime domains, and removal condition for every custom contract.
- [docs/universe-levels.md](docs/universe-levels.md) explains why exact raw
  C++ level structure and semantic Géran canonicalization coexist.
- [bugs-found.md](bugs-found.md) records Lean kernel bugs uncovered by the
  original lean4lean development.
- [divergences.md](divergences.md) records deliberate differences between the
  executable kernel port and Lean's kernel.

Do not infer support or trust from a module merely compiling. In particular,
`Lean4Lean.Experimental` may contain conditional results whose premises are the
subject of current research. Use the audit output and the divergence ledger
to interpret a specific revision.

## License

Copyright (c) 2026 Argument Computer Corporation.

Except for separately identified third-party or upstream material,
Lean4Ix is dual-licensed under either of the following, at your option:

- the [MIT License](LICENSE-MIT); or
- the [Apache License, Version 2.0](LICENSE-APACHE).

The corresponding SPDX expression is `MIT OR Apache-2.0`. Work derived from
lean4lean or other upstream projects may retain its original licensing and
notice requirements. To the maximum extent those licenses allow, we intend to
incorporate, distribute, and, where permitted, sublicense that work as part of
this unified dual-licensed package. We preserve all required copyright,
attribution, notice, and modification statements and comply with every
applicable condition necessary to do so. Where unified dual licensing is not
permitted, the upstream terms continue to control the affected material. See
[LICENSE](LICENSE) for the complete license notice, [NOTICE](NOTICE) for
upstream and third-party provenance, and [CONTRIBUTING.md](CONTRIBUTING.md) for
the inbound-equals-outbound contribution policy.
