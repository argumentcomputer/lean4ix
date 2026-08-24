# Lean-for-Lean

This is an implementation of the Lean 4 kernel written in (mostly) pure Lean 4.
It is derived directly from the C++ kernel implementation, and as such likely
shares some implementation bugs with it (it's not really an independent
implementation), although it also benefits from the same algorithmic performance
improvements existing in the C++ Lean kernel.

The project also houses some metatheory regarding the Lean
system, in the same general direction as the
[MetaCoq project](https://github.com/MetaCoq/metacoq/).

## Building

To compile the code, you will need [Lean](https://lean-lang.org/lean4/doc/quickstart.html), or more specifically `elan`, the Lean version manager, which will make sure you have the right version of lean as specified in the [lean-toolchain](lean-toolchain) file. Assuming you have elan, the project can be compiled with:

```
lake build
```

This builds all components but you can also build them separately:

* `lake build Lean4Lean` builds the `Lean4Lean` library interface, and does not include any of the proofs.
* `lake build lean4lean` (note the capitalization!) builds the `lean4lean` command line tool, again without building proofs.
* `lake build Lean4Lean.Theory` contains the Lean metatheory and properties.
* `lake build Lean4Lean.Verify` is the proof that the `Lean4Lean` implementation satisfies the `Lean4Lean.Theory` abstract specification.

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

* `nix build .#lake-dependency` builds the `Lean4Lean` library artifact
  (oleans, `.export` files, static/shared libraries — no CLI or proofs) that
  downstream Lake packages can consume via lean4-nix's
  `depOverrideDeriv.lean4lean`.
* `nix flake check` builds the `Lean4Lean.Theory` and `Lean4Lean.Verify`
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
* `nix develop` provides a shell with the pinned `lean`/`lake` toolchain, and
  the checked-in [.envrc](.envrc) loads it automatically for
  [direnv](https://direnv.net/) users (run `direnv allow` once).

## Running

After `lake build lean4lean`, the executable will be in `.lake/build/bin/lean4lean`. Because it requires some environment variables to be set for search paths which are provided by lake, you should evaluate it like `lake env .lake/build/bin/lean4lean`.

If you run this as is (with no additional arguments), it will check every olean in the `lean4lean` package itself, which is probably not what you want. To check a different Lean package you should navigate the directory of the target project, then use `lake env path/to/lean4lean/.lake/build/bin/lean4lean <args>` to run `lean4lean` in the context of the target project. The command line arguments are:

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

## More documentation

* [bugs-found.md](bugs-found.md): A list of kernel bugs that the lean4lean project has uncovered.
* [divergences.md](divergences.md): A list of deliberate divergences between lean's kernel and the lean4lean kernel.

## (Selected) file breakdown

* `Main.lean`: command line app
* `Lean4Lean`: source files
  * `Environment.lean`: library entry point
  * `TypeChecker.lean`: main recursive function
  * `Inductive`
    * `Add.lean`: constructing inductive recursors
    * `Reduce.lean`: inductive iota rules
  * `Quot.lean`: quotient types handling
  * `Primitive.lean`: checking correctness of built-ins
  * `Std`: stuff that should exist upstream
  * `Theory`: lean metatheory
    * `VLevel.lean`: level expressions
    * `VExpr.lean`: expressions (boring de Bruijn variable theorems are here)
    * `VDecl.lean`: declarations
    * `VEnv.lean`: environment
    * `Meta.lean`: elaborator producing `VExpr`s
    * `Inductive.lean`: inductive types
    * `Quot.lean`: quotient types
    * `Typing`
      * `Basic.lean`: The typing relation itself
      * `Lemmas.lean`: theorems about the typing relation
      * `Meta.lean`: tactic for proving typing judgments
      * `Strong.lean`: proof that you can have all the inductive hypotheses
      * `UniqueTyping.lean`: conjectures about the typing relation
      * `Env.lean`: typing for environments
  * `Verify`: relation between the metatheory and the kernel
    * `Axioms.lean`: theorems about upstream opaques that shouldn't be opaque
    * `Expr.lean`: correctness of basics on `Expr`
    * `Level.lean`: correctness of basics on `Level`
    * `Level/Std.lean`: soundness of the standard-library level operations
    * `VLCtx.lean`: a "translation context" suitable for translating expressions
    * `LocalContext.lean`: properties of lean's `LocalContext` type
    * `NameGenerator.lean`: properties of the fresh name generator
    * `Typing`
      * `Expr.lean`: translating expressions (`TrExpr` is here)
      * `Lemmas.lean`: properties of `TrExpr`
      * `ConditionallyTyped.lean`: properties of expressions in caches that may be out of scope
    * `Environment`
      * `Basic.lean`: translating environments
      * `Lemmas.lean`: properties of `TrEnv`
    * `TypeChecker`
      * `Basic.lean`: typechecker invariants
      * `EquivManager.lean`: invariants for the union-find defeq cache
      * `InferType.lean`: correctness of `inferType`
      * `WHNF.lean`: correctness of `whnf`
      * `IsDefEq.lean`: correctness of `isDefEq`
    * `TypeChecker.lean`: top-level typechecker correctness
  * `Experimental`: work in progress formalizations and ideas
      * `Stratified.lean`: stratified typing judgment
      * `StratifiedUntyped.lean` another stratified typing judgment
      * `ParallelReduction.lean`: stuff related to church-rosser
      * `Stronger.lean`: a more heavily annotated typing judgment
