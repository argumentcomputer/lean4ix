# Copyright (c) 2026 Argument Computer Corporation
# SPDX-License-Identifier: MIT OR Apache-2.0
{
  description = "Lean4Lean: an implementation of the Lean 4 kernel in Lean 4";

  nixConfig = {
    extra-substituters = [
      "https://argumentcomputer.cachix.org"
    ];
    extra-trusted-public-keys = [
      "argumentcomputer.cachix.org-1:ovhbTx1V56BYDerOWInQvXKXl68LlhNwEA+n7EWk1m4="
    ];
  };

  inputs = {
    # System packages, follows lean4-nix so we stay in sync
    nixpkgs.follows = "lean4-nix/nixpkgs";

    # Lean 4 & Lake
    lean4-nix.url = "github:argumentcomputer/lean4-nix";

    # Helper: flake-parts for easier outputs; follows the copy lean4-nix
    # already locks so the lock file carries a single flake-parts node
    flake-parts.follows = "lean4-nix/flake-parts";
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      # Systems we want to build for
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem = {
        system,
        pkgs,
        ...
      }: let
        # Pinned Lean toolchain (a single sysroot derivation: bin/lean,
        # bin/lake, lib, include), resolved from ./lean-toolchain by
        # lean4-nix's vendored release table.
        lean = lean4-nix.lib.${system}.fromToolchainFile ./lean-toolchain;
        # Lake package
        lake2nix = pkgs.callPackage lean4-nix.lake {inherit lean;};
        # Restrict the Lake build inputs to the files `lake build` reads, so
        # edits to unrelated files (CI, docs, the flake itself) don't
        # invalidate the cached Lean derivations. Keeps `.lean`/`.toml`, the
        # manifests lean4-nix reads while evaluating, and the
        # downstream-consumer fixture built from `${leanSrc}/nix/fixtures`.
        # NOTE: a filtered source is left unrealized under `nix flake check
        # --no-build` (fails with "path '…-lake-source' is not valid"), so the
        # nix CI job builds for real rather than eval-only.
        leanSrc = lake2nix.cleanLakeSource ./.;
        # Dependencies from lake-manifest.json (batteries). lean4-nix's
        # default target guess ("batteries" -> "Batteries") is correct, and
        # batteries ≥ v4.32 ships the shared/static cycle fix that v4.31
        # needed as a backported patch here.
        lakeDeps = lake2nix.buildDeps {
          src = leanSrc;
        };
        # System inputs every Lake build/derivation here needs.
        leanBuildInputs = [
          pkgs.gmp
          lean
          pkgs.rsync
        ];
        lakeBuildArgs = {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = leanBuildInputs;
        };
        installLicenseDocs = ''
          mkdir -p "$out/share/doc/lean4ix"
          install -m 0644 ${./LICENSE} "$out/share/doc/lean4ix/LICENSE"
          install -m 0644 ${./LICENSE-MIT} "$out/share/doc/lean4ix/LICENSE-MIT"
          install -m 0644 ${./LICENSE-APACHE} "$out/share/doc/lean4ix/LICENSE-APACHE"
          install -m 0644 ${./NOTICE} "$out/share/doc/lean4ix/NOTICE"
        '';

        # The Lake dependency artifact: the contract consumed by downstream
        # Lake packages (e.g. Ix) via
        # `lake2nix.buildDeps.depOverrideDeriv.lean4lean`. Builds exactly
        # the `Lean4Lean` library plus its shared/static facets — the
        # facets generate the `.export`/object files consumers need to
        # link executables against this read-only store path. No CLI, no
        # proof targets. (lean4-nix's capitalization heuristic would guess
        # the nonexistent `Lean4lean` target, hence the explicit name.)
        lean4leanLib = lake2nix.mkPackage (
          lakeBuildArgs
          // {
            name = "Lean4Lean";
            buildLibrary = true;
            postInstall = installLicenseDocs;
            meta = {
              description = "Lean4Lean library artifact (oleans, exports, static/shared) for downstream Lake packages";
              license = with pkgs.lib.licenses; [mit asl20];
            };
          }
        );

        # Common mkPackage args that reuse the prebuilt library artifact as the
        # Lake build's starting point and skip re-installing it — for the CLI
        # and checks, which extend the library but don't ship it.
        reuseLibArgs = {
          lakeArtifacts = lean4leanLib;
          installArtifacts = false;
        };

        # Search path covering the library and its Lake deps (batteries).
        leanPath = pkgs.lib.concatStringsSep ":" (
          map (d: "${d}/.lake/build/lib/lean") (
            [lean4leanLib] ++ builtins.attrValues lakeDeps
          )
        );

        # Raw CLI build: reuses the dependency artifact and keeps only
        # bin/lean4lean (no source copy, IR, or duplicate executable).
        lean4leanCLIRaw = lake2nix.mkPackage (
          lakeBuildArgs // reuseLibArgs // {name = "lean4lean";}
        );

        # Wrapped CLI:
        # - LEAN_SYSROOT is pinned: the binary must load core oleans from
        #   the toolchain it was compiled against, so an ambient sysroot
        #   would be wrong anyway.
        # - LEAN_PATH is prepended, not replaced: under
        #   `lake env path/to/lean4lean <mod>` the target project's search
        #   path (set by lake) stays visible, per the README workflow,
        #   while standalone runs still find this package and batteries.
        lean4leanCLI =
          pkgs.runCommand "lean4lean"
          {
            nativeBuildInputs = [pkgs.makeWrapper];
            meta = {
              description = "Lean 4 kernel typechecker CLI (lean4lean)";
              mainProgram = "lean4lean";
              license = with pkgs.lib.licenses; [mit asl20];
            };
          }
          ''
            test -x ${lean4leanCLIRaw}/bin/lean4lean
            mkdir -p $out/bin
            makeWrapper ${lean4leanCLIRaw}/bin/lean4lean $out/bin/lean4lean \
              --set LEAN_SYSROOT "${lean}" \
              --prefix LEAN_PATH : "${leanPath}"
            ${installLicenseDocs}
          '';

        # A check that builds extra Lake targets over the library artifact and
        # installs nothing: the build — including any elaboration-time
        # assertions in those targets — is the test.
        mkLakeCheck = name: targets:
          lake2nix.mkPackage (
            lakeBuildArgs
            // reuseLibArgs
            // {
              inherit name;
              buildPhase = ''
                runHook preBuild
                lake build ${pkgs.lib.concatStringsSep " " targets}
                runHook postBuild
              '';
            }
          );

        # Proof libraries: the abstract metatheory and the proof that the
        # implementation satisfies it, built in one Lake workspace so Theory
        # modules compile once, then the sorry frontier:
        # `Lean4Lean.Audit.SorryFrontier` fails the build if any Theory/Verify
        # declaration gains, loses, or renames a `sorry` versus its allowlist.
        # Its reachability sections pin every custom project and generated
        # decision axiom, reject dead/forbidden entries, and emit exact
        # root-specific closures for Theory, Verify, the shipped library, and
        # the CLI. This is not a default target, so building it over the
        # just-built surface is the whole check.
        proofs = mkLakeCheck "Lean4Lean-proofs" [
          "Lean4Lean.Theory"
          "Lean4Lean.Verify"
          # The audit imports the executable's source module to inspect the
          # real CLI closure; build only its olean facet, not the executable.
          "Main"
          "Lean4Lean.Audit.SorryFrontier"
        ];

        # Basic test suite: the `Lean4Lean.Tests.*` regression modules (the
        # nested-inductive kernel checks and the toolchain audit) run their
        # assertions at elaboration via `run_meta`/`#guard`, so building the
        # target is the test run.
        tests = mkLakeCheck "Lean4Lean-tests" ["Lean4Lean.Tests"];

        # Downstream-consumer check: a minimal Lake package that requires
        # lean4lean, links an executable against the read-only dependency
        # artifact, and runs it. This is the in-repo home for the contract
        # Ix's flake relies on: if target names, installArtifacts, source
        # layout, or the shared/static facets change incompatibly, this
        # fails before any consumer updates its pin.
        consumer = lake2nix.mkPackage {
          name = "consumer";
          # lake2nix reads this fixture's manifest during evaluation; it is
          # included in `leanSrc` (the fileset covers `nix/fixtures`), so it is
          # taken from the library's source path rather than a separate store
          # path.
          src = "${leanSrc}/nix/fixtures/consumer";
          lakeDeps = {
            lean4lean = lean4leanLib;
            batteries = lakeDeps.batteries;
          };
          installArtifacts = false;
          buildInputs = leanBuildInputs;
          postBuild = ''
            ./.lake/build/bin/consumer | grep -q consumer-ok
          '';
        };

        # A CLI check: run `body` (which writes the wrapped CLI's stdout to
        # `out`), then require the "checked N declarations" summary line.
        mkCliCheck = name: body:
          pkgs.runCommand "lean4lean-${name}" {} ''
            ${body}
            grep -Eq "^checked [0-9]+ declarations" out
            touch $out
          '';

        # Regression test for the `replayFromImports` teardown segfault (see
        # divergence ledger D002): run the shipped wrapper from a
        # clean environment on a small module and require a clean exit plus the
        # summary line the crash used to swallow.
        cliSmoke = mkCliCheck "cli-smoke" ''
          unset LEAN_PATH LEAN_SYSROOT
          ${lean4leanCLI}/bin/lean4lean Lean4Lean.Declaration > out
        '';

        # The external-project case: with an ambient LEAN_PATH already set
        # (as `lake env` sets one for a target project), the wrapper must
        # prepend its package paths rather than lose them or clobber the
        # ambient value — a --set/--set-default wrapper fails this check.
        cliSmokeExternal = mkCliCheck "cli-smoke-external" ''
          mkdir ambient
          LEAN_PATH=$PWD/ambient ${lean4leanCLI}/bin/lean4lean Lean4Lean.Declaration > out
        '';

        # No-argument mode: with only the repo's lake-manifest.json in the
        # working directory, the CLI must infer the package (matching the
        # manifest name case-insensitively against the Lean4Lean module
        # root) and check the whole library.
        cliNoArg = mkCliCheck "cli-noarg" ''
          cp ${./lake-manifest.json} lake-manifest.json
          ${lean4leanCLI}/bin/lean4lean > out
        '';

        # Differential-harness primitive: an exact declaration succeeds with
        # the expected replay count, while invalid targets must fail rather
        # than report a misleading zero-declaration success.
        cliSingleDecl = mkCliCheck "cli-single-decl" ''
          unset LEAN_PATH LEAN_SYSROOT
          ${lean4leanCLI}/bin/lean4lean --decl=Lean.Expr.prop Lean4Lean.Expr > out
          grep -qx "checked 1 declarations" out
          if ${lean4leanCLI}/bin/lean4lean --decl=Lean.DoesNotExist \
            Lean4Lean.Declaration > missing 2>&1; then
            echo "missing --decl target unexpectedly succeeded" >&2
            exit 1
          fi
          grep -q "declaration Lean.DoesNotExist is not present in the selected replay set" missing
          if ${lean4leanCLI}/bin/lean4lean --decl=Lean.Expr.prop \
            Lean4Lean > ambiguous 2>&1; then
            echo "ambiguous --decl module unexpectedly succeeded" >&2
            exit 1
          fi
          grep -q -- "--decl flag requires exactly one selected module" ambiguous
        '';

        differentialElaborationFixture =
          pkgs.writeText
          "DifferentialElaborationFixture.lean"
          ''
            namespace DifferentialElaborationFixture

            abbrev FieldAlias := Nat

            inductive RecursiveAlias where
              | base
              | step (payload : FieldAlias) (tail : RecursiveAlias)

            end DifferentialElaborationFixture
          '';

        differentialElaborationRejectFixture =
          pkgs.writeText
          "DifferentialElaborationRejectFixture.lean"
          ''
            namespace DifferentialElaborationRejectFixture

            def broken : Nat := "not a natural number"

            end DifferentialElaborationRejectFixture
          '';

        differentialMutualFixture =
          pkgs.writeText
          "DifferentialMutualFixture.lean"
          ''
            namespace DifferentialMutualFixture

            mutual

            inductive Tree (α : Type u) : Type u where
              | leaf : α → Tree α
              | node : TreeList α → Tree α
              | branch : (α → TreeList α) → Tree α

            inductive TreeList (α : Type u) : Type u where
              | nil : TreeList α
              | cons : Tree α → TreeList α → TreeList α

            end

            end DifferentialMutualFixture
          '';

        # Versioned differential corpus contract: ordinary, normalizing, and
        # nested inductive cases record raw/Theory/generated metadata
        # (including analyzer recursion positions and every rule RHS), while
        # declared selection, elaboration, module-load, and kernel-replay
        # negatives succeed only at their expected phase. A wrong expectation
        # must still fail.
        cliDifferentialCorpus = pkgs.runCommand "lean4lean-cli-differential-corpus" {} ''
          unset LEAN_PATH LEAN_SYSROOT
          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "fuel-config-metadata";
            module = "Lean4Lean.FuelConfig";
            declaration = "Lean4Lean.FuelConfig";
            fresh = false;
            expectedOutcome = "accepted";
            expectedPhase = "metadata-comparison";
          }}' > accepted.json
          ${lean4leanCLI}/bin/lean4lean --case=accepted.json > accepted
          grep -q '"caseId":"fuel-config-metadata"' accepted
          grep -q '"outcome":"accepted"' accepted
          grep -q '"phase":"metadata-comparison"' accepted
          grep -q '"metadataEqual":true' accepted
          grep -q '"displayName":"Lean4Lean.FuelConfig.rec"' accepted
          grep -q '"fieldPositions":\[0,1,2,3,4,5\]' accepted
          grep -q '"k":false' accepted
          grep -q '"ruleCount":1' accepted
          grep -q '"rhs":' accepted
          grep -q '"theoryTranslation":"verify-tr-expr-s-closed-v1"' accepted
          grep -q '"theoryBlocks":\[{' accepted
          grep -q '"normalizationChanged":false' accepted
          grep -q '"theoryRecursive":false' accepted
          grep -q '"recursivePositions":\[\]' accepted

          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "equiv-manager-normalization";
            module = "Lean4Lean.EquivManager";
            declaration = "Lean4Lean.EquivManager";
            fresh = false;
            expectedOutcome = "accepted";
            expectedPhase = "metadata-comparison";
          }}' > normalizing.json
          ${lean4leanCLI}/bin/lean4lean --case=normalizing.json > normalizing
          grep -q '"caseId":"equiv-manager-normalization"' normalizing
          grep -q '"outcome":"accepted"' normalizing
          grep -q '"normalizationChanged":true' normalizing
          grep -q '"displayName":"Lean4Lean.EquivManager.rec"' normalizing

          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "candidate-list-recursion";
            module = "Lean4Lean.Inductive.Add";
            declaration = "Lean4Lean.AddInductive.CandidateList";
            fresh = false;
            expectedOutcome = "accepted";
            expectedPhase = "metadata-comparison";
          }}' > recursive.json
          ${lean4leanCLI}/bin/lean4lean --case=recursive.json > recursive
          grep -q '"caseId":"candidate-list-recursion"' recursive
          grep -q '"outcome":"accepted"' recursive
          grep -q '"theoryRecursive":true' recursive
          grep -q '"kernelRecursive":\[true\]' recursive
          grep -q '"displayName":"Lean4Lean.AddInductive.CandidateList.rec"' recursive
          grep -q '"recursivePositions":\[3\]' recursive

          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "mutual-tree-recursion";
            source = differentialMutualFixture;
            module = "DifferentialMutualFixture";
            declaration = "DifferentialMutualFixture.Tree";
            fresh = false;
            expectedOutcome = "accepted";
            expectedPhase = "metadata-comparison";
          }}' > mutual.json
          ${lean4leanCLI}/bin/lean4lean --case=mutual.json > mutual
          grep -q '"caseId":"mutual-tree-recursion"' mutual
          grep -q '"outcome":"accepted"' mutual
          grep -q '"kernelRecursive":\[true,true\]' mutual
          grep -q '"displayName":"DifferentialMutualFixture.Tree.rec"' mutual
          grep -q '"displayName":"DifferentialMutualFixture.TreeList.rec"' mutual
          grep -q '"recursivePositions":\[0,1\]' mutual

          # Start from source rather than an existing olean: the case runner
          # invokes the pinned Lean compiler in a private module root, then
          # enters the same replay/translation/generation comparison.
          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "source-elaboration-recursion";
            source = differentialElaborationFixture;
            module = "DifferentialElaborationFixture";
            declaration = "DifferentialElaborationFixture.RecursiveAlias";
            fresh = false;
            expectedOutcome = "accepted";
            expectedPhase = "metadata-comparison";
          }}' > elaborated.json
          ${lean4leanCLI}/bin/lean4lean --case=elaborated.json > elaborated-output
          grep -q '"caseId":"source-elaboration-recursion"' elaborated-output
          grep -q '"outcome":"accepted"' elaborated-output
          grep -q '"phase":"metadata-comparison"' elaborated-output
          grep -q '"normalizationChanged":true' elaborated-output
          grep -q '"theoryRecursive":true' elaborated-output
          grep -q '"displayName":"DifferentialElaborationFixture.RecursiveAlias.rec"' \
            elaborated-output
          grep -q '"recursivePositions":\[1\]' elaborated-output

          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "source-elaboration-rejection";
            source = differentialElaborationRejectFixture;
            module = "DifferentialElaborationRejectFixture";
            declaration = "DifferentialElaborationRejectFixture.broken";
            fresh = false;
            expectedOutcome = "rejected";
            expectedPhase = "elaboration";
          }}' > elaboration-rejected.json
          ${lean4leanCLI}/bin/lean4lean --case=elaboration-rejected.json \
            > elaboration-rejected
          grep -q '"caseId":"source-elaboration-rejection"' elaboration-rejected
          grep -q '"outcome":"rejected"' elaboration-rejected
          grep -q '"phase":"elaboration"' elaboration-rejected
          grep -q 'source elaboration failed' elaboration-rejected

          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "syntax-nested-restoration";
            module = "Init.Prelude";
            declaration = "Lean.Syntax";
            fresh = true;
            expectedOutcome = "accepted";
            expectedPhase = "metadata-comparison";
          }}' > nested.json
          ${lean4leanCLI}/bin/lean4lean --case=nested.json > nested
          grep -q '"caseId":"syntax-nested-restoration"' nested
          grep -q '"outcome":"accepted"' nested
          grep -q '"phase":"metadata-comparison"' nested
          grep -q '"transformation":"nested-elimination+normalization"' nested
          grep -q '"auxiliaryFamilyCount":2' nested
          grep -q '"kernelAuxiliaryFamilyCount":2' nested
          grep -q '"displayName":"Lean.Syntax.rec_1"' nested
          grep -q '"displayName":"Lean.Syntax.rec_2"' nested
          grep -q '"displayName":"Lean.Syntax.node"' nested
          grep -q '"recursivePositions":\[2\]' nested

          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "ambiguous-module-selection";
            module = "Lean4Lean";
            declaration = "Lean4Lean.FuelConfig";
            fresh = false;
            expectedOutcome = "rejected";
            expectedPhase = "selection";
          }}' > selection.json
          ${lean4leanCLI}/bin/lean4lean --case=selection.json > selection
          grep -q '"caseId":"ambiguous-module-selection"' selection
          grep -q '"outcome":"rejected"' selection
          grep -q '"phase":"selection"' selection

          # `Lean4Lean.Environment` has child modules. Fresh replay must select
          # the exact root rather than fail as an ambiguous prefix match; the
          # deliberately missing declaration should therefore be rejected only
          # after selection, at kernel replay.
          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "fresh-exact-module-selection";
            module = "Lean4Lean.Environment";
            declaration = "Lean.DoesNotExist";
            fresh = true;
            expectedOutcome = "rejected";
            expectedPhase = "kernel-replay";
          }}' > fresh-selection.json
          ${lean4leanCLI}/bin/lean4lean --case=fresh-selection.json > fresh-selection
          grep -q '"caseId":"fresh-exact-module-selection"' fresh-selection
          grep -q '"outcome":"rejected"' fresh-selection
          grep -q '"phase":"kernel-replay"' fresh-selection

          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "missing-module";
            module = "Lean4Lean.NoSuchDifferentialModule";
            declaration = "Lean.DoesNotExist";
            fresh = false;
            expectedOutcome = "rejected";
            expectedPhase = "module-load";
          }}' > module-load.json
          ${lean4leanCLI}/bin/lean4lean --case=module-load.json > module-load
          grep -q '"caseId":"missing-module"' module-load
          grep -q '"outcome":"rejected"' module-load
          grep -q '"phase":"module-load"' module-load

          printf '%s\n' '${builtins.toJSON {
            schema = "lean4lean.differential";
            version = 1;
            id = "missing-declaration";
            module = "Lean4Lean.Declaration";
            declaration = "Lean.DoesNotExist";
            fresh = false;
            expectedOutcome = "rejected";
            expectedPhase = "kernel-replay";
          }}' > rejected.json
          ${lean4leanCLI}/bin/lean4lean --case=rejected.json > rejected
          grep -q '"caseId":"missing-declaration"' rejected
          grep -q '"outcome":"rejected"' rejected
          grep -q '"phase":"kernel-replay"' rejected

          sed 's/"expectedOutcome":"rejected"/"expectedOutcome":"accepted"/' \
            rejected.json > wrong-expectation.json
          if ${lean4leanCLI}/bin/lean4lean --case=wrong-expectation.json \
            > wrong-expectation; then
            echo "mismatched differential expectation unexpectedly succeeded" >&2
            exit 1
          fi
          grep -q '"outcome":"rejected"' wrong-expectation
          touch $out
        '';
      in {
        _module.args.pkgs = import nixpkgs {
          inherit system;
        };

        packages = {
          default = lean4leanCLI;
          lean4lean = lean4leanCLI;
          lake-dependency = lean4leanLib;
        };

        apps = let
          lean4leanApp = {
            type = "app";
            program = "${lean4leanCLI}/bin/lean4lean";
            meta.description = "Lean 4 kernel typechecker CLI (lean4lean)";
          };
        in {
          default = lean4leanApp;
          lean4lean = lean4leanApp;
        };

        checks = {
          inherit proofs tests;
          downstream-consumer = consumer;
          cli-smoke = cliSmoke;
          cli-smoke-external = cliSmokeExternal;
          cli-noarg = cliNoArg;
          cli-single-decl = cliSingleDecl;
          cli-differential-corpus = cliDifferentialCorpus;
        };

        devShells.default = pkgs.mkShell {
          packages = [
            lean
          ];
        };

        formatter = pkgs.alejandra;
      };
    };
}
