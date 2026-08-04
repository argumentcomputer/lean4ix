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
    lean4-nix.url = "github:lenianiva/lean4-nix";

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
        # Lake package
        lake2nix = pkgs.callPackage lean4-nix.lake {};
        # lean4-nix reads lake-manifest.json while evaluating derivations.
        # Reuse the flake's lazy source instead of creating a nested
        # fileset.toSource path that may be unrealized under --no-build.
        leanSrc = inputs.self.outPath;
        # Batteries v4.31.0 accidentally split deprecated recycling modules
        # into a second Lake library with a dependency back to Batteries.  Its
        # shared/static facets therefore form a cycle, which matters here
        # because lake2nix exports those facets for downstream consumers.
        # Backport the upstream fix released after the v4.31.0 tag.
        batteries431CycleFix = pkgs.fetchurl {
          url = "https://github.com/leanprover-community/batteries/commit/ba9a97018925ecc18fd8411d8c53de6056cf9dff.patch";
          hash = "sha256-HjF68B7QUeioDcGT/q6SWQEqPp8o5OQqErfw5D9rdIY=";
        };
        # Dependencies from lake-manifest.json (batteries). lean4-nix's
        # default target guess ("batteries" -> "Batteries") is correct, so
        # only the v4.31 shared/static cycle backport is needed.
        lakeDeps = lake2nix.buildDeps {
          src = leanSrc;
          depOverride.batteries.patches = [batteries431CycleFix];
        };
        lakeBuildArgs = {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = [
            pkgs.gmp
            pkgs.lean.lean-all
            pkgs.rsync
          ];
        };

        # The Lake dependency artifact: the contract consumed by downstream
        # Lake packages (e.g. Ix) via
        # `lake2nix.buildDeps.depOverrideDeriv.lean4lean`. Builds exactly
        # the `Lean4Lean` library plus its shared/static facets — the
        # facets generate the `.export`/object files consumers need to
        # link executables against this read-only store path. No CLI, no
        # proof targets. (lean4-nix's capitalization heuristic would guess
        # the nonexistent `Lean4lean` target, hence the explicit name.)
        lean4leanLakeDependency = lake2nix.mkPackage (
          lakeBuildArgs
          // {
            name = "Lean4Lean";
            buildLibrary = true;
            meta = {
              description = "Lean4Lean library artifact (oleans, exports, static/shared) for downstream Lake packages";
            };
          }
        );

        # Like lake-dependency, but additionally builds the Theory and
        # Verify proof libraries (default facets), for consumers that
        # import the metatheory too — Ix's IxTcVerify imports both
        # Lean4Lean.Theory.* and Lean4Lean.Verify.*, so the plain
        # implementation-only artifact is not enough for it.
        lean4leanLakeDependencyFull = lake2nix.mkPackage (
          lakeBuildArgs
          // {
            name = "Lean4Lean-full";
            lakeArtifacts = lean4leanLakeDependency;
            buildPhase = ''
              runHook preBuild
              lake build Lean4Lean Lean4Lean.Theory Lean4Lean.Verify
              lake build Lean4Lean:shared Lean4Lean:static
              runHook postBuild
            '';
            meta = {
              description = "Lean4Lean library artifact including the Theory and Verify proof libraries";
            };
          }
        );

        # Search path covering the library and its Lake deps (batteries).
        leanPath = pkgs.lib.concatStringsSep ":" (
          map (d: "${d}/.lake/build/lib/lean") (
            [lean4leanLakeDependency] ++ builtins.attrValues lakeDeps
          )
        );

        # Raw CLI build: reuses the dependency artifact and keeps only
        # bin/lean4lean (no source copy, IR, or duplicate executable).
        lean4leanCLIRaw = lake2nix.mkPackage (
          lakeBuildArgs
          // {
            lakeArtifacts = lean4leanLakeDependency;
            installArtifacts = false;
            name = "lean4lean";
          }
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
            };
          }
          ''
            test -x ${lean4leanCLIRaw}/bin/lean4lean
            mkdir -p $out/bin
            makeWrapper ${lean4leanCLIRaw}/bin/lean4lean $out/bin/lean4lean \
              --set LEAN_SYSROOT "${pkgs.lean.lean-all}" \
              --prefix LEAN_PATH : "${leanPath}"
          '';

        # Proof libraries: the abstract metatheory and the proof that the
        # implementation satisfies it. One derivation builds both targets
        # in one Lake workspace so Theory modules are compiled once.
        proofs = lake2nix.mkPackage (
          lakeBuildArgs
          // {
            name = "Lean4Lean-proofs";
            lakeArtifacts = lean4leanLakeDependency;
            installArtifacts = false;
            buildPhase = ''
              runHook preBuild
              lake build Lean4Lean.Theory Lean4Lean.Verify
              runHook postBuild
            '';
          }
        );

        # Downstream-consumer check: a minimal Lake package that requires
        # lean4lean, links an executable against the read-only dependency
        # artifact, and runs it. This is the in-repo home for the contract
        # Ix's flake relies on: if target names, installArtifacts, source
        # layout, or the shared/static facets change incompatibly, this
        # fails before any consumer updates its pin.
        consumer = lake2nix.mkPackage {
          name = "consumer";
          # lake2nix reads this fixture's manifest during evaluation. Keep it
          # inside the already-realized flake source rather than coercing the
          # subdirectory into a second, not-yet-realized store path.
          src = "${leanSrc}/nix/fixtures/consumer";
          lakeDeps = {
            lean4lean = lean4leanLakeDependency;
            batteries = lakeDeps.batteries;
          };
          installArtifacts = false;
          buildInputs = [
            pkgs.gmp
            pkgs.lean.lean-all
            pkgs.rsync
          ];
          postBuild = ''
            ./.lake/build/bin/consumer | grep -q consumer-ok
          '';
        };

        # Regression test for the `replayFromImports` teardown segfault (see
        # plans/DEPRECATED-segfault-fix-plan.md): run the shipped wrapper from a clean
        # environment on a small module and require a clean exit plus the
        # summary line the crash used to swallow.
        cliSmoke =
          pkgs.runCommand "lean4lean-cli-smoke" {}
          ''
            unset LEAN_PATH LEAN_SYSROOT
            ${lean4leanCLI}/bin/lean4lean Lean4Lean.Declaration > out
            grep -Eq "^checked [0-9]+ declarations" out
            touch $out
          '';

        # The external-project case: with an ambient LEAN_PATH already set
        # (as `lake env` sets one for a target project), the wrapper must
        # prepend its package paths rather than lose them or clobber the
        # ambient value — a --set/--set-default wrapper fails this check.
        cliSmokeExternal =
          pkgs.runCommand "lean4lean-cli-smoke-external" {}
          ''
            mkdir ambient
            LEAN_PATH=$PWD/ambient ${lean4leanCLI}/bin/lean4lean Lean4Lean.Declaration > out
            grep -Eq "^checked [0-9]+ declarations" out
            touch $out
          '';

        # No-argument mode: with only the repo's lake-manifest.json in the
        # working directory, the CLI must infer the package (matching the
        # manifest name case-insensitively against the Lean4Lean module
        # root) and check the whole library.
        cliNoArg =
          pkgs.runCommand "lean4lean-cli-noarg" {}
          ''
            cp ${./lake-manifest.json} lake-manifest.json
            ${lean4leanCLI}/bin/lean4lean > out
            grep -Eq "^checked [0-9]+ declarations" out
            touch $out
          '';
        # Sorry-frontier audit: every real `sorry` token outside
        # Lean4Lean/Experimental/ must match the script's exact allowlist
        # (the upstream-gaps plan's Tier S/P/V/R inventory), so progress
        # shrinks the allowlist and regressions fail loudly. Pure text
        # audit — no Lean toolchain involved.
        sorryFrontier =
          pkgs.runCommand "lean4lean-sorry-frontier" {}
          ''
            ${pkgs.perl}/bin/perl \
              ${./.github/scripts/check_sorry_frontier.pl} ${leanSrc} \
              | tee $out
          '';
      in {
        # Lean overlay
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [
            (lean4-nix.readToolchainFile ./lean-toolchain)
          ];
        };

        packages = {
          default = lean4leanCLI;
          lean4lean = lean4leanCLI;
          lake-dependency = lean4leanLakeDependency;
          lake-dependency-full = lean4leanLakeDependencyFull;
          # Compatibility alias for early users of the staged flake.
          lib = lean4leanLakeDependency;
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
          inherit proofs;
          sorry-frontier = sorryFrontier;
          downstream-consumer = consumer;
          cli-smoke = cliSmoke;
          cli-smoke-external = cliSmokeExternal;
          cli-noarg = cliNoArg;
        };

        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            lean.lean-all
          ];
        };

        formatter = pkgs.alejandra;
      };
    };
}
