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
        # Restrict the Lake build inputs to Lean-relevant files so edits to
        # unrelated files (CI, docs, the flake itself) don't invalidate the
        # cached Lean derivations. Covers the library/CLI/proof/test/audit
        # sources, the manifests lean4-nix reads while evaluating, and the
        # downstream-consumer fixture built from `${leanSrc}/nix/fixtures`.
        # NOTE: a fileset source is left unrealized under `nix flake check
        # --no-build` (fails with "path '…-source' is not valid"), so the nix
        # CI job builds for real rather than eval-only.
        leanSrc = pkgs.lib.fileset.toSource {
          root = ./.;
          fileset = pkgs.lib.fileset.unions [
            ./lakefile.toml
            ./lake-manifest.json
            ./lean-toolchain
            ./nix/fixtures
            (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./.)
          ];
        };
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
        # System inputs every Lake build/derivation here needs.
        leanBuildInputs = [
          pkgs.gmp
          pkgs.lean.lean-all
          pkgs.rsync
        ];
        lakeBuildArgs = {
          inherit lakeDeps;
          src = leanSrc;
          buildInputs = leanBuildInputs;
        };

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
            meta = {
              description = "Lean4Lean library artifact (oleans, exports, static/shared) for downstream Lake packages";
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
            };
          }
          ''
            test -x ${lean4leanCLIRaw}/bin/lean4lean
            mkdir -p $out/bin
            makeWrapper ${lean4leanCLIRaw}/bin/lean4lean $out/bin/lean4lean \
              --set LEAN_SYSROOT "${pkgs.lean.lean-all}" \
              --prefix LEAN_PATH : "${leanPath}"
          '';

        # A check that builds extra Lake targets over the library artifact and
        # installs nothing: the build — including any elaboration-time
        # assertions in those targets — is the test.
        mkLakeCheck = name: buildTargets:
          lake2nix.mkPackage (
            lakeBuildArgs
            // reuseLibArgs
            // {
              inherit name;
              buildPhase = ''
                runHook preBuild
                ${buildTargets}
                runHook postBuild
              '';
            }
          );

        # Proof libraries: the abstract metatheory and the proof that the
        # implementation satisfies it, built in one Lake workspace so Theory
        # modules compile once, then the sorry frontier:
        # `Lean4Lean.Audit.SorryFrontier` fails the build if any Theory/Verify
        # declaration gains, loses, or renames a `sorry` versus its allowlist.
        # It is not a default target, so building it over the just-built
        # surface is the whole check.
        proofs = mkLakeCheck "Lean4Lean-proofs" ''
          lake build Lean4Lean.Theory Lean4Lean.Verify
          lake build Lean4Lean.Audit.SorryFrontier
        '';

        # Basic test suite: the `Lean4Lean.Tests.*` regression modules (the
        # nested-inductive kernel checks and the toolchain audit) run their
        # assertions at elaboration via `run_meta`/`#guard`, so building the
        # target is the test run.
        tests = mkLakeCheck "Lean4Lean-tests" "lake build Lean4Lean.Tests";

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
        # plans/DEPRECATED-segfault-fix-plan.md): run the shipped wrapper from a
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
