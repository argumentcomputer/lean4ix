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

    # Helper: flake-parts for easier outputs
    flake-parts.url = "github:hercules-ci/flake-parts";
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
        # unrelated files (flake.nix, docs, the nix/ fixtures) don't
        # invalidate the build.
        leanSrc = pkgs.lib.fileset.toSource {
          root = ./.;
          fileset =
            pkgs.lib.fileset.difference
            (pkgs.lib.fileset.unions [
              ./lakefile.toml
              ./lake-manifest.json
              ./lean-toolchain
              (pkgs.lib.fileset.fileFilter (f: f.hasExt "lean") ./.)
            ])
            ./nix;
        };
        # Dependencies from lake-manifest.json (batteries). lean4-nix's
        # default target guess ("batteries" -> "Batteries") is correct, so
        # no overrides are needed.
        lakeDeps = lake2nix.buildDeps {
          src = leanSrc;
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
          src = ./nix/fixtures/consumer;
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
        # plans/segfault-fix-plan.md): run the shipped wrapper from a clean
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
      in {
        # Lean overlay
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [(lean4-nix.readToolchainFile ./lean-toolchain)];
        };

        packages = {
          default = lean4leanCLI;
          lean4lean = lean4leanCLI;
          lake-dependency = lean4leanLakeDependency;
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
          downstream-consumer = consumer;
          cli-smoke = cliSmoke;
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
