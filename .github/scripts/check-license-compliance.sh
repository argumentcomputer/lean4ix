#!/usr/bin/env bash
# Copyright (c) 2026 Argument Computer Corporation
# SPDX-License-Identifier: MIT OR Apache-2.0

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

upstream_ref="${1:-upstream/master}"
if ! git rev-parse --verify --quiet "$upstream_ref^{commit}" >/dev/null; then
  echo "license audit: missing upstream ref: $upstream_ref" >&2
  exit 1
fi

base="$(git merge-base HEAD "$upstream_ref")"
change_notice="This file is derived from lean4lean and has been modified by Argument Computer Corporation."
missing=0

while IFS= read -r -d '' file; do
  case "$file" in
    *.lean | *.md | *.nix | *.toml | *.yaml | *.yml | .gitignore | LICENSE)
      if ! rg -qF "$change_notice" "$file"; then
        echo "license audit: modified file lacks change notice: $file" >&2
        missing=1
      fi
      ;;
  esac
done < <(git diff --name-only -z --diff-filter=MRC "$base")

if (( missing != 0 )); then
  exit 1
fi

for file in LICENSE LICENSE-MIT LICENSE-APACHE NOTICE CONTRIBUTING.md; do
  test -f "$file" || {
    echo "license audit: missing required file: $file" >&2
    exit 1
  }
done

if [[ "${CI:-}" == "true" ]]; then
  archive_files="$(git archive --format=tar HEAD | tar -tf -)"
  for file in LICENSE LICENSE-MIT LICENSE-APACHE NOTICE CONTRIBUTING.md; do
    if ! rg -qxF "$file" <<<"$archive_files"; then
      echo "license audit: source archive omits required file: $file" >&2
      exit 1
    fi
  done
fi

rg -qF 'SPDX-License-Identifier: MIT OR Apache-2.0' LICENSE
rg -qF 'Copyright (c) 2026 Argument Computer Corporation' LICENSE-MIT
rg -q '^license = "MIT OR Apache-2.0"$' lakefile.toml
rg -q '^licenseFiles = \["LICENSE", "LICENSE-MIT", "LICENSE-APACHE", "NOTICE"\]$' lakefile.toml
rg -qF 'license = with pkgs.lib.licenses; [mit asl20];' flake.nix
rg -qF 'share/doc/lean4ix' flake.nix

echo "license audit: OK"
