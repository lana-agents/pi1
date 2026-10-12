#!/usr/bin/env bash
set -euo pipefail

# $HOME may be read-only in a sandbox, so keep lake's cache dir inside the repo.
export XDG_CACHE_HOME="$PWD/.cache-home"

# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
lake exe mk_all --lib Pi1 --git --check || exit 1

# No `sorry` / `axiom` in the library.
if grep -rnE "^\s*axiom |\bsorry\b" Pi1 Pi1.lean; then
  echo "Found sorry/axiom."
  exit 1
fi

# Fetch build cache
lake exe cache get

# Verify everything builds.
lake build --wfail
