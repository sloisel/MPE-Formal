#!/usr/bin/env bash
# Palomar check (a), run on every push: Comparator (leanprover/comparator)
# certifies that `Solution` proves exactly the statements of `Challenge` from
# propext, Classical.choice and Quot.sound alone, re-running the Lean kernel on
# the exported proof.  This is the same mechanical check the Palomar registry
# runs at submission.
#
# Comparator publishes one tag per Lean release and has none for the patch
# release this repository pins (v4.32.1), so its v4.32.0 source — same patch
# family — is built under our own toolchain; likewise lean4export (nearest
# family tag v4.32.2).  Olean files are only readable by the exact compiler
# that wrote them, so both tools MUST be built with ./lean-toolchain.
set -euo pipefail

COMPARATOR_TAG=v4.32.0
LEAN4EXPORT_TAG=v4.32.2
TOOLCHAIN=$(cat lean-toolchain)
CACHE="${COMPARATOR_CACHE:-$HOME/.cache/mpe-comparator}"
mkdir -p "$CACHE/bin"

# The sorried Challenge is deliberately not a default target (the default
# build runs --wfail, which a sorried module cannot pass); build it here.
lake build Challenge

clone_build () { # $1 = repo/binary name, $2 = tag
  if [ ! -x "$CACHE/$1/.lake/build/bin/$1" ]; then
    rm -rf "$CACHE/$1"
    git clone --quiet --depth 1 --branch "$2" "https://github.com/leanprover/$1.git" "$CACHE/$1"
    echo "$TOOLCHAIN" > "$CACHE/$1/lean-toolchain"
    (cd "$CACHE/$1" && lake build)
  fi
}
clone_build comparator  "$COMPARATOR_TAG"
clone_build lean4export "$LEAN4EXPORT_TAG"

# landrun, comparator's sandbox for child processes, is Linux-only (Landlock).
# On macOS fall back to the passthrough (see its header for why that is sound
# here).
if [ "$(uname)" = "Linux" ]; then
  if ! command -v landrun >/dev/null && [ ! -x "$CACHE/bin/landrun" ]; then
    GOBIN="$CACHE/bin" go install github.com/zouuup/landrun/cmd/landrun@main
  fi
  LANDRUN="$(command -v landrun || true)"
  LANDRUN="${LANDRUN:-$CACHE/bin/landrun}"
else
  LANDRUN="$(pwd)/scripts/landrun-passthrough"
fi

COMPARATOR_LANDRUN="$LANDRUN" \
COMPARATOR_LEAN4EXPORT="$CACHE/lean4export/.lake/build/bin/lean4export" \
  lake env "$CACHE/comparator/.lake/build/bin/comparator" comparator.json
