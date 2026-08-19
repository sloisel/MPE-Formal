#!/usr/bin/env bash
# Palomar check (a), run on every push: Comparator (leanprover/comparator)
# certifies that `Solution` proves exactly the statements of `Challenge` from
# propext, Classical.choice and Quot.sound alone, re-running the Lean kernel on
# the exported proof.  This is the same mechanical check the Palomar registry
# runs at submission.
#
# Comparator publishes one tag per Lean release and has none for v4.32.2, so
# its v4.32.0 source — same patch family — is built under our own toolchain;
# lean4export has an exact v4.32.2 tag.  Olean files are only readable by the
# exact compiler that wrote them, so both tools MUST be built with
# ./lean-toolchain; the cache directory is keyed by the toolchain for the
# same reason.
set -euo pipefail

COMPARATOR_TAG=v4.32.0
LEAN4EXPORT_TAG=v4.32.2
TOOLCHAIN=$(cat lean-toolchain)
CACHE="${COMPARATOR_CACHE:-$HOME/.cache/mpe-comparator}/${TOOLCHAIN//[:\/]/-}"
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

# Comparator wraps every child process in landrun, its Landlock sandbox.  We
# substitute the passthrough (scripts/landrun-passthrough) on every platform,
# for two reasons.  First, the sandbox exists to protect a checker who must
# *build* an adversarial Solution; here the Solution is this repository's own
# code and is already built by the preceding CI step, so the sandboxed builds
# are replays of trusted artifacts (comparator's README makes the same point
# about pre-built .lake directories).  Second, this comparator release
# (v4.32.0) passes lean4export a literal "--" separating the module from the
# declaration names, and landrun's flag parser (urfave/cli v3) consumes that
# "--" as its own terminator, so under the real landrun lean4export receives
# the declarations as module names and aborts: the sandboxed path is broken
# at this version pair regardless.  The Palomar registry runs its own
# comparator under its own sandbox at submission; this script mirrors the
# mathematical checks, not the sandboxing.
LANDRUN="$(pwd)/scripts/landrun-passthrough"

COMPARATOR_LANDRUN="$LANDRUN" \
COMPARATOR_LEAN4EXPORT="$CACHE/lean4export/.lake/build/bin/lean4export" \
  lake env "$CACHE/comparator/.lake/build/bin/comparator" comparator.json
