# MPE-Formal

[![build](https://github.com/sloisel/MPE-Formal/actions/workflows/ci.yml/badge.svg)](https://github.com/sloisel/MPE-Formal/actions/workflows/ci.yml)

Lean 4 formalisation accompanying the paper *Local convergence of MPE and RRE*
(S. Loisel).  The main theorems of the paper are proved here, sorry-free and
depending only on Lean's standard axioms:

| paper | Lean |
| --- | --- |
| Theorem 4.7 — dithered restarts, `C²`, no spectral hypothesis beyond `1 ∉ spec(A)`, window `k = deg m_A` (`A` may be derogatory) | `MPE.mpe_dithered` |
| Theorem 4.9 — quadratic order under simple spectrum | `MPE.mpe_quadratic` |
| Theorem 5.5 — the undithered algorithm | `MPE.mpe_undithered` |

All three are stated in `Formal/Statement.lean`, in a form that mentions **no definition
from this development** — only mathlib notions — so that a reader who accepts mathlib can
audit them without reading anything else.  A `run_cmd` at the bottom of that file fails the
build if that ever stops being true.  The same `run_cmd` also **fails the build** unless
each theorem rests on nothing beyond `propext`, `Classical.choice` and `Quot.sound` — which
is what rules out `sorryAx`.  That check is not decorative: in Lean a `sorry` is only a
*warning*, so a project that merely compiles proves nothing.  CI is exactly this
`lake build`, run on every push, with `--wfail` so that a stray `sorry` anywhere in the
tree — even in a file the three theorems do not reach — fails the build as a warning
turned error.  There is one workflow and it is synchronous: a green badge means the
build, the axiom audit and the warning check all passed for that commit.

The repository also carries the [Palomar](https://palomar-registry.org/) layout:
`Challenge.lean` states the three theorems with `sorry` bodies and imports only
mathlib — the statement of record — `Solution.lean` proves them by importing the
development, and `comparator.json` names them.  The workflow's second step runs
[Comparator](https://github.com/leanprover/comparator) on every push: it rebuilds both
modules, checks that the Solution proves exactly the Challenge's statements, re-runs
the Lean kernel on the exported proofs, and enforces the three-axiom allowlist — the
registry's mechanical check (a), mirrored locally.  The registry's other check,
whether the informal accounts in `formalization.yaml` match the formal statements, is
a judgment call and deliberately not in CI; the author reviews it before each
submission.

Some source files carry docstrings referring to `../../paper.tex`, `../../appendix.tex`
and similar.  Those are the paper and its working notes, which live in a separate
repository; the references are historical pointers and nothing here depends on them.

## Layout, and why

Only the proof is versioned here — a few tens of KB of `.lean`, alongside the paper.
Everything it depends on is *declared*, not stored:

    lean-toolchain           the compiler version, `leanprover/lean4:v4.32.0`
    lakefile.toml            what we require: mathlib, pinned by commit
    lake-manifest.json       the exact commit of mathlib and its 8 transitive deps

This is the standard Lean layout, and it is what makes the development reproducible: a
reader clones the repo and runs the two commands under **Build** below.  Mathlib is
pinned to `3dffaf2f…`, the last master commit on toolchain `v4.32.0` — a master
commit rather than a version tag because the Palomar registry checks that the pin
is an ancestor of mathlib's canonical master, and mathlib's patch-release tags
live on release branches that never merge back.  Master content at this commit
supersedes the v4.32.2 tag previously pinned here.

`.lake/` holds the fetched packages and all build output — about 7.5 GB, of which 6.4 GB
is mathlib's compiled `.olean` files.  It is derived, so it is gitignored.  It is also
marked so that Dropbox does not sync it (only relevant if you keep it inside Dropbox):

    xattr -w com.dropbox.ignored 1 .lake

**Re-run that after any `rm -rf .lake`**, before the next build, or Dropbox will start
syncing several gigabytes of build artifacts.

## Build

    lake exe cache get      # download mathlib's prebuilt .olean files
    lake build

If `.lake` is ever deleted:  `lake resolve-deps` restores it in seconds.

## Checking a result is real

    lake env lean Formal/Schedule.lean     # must produce no output
    #print axioms <theorem name>           # must not mention sorryAx
    bash scripts/comparator.sh             # the Palomar check: statements + axioms + kernel replay

`propext`, `Classical.choice`, `Quot.sound` are Lean's standard foundations and are
expected.  Anything else — especially `sorryAx` — means the proof has a hole.

A reader wanting the strongest available check can replay a module's declarations
through the kernel, which trusts neither the elaborator nor the environment it built:

    lake env leanchecker Formal.Statement

CI does not run this.  It defends against declarations entering the environment without
full kernel checking, and this development contains no `unsafe`, `implemented_by`,
`native_decide`, `opaque`, `extern` or custom `axiom` for it to catch; invoked with no
argument it also tries to replay all of mathlib, which exhausts a standard runner.

## License

MIT (see `LICENSE`).  Mathlib, on which this development depends, is separately
licensed under Apache 2.0; it is fetched by `lake`, not redistributed here.
