# MPE-Formal

Lean 4 formalisation accompanying the paper *Local convergence of MPE and RRE*
(S. Loisel).  The three main theorems of the paper are proved here, sorry-free and
depending only on Lean's standard axioms:

| paper | Lean |
| --- | --- |
| Theorem 4.7 — dithered restarts, `C²`, no spectral hypothesis beyond `1 ∉ spec(A)` | `MPE.mpe_dithered` |
| Theorem 4.9 — quadratic order under simple spectrum | `MPE.mpe_quadratic` |
| Theorem 5.5 — the undithered algorithm | `MPE.mpe_undithered` |

All three are stated in `Formal/Statement.lean`, in a form that mentions **no definition
from this development** — only mathlib notions — so that a reader who accepts mathlib can
audit them without reading anything else.  A `run_cmd` at the bottom of that file fails the
build if that ever stops being true, and `#print axioms` is run on each.

Some source files carry docstrings referring to `../../paper.tex`, `../../appendix.tex`
and similar.  Those are the paper and its working notes, which live in a separate
repository; the references are historical pointers and nothing here depends on them.

## Layout, and why

Only the proof is versioned here — a few tens of KB of `.lean`, alongside the paper.
Everything it depends on is *declared*, not stored:

    lean-toolchain           the compiler version, `leanprover/lean4:v4.32.1`
    lakefile.toml            what we require: mathlib, pinned by commit
    lake-manifest.json       the exact commit of mathlib and its 8 transitive deps

This is the standard Lean layout, and it is what makes the development reproducible: a
reader clones the repo and runs the two commands under **Build** below.  Mathlib is
pinned to `520045ab…`, the commit of tag `v4.32.1`, matching `lean-toolchain`.

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

`propext`, `Classical.choice`, `Quot.sound` are Lean's standard foundations and are
expected.  Anything else — especially `sorryAx` — means the proof has a hole.

## License

MIT (see `LICENSE`).  Mathlib, on which this development depends, is separately
licensed under Apache 2.0; it is fetched by `lake`, not redistributed here.
