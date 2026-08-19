import Formal.Statement

/-!
# Solution to the Challenge

The three declarations of `Challenge.lean`, proved.  Nothing is restated here: the
development's statement file, `Formal/Statement.lean`, already declares
`MPE.mpe_dithered`, `MPE.mpe_quadratic` and `MPE.mpe_undithered` with exactly the
Challenge's statements, each proved by a one-line reference into the development, and
this module imports it.  Comparator inspects the resulting environment: it checks that
the three names carry the same statements as in `Challenge.lean` and that their proofs
use no axiom beyond `propext`, `Classical.choice` and `Quot.sound`.

`Formal/Statement.lean` also re-asserts both properties on every build of this
repository, independently of Comparator: a `run_cmd` there fails the build if a
statement mentions a name from this development or if a proof picks up an unexpected
axiom.
-/
