# What is proved, and what is assumed

Read `Formal/Toplevel.lean` for the assembled theorem, and `Formal/Instantiate.lean` for
the concrete construction.  Nothing is hidden in an `axiom`: every result reports only
`propext`, `Classical.choice`, `Quot.sound`, and there is no `sorry` in the development.

    lake build
    #print axioms MPE.Poly.structural_hypotheses_discharged

## The bottom line

For a polynomial map `f = Ax + q` under the paper's standing assumptions (`q` of degree
`≥ 2`, `A - I` invertible), **both structural hypotheses of Theorem 4.9 are theorems**:

```lean
theorem structural_hypotheses_discharged (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) :
    ∃ C : CycleData (Fin n → ℝ), Nonempty (SharpBound C)
```

* `CycleData.hN`  — Lemma 4.1(iii) — proved (`cycleData`);
* `SharpBound.bound` — Lemma 4.4(iii) — proved (`nonempty_sharpBound`).

The **only** remaining input to `MPE.dither_sharp` is `hΨ`, the per-cycle margin
probability.

## Proved

| file | content | paper |
|---|---|---|
| `Schedule.lean` | Bernoulli; geometric term bound; `∑ q^(θ^m) ≤ 2q` | Step 3 |
| `Schedule.lean` | `paper_claim_false`: `θ^m ≥ m+1` is **false** on `(1,2)` | corrected error |
| `Algebra.lean` | Cayley–Hamilton; the Krylov identity; `U·adj U = D·I` | Lemmas 4.1, 3 |
| `Degree.lean` | `LowDeg` calculus: det, adjugate, mulVec; `Ñ` has degree `≥ n+2` | Lemma 4.1(iii) |
| `Degree.lean` | degree bound ⟹ `O(‖y‖^k)`, explicit constant | — |
| `Leading.lean` | leading parts: splitting, products, next order, det, adjugate | Lemma 4.3 |
| `Construction.lean` | composition preserves degree; `f^j = A^j x + g_j` | Lemma 4.1 |
| `Factor.lean` | the extraction `(A-I)G = -Δ·W`, over any commutative ring | **Lemma 4.3** |
| `Instantiate.lean` | the construction `F, u, U, c̃, Ñ, σ̃`; `∑_j c̃_j u_j = 0` | §2 |
| `Instantiate.lean` | `c̃`'s leading part is `Δ·c⁰`; `σ̃`'s is `p_A(1)·Δ` | Lemma 4.1 proof |
| `Instantiate.lean` | `factorization_construction`: `Δ ∣ G` for the real construction | **Lemma 4.3** |
| `Instantiate.lean` | `sharp_estimate`, and hence **`cycleData`, `nonempty_sharpBound`** | **Lemmas 4.1(iii), 4(iii)** |
| `Cycle.lean` | one cycle in terms of the margin; the three contraction steps | Lemma 4.4.5(i), Thms 4.7, 4.9 |
| `Induction.lean` | first-failure decomposition; union bound; schedule induction | Lemma 4.5 |
| `Main.lean` | `dither_general`, `dither_sharp` | Theorems 4.7, 3 |
| `Toplevel.lean` | per-cycle bounds summed to an explicit `2Aδ^p` | Step 3 |
| `Witness.lean` | **non-vacuity**: the hypotheses are satisfiable | — |

Two proofs improve on the paper.  The degree count for `Ñ` avoids the leading-part analysis
of the adjugate: from the exact relation `∑_j c̃_j u_j = 0` one gets
`(A-I)T = -∑_j c̃_j (g_{j+1}-g_j)`, whose right side has degree `≥ n+2`, and `A-I` is an
invertible matrix of *scalars*, so it can neither create nor destroy low-degree monomials.
And the factorisation is stated inverse-free, as `(A-I)G = -Δ·W`.

## Assumed

**`hΨ`** only.  Verified absent from the pinned mathlib (`~/lean/mathlib4`, v4.32.1): no
`Remez`/`Brudnyi`/`Ganzburg`, no polynomial sublevel-set measure results, and **no coarea
formula**.  Theorem 4.7 needs Brudnyi–Ganzburg; Theorem 4.9 needs the paper's anticoncentration
lemma, whose proof fibres over level sets and so needs coarea.  Either would be a mathlib
contribution in its own right, independent of this paper.

## In progress: discharging `hΨ`

`appendix.tex` (repo root) writes out, in ordinary mathematics, every ingredient of `hΨ`
that mathlib lacks.  Two of its findings narrowed the job: the sharp route needs **no**
Remez/Brudnyi–Ganzburg inequality (that is Theorem 4.7's route, via Lemma 4.6), and Lemma 4.8's
Step 4 is Fubini in fixed coordinates, **not** the coarea formula.

Proved so far (all `sorry`-free, all reporting only the three standard axioms):

| file | appendix | content |
|---|---|---|
| `Weight.lean` | §2 | `Λ t = 1 + log⁺(1/t)`; multiplicative constant absorption |
| `OneDim.lean` | §3 | `|g'| ≥ c ⟹ vol{|g| ≤ s} ≤ 2s/c`, via a diameter bound |
| `Dyadic.lean` | §4 | `∫ min(1,t/Y) ≤ (4C₀+M) t Λ(t)^(j+1)` |
| `Blocks.lean` | §5–6 | block anticoncentration; the `N`-fold product estimate |
| `DeltaFactor.lean` | §7 | `K(Pw) = P·diag w·vandermonde lam`; blocks; real-spectrum case |
| `RealForm.lean` | §6 | `charpoly` factors; `restrictKer`; `minpoly`; `det_piMap` |
| `Primary.lean` | §6 | **the real block factorization of `Δ`, for any squarefree `charpoly`** |
| `SchedLog.lean` | Ob.12 | `∑ δₘ^p Λ(δₘ)^k ≤ 2 δ^p Λ(δ)^k` |
| `Anticonc.lean` | §9 | Lemma 4.8, real spectrum |
| `Psi.lean` | §10 | `hPsi`; **Theorem 4.9 for a real spectrum**, `C δ Λ(δ)^(n-1)` |
| `Annulus.lean` | §8 | chart/fiber bound; the sublevel estimate on the cube, all-lines case |
| `Weight.lean` | §9 | dyadic scaling of `Λ`; `∑ⱼ2⁻ⁿʲ(1+j)^p`; `xΛ(x)^k ≤ C x^p` |
| `PolyDeriv.lean` | §9 | derivative of a polynomial along one coordinate; rescaling |

`PolyDeriv.lean` closes what looked like a mathlib gap.  Mathlib's `MvPolynomial.pderiv` is
the *formal* derivative, with no bridge to `HasDerivAt` of the evaluation map — but no
bridge is needed: freezing all but the first coordinate exhibits the evaluation as a finite
sum `∑_d c_d(u') t^{d 0}`, which differentiates termwise.  The same expansion gives the
bound, with explicit constant `∑ |coeff d| · deg d`, and rescaling then yields
`|∂ₜ (R(rz)/r^k)| ≤ derivBound R · r` on the unit ball.

Four places where the Lean improves on `appendix.tex`, all proved in the stronger form:

* the dyadic lemma needs no partition into shells — a **finite** pointwise bound
  `min(1,t/y) ≤ (1/2)^K + ∑_{k<K} 2^{-k}·1_{y ≤ 2^{k+1}t}` suffices, giving `4C₀+M`
  rather than `5C₀+4`;
* a plane block needs no disc area: `a²+b² ≤ v` forces `|a|,|b| ≤ √v`, so the box bound
  gives the anticoncentration constant `1`, not `π/4`;
* when every block is a line, **no chart cover and no annulus are needed** — the fiber
  derivative `∂ₜ(t·h) = h` is bounded below on all of `[-1,1]`, so the estimate holds on
  the full cube.  The `c⋆` of the appendix exists only to keep `∂_ρ ρ² = 2ρ` off zero on
  plane blocks;
* the two fiber bounds combine *before* integrating, via `min(2,4s/|h|) ≤ 4 min(1,s/|h|)`.

### Done: Theorem 4.9 for a `C³` iteration

**Scope, stated plainly.**  The paper's Theorem 4.9 assumes `f` is `C³` near `0`, and that is
what `MPE.mpe_dithered_sharp` now assumes: `ContDiffOn ℝ 3 f (Metric.ball 0 R)` together with
`f 0 = 0`.  There is no polynomial hypothesis.  (In fact only `C²` is used — the proof needs
`Df` Lipschitz at `0` and nothing more — but the statement is given for `C³` to match the
paper.)

One hypothesis is *not* part of "`f` is `C³` near `0`", and is flagged rather than buried:
`Measurable f`.  The dithered process is defined by the **global** map, and a `C³`-on-a-ball
hypothesis says nothing about `f` away from the origin, so without some global regularity the
failure event need not even be measurable.  Any continuous iteration satisfies it, and nothing
else about `f` outside the ball is used.

The `C³` argument rests on two facts and no Taylor expansion (`../appendix.tex` §11, Remark
`rem:noquad`): the exact identity `(A−I)Ñ = −∑ⱼ c̃ⱼ q(f^j)`, which is `U·adj U = (det U)·I`
rearranged and holds for any map at all; and the single structural estimate
`c̃ⱼ = pⱼ·Δ + O(‖y‖^{n+1})`, from Cramer's rule plus Cayley–Hamilton.  In particular the
quadratic Taylor truncation is *not* needed, so neither is a multivariate Taylor theorem with
remainder (absent from mathlib) nor the symmetry of `D²f(0)`.  The polynomial theorem
(`MPE.theorem3`) survives unchanged as an instance of the same abstract `MPE.theorem3_gen`.


```lean
theorem MPE.theorem3 (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1))
    (hsq : Squarefree A.charpoly) (B : SharpBound (cycleData hq hA))
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ δ, 0 < δ → δ ≤ 1 → 2 * δ ≤ 1 → … →
      (Measure.infinitePi fun _ => blockMeasure (M+2))
          {ω | ∃ m, ¬ ‖xProc (cycleData hq hA) x₀ δ θ m ω‖ ≤ sched δ θ m}
        ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1))
```

`Squarefree A.charpoly` is the paper's "`n` distinct eigenvalues" (over the perfect field `ℝ`
the two are equivalent); there is **no** assumption that the spectrum is real.  The exponent of
`δ` is exactly `1` and the logarithms are kept — not a pure-power weakening.  `hΨ` is a
theorem, and `dither_sharp`/`mpe_converges` have no remaining hypotheses beyond the paper's.

Everything reports only `propext, Classical.choice, Quot.sound`, and there is no `sorry`.

    lake build
    #print axioms MPE.theorem3

The general case rests on three structural results, none of which is in mathlib:

| result | Lean |
|---|---|
| the real block factorization `det K_A(z) = γ ∏ᵢ factorᵢ(T z i)` | `nonempty_realBlockFactorization_of_squarefree` (`Primary.lean`) |
| the sublevel estimate for blocks of both kinds, on a shell | `measure_sublevel_shell_le` (`Annulus.lean`) |
| the assembly, in flattened block coordinates | `theorem3` (`General.lean`) |

and on four pieces of glue that were the actual work:

* **`BlockKind.dim` is *defined* as `dm + 1`**, so `MeasurableEquiv.piFinSuccAbove` peels one
  coordinate off a block with no dependent-type cast.  Without this the chart cover needs a
  `finCongr` transport inside a `MeasurableEquiv`.
* **`BlockKind.fib`/`negSign`** keep the fibre polynomial uniform in the kind of block, and the
  sign `σ` (with `σ² = 1`) makes the *negative* half of each chart work:
  `|Qh + G| = |(σQ)(σh) + G|` and `|σh| = |h|`, so the tail bound is untouched while
  `∂ₜ(σQ)` becomes positive.
* **`blkFlatM`/`blkFlatL`**, the flattening `Blk kind ≃ ℝⁿ`, measure-preserving *and* linear —
  this is what turns `T` into a matrix so that §9's Jacobian applies.  Currying is
  measure-preserving; mathlib has `MeasurableEquiv.piCurry` but not the measure statement,
  which follows from `Measure.pi_eq` because the *uncurried* preimage of a rectangle is a
  rectangle-of-rectangles.
* **`LowDeg.exists_deriv_update`**, the derivative of a polynomial along an *arbitrary*
  coordinate, obtained from the coordinate-`0` case by renaming along `Equiv.swap 0 κ` —
  which changes neither `LowDeg` (degrees are permutation-invariant) nor `derivBound` (only
  `|coeff|` and the *total* degree).

Two edge cases were found while wiring this up and fixed rather than excluded:

* `n = 2` with irreducible `charpoly` gives a **single plane block**, so the "other blocks"
  product is empty.  The shell estimate now takes `kind : Fin (N+1)` with the tail exponent as
  a parameter, and `exists_shell_const` covers both cases.  Taking the exponent `N - 1` one
  always has `(N-1)+1 ≤ n-1`, so the sharp exponent survives in every case.
* `c` in the chart cover must be a **constant**.  That is what the shell decomposition buys —
  a chart cover of the *full* cube would force `c ≈ √s` and degrade the bound to `√s`.  This
  is the one place the shell decomposition does real work rather than bookkeeping.

`§9`–`§10` were refactored to take Lemma 4.8 as a *hypothesis* (`lemma7_prob`, `slice_bound`,
`theorem3_of_lemma7`), so the real-spectrum specialization `theorem3_realSpectrum` and the
general `theorem3` are two corollaries of one proof.
