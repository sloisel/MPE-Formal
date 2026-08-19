import Mathlib

/-!
# Challenge: statement of the main theorems

This is the statement of record for the Palomar registry, in the Challenge/Solution
convention of `leanprover/comparator`: this file *states* the three theorems and proves
nothing — each proof body below is a deliberate `sorry`.  The proved versions, with
identical names and statements, are in `Solution.lean` (via `Formal/Statement.lean`,
where the development's own build-time axiom checks also live).  Comparator certifies
that the Solution proves exactly the statements in this file from `propext`,
`Classical.choice` and `Quot.sound` alone.

The paper's three probabilistic theorems, one Lean theorem each:

| paper                                                | Lean             |
| ---------------------------------------------------- | ---------------- |
| Theorem 4.7 — dithered restarts                      | `mpe_dithered`   |
| Theorem 4.9 — quadratic order under simple spectrum  | `mpe_quadratic`  |
| Theorem 5.5 — the undithered algorithm               | `mpe_undithered` |

This file is self-contained: the statements mention no definition from this
development — only mathlib notions — and every object of the construction (the matrix
of increments `U`, the cleared coefficients, denominator and numerator, the degeneracy
form, the process itself) is introduced by an explicit defining equation among the
hypotheses.  A reader who accepts mathlib can audit the claims from this file alone.
See `formalization.yaml` for the informal accounts and the fidelity notes.
-/

set_option autoImplicit false

namespace MPE

open MeasureTheory

-- the ambient dimension is `n = M + 2`, so `n ≥ 2` holds by construction
variable {M : ℕ}

/-- **The paper's Theorem 4.7** (dithered restarts).  `f` is `C²` near its fixed point
`0` and measurable, `A = Df(0)` with `A - I` invertible — `A` may be derogatory — and
the window is `k = deg m_A` (written `kk + 1`, so `k ≥ 1` by construction).  Restarted
MPE in the cleared form, each restart dithered by `δ_m = δ^(θ^m)`, satisfies with
probability at least `1 - Cst·δ^((2-θ)/(2k))` over the dither: every cycle is defined
(`σ̃ ≠ 0` at every dithered point) and `‖x_m‖ ≤ δ_m` for all `m`.  The starting point
is arbitrary and may lie on the breakdown set. -/
theorem mpe_dithered
    -- the iteration: `C²` near its fixed point `0`, and measurable elsewhere
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 2 f (Metric.ball 0 R))
    -- the linear part `A = Df(0)`, with `A - 1` invertible
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1))
    -- the window is the degree of the minimal polynomial
    {kk : ℕ} (hk : kk + 1 = (minpoly ℝ A).natDegree)
    -- the `n × k` matrix of increments, its normal matrix, and the right-hand side
    (U : (Fin (M + 2) → ℝ) → Matrix (Fin (M + 2)) (Fin (kk + 1)) ℝ)
    (hU : ∀ y i j, U y i j = f^[(j : ℕ) + 1] y i - f^[(j : ℕ)] y i)
    (Gm : (Fin (M + 2) → ℝ) → Matrix (Fin (kk + 1)) (Fin (kk + 1)) ℝ)
    (hGm : ∀ y, Gm y = (U y).transpose * U y)
    (b : (Fin (M + 2) → ℝ) → Fin (kk + 1) → ℝ)
    (hb : ∀ y j, b y j
      = -∑ l : Fin (M + 2), U y l j * (f^[kk + 2] y l - f^[kk + 1] y l))
    -- the cleared coefficients, by Cramer's rule on `Γ c = b`
    (c : ℕ → (Fin (M + 2) → ℝ) → ℝ)
    (hcCramer : ∀ (j : Fin (kk + 1)) y, c (j : ℕ) y = (Gm y).cramer (b y) j)
    (hcDet : ∀ y, c (kk + 1) y = (Gm y).det)
    -- the cleared denominator and numerator
    (sg : (Fin (M + 2) → ℝ) → ℝ) (Nt : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hsg : ∀ y, sg y = ∑ j ∈ Finset.range (kk + 2), c j y)
    (hNt : ∀ y, Nt y = ∑ j ∈ Finset.range (kk + 2), c j y • f^[j] y)
    -- the dither schedule exponent
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ dstar Cst : ℝ, 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
      -- the dithered process: `x₀`, then `x_{m+1} = S (x_m + δ_m · clamp ω_m)`, `S = Ñ/σ̃`
      ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
        (∀ ω, x 0 ω = x₀) →
        (∀ m ω, x (m + 1) ω
          = (sg (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i))))⁻¹
            • Nt (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i)))) →
        -- the dither `ω_m` is uniform on the cube `[-1,1]ⁿ`, independently in `m`
        (Measure.infinitePi fun _ : ℕ =>
            Measure.pi fun _ : Fin (M + 2) =>
              ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
            -- the failure event: the schedule invariant breaks, or some cycle is
            -- undefined (`σ̃ = 0` at the dithered point)
            {ω | ∃ m, δ ^ (θ ^ m) < ‖x m ω‖
                  ∨ sg (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i))) = 0}
          ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / (2 * (kk : ℝ) + 2))) :=
  sorry

/-- **The paper's Theorem 4.9** (quadratic order under simple spectrum).  Same iteration
and dither as `mpe_dithered`, but `A` has `n` distinct eigenvalues (`hsq`), the window is
full (`k = n`, adjugate form), and the schedule is `δ₀ = δ`, `δₖ₊₁ = K·δₖ²` — order
exactly `2`.  With probability at least `1 - Cst·δ·(1 + log(1/δ))^(n-1)` over the dither:
every cycle is defined in the cleared form (`σ̃ ≠ 0`), the least-squares system is
nonsingular (`det U ≠ 0`, so MPE and RRE agree at every cycle), and `‖xₖ‖ ≤ δₖ` for
all `k`. -/
theorem mpe_quadratic
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 2 f (Metric.ball 0 R))
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1)) (hsq : Squarefree A.charpoly)
    (U : (Fin (M + 2) → ℝ) → Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hU : ∀ y i j, U y i j = f^[(j : ℕ) + 1] y i - f^[(j : ℕ)] y i)
    (c : ℕ → (Fin (M + 2) → ℝ) → ℝ)
    (hcAdj : ∀ (j : Fin (M + 2)) y,
      c (j : ℕ) y = (U y).adjugate.mulVec (fun i => -(f^[M + 3] y i - f^[M + 2] y i)) j)
    (hcDet : ∀ y, c (M + 2) y = (U y).det)
    (sg : (Fin (M + 2) → ℝ) → ℝ) (Nt : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hsg : ∀ y, sg y = ∑ j ∈ Finset.range (M + 3), c j y)
    (hNt : ∀ y, Nt y = ∑ j ∈ Finset.range (M + 3), c j y • f^[j] y) :
    ∃ K dstar Cst : ℝ, 1 ≤ K ∧ 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
      -- the quadratic schedule: `δ₀ = δ`, `δₖ₊₁ = K δₖ²`
      ∀ dl : ℕ → ℝ, dl 0 = δ → (∀ k, dl (k + 1) = K * (dl k) ^ 2) →
      -- the dithered process, with that schedule
      ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
        (∀ ω, x 0 ω = x₀) →
        (∀ k ω, x (k + 1) ω
          = (sg (x k ω + (dl k) • fun i => max (-1) (min 1 (ω k i))))⁻¹
            • Nt (x k ω + (dl k) • fun i => max (-1) (min 1 (ω k i)))) →
        (Measure.infinitePi fun _ : ℕ =>
            Measure.pi fun _ : Fin (M + 2) =>
              ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
            -- the failure event: the schedule invariant breaks, or the least-squares
            -- system is singular, or some cycle is undefined in the cleared form
            {ω | ∃ k, dl k < ‖x k ω‖
                  ∨ Matrix.det (U (x k ω + dl k • fun i => max (-1) (min 1 (ω k i)))) = 0
                  ∨ sg (x k ω + dl k • fun i => max (-1) (min 1 (ω k i))) = 0}
          ≤ ENNReal.ofReal (Cst * δ * (1 + max 0 (-Real.log δ)) ^ (M + 1)) :=
  sorry


/-- **The paper's Theorem 5.5** (the undithered algorithm).  No dither: the orbit is
deterministic, and the only randomness is the starting point `x₀ = ρ·b`, `b` uniform on
the cube `[-1,1]ⁿ`.  Under the paper's Hypotheses 5.1 and 5.2 — here `hA2` and `hA3`,
conditions on the degeneracy form `Q` and the leading form `G`, both given by defining
equations — with probability at least `1 - Cst·ρ^(1/(n(β+1)))`: every cycle is defined
(`σ̃ ≠ 0` and `det U ≠ 0`) and each cycle squares the error, so the decay is doubly
exponential. -/
theorem mpe_undithered
    -- the iteration: `C³` near its fixed point `0`, and measurable elsewhere
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 3 f (Metric.ball 0 R))
    -- the linear part `A = Df(0)`, invertible at `1` and nonderogatory
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1))
    (hnd : ∃ v : Fin (M + 2) → ℝ,
      Matrix.det (Matrix.of fun i j : Fin (M + 2) => ((A ^ (j : ℕ)).mulVec v) i) ≠ 0)
    -- the MPE matrix, the cleared coefficients, denominator and numerator
    (U : (Fin (M + 2) → ℝ) → Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hU : ∀ y i j, U y i j = f^[(j : ℕ) + 1] y i - f^[(j : ℕ)] y i)
    (c : ℕ → (Fin (M + 2) → ℝ) → ℝ)
    (hcAdj : ∀ (j : Fin (M + 2)) y,
      c (j : ℕ) y = (U y).adjugate.mulVec (fun i => -(f^[M + 3] y i - f^[M + 2] y i)) j)
    (hcDet : ∀ y, c (M + 2) y = (U y).det)
    (sg : (Fin (M + 2) → ℝ) → ℝ) (Nt : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hsg : ∀ y, sg y = ∑ j ∈ Finset.range (M + 3), c j y)
    (hNt : ∀ y, Nt y = ∑ j ∈ Finset.range (M + 3), c j y • f^[j] y)
    -- the degeneracy form `Q̃ = p_A(1)·det K`, `K(v) = [(A-I)v, …, (A-I)A^{n-1}v]`
    (Q : (Fin (M + 2) → ℝ) → ℝ)
    (hQ : ∀ v, Q v = A.charpoly.eval 1 *
      Matrix.det (Matrix.of fun i j : Fin (M + 2) => (((A - 1) * A ^ (j : ℕ)).mulVec v) i))
    -- the quadratic Taylor part of `f` at `0`, and the leading form `G = Δ·N⁽²⁾`
    (q₂ : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hq₂ : ∀ x, q₂ x = (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ f) 0) x) x)
    (G : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hG : ∀ v, G v =
      Matrix.det (Matrix.of fun i j : Fin (M + 2) => (((A - 1) * A ^ (j : ℕ)).mulVec v) i) •
        (A - 1)⁻¹.mulVec
          (-∑ j ∈ Finset.range (M + 3), A.charpoly.coeff j • q₂ ((A ^ j).mulVec v)))
    -- Hypotheses 5.1 (comparable vanishing) and 5.2 (the degeneracy takes the power `β`)
    {c₀ C₀ c₃ β : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hc₃ : 0 < c₃)
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hA2 : ∀ v : Fin (M + 2) → ℝ, ‖v‖ = 1 → c₀ * |Q v| ≤ ‖G v‖ ∧ ‖G v‖ ≤ C₀ * |Q v|)
    (hA3 : ∀ v : Fin (M + 2) → ℝ, ‖v‖ = 1 → Q v ≠ 0 →
      c₃ * |Q v| ^ β ≤ |Q (‖G v‖⁻¹ • G v)|) :
    ∃ Cst ρ₀ : ℝ, 0 < Cst ∧ 0 < ρ₀ ∧ 4 * C₀ * ρ₀ ≤ 1 / 2 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      -- `x₀ = ρ·b` with `b` uniform on the cube `[-1,1]ⁿ`; the orbit is deterministic
      (Measure.pi fun _ : Fin (M + 2) =>
          ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
        {b : Fin (M + 2) → ℝ | ¬ ∀ k : ℕ,
            sg ((fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b)) ≠ 0 ∧
            (U ((fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b))).det ≠ 0 ∧
            ‖(fun y => (sg y)⁻¹ • Nt y)^[k + 1] (ρ • b)‖
              ≤ 4 * C₀ * ‖(fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b)‖ ^ 2 ∧
            ‖(fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b)‖
              ≤ (4 * C₀ * ‖ρ • b‖) ^ (2 ^ k) / (4 * C₀)}
        ≤ ENNReal.ofReal (Cst * ρ ^ ((β + 1)⁻¹ * ((M : ℝ) + 2)⁻¹)) :=
  sorry

end MPE
