import Mathlib
import Formal.General

/-!
# Reducing Theorem 4.9 to a self-contained statement

The working half of `Formal/Statement.lean`.  Nothing here is meant to be read as part of the
audit: the *claim* is in `Statement.lean`, and this file only connects it to the development.

Three steps:

* `exists_thresh` and `theorem3_small` collapse the three technical smallness conditions on
  `δ` that `theorem3` carries into the paper's single `δ ≤ δ_*`, and discharge the
  `SharpBound` hypothesis from `nonempty_sharpBound` — so that no *unsatisfiable* hypothesis
  can sit in the statement and make it vacuous.
* `F_eq` identifies iterates given by defining equations with the construction's `Poly.F`.
* `mpe_dithered_sharp_proof` does the same for `U`, `c̃`, `σ̃`, `Ñ`, the cycle map and the
  dithered process, and then applies `theorem3_small`.
-/

namespace MPE

open MeasureTheory MvPolynomial

variable {M : ℕ} {A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
  {q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ}

/-! ### Making the smallness conditions on `δ` explicit

`theorem3` takes three technical inequalities relating `δ`, `θ` and the constants of Lemma 4.4.
The paper states them as `δ ≤ δ_*`.  They are monotone in `δ`, so a threshold exists. -/

/-- For `a, p > 0` there is a threshold below which `a δ^p ≤ 1`. -/
lemma exists_thresh {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ t → a * δ ^ p ≤ 1 := by
  refine ⟨min 1 ((1 / a) ^ (1 / p)),
    lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _), min_le_left _ _, ?_⟩
  intro δ hδ hδt
  have h1 : δ ^ p ≤ ((1 / a) ^ (1 / p)) ^ p :=
    Real.rpow_le_rpow hδ.le (le_trans hδt (min_le_right _ _)) hp.le
  have h2 : ((1 / a) ^ (1 / p)) ^ p = 1 / a := by
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1 / a), one_div_mul_cancel hp.ne',
      Real.rpow_one]
  rw [h2] at h1
  calc a * δ ^ p ≤ a * (1 / a) := mul_le_mul_of_nonneg_left h1 ha.le
    _ = 1 := by field_simp

variable {M : ℕ} {A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
  {q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ}

/-- **Theorem 4.9, with the three smallness conditions collapsed to `δ ≤ δ_*`.** -/
theorem theorem3_small (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1))
    (hsq : Squarefree A.charpoly) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ dstar Cst : ℝ, 0 < dstar ∧ 0 < Cst ∧ ∀ δ : ℝ, 0 < δ → δ ≤ dstar →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
            {ω | ∃ m, ¬ ‖xProc (Poly.cycleData hq hA) x₀ δ θ m ω‖ ≤ sched δ θ m}
          ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) := by
  obtain ⟨B⟩ := Poly.nonempty_sharpBound hq hA
  obtain ⟨Cst, hCst, hmain⟩ := theorem3 hq hA hsq B hθ1 hθ2
  obtain ⟨t₁, ht₁, -, h₁⟩ := exists_thresh (a := 8 * B.C₁) (p := 2 - θ)
    (by have := B.hC₁; positivity) (by linarith)
  obtain ⟨t₂, ht₂, -, h₂⟩ := exists_thresh (a := 16 * B.C₂) (p := 3 - θ)
    (by have := B.hC₂; positivity) (by linarith)
  obtain ⟨t₃, ht₃, -, h₃⟩ := exists_thresh (a := 2 * θ ^ (M + 1)) (p := θ - 1)
    (by have : (0:ℝ) < θ := by linarith
        positivity) (by linarith)
  refine ⟨min (min t₁ t₂) (min t₃ (1 / 2)), Cst,
    lt_min (lt_min ht₁ ht₂) (lt_min ht₃ (by norm_num)), hCst, ?_⟩
  intro δ hδ hδt x₀ hx₀
  have hδ2 : δ ≤ 1 / 2 := le_trans hδt (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ1 : δ ≤ 1 := by linarith
  have h2δ : 2 * δ ≤ 1 := by linarith
  -- each schedule value is at most `δ`, and the exponents are positive
  have hsch : ∀ m, sched δ θ m ≤ δ := fun m => sched_le hδ hδ1 hθ1.le m
  have hschpos : ∀ m, 0 < sched δ θ m := fun m => sched_pos hδ θ m
  refine hmain δ hδ hδ1 h2δ (fun m => ?_) (fun m => ?_) ?_ x₀ hx₀
  · refine le_trans ?_ (h₁ δ hδ (le_trans hδt (le_trans (min_le_left _ _) (min_le_left _ _))))
    refine mul_le_mul_of_nonneg_left ?_ (by have := B.hC₁; positivity)
    exact Real.rpow_le_rpow (hschpos m).le (hsch m) (by linarith)
  · refine le_trans ?_ (h₂ δ hδ (le_trans hδt (le_trans (min_le_left _ _) (min_le_right _ _))))
    refine mul_le_mul_of_nonneg_left ?_ (by have := B.hC₂; positivity)
    exact Real.rpow_le_rpow (hschpos m).le (hsch m) (by linarith)
  · have h := h₃ δ hδ (le_trans hδt (le_trans (min_le_right _ _) (min_le_left _ _)))
    rw [Real.rpow_one]
    linarith

/-! ### The self-contained statement -/

/-- The polynomial iterates are determined by the two defining equations. -/
private lemma F_eq {F : ℕ → Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ}
    (hF0 : ∀ i, F 0 i = X i)
    (hFs : ∀ j i, F (j + 1) i = bind₁ (F j) ((∑ k, C (A i k) * X k) + q i)) :
    ∀ j, F j = Poly.F A q j := by
  intro j
  induction j with
  | zero => funext i; rw [hF0]; rfl
  | succ j ih =>
      funext i
      rw [hFs j i, ih]
      rfl

/-- **The theorem.**  Minimal polynomial extrapolation with dithered restarts, for a
polynomial map `f x = A x + q x`.

Read the hypotheses as definitions: `F j` is `f^j`, `U` has the differences
`u_j = f^{j+1} - f^j` as columns, `c` are the cleared coefficients from Cramer's rule, `sigt`
and `Ntil` are the cleared denominator and numerator, `S = Ntil / sigt` is one cycle, and `x`
is the dithered process with schedule `δ^(θᵐ)` and dither uniform on `[-1,1]ⁿ`.

The conclusion is the paper's Theorem 4.9: the schedule invariant `‖xₘ‖ ≤ δₘ` fails with
probability at most `C · δ · (1 + log⁺(1/δ))^(n-1)`, with the exponent of `δ` equal to `1`. -/
theorem mpe_dithered_sharp_proof
    -- the linear part, invertible at `1`, with `n = M+2` distinct eigenvalues
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ) (hA : IsUnit (A - 1))
    (hsq : Squarefree A.charpoly)
    -- the nonlinear part: every monomial of every component has total degree `≥ 2`
    (q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ)
    (hq : ∀ i, ∀ d ∈ (q i).support, 2 ≤ d.degree)
    -- the iterates of `f x = A x + q x`
    (F : ℕ → Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ)
    (hF0 : ∀ i, F 0 i = X i)
    (hFs : ∀ j i, F (j + 1) i = bind₁ (F j) ((∑ k, C (A i k) * X k) + q i))
    -- the MPE matrix: columns `u_j = f^{j+1} - f^j`, `j < n`
    (U : Matrix (Fin (M + 2)) (Fin (M + 2)) (MvPolynomial (Fin (M + 2)) ℝ))
    (hU : ∀ i j, U i j = F ((j : ℕ) + 1) i - F (j : ℕ) i)
    -- the cleared coefficients, by Cramer's rule
    (c : ℕ → MvPolynomial (Fin (M + 2)) ℝ)
    (hcAdj : ∀ j : Fin (M + 2),
      c (j : ℕ) = U.adjugate.mulVec (fun i => -(F (M + 3) i - F (M + 2) i)) j)
    (hcDet : c (M + 2) = U.det)
    -- the cleared denominator and numerator
    (sigt : MvPolynomial (Fin (M + 2)) ℝ)
    (Ntil : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ)
    (hsigt : sigt = ∑ j ∈ Finset.range (M + 3), c j)
    (hNtil : ∀ i, Ntil i = ∑ j ∈ Finset.range (M + 3), c j * F j i)
    -- one cycle of MPE, in cleared form
    (S : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hS : ∀ y, S y = (eval y sigt)⁻¹ • fun i => eval y (Ntil i))
    -- the dither schedule exponent
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ dstar Cst : ℝ, 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
      -- the dithered process: `x₀`, then `xₘ₊₁ = S (xₘ + δₘ · clamp ωₘ)`
      ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
        (∀ ω, x 0 ω = x₀) →
        (∀ m ω, x (m + 1) ω
          = S (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i)))) →
        -- the dither `ωₘ` is uniform on the cube `[-1,1]ⁿ`, independently in `m`
        (Measure.infinitePi fun _ : ℕ =>
            Measure.pi fun _ : Fin (M + 2) =>
              ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
            {ω | ∃ m, δ ^ (θ ^ m) < ‖x m ω‖}
          ≤ ENNReal.ofReal (Cst * δ * (1 + max 0 (-Real.log δ)) ^ (M + 1)) := by
  -- identify the data with the construction of `Formal/Instantiate.lean`
  have hF : ∀ j, F j = Poly.F A q j := F_eq hF0 hFs
  have hUeq : U = Poly.Umat A q := by
    funext i j
    rw [hU i j]
    show F ((j : ℕ) + 1) i - F (j : ℕ) i = Poly.F A q ((j : ℕ) + 1) i - Poly.F A q (j : ℕ) i
    rw [hF, hF]
  have hceq : ∀ j ∈ Finset.range (M + 3), c j = Poly.cc A q j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases Nat.lt_or_ge j (M + 2) with hlt | hge
    · have := hcAdj ⟨j, hlt⟩
      rw [Poly.cc, dif_pos hlt, this, hUeq]
      congr 1
      funext i
      show -(F (M + 3) i - F (M + 2) i) = Poly.unegN A q i
      rw [Poly.unegN]
      show -(F (M + 3) i - F (M + 2) i) = -(Poly.u A q (M + 2) i)
      rw [Poly.u, hF, hF]
    · have hjeq : j = M + 2 := by omega
      subst hjeq
      rw [hcDet, Poly.cc, dif_neg (by omega), hUeq]
  have hsigteq : sigt = Poly.sigtPoly A q := by
    rw [hsigt, Poly.sigtPoly]
    exact Finset.sum_congr rfl hceq
  have hNtileq : ∀ i, Ntil i = Poly.Nt A q i := by
    intro i
    rw [hNtil i, Poly.Nt]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hceq j hj, hF]
  -- the abstract cycle data of the development
  have hq' : ∀ i, LowDeg 2 (q i) := hq
  have hSeq : ∀ y, S y = (Poly.cycleData hq' hA).S y := by
    intro y
    rw [hS y]
    show _ = ((Poly.cycleData hq' hA).sigt y)⁻¹ • (Poly.cycleData hq' hA).Ntil y
    show (eval y sigt)⁻¹ • (fun i => eval y (Ntil i))
      = (eval y (Poly.sigtPoly A q))⁻¹ • fun i => eval y (Poly.Nt A q i)
    rw [hsigteq]
    congr 1
    funext i
    rw [hNtileq i]
  -- transport `theorem3_small`
  obtain ⟨dstar, Cst, hd0, hC0, hmain⟩ := theorem3_small hq' hA hsq hθ1 hθ2
  refine ⟨dstar, Cst, hd0, hC0, ?_⟩
  intro δ hδ hδt x₀ hx₀ x hx0 hxs
  have hxeq : ∀ m ω, x m ω = xProc (Poly.cycleData hq' hA) x₀ δ θ m ω := by
    intro m
    induction m with
    | zero => intro ω; rw [hx0]; rfl
    | succ m ih =>
        intro ω
        rw [hxs m ω, ih ω, hSeq, xProc_succ]
        rfl
  have hset : {ω : ℕ → Fin (M + 2) → ℝ | ∃ m, δ ^ (θ ^ m) < ‖x m ω‖}
      = {ω | ∃ m, ¬ ‖xProc (Poly.cycleData hq' hA) x₀ δ θ m ω‖ ≤ sched δ θ m} := by
    ext ω
    simp only [Set.mem_setOf_eq, not_le]
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m, by rw [← hxeq m ω]; exact hm⟩
    · rintro ⟨m, hm⟩; exact ⟨m, by rw [hxeq m ω]; exact hm⟩
  rw [hset]
  exact hmain δ hδ hδt x₀ hx₀


end MPE
