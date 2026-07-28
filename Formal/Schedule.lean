import Mathlib

/-!
# The schedule inequality from the dithered-restart proof

The doubly exponential schedule is `δ_m = δ ^ (θ ^ m)` with `θ ∈ (1,2)`.  Step 3 of the
union bound needs the terms `q ^ (θ ^ m)` to be dominated by a geometric series.

The paper justified this with `θ ^ m ≥ m + 1`.  That claim is **false** for every
`θ ∈ (1,2)`; `paper_claim_false` below exhibits the failure.  The correct tool is
Bernoulli's inequality, `bernoulli_pow`, and `geometric_term_bound` is the estimate the
proof actually needs.
-/

namespace Schedule

open Real

/-- **Bernoulli.**  For `θ ≥ 1`, `1 + m(θ-1) ≤ θ ^ m`.  This is what replaces the paper's
false claim. -/
theorem bernoulli_pow {θ : ℝ} (hθ : 1 ≤ θ) (m : ℕ) :
    1 + (m : ℝ) * (θ - 1) ≤ θ ^ m := by
  have h : (-2 : ℝ) ≤ θ - 1 := by linarith
  have := one_add_mul_le_pow h m
  simpa using this

/-- **The paper's claim was false.**  It is not the case that `m + 1 ≤ θ ^ m` for all
`θ ∈ (1,2)` and all `m` — already `θ = 1.9`, `m = 1` fails. -/
theorem paper_claim_false :
    ¬ (∀ θ : ℝ, 1 < θ → θ < 2 → ∀ m : ℕ, ((m : ℝ) + 1) ≤ θ ^ m) := by
  intro h
  have := h 1.9 (by norm_num) (by norm_num) 1
  norm_num at this

/-- **The estimate the union bound needs.**  For `0 < q ≤ 1` and `θ ≥ 1`,
`q ^ (θ ^ m) ≤ q * (q ^ (θ - 1)) ^ m`, so the series is dominated by a geometric one of
ratio `q ^ (θ - 1)`. -/
theorem geometric_term_bound {q θ : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hθ : 1 ≤ θ) (m : ℕ) :
    q ^ (θ ^ m) ≤ q * (q ^ (θ - 1)) ^ (m : ℕ) := by
  have key : q ^ (θ ^ m) ≤ q ^ (1 + (m : ℝ) * (θ - 1)) :=
    rpow_le_rpow_of_exponent_ge hq0 hq1 (bernoulli_pow hθ m)
  calc q ^ (θ ^ m)
      ≤ q ^ (1 + (m : ℝ) * (θ - 1)) := key
    _ = q * (q ^ (θ - 1)) ^ (m : ℕ) := by
        rw [rpow_add hq0, rpow_one, mul_comm (m : ℝ) (θ - 1), rpow_mul hq0.le,
          rpow_natCast]

/-- **Summability.**  With ratio at most `1/2`, the whole series is at most `2q`: this is
the "at most twice its first term" step of the union bound. -/
theorem schedule_series_bound {q θ : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hθ : 1 ≤ θ)
    (hratio : q ^ (θ - 1) ≤ 1 / 2) :
    ∑' m : ℕ, q ^ (θ ^ m) ≤ 2 * q := by
  have hr0 : 0 ≤ q ^ (θ - 1) := (rpow_pos_of_pos hq0 _).le
  have hr1 : q ^ (θ - 1) < 1 := lt_of_le_of_lt hratio (by norm_num)
  have hsummable : Summable fun m : ℕ => q * (q ^ (θ - 1)) ^ m :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left q
  have hle : ∀ m : ℕ, q ^ (θ ^ m) ≤ q * (q ^ (θ - 1)) ^ m :=
    fun m => geometric_term_bound hq0 hq1 hθ m
  have hnn : ∀ m : ℕ, 0 ≤ q ^ (θ ^ m) := fun m => (rpow_pos_of_pos hq0 _).le
  have hsum : Summable fun m : ℕ => q ^ (θ ^ m) :=
    hsummable.of_nonneg_of_le hnn hle
  calc ∑' m : ℕ, q ^ (θ ^ m)
      ≤ ∑' m : ℕ, q * (q ^ (θ - 1)) ^ m := hsum.tsum_le_tsum hle hsummable
    _ = q * (1 - q ^ (θ - 1))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ 2 * q := by
        rw [mul_comm]
        have h2 : (1 : ℝ) / 2 ≤ 1 - q ^ (θ - 1) := by linarith
        have hpos : (0 : ℝ) < 1 - q ^ (θ - 1) := by linarith
        have : (1 - q ^ (θ - 1))⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hpos (by norm_num)]
          linarith
        nlinarith [hq0.le]

end Schedule
