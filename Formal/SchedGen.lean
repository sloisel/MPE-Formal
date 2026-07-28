import Mathlib
import Formal.Weight

/-!
# The log-weighted schedule sum, for an arbitrary schedule

`SchedLog.lean` sums `∑ δₘ^p Λ(δₘ)^k` for the doubly-exponential schedule
`δₘ = δ^(θᵐ)`.  The quadratic schedule of the paper's Theorem 4.9,
`δₘ₊₁ = Kδₘ²`, needs the same sum for a different sequence.

Nothing in the argument is specific to either.  What both schedules supply is a pair of
geometric bounds — one on the schedule, one on its weight —

    tₘ ≤ δ βᵐ,        Λ(tₘ) ≤ λᵐ Λ(δ),

and the summability condition `βᵖ λᵏ ≤ 1/2`.  That is the whole input, and it is exactly
the shape of the paper's Lemma 4.5.  This file proves the sum from it, so that both
schedules become instances.

See `../../corollary.tex` §4 (Obligation 1).
-/

namespace MPE

open Real

/-- `(βᵐ)^p = (βᵖ)ᵐ`, mixing the natural power with the real one. -/
lemma rpow_npow_comm {β : ℝ} (hβ : 0 ≤ β) (p : ℝ) (m : ℕ) :
    (β ^ m) ^ p = (β ^ p) ^ m := by
  rw [← Real.rpow_natCast β m, ← Real.rpow_natCast (β ^ p) m, ← Real.rpow_mul hβ,
    ← Real.rpow_mul hβ]
  congr 1
  ring

/-- **The termwise bound.**  A schedule dominated geometrically, with a weight that grows
geometrically, has terms dominated by a geometric series of ratio `βᵖλᵏ`. -/
theorem sched_term_le {δ p β lam : ℝ} {k : ℕ} {t : ℕ → ℝ}
    (hδ0 : 0 < δ) (hp : 0 ≤ p) (hβ0 : 0 ≤ β) (_hlam : 0 ≤ lam)
    (ht0 : ∀ m, 0 < t m)
    (htβ : ∀ m, t m ≤ δ * β ^ m)
    (htΛ : ∀ m, Lam (t m) ≤ lam ^ m * Lam δ)
    (m : ℕ) :
    (t m) ^ p * Lam (t m) ^ k ≤ (δ ^ p * Lam δ ^ k) * (β ^ p * lam ^ k) ^ m := by
  have hval : (t m) ^ p ≤ δ ^ p * (β ^ p) ^ m := by
    calc (t m) ^ p ≤ (δ * β ^ m) ^ p := Real.rpow_le_rpow (ht0 m).le (htβ m) hp
      _ = δ ^ p * (β ^ m) ^ p := Real.mul_rpow hδ0.le (pow_nonneg hβ0 m)
      _ = δ ^ p * (β ^ p) ^ m := by rw [rpow_npow_comm hβ0]
  have hwt : Lam (t m) ^ k ≤ (lam ^ k) ^ m * Lam δ ^ k := by
    calc Lam (t m) ^ k ≤ (lam ^ m * Lam δ) ^ k :=
          pow_le_pow_left₀ (Lam_nonneg _) (htΛ m) k
      _ = (lam ^ k) ^ m * Lam δ ^ k := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k m]
  have hnn1 : (0:ℝ) ≤ δ ^ p * (β ^ p) ^ m :=
    mul_nonneg (Real.rpow_nonneg hδ0.le p) (pow_nonneg (Real.rpow_nonneg hβ0 p) m)
  calc (t m) ^ p * Lam (t m) ^ k
      ≤ (δ ^ p * (β ^ p) ^ m) * ((lam ^ k) ^ m * Lam δ ^ k) :=
        mul_le_mul hval hwt (Lam_pow_pos _ k).le hnn1
    _ = (δ ^ p * Lam δ ^ k) * (β ^ p * lam ^ k) ^ m := by rw [mul_pow]; ring

/-- Summability of the log-weighted schedule sum, for an arbitrary schedule. -/
theorem summable_sched_gen {δ p β lam : ℝ} {k : ℕ} {t : ℕ → ℝ}
    (hδ0 : 0 < δ) (hp : 0 ≤ p) (hβ0 : 0 ≤ β) (hlam : 0 ≤ lam)
    (ht0 : ∀ m, 0 < t m)
    (htβ : ∀ m, t m ≤ δ * β ^ m)
    (htΛ : ∀ m, Lam (t m) ≤ lam ^ m * Lam δ)
    (hratio : β ^ p * lam ^ k ≤ 1 / 2) :
    Summable fun m : ℕ => (t m) ^ p * Lam (t m) ^ k := by
  have hr0 : (0:ℝ) ≤ β ^ p * lam ^ k :=
    mul_nonneg (Real.rpow_nonneg hβ0 p) (pow_nonneg hlam k)
  have hr1 : β ^ p * lam ^ k < 1 := lt_of_le_of_lt hratio (by norm_num)
  have hmaj : Summable fun m : ℕ => (δ ^ p * Lam δ ^ k) * (β ^ p * lam ^ k) ^ m :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine hmaj.of_nonneg_of_le (fun m => ?_)
    (fun m => sched_term_le hδ0 hp hβ0 hlam ht0 htβ htΛ m)
  have h1 : (0:ℝ) ≤ (t m) ^ p := Real.rpow_nonneg (ht0 m).le p
  exact mul_nonneg h1 (Lam_pow_pos _ k).le

/-- **Geometric domination.**  If a schedule and its weight are both dominated
geometrically, and the resulting ratio is at most `1/2`, the log-weighted sum is at most
twice its first term.

This is `corollary.tex` Lemma 2, and it replaces `schedule_series_bound_log` for both the
doubly-exponential and the quadratic schedule. -/
theorem geometric_domination {δ p β lam : ℝ} {k : ℕ} {t : ℕ → ℝ}
    (hδ0 : 0 < δ) (hp : 0 ≤ p) (hβ0 : 0 ≤ β) (hlam : 0 ≤ lam)
    (ht0 : ∀ m, 0 < t m)
    (htβ : ∀ m, t m ≤ δ * β ^ m)
    (htΛ : ∀ m, Lam (t m) ≤ lam ^ m * Lam δ)
    (hratio : β ^ p * lam ^ k ≤ 1 / 2) :
    ∑' m : ℕ, (t m) ^ p * Lam (t m) ^ k ≤ 2 * (δ ^ p * Lam δ ^ k) := by
  have hr0 : (0:ℝ) ≤ β ^ p * lam ^ k :=
    mul_nonneg (Real.rpow_nonneg hβ0 p) (pow_nonneg hlam k)
  have hr1 : β ^ p * lam ^ k < 1 := lt_of_le_of_lt hratio (by norm_num)
  have hsum := summable_sched_gen hδ0 hp hβ0 hlam ht0 htβ htΛ hratio
  have hmaj : Summable fun m : ℕ => (δ ^ p * Lam δ ^ k) * (β ^ p * lam ^ k) ^ m :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  calc ∑' m : ℕ, (t m) ^ p * Lam (t m) ^ k
      ≤ ∑' m : ℕ, (δ ^ p * Lam δ ^ k) * (β ^ p * lam ^ k) ^ m :=
        hsum.tsum_le_tsum (fun m => sched_term_le hδ0 hp hβ0 hlam ht0 htβ htΛ m) hmaj
    _ = (δ ^ p * Lam δ ^ k) * (1 - (β ^ p * lam ^ k))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ 2 * (δ ^ p * Lam δ ^ k) := by
        have hpos : (0:ℝ) < 1 - (β ^ p * lam ^ k) := by linarith
        have hinv : (1 - (β ^ p * lam ^ k))⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hpos (by norm_num)]
          linarith
        have hqL : (0:ℝ) ≤ δ ^ p * Lam δ ^ k :=
          mul_nonneg (Real.rpow_nonneg hδ0.le p) (Lam_pow_pos _ k).le
        nlinarith

/-- **Geometric domination at `p = 1`**, the case the quadratic schedule needs: both terms
of `hΨ` are then linear in `δₘ`. -/
theorem geometric_domination_one {δ β lam : ℝ} {k : ℕ} {t : ℕ → ℝ}
    (hδ0 : 0 < δ) (hβ0 : 0 ≤ β) (hlam : 0 ≤ lam)
    (ht0 : ∀ m, 0 < t m)
    (htβ : ∀ m, t m ≤ δ * β ^ m)
    (htΛ : ∀ m, Lam (t m) ≤ lam ^ m * Lam δ)
    (hratio : β * lam ^ k ≤ 1 / 2) :
    ∑' m : ℕ, t m * Lam (t m) ^ k ≤ 2 * (δ * Lam δ ^ k) := by
  have hr : β ^ (1:ℝ) * lam ^ k ≤ 1 / 2 := by rwa [Real.rpow_one]
  have h := geometric_domination (p := 1) hδ0 zero_le_one hβ0 hlam ht0 htβ htΛ hr
  simpa only [Real.rpow_one] using h

end MPE
