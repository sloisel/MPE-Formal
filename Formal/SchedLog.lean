import Mathlib
import Formal.Weight
import Formal.Schedule

/-!
# The log-weighted schedule sum

Appendix Obligation 12.  Lemma 4.8 produces a per-cycle bound of the shape
`δₘ^p · Λ(δₘ)^k`, not a pure power.  `MPE.dither_sharp` accepts an *arbitrary* `Ψ` and
concludes `≤ ∑' m, Ψ m`, so nothing forces the logarithms to be discarded: it suffices to
sum this shape.  That is what this file does, and it is what lets the formalization prove
the paper's Theorem 4.9 as stated, with exponent `1` and a `log^(n-1)` factor, rather than a
pure-power weakening.

The proof is the one of `Schedule.schedule_series_bound` with the extra factor `θ^(km)`
folded into the geometric ratio.  Two ingredients:

* `Λ(δₘ) ≤ θᵐ Λ(δ)` — one line, since `Λ(δₘ) = 1 + θᵐ log(1/δ)` while
  `θᵐ Λ(δ) = θᵐ + θᵐ log(1/δ)` and `θᵐ ≥ 1`;
* `δₘ^p = q^(θᵐ) ≤ q (q^(θ-1))ᵐ` with `q = δ^p` — this is
  `Schedule.geometric_term_bound`, already proved.
-/

namespace MPE

open Real

/-- **The weight along the schedule.**  `Λ(δ^(θᵐ)) ≤ θᵐ Λ(δ)`. -/
lemma Lam_rpow_le {δ θ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 1 ≤ θ) (m : ℕ) :
    Lam (δ ^ (θ ^ m)) ≤ θ ^ m * Lam δ := by
  have hθm : (1 : ℝ) ≤ θ ^ m := one_le_pow₀ hθ
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ0.le hδ1
  have hlog : Real.log (δ ^ (θ ^ m)) = θ ^ m * Real.log δ := Real.log_rpow hδ0 _
  have hnn : 0 ≤ -(θ ^ m * Real.log δ) := by nlinarith
  rw [Lam, hlog, max_eq_right hnn, Lam, max_eq_right (by linarith : (0:ℝ) ≤ -Real.log δ)]
  nlinarith

/-- The termwise geometric bound behind the schedule sum, exported so that summability is
available separately (the `ENNReal` assembly needs it). -/
theorem summable_schedule_log {δ θ p : ℝ} (k : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 1 ≤ θ) (hp : 0 < p)
    (hratio : (δ ^ p) ^ (θ - 1) * θ ^ k ≤ 1 / 2) :
    Summable fun m : ℕ => (δ ^ (θ ^ m)) ^ p * Lam (δ ^ (θ ^ m)) ^ k := by
  set q : ℝ := δ ^ p with hq
  have hq0 : 0 < q := rpow_pos_of_pos hδ0 p
  have hq1 : q ≤ 1 := rpow_le_one hδ0.le hδ1 hp.le
  set r : ℝ := q ^ (θ - 1) * θ ^ k with hr
  have hr0 : 0 ≤ r := by
    have h1 : 0 < q ^ (θ - 1) := rpow_pos_of_pos hq0 _
    have hθ0 : (0:ℝ) < θ ^ k := pow_pos (lt_of_lt_of_le one_pos hθ) k
    positivity
  have hr1 : r < 1 := lt_of_le_of_lt hratio (by norm_num)
  have hLam0 : 0 < Lam δ ^ k := Lam_pow_pos δ k
  have hterm : ∀ m : ℕ,
      (δ ^ (θ ^ m)) ^ p * Lam (δ ^ (θ ^ m)) ^ k ≤ (q * Lam δ ^ k) * r ^ m := by
    intro m
    have hpow : (δ ^ (θ ^ m)) ^ p = q ^ (θ ^ m) := by
      rw [hq, ← Real.rpow_mul hδ0.le, ← Real.rpow_mul hδ0.le, mul_comm]
    have h1 : q ^ (θ ^ m) ≤ q * (q ^ (θ - 1)) ^ m :=
      Schedule.geometric_term_bound hq0 hq1 hθ m
    have h2 : Lam (δ ^ (θ ^ m)) ^ k ≤ (θ ^ m) ^ k * Lam δ ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Lam_nonneg _) (Lam_rpow_le hδ0 hδ1 hθ m) k
    calc (δ ^ (θ ^ m)) ^ p * Lam (δ ^ (θ ^ m)) ^ k
        = q ^ (θ ^ m) * Lam (δ ^ (θ ^ m)) ^ k := by rw [hpow]
      _ ≤ (q * (q ^ (θ - 1)) ^ m) * ((θ ^ m) ^ k * Lam δ ^ k) := by
          refine mul_le_mul h1 h2 (Lam_pow_pos _ k).le ?_
          have hqp : 0 < q ^ (θ - 1) := rpow_pos_of_pos hq0 (θ - 1)
          positivity
      _ = (q * Lam δ ^ k) * r ^ m := by
          rw [hr, mul_pow, ← pow_mul, ← pow_mul, mul_comm k m]
          ring
  have hnn : ∀ m : ℕ, 0 ≤ (δ ^ (θ ^ m)) ^ p * Lam (δ ^ (θ ^ m)) ^ k := fun m =>
    mul_nonneg (rpow_pos_of_pos (rpow_pos_of_pos hδ0 _) p).le (Lam_pow_pos _ k).le
  exact ((summable_geometric_of_lt_one hr0 hr1).mul_left _).of_nonneg_of_le hnn hterm

/-- **The log-weighted schedule sum.**  With geometric ratio `q^(θ-1) θ^k ≤ 1/2`,
`∑ₘ δₘ^p Λ(δₘ)^k ≤ 2 δ^p Λ(δ)^k`. -/
theorem schedule_series_bound_log {δ θ p : ℝ} (k : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 1 ≤ θ) (hp : 0 < p)
    (hratio : (δ ^ p) ^ (θ - 1) * θ ^ k ≤ 1 / 2) :
    ∑' m : ℕ, (δ ^ (θ ^ m)) ^ p * Lam (δ ^ (θ ^ m)) ^ k
      ≤ 2 * (δ ^ p * Lam δ ^ k) := by
  set q : ℝ := δ ^ p with hq
  have hq0 : 0 < q := rpow_pos_of_pos hδ0 p
  have hq1 : q ≤ 1 := rpow_le_one hδ0.le hδ1 hp.le
  set r : ℝ := q ^ (θ - 1) * θ ^ k with hr
  have hr0 : 0 ≤ r := by
    have : 0 < q ^ (θ - 1) := rpow_pos_of_pos hq0 _
    have hθ0 : (0:ℝ) < θ ^ k := pow_pos (lt_of_lt_of_le one_pos hθ) k
    positivity
  have hr1 : r < 1 := lt_of_le_of_lt hratio (by norm_num)
  have hLam0 : 0 < Lam δ ^ k := Lam_pow_pos δ k
  -- the termwise bound
  have hterm : ∀ m : ℕ,
      (δ ^ (θ ^ m)) ^ p * Lam (δ ^ (θ ^ m)) ^ k ≤ (q * Lam δ ^ k) * r ^ m := by
    intro m
    have hpow : (δ ^ (θ ^ m)) ^ p = q ^ (θ ^ m) := by
      rw [hq, ← Real.rpow_mul hδ0.le, ← Real.rpow_mul hδ0.le, mul_comm]
    have h1 : q ^ (θ ^ m) ≤ q * (q ^ (θ - 1)) ^ m :=
      Schedule.geometric_term_bound hq0 hq1 hθ m
    have h2 : Lam (δ ^ (θ ^ m)) ^ k ≤ (θ ^ m) ^ k * Lam δ ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Lam_nonneg _) (Lam_rpow_le hδ0 hδ1 hθ m) k
    have hq0' : (0:ℝ) ≤ q ^ (θ ^ m) := (rpow_pos_of_pos hq0 _).le
    calc (δ ^ (θ ^ m)) ^ p * Lam (δ ^ (θ ^ m)) ^ k
        = q ^ (θ ^ m) * Lam (δ ^ (θ ^ m)) ^ k := by rw [hpow]
      _ ≤ (q * (q ^ (θ - 1)) ^ m) * ((θ ^ m) ^ k * Lam δ ^ k) := by
          refine mul_le_mul h1 h2 (Lam_pow_pos _ k).le ?_
          have hqp : 0 < q ^ (θ - 1) := rpow_pos_of_pos hq0 (θ - 1)
          positivity
      _ = (q * Lam δ ^ k) * r ^ m := by
          rw [hr, mul_pow, ← pow_mul, ← pow_mul, mul_comm k m]
          ring
  -- summability and the geometric sum
  have hsummable : Summable fun m : ℕ => (q * Lam δ ^ k) * r ^ m :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hnn : ∀ m : ℕ, 0 ≤ (δ ^ (θ ^ m)) ^ p * Lam (δ ^ (θ ^ m)) ^ k := fun m => by
    have h1 : (0:ℝ) ≤ (δ ^ (θ ^ m)) ^ p := (rpow_pos_of_pos (rpow_pos_of_pos hδ0 _) p).le
    have h2 : (0:ℝ) ≤ Lam (δ ^ (θ ^ m)) ^ k := (Lam_pow_pos _ k).le
    exact mul_nonneg h1 h2
  have hsum : Summable fun m : ℕ => (δ ^ (θ ^ m)) ^ p * Lam (δ ^ (θ ^ m)) ^ k :=
    hsummable.of_nonneg_of_le hnn hterm
  calc ∑' m : ℕ, (δ ^ (θ ^ m)) ^ p * Lam (δ ^ (θ ^ m)) ^ k
      ≤ ∑' m : ℕ, (q * Lam δ ^ k) * r ^ m := hsum.tsum_le_tsum hterm hsummable
    _ = (q * Lam δ ^ k) * (1 - r)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ ≤ 2 * (q * Lam δ ^ k) := by
        have hpos : (0:ℝ) < 1 - r := by linarith
        have hinv : (1 - r)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hpos (by norm_num)]
          linarith
        have hqL : (0:ℝ) < q * Lam δ ^ k := by positivity
        nlinarith

end MPE
