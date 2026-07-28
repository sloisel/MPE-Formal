import Mathlib
import Formal.Weight
import Formal.SchedGen

/-!
# The quadratic schedule

The paper's Theorem 4.9 runs `δ₀ = δ`, `δₘ₊₁ = K δₘ²`, whose closed form is
`δₘ = K⁻¹ (Kδ)^(2ᵐ)`.  This file establishes the four facts that make it an admissible
schedule in the sense of `../../corollary.tex` §3, so that `geometric_domination` applies:

* `qsched_zero`, `qsched_succ` — it is the schedule the corollary describes;
* `qsched_le` — `δₘ ≤ δ (Kδ)ᵐ`, so `β = Kδ`;
* `Lam_qsched_le` — `Λ(δₘ) ≤ 2ᵐ Λ(δ)`, so `λ = 2`.

The last is the only one that is not immediate: `δₘ` carries a stray `log K`, and the bound
reduces to `1 + log K ≤ 2ᵐ (1 + log K)`, which holds because `1 + log K ≥ 1 > 0`.  Note it
is an equality at `m = 0`, as it must be since `δ₀ = δ`.
-/

namespace MPE

open Real

/-- The quadratic schedule `δₘ = K⁻¹ (Kδ)^(2ᵐ)`, i.e. `δ₀ = δ` and `δₘ₊₁ = K δₘ²`. -/
noncomputable def qsched (K δ : ℝ) (m : ℕ) : ℝ := K⁻¹ * (K * δ) ^ (2 ^ m)

variable {K δ : ℝ}

lemma qsched_pos (hK : 0 < K) (hδ : 0 < δ) (m : ℕ) : 0 < qsched K δ m :=
  mul_pos (inv_pos.mpr hK) (pow_pos (mul_pos hK hδ) _)

/-- **(Q1a)** The schedule starts at `δ`. -/
@[simp] lemma qsched_zero (hK : K ≠ 0) (δ : ℝ) : qsched K δ 0 = δ := by
  simp only [qsched, pow_zero, pow_one]
  field_simp

/-- **(Q1b)** The schedule satisfies `δₘ₊₁ = K δₘ²`. -/
lemma qsched_succ (hK : K ≠ 0) (δ : ℝ) (m : ℕ) :
    qsched K δ (m + 1) = K * (qsched K δ m) ^ 2 := by
  simp only [qsched]
  rw [pow_succ, pow_mul]
  field_simp

/-- **(Q2)** Geometric domination with ratio `β = Kδ`.  This is where `2ᵐ ≥ m+1` enters. -/
lemma qsched_le (hK : 1 ≤ K) (hδ : 0 < δ) (hKδ : K * δ ≤ 1) (m : ℕ) :
    qsched K δ m ≤ δ * (K * δ) ^ m := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hKδ0 : 0 < K * δ := mul_pos hK0 hδ
  have hm : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have h1 : (K * δ) ^ (2 ^ m) ≤ (K * δ) ^ (m + 1) :=
    pow_le_pow_of_le_one hKδ0.le hKδ hm
  calc qsched K δ m = K⁻¹ * (K * δ) ^ (2 ^ m) := rfl
    _ ≤ K⁻¹ * (K * δ) ^ (m + 1) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hK0.le)
    _ = δ * (K * δ) ^ m := by rw [pow_succ']; field_simp

/-- **(Q3)** The weight grows at most like `2ᵐ`. -/
lemma Lam_qsched_le (hK : 1 ≤ K) (hδ : 0 < δ) (hKδ : K * δ ≤ 1) (m : ℕ) :
    Lam (qsched K δ m) ≤ 2 ^ m * Lam δ := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hKδ0 : 0 < K * δ := mul_pos hK0 hδ
  have hδ1 : δ ≤ 1 := by nlinarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hlogKδ : Real.log (K * δ) ≤ 0 := Real.log_nonpos hKδ0.le hKδ
  have h2m : (1:ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hqpos : 0 < qsched K δ m := qsched_pos hK0 hδ m
  -- the logarithm of the schedule
  have hlog : Real.log (qsched K δ m) = -Real.log K + 2 ^ m * Real.log (K * δ) := by
    rw [qsched, Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hlognp : Real.log (qsched K δ m) ≤ 0 := by
    rw [hlog]; nlinarith
  rw [Lam, Lam, max_eq_right (by linarith : (0:ℝ) ≤ -Real.log (qsched K δ m)),
    max_eq_right (by linarith : (0:ℝ) ≤ -Real.log δ), hlog,
    Real.log_mul hK0.ne' hδ.ne']
  nlinarith [mul_nonneg (sub_nonneg.mpr h2m) (by linarith : (0:ℝ) ≤ 1 + Real.log K)]

end MPE
