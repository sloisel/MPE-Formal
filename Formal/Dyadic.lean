import Mathlib
import Formal.Weight

/-!
# The dyadic tail lemma

Appendix §4.  If `Y ≥ 0` satisfies `μ{Y ≤ u} ≤ C₀ u Λ(u)^j` for all `u > 0`, then

    ∫ min(1, t/Y) dμ  ≤  (4C₀ + M) · t · Λ(t)^(j+1),        M := μ(univ).

This is the one real computation in the anticoncentration argument, and it is used twice:
to run the induction of `Formal/Blocks.lean`, and in the fibering step of
`Formal/Annulus.lean`.

The proof here improves slightly on the appendix.  Rather than partitioning `Ω` into
dyadic shells, we bound the integrand **pointwise** by a *finite* sum of indicators plus a
constant,

    min(1, t/y)  ≤  (1/2)^K  +  ∑_{k < K} (1/2)^k · 1_{y ≤ 2^(k+1) t},

for any `K` with `(1/2)^K ≤ t`.  Integrating is then `lintegral_finset_sum` and
`lintegral_indicator_one`; no shell is ever named, no infinite sum appears, and no
partition has to be shown to cover.

Note that no positivity hypothesis on `Y` is needed: where `Y ω ≤ 0` the Lean value of
`t / Y ω` is `≤ 0`, so the integrand is `0` there and the pointwise bound is trivial.
-/

namespace MPE

open MeasureTheory Set Finset
open scoped ENNReal

/-- A dyadic index adapted to `t`: small enough that `(1/2)^K ≤ t`, but no larger than
`2Λ(t)`.  This is the only place a logarithm appears. -/
lemma exists_dyadic_index {t : ℝ} (ht : 0 < t) :
    ∃ K : ℕ, (1/2 : ℝ) ^ K ≤ t ∧ (K : ℝ) ≤ 2 * Lam t := by
  refine ⟨⌈Real.logb 2 (1/t)⌉₊, ?_, ?_⟩
  · -- `(1/2)^K ≤ t` ⟺ `1/t ≤ 2^K`
    have hle : Real.logb 2 (1/t) ≤ (⌈Real.logb 2 (1/t)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (1 : ℝ) < 2 := by norm_num
    have hrpow : (1/t : ℝ) ≤ (2 : ℝ) ^ ((⌈Real.logb 2 (1/t)⌉₊ : ℕ) : ℝ) := by
      calc (1/t : ℝ) = (2 : ℝ) ^ (Real.logb 2 (1/t)) :=
            (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
        _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 (1/t)⌉₊ : ℕ) : ℝ) :=
            Real.rpow_le_rpow_left_iff h2 |>.mpr hle
    rw [Real.rpow_natCast] at hrpow
    have hpow : (0 : ℝ) < (2 : ℝ) ^ (⌈Real.logb 2 (1/t)⌉₊) := by positivity
    rw [div_pow, one_pow]
    rw [div_le_iff₀ hpow]
    rw [div_le_iff₀ ht] at hrpow
    linarith
  · -- `K ≤ 2Λ(t)`
    rcases le_or_gt (Real.logb 2 (1/t)) 0 with h | h
    · have : ⌈Real.logb 2 (1/t)⌉₊ = 0 := Nat.ceil_eq_zero.mpr h
      rw [this]
      have := Lam_pos t
      simp; linarith
    · have hceil : ((⌈Real.logb 2 (1/t)⌉₊ : ℕ) : ℝ) < Real.logb 2 (1/t) + 1 :=
        Nat.ceil_lt_add_one h.le
      -- `logb 2 (1/t) = (-log t)/log 2`, and `-log t = Λ t - 1` here
      have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hlogt : Real.log (1/t) = -Real.log t := by
        rw [one_div, Real.log_inv]
      have hpos : 0 < -Real.log t := by
        by_contra hc
        push_neg at hc
        have : Real.logb 2 (1/t) ≤ 0 := by
          rw [Real.logb, hlogt]
          exact div_nonpos_of_nonpos_of_nonneg hc (by linarith)
        linarith
      have hLam : Lam t = 1 + (-Real.log t) := by
        rw [Lam, max_eq_right hpos.le]
      have hval : Real.logb 2 (1/t) = (-Real.log t) / Real.log 2 := by
        rw [Real.logb, hlogt]
      have hbound : (-Real.log t) / Real.log 2 ≤ 2 * (-Real.log t) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have hL : (1:ℝ) ≤ Lam t := one_le_Lam t
      rw [hval] at hceil ⊢
      rw [hLam]
      linarith

/-- **The pointwise bound.**  For any `K` with `(1/2)^K ≤ t`,
`min(1, t/y) ≤ (1/2)^K + ∑_{k<K} (1/2)^k · 1_{y ≤ 2^(k+1)t}`. -/
lemma min_one_div_le_dyadic {t y : ℝ} (ht : 0 < t) (K : ℕ) :
    ENNReal.ofReal (min 1 (t / y))
      ≤ ENNReal.ofReal ((1/2 : ℝ) ^ K)
        + ∑ k ∈ range K, ENNReal.ofReal ((1/2 : ℝ) ^ k) *
            Set.indicator {z : ℝ | z ≤ 2 ^ (k+1) * t} 1 y := by
  rcases le_or_gt y 0 with hy | hy
  · -- the integrand is `0`: either `t/y < 0`, or `y = 0` and Lean's `t/0 = 0`
    have : min 1 (t / y) ≤ 0 := by
      rcases eq_or_lt_of_le hy with rfl | hy'
      · simp
      · have : t / y < 0 := div_neg_of_pos_of_neg ht hy'
        exact le_trans (min_le_right _ _) this.le
    simp [ENNReal.ofReal_eq_zero.mpr this]
  -- `y > 0`
  rcases le_or_gt ((2:ℝ) ^ K * t) y with hcase | hcase
  · -- Case A: `y ≥ 2^K t`, so `t/y ≤ (1/2)^K`
    have hKt : t / y ≤ (1/2 : ℝ) ^ K := by
      rw [div_le_iff₀ hy, div_pow, one_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    refine le_trans (ENNReal.ofReal_le_ofReal (le_trans (min_le_right _ _) hKt)) ?_
    exact le_self_add
  -- Case B: `y < 2^K t`
  rcases Nat.eq_zero_or_pos K with rfl | hKpos
  · -- `K = 0`: the constant term is `1`, and `min 1 _ ≤ 1`
    simp only [pow_zero, range_zero, Finset.sum_empty, add_zero]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  -- `K ≥ 1`: locate the least `k` with `y ≤ 2^(k+1) t`
  have hex : ∃ k : ℕ, y ≤ 2 ^ (k+1) * t := by
    refine ⟨K - 1, ?_⟩
    rw [Nat.sub_add_cancel hKpos]
    exact hcase.le
  classical
  set k₀ := Nat.find hex with hk₀def
  have hk₀ : y ≤ 2 ^ (k₀ + 1) * t := Nat.find_spec hex
  have hk₀lt : k₀ < K := by
    have : k₀ ≤ K - 1 := Nat.find_le (by rw [Nat.sub_add_cancel hKpos]; exact hcase.le)
    omega
  -- `min(1, t/y) ≤ (1/2)^k₀`
  have hmin : min 1 (t / y) ≤ (1/2 : ℝ) ^ k₀ := by
    rcases Nat.eq_zero_or_pos k₀ with h0 | hpos
    · rw [h0]; simpa using min_le_left (1:ℝ) (t/y)
    · -- `k₀ ≥ 1`, so `k₀ - 1` fails the predicate: `y > 2^k₀ t`
      have hnot : ¬ (y ≤ 2 ^ ((k₀ - 1) + 1) * t) := Nat.find_min hex (by omega)
      rw [Nat.sub_add_cancel hpos] at hnot
      push_neg at hnot
      have : t / y ≤ (1/2 : ℝ) ^ k₀ := by
        rw [div_le_iff₀ hy, div_pow, one_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      exact le_trans (min_le_right _ _) this
  -- the `k₀` term of the sum already dominates
  have hterm : ENNReal.ofReal ((1/2 : ℝ) ^ k₀) *
      Set.indicator {z : ℝ | z ≤ 2 ^ (k₀+1) * t} 1 y
      ≤ ∑ k ∈ range K, ENNReal.ofReal ((1/2 : ℝ) ^ k) *
          Set.indicator {z : ℝ | z ≤ 2 ^ (k+1) * t} 1 y :=
    Finset.single_le_sum (f := fun k => ENNReal.ofReal ((1/2 : ℝ) ^ k) *
        Set.indicator {z : ℝ | z ≤ 2 ^ (k+1) * t} 1 y)
      (fun _ _ => zero_le) (Finset.mem_range.mpr hk₀lt)
  have hind : Set.indicator {z : ℝ | z ≤ 2 ^ (k₀+1) * t} (1 : ℝ → ℝ≥0∞) y = 1 := by
    rw [Set.indicator_of_mem (show y ∈ {z : ℝ | z ≤ 2 ^ (k₀+1) * t} from hk₀)]
    rfl
  rw [hind, mul_one] at hterm
  calc ENNReal.ofReal (min 1 (t / y)) ≤ ENNReal.ofReal ((1/2 : ℝ) ^ k₀) :=
        ENNReal.ofReal_le_ofReal hmin
    _ ≤ _ := le_trans hterm le_add_self

/-- **The dyadic tail lemma.**  From a tail bound `μ{Y ≤ u} ≤ C₀ u Λ(u)^j` one gets
`∫ min(1, t/Y) ≤ (4C₀ + M) t Λ(t)^(j+1)`, where `M` bounds the total mass. -/
theorem lintegral_min_one_div_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}
    (hY : Measurable Y) {M C₀ t : ℝ} (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀) (ht : 0 < t) (j : ℕ)
    (hμ : μ Set.univ ≤ ENNReal.ofReal M)
    (htail : ∀ u : ℝ, 0 < u → μ {ω | Y ω ≤ u} ≤ ENNReal.ofReal (C₀ * u * Lam u ^ j)) :
    ∫⁻ ω, ENNReal.ofReal (min 1 (t / Y ω)) ∂μ
      ≤ ENNReal.ofReal ((4 * C₀ + M) * t * Lam t ^ (j + 1)) := by
  classical
  obtain ⟨K, hKt, hKLam⟩ := exists_dyadic_index ht
  have hmeas : ∀ k : ℕ, MeasurableSet {ω | Y ω ≤ 2 ^ (k+1) * t} :=
    fun k => hY measurableSet_Iic
  -- integrate the pointwise bound
  have hstep : ∫⁻ ω, ENNReal.ofReal (min 1 (t / Y ω)) ∂μ
      ≤ ENNReal.ofReal ((1/2 : ℝ) ^ K) * μ Set.univ
        + ∑ k ∈ range K, ENNReal.ofReal ((1/2 : ℝ) ^ k) * μ {ω | Y ω ≤ 2 ^ (k+1) * t} := by
    calc ∫⁻ ω, ENNReal.ofReal (min 1 (t / Y ω)) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal ((1/2 : ℝ) ^ K)
            + ∑ k ∈ range K, ENNReal.ofReal ((1/2 : ℝ) ^ k) *
                Set.indicator {ω | Y ω ≤ 2 ^ (k+1) * t} 1 ω) ∂μ := by
          refine lintegral_mono fun ω => ?_
          have := min_one_div_le_dyadic (t := t) (y := Y ω) ht K
          simpa [Set.indicator, Set.mem_setOf_eq] using this
      _ = _ := by
          rw [lintegral_add_left (by fun_prop)]
          congr 1
          · rw [lintegral_const]
          · rw [lintegral_finset_sum _ (fun k _ => by
              exact (measurable_const.mul ((measurable_indicator_const_iff 1).mpr
                (hmeas k)))) ]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_indicator_one (hmeas k)]
  refine le_trans hstep ?_
  have hL0 : (0:ℝ) < Lam t := Lam_pos t
  have hLj : (0:ℝ) < Lam t ^ j := Lam_pow_pos t j
  have hLj1 : (0:ℝ) < Lam t ^ (j+1) := Lam_pow_pos t (j+1)
  -- bound the constant term by `M t`
  have hconst : ENNReal.ofReal ((1/2 : ℝ) ^ K) * μ Set.univ ≤ ENNReal.ofReal (M * t) := by
    calc ENNReal.ofReal ((1/2 : ℝ) ^ K) * μ Set.univ
        ≤ ENNReal.ofReal ((1/2 : ℝ) ^ K) * ENNReal.ofReal M :=
          mul_le_mul_left' hμ _
      _ = ENNReal.ofReal ((1/2 : ℝ) ^ K * M) := (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (M * t) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc (1/2 : ℝ) ^ K * M ≤ t * M := mul_le_mul_of_nonneg_right hKt hM
            _ = M * t := by ring
  -- each summand is at most `2 C₀ t Λ(t)^j`
  have hsummand : ∀ k ∈ range K,
      ENNReal.ofReal ((1/2 : ℝ) ^ k) * μ {ω | Y ω ≤ 2 ^ (k+1) * t}
        ≤ ENNReal.ofReal (2 * C₀ * t * Lam t ^ j) := by
    intro k _
    have hu : (0:ℝ) < 2 ^ (k+1) * t := by positivity
    have h2k : (1:ℝ) ≤ 2 ^ (k+1) := one_le_pow₀ (by norm_num)
    have hLam : Lam (2 ^ (k+1) * t) ^ j ≤ Lam t ^ j :=
      Lam_pow_le_Lam_pow ht (by nlinarith) j
    calc ENNReal.ofReal ((1/2 : ℝ) ^ k) * μ {ω | Y ω ≤ 2 ^ (k+1) * t}
        ≤ ENNReal.ofReal ((1/2 : ℝ) ^ k) *
            ENNReal.ofReal (C₀ * (2 ^ (k+1) * t) * Lam (2 ^ (k+1) * t) ^ j) :=
          mul_le_mul_left' (htail _ hu) _
      _ = ENNReal.ofReal ((1/2 : ℝ) ^ k * (C₀ * (2 ^ (k+1) * t) * Lam (2 ^ (k+1) * t) ^ j)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (2 * C₀ * t * Lam t ^ j) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hid : (1/2 : ℝ) ^ k * (2:ℝ) ^ (k+1) = 2 := by
            rw [div_pow, one_pow, pow_succ]
            field_simp
          calc (1/2 : ℝ) ^ k * (C₀ * (2 ^ (k+1) * t) * Lam (2 ^ (k+1) * t) ^ j)
              = ((1/2 : ℝ) ^ k * 2 ^ (k+1)) * (C₀ * t * Lam (2 ^ (k+1) * t) ^ j) := by ring
            _ = 2 * (C₀ * t * Lam (2 ^ (k+1) * t) ^ j) := by rw [hid]
            _ ≤ 2 * (C₀ * t * Lam t ^ j) := by
                have := mul_le_mul_of_nonneg_left hLam
                  (by positivity : (0:ℝ) ≤ C₀ * t)
                linarith
            _ = 2 * C₀ * t * Lam t ^ j := by ring
  -- sum up
  have hsum : ∑ k ∈ range K, ENNReal.ofReal ((1/2 : ℝ) ^ k) * μ {ω | Y ω ≤ 2 ^ (k+1) * t}
      ≤ ENNReal.ofReal (4 * C₀ * t * Lam t ^ (j+1)) := by
    calc ∑ k ∈ range K, ENNReal.ofReal ((1/2 : ℝ) ^ k) * μ {ω | Y ω ≤ 2 ^ (k+1) * t}
        ≤ ∑ _k ∈ range K, ENNReal.ofReal (2 * C₀ * t * Lam t ^ j) :=
          Finset.sum_le_sum hsummand
      _ = (K : ℝ≥0∞) * ENNReal.ofReal (2 * C₀ * t * Lam t ^ j) := by
          rw [Finset.sum_const, card_range, nsmul_eq_mul]
      _ = ENNReal.ofReal ((K : ℝ)) * ENNReal.ofReal (2 * C₀ * t * Lam t ^ j) := by
          rw [ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal ((K : ℝ) * (2 * C₀ * t * Lam t ^ j)) :=
          (ENNReal.ofReal_mul (Nat.cast_nonneg K)).symm
      _ ≤ ENNReal.ofReal (4 * C₀ * t * Lam t ^ (j+1)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hpos : (0:ℝ) ≤ 2 * C₀ * t * Lam t ^ j :=
            mul_nonneg (by positivity) hLj.le
          calc (K : ℝ) * (2 * C₀ * t * Lam t ^ j)
              ≤ (2 * Lam t) * (2 * C₀ * t * Lam t ^ j) :=
                mul_le_mul_of_nonneg_right hKLam hpos
            _ = 4 * C₀ * t * (Lam t ^ j * Lam t) := by ring
            _ = 4 * C₀ * t * Lam t ^ (j+1) := by rw [← pow_succ]
  calc ENNReal.ofReal ((1/2 : ℝ) ^ K) * μ Set.univ
        + ∑ k ∈ range K, ENNReal.ofReal ((1/2 : ℝ) ^ k) * μ {ω | Y ω ≤ 2 ^ (k+1) * t}
      ≤ ENNReal.ofReal (M * t) + ENNReal.ofReal (4 * C₀ * t * Lam t ^ (j+1)) :=
        add_le_add hconst hsum
    _ = ENNReal.ofReal (M * t + 4 * C₀ * t * Lam t ^ (j+1)) :=
        (ENNReal.ofReal_add (mul_nonneg hM ht.le)
          (mul_nonneg (by positivity) hLj1.le)).symm
    _ ≤ ENNReal.ofReal ((4 * C₀ + M) * t * Lam t ^ (j+1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hL1 : (1:ℝ) ≤ Lam t ^ (j+1) := one_le_Lam_pow t (j+1)
        have hmt : M * t ≤ M * t * Lam t ^ (j+1) :=
          le_mul_of_one_le_right (mul_nonneg hM ht.le) hL1
        nlinarith [hmt]

end MPE
