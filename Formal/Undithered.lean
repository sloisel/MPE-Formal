import Mathlib
import Formal.Percycle
import Formal.Excluded

/-!
# Theorem 5.5: the undithered algorithm

The orbit is deterministic, so the whole argument is one induction over cycles plus one
measure bound on the set of bad starting points.

`GoodOrbit` is the conclusion: every cycle is defined — in the cleared form (`σ̃ ≠ 0`) and
in the sense of the paper's §2 (`det U ≠ 0`) — and each cycle squares the error.
-/

namespace MPE

open MeasureTheory Metric Set
open scoped ENNReal

/-! ### `blockMeasure` lives on the cube -/

/-- Any set may be intersected with the cube without changing its `blockMeasure` bound. -/
lemma blockMeasure_le_inter_cube (d : ℕ) (S : Set (Fin d → ℝ)) :
    blockMeasure d S ≤ blockMeasure d (S ∩ cube d) := by
  have hsub : S ⊆ (S ∩ cube d) ∪ (cube d)ᶜ := by
    intro x hx
    by_cases hc : x ∈ cube d
    · exact Or.inl ⟨hx, hc⟩
    · exact Or.inr hc
  calc blockMeasure d S ≤ blockMeasure d ((S ∩ cube d) ∪ (cube d)ᶜ) := measure_mono hsub
    _ ≤ blockMeasure d (S ∩ cube d) + blockMeasure d (cube d)ᶜ := measure_union_le _ _
    _ = blockMeasure d (S ∩ cube d) := by rw [blockMeasure_compl_cube]; simp

/-! ### The good orbit -/

namespace SmoothData3

section Undith

variable {m : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}

local notation "n" => m + 1

/-- **The conclusion of Theorem 5.5, pointwise.**  Every cycle of the deterministic orbit is
defined, and each squares the error. -/
def GoodOrbit (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (C₀ : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ k : ℕ, sigt f ((cycS f)^[k] x) ≠ 0 ∧ cct f n ((cycS f)^[k] x) ≠ 0 ∧
    ‖(cycS f)^[k + 1] x‖ ≤ 4 * C₀ * ‖(cycS f)^[k] x‖ ^ 2

/-- `Q̃` vanishes at the origin, so `0` lies in every excluded set. -/
lemma QtR_zero : QtR f (0 : Fin n → ℝ) = 0 := by
  have h := QtR_smul (f := f) (0 : ℝ) 0
  rw [smul_zero] at h
  rw [h, zero_pow (by omega : n ≠ 0), zero_mul]

lemma zero_mem_excl {t : ℝ} (_ht : 0 ≤ t) : (0 : Fin n → ℝ) ∈ excl f t := by
  rw [excl, Set.mem_setOf_eq, QtR_zero, abs_zero, norm_zero, zero_pow (by omega : n ≠ 0),
    mul_zero]

/-- **The doubly exponential display.**  On the good event,
`‖xₖ‖ ≤ (4C₀‖x₀‖)^(2^k) / (4C₀)`: the squaring recurrence compounds. -/
theorem GoodOrbit.doubly_exp {C₀ : ℝ} (hC₀ : 0 < C₀) {x : Fin n → ℝ}
    (hg : GoodOrbit f C₀ x) (k : ℕ) :
    ‖(cycS f)^[k] x‖ ≤ (4 * C₀ * ‖x‖) ^ (2 ^ k) / (4 * C₀) := by
  have h0 : ∀ j : ℕ, 0 ≤ 4 * C₀ * ‖(cycS f)^[j] x‖ := fun j => by positivity
  have hstep : ∀ j : ℕ,
      4 * C₀ * ‖(cycS f)^[j + 1] x‖ ≤ (4 * C₀ * ‖(cycS f)^[j] x‖) ^ 2 := by
    intro j
    have h := (hg j).2.2
    calc 4 * C₀ * ‖(cycS f)^[j + 1] x‖
        ≤ 4 * C₀ * (4 * C₀ * ‖(cycS f)^[j] x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = (4 * C₀ * ‖(cycS f)^[j] x‖) ^ 2 := by ring
  have hiter := sq_iter_le h0 hstep k
  simp only [Function.iterate_zero_apply] at hiter
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 4 * C₀)]
  linarith [hiter]

open Filter in
/-- On the good event with `4C₀‖x₀‖ ≤ ½`, the orbit converges to the fixed point. -/
theorem GoodOrbit.tendsto_zero {C₀ : ℝ} (hC₀ : 0 < C₀) {x : Fin n → ℝ}
    (hg : GoodOrbit f C₀ x) (hsmall : 4 * C₀ * ‖x‖ ≤ 1 / 2) :
    Tendsto (fun k => ‖(cycS f)^[k] x‖) atTop (nhds 0) := by
  have hb : ∀ k : ℕ, ‖(cycS f)^[k] x‖ ≤ (1 / 2 : ℝ) ^ (k + 1) / (4 * C₀) := by
    intro k
    refine le_trans (hg.doubly_exp hC₀ k) ?_
    have h1 : (4 * C₀ * ‖x‖) ^ (2 ^ k) ≤ (1 / 2 : ℝ) ^ (2 ^ k) :=
      pow_le_pow_left₀ (by positivity) hsmall _
    have h2 : (1 / 2 : ℝ) ^ (2 ^ k) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
      refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
      have hk : k < 2 ^ k := Nat.lt_two_pow_self
      omega
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_trans h1 h2) (by positivity)
  have hupper : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) / (4 * C₀)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1/2 : ℝ) < 1)
    have h2 := h.comp (tendsto_add_atTop_nat 1)
    have h3 := h2.div_const (4 * C₀)
    simpa [Function.comp] using h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun k => norm_nonneg _) hb

/-! ### The induction -/

variable (D3 : SmoothData3 f)

set_option maxHeartbeats 1600000 in
/-- **The induction of Theorem 5.5.**  A starting point outside the excluded set has a good
orbit.  The invariant is `M₁ r_k^{1/(β+1)} ≤ h_k`: by Lemma 5.3(c) the degeneracy measure
`h` at worst takes the power `β`, while by 5.3(a) the radius is squared — and because
`β ≤ 2`, the first decays no faster than the second, so the invariant reproduces itself. -/
theorem exists_good_of_not_excl {N : ℕ} (hN : n + 1 ≤ N) (hA : IsUnit (Amat f - 1))
    {c₀ C₀ : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hA2 : ∀ v : Fin n → ℝ, ‖v‖ = 1 →
      c₀ * |QtR f v| ≤ ‖Glead D3 v‖ ∧ ‖Glead D3 v‖ ≤ C₀ * |QtR f v|)
    {c₃ β : ℝ} (hc₃ : 0 < c₃) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hA3 : ∀ v : Fin n → ℝ, ‖v‖ = 1 → QtR f v ≠ 0 →
      c₃ * |QtR f v| ^ β ≤ |QtR f (‖Glead D3 v‖⁻¹ • Glead D3 v)|) :
    ∃ M₁ ρ₀ : ℝ, 1 ≤ M₁ ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ 4 * C₀ * ρ₀ ≤ 1 / 2 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ x : Fin n → ℝ, ‖x‖ ≤ ρ →
        x ∉ excl f (M₁ * ρ ^ ((β + 1)⁻¹)) → GoodOrbit f C₀ x := by
  classical
  obtain ⟨M₁₀, ρ₂, hM₁₀1, hρ₂0, hρ₂1, hper⟩ :=
    D3.exists_percycle hN hA hc₀ hC₀ hA2 hc₃ hβ0 hA3
  have hβ1 : (0:ℝ) < β + 1 := by linarith
  set q : ℝ := (β + 1)⁻¹ with hqdef
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef, inv_le_one_iff₀]
    right; linarith
  have h4C : (0:ℝ) < (4 * C₀) ^ q := Real.rpow_pos_of_pos (by linarith) q
  set M₁ : ℝ := max M₁₀ (2 / c₃ * (4 * C₀) ^ q) with hM₁def
  have hM₁₀le : M₁₀ ≤ M₁ := le_max_left _ _
  have hM₁1 : 1 ≤ M₁ := le_trans hM₁₀1 hM₁₀le
  have hM₁0 : 0 < M₁ := lt_of_lt_of_le one_pos hM₁1
  have hM₁c : 2 / c₃ * (4 * C₀) ^ q ≤ M₁ := le_max_right _ _
  -- the smallness condition on `ρ₀`, handled without casing on `β`
  set θ : ℝ := (2 - β) / (β + 1) with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  set K : ℝ := c₃ / 2 * M₁ ^ (β - 1) / (4 * C₀) ^ q with hKdef
  have hMβ : (0:ℝ) < M₁ ^ (β - 1) := Real.rpow_pos_of_pos hM₁0 _
  have hK0 : 0 < K := by rw [hKdef]; positivity
  obtain ⟨ρa, hρa0, hρa1, hρaK⟩ : ∃ ρa : ℝ, 0 < ρa ∧ ρa ≤ 1 ∧ ρa ^ θ ≤ K := by
    by_cases hK1 : 1 ≤ K
    · exact ⟨1, one_pos, le_refl _, by rw [Real.one_rpow]; exact hK1⟩
    · -- `K < 1` forces `β < 2`, hence `θ > 0`
      rw [not_le] at hK1
      have hβlt : β < 2 := by
        rcases lt_or_eq_of_le hβ2 with h | h
        · exact h
        · exfalso
          have hKge : 1 ≤ K := by
            rw [hKdef, h]
            have hone : M₁ ^ ((2:ℝ) - 1) = M₁ := by norm_num
            rw [hone, le_div_iff₀ h4C, one_mul]
            rw [div_mul_eq_mul_div, div_le_iff₀ hc₃] at hM₁c
            linarith [hM₁c]
          linarith [hK1, hKge]
      have hθpos : 0 < θ := by
        rw [hθdef]
        exact div_pos (by linarith) hβ1
      refine ⟨min 1 (K ^ θ⁻¹), lt_min one_pos (Real.rpow_pos_of_pos hK0 _),
        min_le_left _ _, ?_⟩
      calc (min 1 (K ^ θ⁻¹)) ^ θ ≤ (K ^ θ⁻¹) ^ θ :=
            Real.rpow_le_rpow (le_of_lt (lt_min one_pos (Real.rpow_pos_of_pos hK0 _)))
              (min_le_right _ _) hθ0
        _ = K := by
            rw [← Real.rpow_mul hK0.le, inv_mul_cancel₀ hθpos.ne', Real.rpow_one]
  set ρ₀ : ℝ := min (min ρa ρ₂) (1 / (8 * C₀)) with hρ₀def
  have hρ₀0 : 0 < ρ₀ := lt_min (lt_min hρa0 hρ₂0) (by positivity)
  have hρ₀a : ρ₀ ≤ ρa := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ₀ρ₂ : ρ₀ ≤ ρ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ₀1 : ρ₀ ≤ 1 := le_trans hρ₀a hρa1
  have hρ₀C : 4 * C₀ * ρ₀ ≤ 1 / 2 := by
    have h := min_le_right (min ρa ρ₂) (1 / (8 * C₀))
    rw [← hρ₀def] at h
    have hne : C₀ ≠ 0 := hC₀.ne'
    calc 4 * C₀ * ρ₀ ≤ 4 * C₀ * (1 / (8 * C₀)) :=
          mul_le_mul_of_nonneg_left h (by linarith)
      _ = 1 / 2 := by field_simp; ring
  have hρ₀K : ρ₀ ^ θ ≤ K :=
    le_trans (Real.rpow_le_rpow hρ₀0.le hρ₀a hθ0) hρaK
  refine ⟨M₁, ρ₀, hM₁1, hρ₀0, hρ₀1, hρ₀C, ?_⟩
  intro ρ hρ hρρ₀ x hx hxn
  set xk : ℕ → Fin n → ℝ := fun k => (cycS f)^[k] x with hxkdef
  have hxk0 : xk 0 = x := rfl
  have hxksucc : ∀ k, xk (k + 1) = cycS f (xk k) := fun k =>
    Function.iterate_succ_apply' _ _ _
  -- the invariant
  have hINV : ∀ k : ℕ, 0 < ‖xk k‖ ∧ ‖xk k‖ ≤ ρ₀ ∧
      M₁ * ‖xk k‖ ^ q ≤ |QtR f (‖xk k‖⁻¹ • xk k)| := by
    intro k
    induction k with
    | zero =>
        -- `x ∉ excl` gives both positivity and the threshold
        rw [hxk0]
        rw [excl, Set.mem_setOf_eq, not_le] at hxn
        have hxne : ‖x‖ ≠ 0 := by
          intro hz
          rw [norm_eq_zero] at hz
          rw [hz, QtR_zero, abs_zero, norm_zero, zero_pow (by omega : n ≠ 0), mul_zero] at hxn
          exact lt_irrefl _ hxn
        have hx0 : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hxne)
        refine ⟨hx0, le_trans hx hρρ₀, ?_⟩
        have hsplit : x = ‖x‖ • (‖x‖⁻¹ • x) := by
          rw [smul_smul, mul_inv_cancel₀ hxne, one_smul]
        have hQ : |QtR f x| = ‖x‖ ^ n * |QtR f (‖x‖⁻¹ • x)| := by
          conv_lhs => rw [hsplit]
          rw [QtR_smul, abs_mul, abs_pow, abs_of_pos hx0]
        rw [hQ] at hxn
        have hpow : (0:ℝ) < ‖x‖ ^ n := pow_pos hx0 n
        have hlt : M₁ * ρ ^ q < |QtR f (‖x‖⁻¹ • x)| := by
          nlinarith [hxn, hpow]
        have hmono : ‖x‖ ^ q ≤ ρ ^ q := Real.rpow_le_rpow (norm_nonneg x) hx hq0.le
        have hmul := mul_le_mul_of_nonneg_left hmono hM₁0.le
        linarith [hlt, hmul]
    | succ k ih =>
        obtain ⟨hr0, hrρ, hthr⟩ := ih
        have hrne : ‖xk k‖ ≠ 0 := hr0.ne'
        have hvn : ‖‖xk k‖⁻¹ • xk k‖ = 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          field_simp
        have hxeq : ‖xk k‖ • (‖xk k‖⁻¹ • xk k) = xk k := by
          rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
        have hr1 : ‖xk k‖ ≤ 1 := le_trans hrρ hρ₀1
        -- the weak threshold, from the strong one
        have hweak : M₁₀ * ‖xk k‖ ≤ |QtR f (‖xk k‖⁻¹ • xk k)| := by
          have hmono : ‖xk k‖ ≤ ‖xk k‖ ^ q := by
            have := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hq1
            rwa [Real.rpow_one] at this
          have hmul := mul_le_mul_of_nonneg_left hmono hM₁0.le
          have hle : M₁₀ * ‖xk k‖ ≤ M₁ * ‖xk k‖ :=
            mul_le_mul_of_nonneg_right hM₁₀le hr0.le
          linarith [hthr, hmul, hle]
        have hcyc := hper (‖xk k‖) (‖xk k‖⁻¹ • xk k) hr0 (le_trans hrρ hρ₀ρ₂) hvn hweak
        rw [hxeq] at hcyc
        obtain ⟨-, -, hlo, hhi, hc⟩ := hcyc
        rw [← hxksucc k] at hlo hhi hc
        -- positivity and smallness of the new radius
        have hr0' : 0 < ‖xk (k + 1)‖ := lt_of_lt_of_le (by positivity) hlo
        have hrρ' : ‖xk (k + 1)‖ ≤ ρ₀ := by
          have h1 : 4 * C₀ * ‖xk k‖ ^ 2 ≤ ‖xk k‖ := by
            have h2 : 4 * C₀ * ‖xk k‖ ≤ 1 := by
              have hm := mul_le_mul_of_nonneg_left hrρ (by linarith : (0:ℝ) ≤ 4 * C₀)
              linarith [hρ₀C, hm]
            nlinarith [h2, hr0]
          exact le_trans hhi (le_trans h1 hrρ)
        refine ⟨hr0', hrρ', ?_⟩
        -- the strong threshold reproduces itself
        have hstrong : M₁ * ‖xk k‖ ^ q ≤ |QtR f (‖xk k‖⁻¹ • xk k)| := hthr
        have hc' := hc (by
          have hle : M₁₀ * ‖xk k‖ ^ q ≤ M₁ * ‖xk k‖ ^ q :=
            mul_le_mul_of_nonneg_right hM₁₀le (Real.rpow_nonneg hr0.le _)
          rw [hqdef] at hle hstrong ⊢
          linarith [hle, hstrong])
        set hk : ℝ := |QtR f (‖xk k‖⁻¹ • xk k)| with hhkdef
        have hhk0 : 0 < hk := lt_of_lt_of_le (by positivity) hstrong
        -- lower bound for the new degeneracy measure
        have hstep1 : c₃ / 2 * (M₁ * ‖xk k‖ ^ q) ^ β ≤ c₃ / 2 * hk ^ β := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact Real.rpow_le_rpow (by positivity) hstrong hβ0
        have hexp1 : (M₁ * ‖xk k‖ ^ q) ^ β = M₁ ^ β * ‖xk k‖ ^ (q * β) := by
          rw [Real.mul_rpow hM₁0.le (Real.rpow_nonneg hr0.le _), ← Real.rpow_mul hr0.le]
        -- upper bound for the new threshold
        have hexp2 : ‖xk (k + 1)‖ ^ q ≤ (4 * C₀) ^ q * ‖xk k‖ ^ (2 * q) := by
          have h1 : ‖xk (k + 1)‖ ^ q ≤ (4 * C₀ * ‖xk k‖ ^ 2) ^ q :=
            Real.rpow_le_rpow hr0'.le hhi hq0.le
          refine le_trans h1 (le_of_eq ?_)
          rw [Real.mul_rpow (by linarith) (by positivity)]
          congr 1
          rw [← Real.rpow_natCast ‖xk k‖ 2, ← Real.rpow_mul hr0.le]
          norm_num
        -- the exponent bookkeeping
        have hsplitpow : ‖xk k‖ ^ (2 * q) = ‖xk k‖ ^ (q * β) * ‖xk k‖ ^ θ := by
          rw [← Real.rpow_add hr0, hqdef, hθdef]
          congr 1
          field_simp
          ring
        have hKbd : (4 * C₀) ^ q * ‖xk k‖ ^ θ ≤ c₃ / 2 * M₁ ^ (β - 1) := by
          have h1 : ‖xk k‖ ^ θ ≤ ρ₀ ^ θ := Real.rpow_le_rpow hr0.le hrρ hθ0
          have h2 : ‖xk k‖ ^ θ ≤ K := le_trans h1 hρ₀K
          rw [hKdef, le_div_iff₀ h4C] at h2
          linarith [h2]
        have hMsplit : M₁ * M₁ ^ (β - 1) = M₁ ^ β := by
          have hadd := Real.rpow_add hM₁0 1 (β - 1)
          rw [Real.rpow_one] at hadd
          rw [← hadd]
          congr 1
          ring
        calc M₁ * ‖xk (k + 1)‖ ^ q
            ≤ M₁ * ((4 * C₀) ^ q * ‖xk k‖ ^ (2 * q)) :=
              mul_le_mul_of_nonneg_left hexp2 hM₁0.le
          _ = M₁ * ((4 * C₀) ^ q * ‖xk k‖ ^ θ) * ‖xk k‖ ^ (q * β) := by
              rw [hsplitpow]; ring
          _ ≤ M₁ * (c₃ / 2 * M₁ ^ (β - 1)) * ‖xk k‖ ^ (q * β) := by
              refine mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hKbd hM₁0.le) (Real.rpow_nonneg hr0.le _)
          _ = c₃ / 2 * (M₁ ^ β * ‖xk k‖ ^ (q * β)) := by rw [← hMsplit]; ring
          _ = c₃ / 2 * (M₁ * ‖xk k‖ ^ q) ^ β := by rw [hexp1]
          _ ≤ c₃ / 2 * hk ^ β := hstep1
          _ ≤ |QtR f (‖xk (k + 1)‖⁻¹ • xk (k + 1))| := hc'
  -- from the invariant to `GoodOrbit`
  intro k
  obtain ⟨hr0, hrρ, hthr⟩ := hINV k
  have hrne : ‖xk k‖ ≠ 0 := hr0.ne'
  have hvn : ‖‖xk k‖⁻¹ • xk k‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hxeq : ‖xk k‖ • (‖xk k‖⁻¹ • xk k) = xk k := by
    rw [smul_smul, mul_inv_cancel₀ hrne, one_smul]
  have hr1 : ‖xk k‖ ≤ 1 := le_trans hrρ hρ₀1
  have hweak : M₁₀ * ‖xk k‖ ≤ |QtR f (‖xk k‖⁻¹ • xk k)| := by
    have hmono : ‖xk k‖ ≤ ‖xk k‖ ^ q := by
      have := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hq1
      rwa [Real.rpow_one] at this
    have hmul := mul_le_mul_of_nonneg_left hmono hM₁0.le
    have hle : M₁₀ * ‖xk k‖ ≤ M₁ * ‖xk k‖ :=
      mul_le_mul_of_nonneg_right hM₁₀le hr0.le
    linarith [hthr, hmul, hle]
  have hcyc := hper (‖xk k‖) (‖xk k‖⁻¹ • xk k) hr0 (le_trans hrρ hρ₀ρ₂) hvn hweak
  rw [hxeq] at hcyc
  obtain ⟨hσ, hdet, -, hhi, -⟩ := hcyc
  rw [← hxksucc k] at hhi
  exact ⟨hσ, hdet, hhi⟩

/-! ### Theorem 5.5 -/

set_option maxHeartbeats 800000 in
/-- **Theorem 5.5.**  Under Hypotheses A2 and A3, for a uniformly random start in the ball
of radius `ρ`, restarted full-window MPE converges with probability at least
`1 - C ρ^{1/(n(β+1))}`: every cycle is defined and each squares the error.

There is no dither: the orbit is deterministic and the only randomness is `x₀`. -/
theorem exists_undithered {N : ℕ} (hN : n + 1 ≤ N) (hA : IsUnit (Amat f - 1))
    (hnd : ∃ v : Fin n → ℝ, (krylov (Amat f) v).det ≠ 0)
    {c₀ C₀ : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hA2 : ∀ v : Fin n → ℝ, ‖v‖ = 1 →
      c₀ * |QtR f v| ≤ ‖Glead D3 v‖ ∧ ‖Glead D3 v‖ ≤ C₀ * |QtR f v|)
    {c₃ β : ℝ} (hc₃ : 0 < c₃) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hA3 : ∀ v : Fin n → ℝ, ‖v‖ = 1 → QtR f v ≠ 0 →
      c₃ * |QtR f v| ^ β ≤ |QtR f (‖Glead D3 v‖⁻¹ • Glead D3 v)|) :
    ∃ C ρ₀ : ℝ, 0 < C ∧ 0 < ρ₀ ∧ 4 * C₀ * ρ₀ ≤ 1 / 2 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
        blockMeasure n {b : Fin n → ℝ | ¬ GoodOrbit f C₀ (ρ • b)}
          ≤ ENNReal.ofReal (C * ρ ^ ((β + 1)⁻¹ * ((m : ℝ) + 1)⁻¹)) := by
  classical
  obtain ⟨M₁, ρ₀, hM₁1, hρ₀0, hρ₀1, hρ₀half, hgood⟩ :=
    D3.exists_good_of_not_excl hN hA hc₀ hC₀ hA2 hc₃ hβ0 hβ2 hA3
  obtain ⟨Cm, hCm0, hexcl⟩ := blockMeasure_excl_le hA hnd
  have hM₁0 : 0 < M₁ := lt_of_lt_of_le one_pos hM₁1
  set p : ℝ := ((m : ℝ) + 1)⁻¹ with hpdef
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hβ1 : (0:ℝ) < β + 1 := by linarith
  set q : ℝ := (β + 1)⁻¹ with hqdef
  have hq0 : 0 < q := by rw [hqdef]; positivity
  refine ⟨Cm * M₁ ^ p, ρ₀, mul_pos hCm0 (Real.rpow_pos_of_pos hM₁0 p), hρ₀0, hρ₀half, ?_⟩
  intro ρ hρ hρρ₀
  set t : ℝ := M₁ * ρ ^ q with htdef
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  -- the failure set sits inside the excluded set
  have hsub : {b : Fin n → ℝ | ¬ GoodOrbit f C₀ (ρ • b)} ∩ cube n
      ⊆ (fun b : Fin n → ℝ => ρ • b) ⁻¹' (excl f t) := by
    rintro b ⟨hb, hbc⟩
    by_contra hcon
    exact hb (hgood ρ hρ hρρ₀ (ρ • b)
      (by
        have hbn : ‖b‖ ≤ 1 := by rwa [← closedBall_eq_cube] at hbc
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
        nlinarith [hbn, hρ.le])
      hcon)
  -- the exponent bookkeeping
  have hpow : t ^ p = M₁ ^ p * ρ ^ (q * p) := by
    rw [htdef, Real.mul_rpow hM₁0.le (Real.rpow_nonneg hρ.le _), ← Real.rpow_mul hρ.le]
  calc blockMeasure n {b : Fin n → ℝ | ¬ GoodOrbit f C₀ (ρ • b)}
      ≤ blockMeasure n ({b : Fin n → ℝ | ¬ GoodOrbit f C₀ (ρ • b)} ∩ cube n) :=
        blockMeasure_le_inter_cube _ _
    _ ≤ blockMeasure n ((fun b : Fin n → ℝ => ρ • b) ⁻¹' (excl f t)) := measure_mono hsub
    _ = blockMeasure n (excl f t) := by rw [preimage_smul_excl hρ]
    _ ≤ ENNReal.ofReal (Cm * t ^ p) := hexcl t ht0
    _ = ENNReal.ofReal (Cm * M₁ ^ p * ρ ^ (q * p)) := by rw [hpow]; ring_nf

end Undith

/-! ### The paper's statement

Theorem 5.5 with the smoothness hypothesis as the paper writes it: `f` is `C³` on a ball
about its fixed point.  `nonempty_smoothData3` produces the quadratic Taylor data, and
Hypotheses A2 and A3 — which are conditions on the leading form `G = Δ·N²` built from that
data — are then the paper's own. -/

section Top

open Metric

variable {M : ℕ} {f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ)}

/-- **Theorem 5.5.**  Let `f` be `C³` near its fixed point `0`, with `I - A` invertible and
`A` nonderogatory.  The quadratic Taylor data exists, and under Hypotheses A2 and A3 for the
resulting leading form, a uniformly random start in the ball of radius `ρ` gives, with
probability at least `1 - C ρ^{1/(n(β+1))}`, an orbit every cycle of which is defined and
squares the error. -/
theorem mpe_undithered_C3
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 3 f (Metric.ball 0 R))
    (hA : IsUnit (Amat f - 1))
    (hnd : ∃ v : Fin (M + 2) → ℝ, (krylov (Amat f) v).det ≠ 0)
    {c₀ C₀ c₃ β : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hc₃ : 0 < c₃)
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) :
    ∃ D3 : SmoothData3 f,
      (∀ v : Fin (M + 2) → ℝ, ‖v‖ = 1 →
          c₀ * |QtR f v| ≤ ‖Glead D3 v‖ ∧ ‖Glead D3 v‖ ≤ C₀ * |QtR f v|) →
      (∀ v : Fin (M + 2) → ℝ, ‖v‖ = 1 → QtR f v ≠ 0 →
          c₃ * |QtR f v| ^ β ≤ |QtR f (‖Glead D3 v‖⁻¹ • Glead D3 v)|) →
      ∃ C ρ₀ : ℝ, 0 < C ∧ 0 < ρ₀ ∧ 4 * C₀ * ρ₀ ≤ 1 / 2 ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
          blockMeasure (M + 2) {b : Fin (M + 2) → ℝ | ¬ SmoothData3.GoodOrbit f C₀ (ρ • b)}
            ≤ ENNReal.ofReal (C * ρ ^ ((β + 1)⁻¹ * ((M : ℝ) + 2)⁻¹)) := by
  obtain ⟨D3, -⟩ := nonempty_smoothData3 hR hf0 hmeas hf
  refine ⟨D3, fun hA2 hA3 => ?_⟩
  have hcast : (((M + 1 : ℕ) : ℝ) + 1)⁻¹ = ((M : ℝ) + 2)⁻¹ := by push_cast; ring_nf
  obtain ⟨C, ρ₀, hC0, hρ₀0, hhalf, hmain⟩ :=
    D3.exists_undithered (N := M + 3) (by omega) hA hnd hc₀ hC₀ hA2 hc₃ hβ0 hβ2 hA3
  refine ⟨C, ρ₀, hC0, hρ₀0, hhalf, ?_⟩
  intro ρ hρ hρρ₀
  have h := hmain ρ hρ hρρ₀
  rwa [hcast] at h

/-- **Theorem 5.5, with every object given by a defining equation.**  The bridging lemma
behind `Formal/Statement.lean`'s self-contained statement: `U`, `c`, `σ̃`, `Ñ`, `Q̃`, `q₂`
and `G` are supplied as data satisfying their paper definitions, and identified here with
the construction. -/
theorem mpe_undithered_stmt
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 3 f (Metric.ball 0 R))
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1))
    (hnd : ∃ v : Fin (M + 2) → ℝ,
      Matrix.det (Matrix.of fun i j : Fin (M + 2) => ((A ^ (j : ℕ)).mulVec v) i) ≠ 0)
    (U : (Fin (M + 2) → ℝ) → Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hU : ∀ y i j, U y i j = f^[(j : ℕ) + 1] y i - f^[(j : ℕ)] y i)
    (c : ℕ → (Fin (M + 2) → ℝ) → ℝ)
    (hcAdj : ∀ (j : Fin (M + 2)) y,
      c (j : ℕ) y = (U y).adjugate.mulVec (fun i => -(f^[M + 3] y i - f^[M + 2] y i)) j)
    (hcDet : ∀ y, c (M + 2) y = (U y).det)
    (sg : (Fin (M + 2) → ℝ) → ℝ) (Nt : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hsg : ∀ y, sg y = ∑ j ∈ Finset.range (M + 3), c j y)
    (hNt : ∀ y, Nt y = ∑ j ∈ Finset.range (M + 3), c j y • f^[j] y)
    (Q : (Fin (M + 2) → ℝ) → ℝ)
    (hQ : ∀ v, Q v = A.charpoly.eval 1 *
      Matrix.det (Matrix.of fun i j : Fin (M + 2) => (((A - 1) * A ^ (j : ℕ)).mulVec v) i))
    (q₂ : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hq₂ : ∀ x, q₂ x = (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ f) 0) x) x)
    (Gl : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hGl : ∀ v, Gl v =
      Matrix.det (Matrix.of fun i j : Fin (M + 2) => (((A - 1) * A ^ (j : ℕ)).mulVec v) i) •
        (A - 1)⁻¹.mulVec
          (-∑ j ∈ Finset.range (M + 3), A.charpoly.coeff j • q₂ ((A ^ j).mulVec v)))
    {c₀ C₀ c₃ β : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hc₃ : 0 < c₃)
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hA2 : ∀ v : Fin (M + 2) → ℝ, ‖v‖ = 1 → c₀ * |Q v| ≤ ‖Gl v‖ ∧ ‖Gl v‖ ≤ C₀ * |Q v|)
    (hA3 : ∀ v : Fin (M + 2) → ℝ, ‖v‖ = 1 → Q v ≠ 0 →
      c₃ * |Q v| ^ β ≤ |Q (‖Gl v‖⁻¹ • Gl v)|) :
    ∃ Cst ρ₀ : ℝ, 0 < Cst ∧ 0 < ρ₀ ∧ 4 * C₀ * ρ₀ ≤ 1 / 2 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
        (Measure.pi fun _ : Fin (M + 2) =>
            ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
          {b : Fin (M + 2) → ℝ | ¬ ∀ k : ℕ,
              sg ((fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b)) ≠ 0 ∧
              (U ((fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b))).det ≠ 0 ∧
              ‖(fun y => (sg y)⁻¹ • Nt y)^[k + 1] (ρ • b)‖
                ≤ 4 * C₀ * ‖(fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b)‖ ^ 2 ∧
              ‖(fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b)‖
                ≤ (4 * C₀ * ‖ρ • b‖) ^ (2 ^ k) / (4 * C₀)}
          ≤ ENNReal.ofReal (Cst * ρ ^ ((β + 1)⁻¹ * ((M : ℝ) + 2)⁻¹)) := by
  classical
  -- identify the supplied data with the construction
  have hAeq : A = Amat f := by rw [hAdef, Amat]
  subst hAeq
  have hUeq : ∀ y, U y = Ueval f y := by
    intro y; funext i j; rw [hU y i j]; rfl
  have hceq : ∀ j ∈ Finset.range (M + 3), ∀ y, c j y = cct f j y := by
    intro j hj y
    rw [Finset.mem_range] at hj
    rcases Nat.lt_or_ge j (M + 2) with hlt | hge
    · rw [cct, dif_pos hlt, ← hUeq y]
      rw [hcAdj ⟨j, hlt⟩ y]; rfl
    · have hjeq : j = M + 2 := by omega
      subst hjeq
      rw [hcDet y, cct, dif_neg (by omega), hUeq y]
  have hsgeq : ∀ y, sg y = sigt f y := by
    intro y; rw [hsg y, sigt]
    exact Finset.sum_congr rfl fun j hj => hceq j hj y
  have hNteq : ∀ y, Nt y = Ntil f y := by
    intro y; rw [hNt y, Ntil]
    exact Finset.sum_congr rfl fun j hj => by rw [hceq j hj y]
  have hPeq : (fun y => (sg y)⁻¹ • Nt y) = cycS f := by
    funext y; rw [hsgeq y, hNteq y, cycS]
  have hKeq : ∀ v : Fin (M + 2) → ℝ,
      Matrix.det (Matrix.of fun i j : Fin (M + 2) =>
        (((Amat f - 1) * (Amat f) ^ (j : ℕ)).mulVec v) i) = DeltaR f v := fun v => rfl
  have hQeq : ∀ v, Q v = QtR f v := by intro v; rw [hQ v, QtR, hKeq v]
  have hndeq : ∃ v : Fin (M + 2) → ℝ, (krylov (Amat f) v).det ≠ 0 := hnd
  -- the cubic data, with `q₂` pinned to the supplied one
  obtain ⟨D3, hD3q⟩ := nonempty_smoothData3 hR hf0 hmeas hf
  have hq₂eq : ∀ x, D3.q₂ x = q₂ x := by intro x; rw [hD3q x, hq₂ x]
  have hGeq : ∀ v, Gl v = Glead D3 v := by
    intro v
    rw [hGl v, Glead, NtwoR, hKeq v]
    congr 2
    refine congrArg Neg.neg ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hq₂eq]
  -- transport the hypotheses
  have hA2' : ∀ v : Fin (M + 2) → ℝ, ‖v‖ = 1 →
      c₀ * |QtR f v| ≤ ‖Glead D3 v‖ ∧ ‖Glead D3 v‖ ≤ C₀ * |QtR f v| := by
    intro v hv; rw [← hQeq v, ← hGeq v]; exact hA2 v hv
  have hA3' : ∀ v : Fin (M + 2) → ℝ, ‖v‖ = 1 → QtR f v ≠ 0 →
      c₃ * |QtR f v| ^ β ≤ |QtR f (‖Glead D3 v‖⁻¹ • Glead D3 v)| := by
    intro v hv hQv
    rw [← hQeq v, ← hGeq v, ← hQeq]
    exact hA3 v hv (by rwa [hQeq v])
  obtain ⟨Cst, ρ₀, hC0, hρ₀0, hhalf, hmain⟩ :=
    D3.exists_undithered (N := M + 3) (by omega) hA hndeq hc₀ hC₀ hA2' hc₃ hβ0 hβ2 hA3'
  refine ⟨Cst, ρ₀, hC0, hρ₀0, hhalf, ?_⟩
  intro ρ hρ hρρ₀
  have hcast : (((M + 1 : ℕ) : ℝ) + 1)⁻¹ = ((M : ℝ) + 2)⁻¹ := by push_cast; ring_nf
  have h := hmain ρ hρ hρρ₀
  rw [hcast] at h
  refine le_trans (measure_mono ?_) h
  intro b hb
  rw [Set.mem_setOf_eq] at hb ⊢
  intro hgood
  refine hb (fun k => ?_)
  rw [hPeq]
  exact ⟨by rw [hsgeq]; exact (hgood k).1,
    by rw [← hcDet, hceq (M + 2) (by simp) _]; exact (hgood k).2.1,
    (hgood k).2.2, hgood.doubly_exp hC₀ k⟩

end Top

end SmoothData3

end MPE
