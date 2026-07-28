import Mathlib
import Formal.Cubic

/-!
# Ingredients for the per-cycle lemma (the paper's Lemma 5.3)

Three elementary facts, each independent of the MPE construction except the first.

* `QtR_lipschitz`: `Q̃` is Lipschitz on the unit ball.  The `Van` calculus already bounds
  `‖D Δ‖` on the *small* ball `closedBall 0 (rad N)`, and homogeneity transports that to the
  unit ball at no cost: rescaling by `r` multiplies the derivative bound by `r^m` and the
  displacement by `r`, against `r^(m+1)` from the values — the powers cancel exactly.
* `norm_normalize_sub_le`: `‖b/‖b‖ - a/‖a‖‖ ≤ 2‖b-a‖/‖a‖`.
* `sq_iter_le`: a nonnegative sequence with `u (k+1) ≤ (u k)²` satisfies `u k ≤ (u 0)^(2^k)`
  — the doubly exponential decay, isolated from everything else.
-/

namespace MPE

open Metric Set

/-! ### Normalisation is stable -/

section Normalize

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The normalized-difference inequality.**  Perturbing a nonzero vector moves its
direction by at most twice the relative size of the perturbation. -/
theorem norm_normalize_sub_le {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖‖b‖⁻¹ • b - ‖a‖⁻¹ • a‖ ≤ 2 * ‖b - a‖ / ‖a‖ := by
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hb0 : 0 < ‖b‖ := norm_pos_iff.mpr hb
  -- `‖a‖‖b‖ • (b/‖b‖ - a/‖a‖) = ‖a‖ • b - ‖b‖ • a`
  have hkey : (‖a‖ * ‖b‖) • (‖b‖⁻¹ • b - ‖a‖⁻¹ • a) = ‖a‖ • b - ‖b‖ • a := by
    rw [smul_sub, smul_smul, smul_smul]
    congr 1
    · congr 1; field_simp
    · rw [mul_comm ‖a‖ ‖b‖, mul_assoc, mul_inv_cancel₀ ha0.ne', mul_one]
  -- the second grouping: `‖a‖•b - ‖b‖•a = ‖b‖•(b-a) + (‖a‖-‖b‖)•b`
  have hsplit : ‖a‖ • b - ‖b‖ • a = ‖b‖ • (b - a) + (‖a‖ - ‖b‖) • b := by
    rw [smul_sub, sub_smul]
    abel
  have hbd : ‖‖a‖ • b - ‖b‖ • a‖ ≤ 2 * ‖b‖ * ‖b - a‖ := by
    rw [hsplit]
    have h1 : ‖‖b‖ • (b - a)‖ = ‖b‖ * ‖b - a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
    have h2 : ‖(‖a‖ - ‖b‖) • b‖ ≤ ‖b - a‖ * ‖b‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg b)
      have := abs_norm_sub_norm_le a b
      calc |‖a‖ - ‖b‖| ≤ ‖a - b‖ := this
        _ = ‖b - a‖ := by rw [norm_sub_rev]
    calc ‖‖b‖ • (b - a) + (‖a‖ - ‖b‖) • b‖
        ≤ ‖‖b‖ • (b - a)‖ + ‖(‖a‖ - ‖b‖) • b‖ := norm_add_le _ _
      _ ≤ ‖b‖ * ‖b - a‖ + ‖b - a‖ * ‖b‖ := by rw [h1]; linarith [h2]
      _ = 2 * ‖b‖ * ‖b - a‖ := by ring
  have hnorm : (‖a‖ * ‖b‖) * ‖‖b‖⁻¹ • b - ‖a‖⁻¹ • a‖ ≤ 2 * ‖b‖ * ‖b - a‖ := by
    have := congrArg norm hkey
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos ha0 hb0)] at this
    rw [this]
    exact hbd
  rw [le_div_iff₀ ha0]
  nlinarith [hnorm, ha0, hb0, norm_nonneg (b - a)]

end Normalize

/-! ### Doubly exponential decay -/

/-- **The squaring recursion.**  `u (k+1) ≤ (u k)²` with `u ≥ 0` forces `u k ≤ (u 0)^(2^k)`. -/
theorem sq_iter_le {u : ℕ → ℝ} (h0 : ∀ k, 0 ≤ u k) (hstep : ∀ k, u (k + 1) ≤ (u k) ^ 2) :
    ∀ k, u k ≤ (u 0) ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      calc u (k + 1) ≤ (u k) ^ 2 := hstep k
        _ ≤ ((u 0) ^ (2 ^ k)) ^ 2 := by
            refine pow_le_pow_left₀ (h0 k) ih 2
        _ = (u 0) ^ (2 ^ (k + 1)) := by
            rw [← pow_mul, pow_succ]

/-! ### `Q̃` is Lipschitz on the unit ball -/

section Lip

variable {m : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)} (D : SmoothData f)

local notation "n" => m + 1

/-- **Ob lip.**  `|Q̃(a) - Q̃(b)| ≤ L ‖a - b‖` for `‖a‖, ‖b‖ ≤ 1`.

The proof rescales to the ball of radius `rad N`, where `van_DeltaR` already supplies
`‖D Δ(z)‖ ≤ CΔ ‖z‖^m`, and applies the mean value inequality on that convex set.  Under
`z ↦ r z` the values of `Q̃` scale by `r^(m+1)`, the derivative bound by `r^m` and the
displacement by `r`: the powers cancel, so the constant is `|p_A(1)| CΔ`, independent of
`r`. -/
theorem QtR_lipschitz (N : ℕ) {a b : Fin n → ℝ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |QtR f a - QtR f b| ≤ |(Amat f).charpoly.eval 1| * D.CDelta N * ‖a - b‖ := by
  classical
  set r : ℝ := D.rad N with hrdef
  have hr0 : 0 < r := D.rad_pos N
  have hCD : 0 ≤ D.CDelta N := D.CDelta_nonneg N
  set p1 : ℝ := |(Amat f).charpoly.eval 1| with hp1def
  have hp10 : 0 ≤ p1 := abs_nonneg _
  -- the mean value inequality for `Δ` on the small ball
  have hconv : Convex ℝ (closedBall (0 : Fin n → ℝ) r) := convex_closedBall _ _
  have hmemA : (r • a) ∈ closedBall (0 : Fin n → ℝ) r := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    nlinarith [ha, hr0, norm_nonneg a]
  have hmemB : (r • b) ∈ closedBall (0 : Fin n → ℝ) r := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    nlinarith [hb, hr0, norm_nonneg b]
  have hvan := D.van_DeltaR N
  have hmvt : ‖DeltaR f (r • a) - DeltaR f (r • b)‖
      ≤ (D.CDelta N * r ^ m) * ‖r • a - r • b‖ := by
    refine hconv.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => hvan.diff z hz) (fun z hz => ?_) hmemB hmemA
    refine le_trans (hvan.der z hz) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCD
    have hz' : ‖z‖ ≤ r := by rwa [mem_closedBall, dist_zero_right] at hz
    exact pow_le_pow_left₀ (norm_nonneg z) hz' m
  -- transport by homogeneity
  have hscale : QtR f (r • a) - QtR f (r • b) = r ^ n * (QtR f a - QtR f b) := by
    rw [QtR_smul, QtR_smul]; ring
  have hQD : ∀ z : Fin n → ℝ, QtR f z = (Amat f).charpoly.eval 1 * DeltaR f z := fun z => rfl
  have hdisp : ‖r • a - r • b‖ = r * ‖a - b‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
  have hrn : (0:ℝ) < r ^ n := pow_pos hr0 n
  have hstep : r ^ n * |QtR f a - QtR f b| ≤ (p1 * D.CDelta N) * (r ^ n * ‖a - b‖) := by
    have hL : |QtR f (r • a) - QtR f (r • b)| = r ^ n * |QtR f a - QtR f b| := by
      rw [hscale, abs_mul, abs_of_pos hrn]
    rw [← hL, hQD, hQD, ← mul_sub, abs_mul, ← hp1def]
    have h2 : |DeltaR f (r • a) - DeltaR f (r • b)| ≤ (D.CDelta N * r ^ m) * (r * ‖a - b‖) := by
      rw [← hdisp]
      have := hmvt
      rwa [Real.norm_eq_abs] at this
    have hexp : (D.CDelta N * r ^ m) * (r * ‖a - b‖) = D.CDelta N * (r ^ n * ‖a - b‖) := by
      rw [pow_succ]; ring
    rw [hexp] at h2
    calc p1 * |DeltaR f (r • a) - DeltaR f (r • b)|
        ≤ p1 * (D.CDelta N * (r ^ n * ‖a - b‖)) := mul_le_mul_of_nonneg_left h2 hp10
      _ = (p1 * D.CDelta N) * (r ^ n * ‖a - b‖) := by ring
  have hfin : r ^ n * |QtR f a - QtR f b| ≤ r ^ n * ((p1 * D.CDelta N) * ‖a - b‖) := by
    calc r ^ n * |QtR f a - QtR f b|
        ≤ (p1 * D.CDelta N) * (r ^ n * ‖a - b‖) := hstep
      _ = r ^ n * ((p1 * D.CDelta N) * ‖a - b‖) := by ring
  exact le_of_mul_le_mul_left hfin hrn

end Lip

/-! ### The per-cycle lemma (Lemma 5.3) -/

namespace SmoothData3

section Per

variable {m : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)} (D3 : SmoothData3 f)

local notation "n" => m + 1

set_option maxHeartbeats 1600000 in
/-- **Lemma 5.3.**  One cycle, pointwise and deterministically.  If the direction `v` is
clear of degeneracy at scale `r` — `|Q̃(v)| ≥ M₁ r` — then the cycle at `r v` is defined
(both in the cleared form and in the sense of the paper's §2, `det U ≠ 0`), the radius is
squared up to constants, and, under the stronger threshold and Hypothesis A3, the new
direction is still clear of degeneracy at the reduced level `(c₃/2)|Q̃(v)|^β`. -/
theorem exists_percycle {N : ℕ} (hN : n + 1 ≤ N) (hA : IsUnit (Amat f - 1))
    {c₀ C₀ : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hA2 : ∀ v : Fin n → ℝ, ‖v‖ = 1 →
      c₀ * |QtR f v| ≤ ‖Glead D3 v‖ ∧ ‖Glead D3 v‖ ≤ C₀ * |QtR f v|)
    {c₃ β : ℝ} (hc₃ : 0 < c₃) (hβ0 : 0 ≤ β)
    (hA3 : ∀ v : Fin n → ℝ, ‖v‖ = 1 → QtR f v ≠ 0 →
      c₃ * |QtR f v| ^ β ≤ |QtR f (‖Glead D3 v‖⁻¹ • Glead D3 v)|) :
    ∃ M₁ ρ₂ : ℝ, 1 ≤ M₁ ∧ 0 < ρ₂ ∧ ρ₂ ≤ 1 ∧
      ∀ (r : ℝ) (v : Fin n → ℝ), 0 < r → r ≤ ρ₂ → ‖v‖ = 1 →
        M₁ * r ≤ |QtR f v| →
        sigt f (r • v) ≠ 0 ∧ cct f n (r • v) ≠ 0 ∧
        c₀ / 4 * r ^ 2 ≤ ‖cycS f (r • v)‖ ∧ ‖cycS f (r • v)‖ ≤ 4 * C₀ * r ^ 2 ∧
        (M₁ * r ^ ((β + 1)⁻¹) ≤ |QtR f v| →
          c₃ / 2 * |QtR f v| ^ β
            ≤ |QtR f (‖cycS f (r • v)‖⁻¹ • cycS f (r • v))|) := by
  classical
  set D : SmoothData f := D3.toSmoothData with hDdef
  obtain ⟨Cs, hCs0, hCsv⟩ := D.sigt_split hN
  obtain ⟨CG, hCG0, hCGv⟩ := D3.exists_lead_bound hN hA
  obtain ⟨M₀, hM₀0, hM₀v⟩ := D.exists_M0_det_ne_zero hN hA
  set L : ℝ := |(Amat f).charpoly.eval 1| * D.CDelta N with hLdef
  have hL0 : 0 ≤ L := by
    have := D.CDelta_nonneg N
    rw [hLdef]; positivity
  set C₂ : ℝ := 2 * CG / c₀ + 1 with hC₂def
  have hC₂0 : 0 < C₂ := by rw [hC₂def]; positivity
  set M₁ : ℝ := max (max 1 (2 * Cs)) (max (2 * CG / c₀ + CG / C₀)
    (max (2 * M₀) (2 * L * C₂ / c₃))) with hM₁def
  have hM₁1 : 1 ≤ M₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM₁0 : 0 < M₁ := lt_of_lt_of_le one_pos hM₁1
  have hM₁Cs : 2 * Cs ≤ M₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM₁G : 2 * CG / c₀ + CG / C₀ ≤ M₁ :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hM₁M₀ : 2 * M₀ ≤ M₁ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hM₁L : 2 * L * C₂ / c₃ ≤ M₁ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  set ρ₂ : ℝ := min 1 (D.rad N) with hρ₂def
  have hρ₂0 : 0 < ρ₂ := lt_min one_pos (D.rad_pos N)
  have hρ₂1 : ρ₂ ≤ 1 := min_le_left _ _
  refine ⟨M₁, ρ₂, hM₁1, hρ₂0, hρ₂1, ?_⟩
  intro r v hr hrρ hv hthr
  set y : Fin n → ℝ := r • v with hydef
  set h : ℝ := |QtR f v| with hhdef
  have hh0 : 0 < h := lt_of_lt_of_le (by positivity) hthr
  have hr1 : r ≤ 1 := le_trans hrρ hρ₂1
  have hyn : ‖y‖ = r := by
    rw [hydef, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hv, mul_one]
  have hymem : y ∈ closedBall (0 : Fin n → ℝ) (D.rad N) := by
    rw [mem_closedBall, dist_zero_right, hyn]
    exact le_trans hrρ (min_le_right _ _)
  have hrn0 : (0:ℝ) < r ^ n := pow_pos hr n
  -- the denominator
  have hQy : |QtR f y| = r ^ n * h := by
    rw [hydef, QtR_smul, abs_mul, abs_pow, abs_of_pos hr, hhdef]
  have hsig1 : |sigt f y - QtR f y| ≤ Cs * r ^ (n + 1) := by
    have := hCsv.val y hymem
    rw [Real.norm_eq_abs, hyn] at this
    exact this
  have hCsr : Cs * r ≤ h / 2 := by
    have h1 : 2 * Cs * r ≤ M₁ * r := mul_le_mul_of_nonneg_right hM₁Cs hr.le
    linarith [hthr, h1]
  have hsiglo : r ^ n * h / 2 ≤ |sigt f y| := by
    have habs := abs_sub_abs_le_abs_sub (QtR f y) (sigt f y)
    rw [abs_sub_comm (QtR f y) (sigt f y), hQy] at habs
    have hpow : Cs * r ^ (n + 1) = (Cs * r) * r ^ n := by rw [pow_succ]; ring
    rw [hpow] at hsig1
    have hstep : (Cs * r) * r ^ n ≤ (h / 2) * r ^ n :=
      mul_le_mul_of_nonneg_right hCsr hrn0.le
    linarith [habs, hsig1, hstep]
  have hsighi : |sigt f y| ≤ 2 * (r ^ n * h) := by
    have habs : |sigt f y| ≤ |QtR f y| + |sigt f y - QtR f y| := by
      have := abs_sub_abs_le_abs_sub (sigt f y) (QtR f y)
      linarith [this]
    have hpow : Cs * r ^ (n + 1) = (Cs * r) * r ^ n := by rw [pow_succ]; ring
    rw [hpow] at hsig1
    have : (Cs * r) * r ^ n ≤ (h / 2) * r ^ n :=
      mul_le_mul_of_nonneg_right hCsr hrn0.le
    rw [hQy] at habs
    linarith [habs, hsig1, this]
  have hsigne : sigt f y ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hsiglo
    have hpos : (0:ℝ) < r ^ n * h / 2 := by
      have := mul_pos hrn0 hh0; linarith
    linarith [hsiglo, hpos]
  have hsigabs : 0 < |sigt f y| := abs_pos.mpr hsigne
  -- the numerator
  have hGA2 := hA2 v hv
  have hGlo : c₀ * h ≤ ‖Glead D3 v‖ := by rw [hhdef]; exact hGA2.1
  have hGhi : ‖Glead D3 v‖ ≤ C₀ * h := by rw [hhdef]; exact hGA2.2
  have hGpos : (0:ℝ) < ‖Glead D3 v‖ := lt_of_lt_of_le (by positivity) hGlo
  have hGne : Glead D3 v ≠ 0 := by
    intro hz; rw [hz, norm_zero] at hGpos; exact lt_irrefl _ hGpos
  set a : Fin n → ℝ := r ^ (n + 2) • Glead D3 v with hadef
  have hane : a ≠ 0 := by
    rw [hadef]
    exact smul_ne_zero (by positivity) hGne
  have han : ‖a‖ = r ^ (n + 2) * ‖Glead D3 v‖ := by
    rw [hadef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hNsub : ‖Ntil f y - a‖ ≤ CG * r ^ (n + 3) := by
    have hgy : DeltaR f y • NtwoR D3 y = a := by
      rw [hadef, hydef, ← Glead, Glead_smul]
    have := hCGv y hymem
    rw [hgy, hyn] at this
    exact this
  have hNlo : r ^ (n + 2) * (c₀ * h / 2) ≤ ‖Ntil f y‖ := by
    have hCGr : CG * r ≤ c₀ * h / 2 := by
      have h1 : (2 * CG / c₀) * r ≤ M₁ * r := by
        refine mul_le_mul_of_nonneg_right (le_trans ?_ hM₁G) hr.le
        have : (0:ℝ) ≤ CG / C₀ := by positivity
        linarith
      have h2 : (2 * CG / c₀) * r ≤ h := le_trans h1 hthr
      rw [div_mul_eq_mul_div, div_le_iff₀ hc₀] at h2
      linarith [h2]
    have hrev : ‖a‖ - ‖Ntil f y - a‖ ≤ ‖Ntil f y‖ := by
      have := norm_sub_norm_le a (Ntil f y)
      rw [norm_sub_rev] at this
      linarith [this]
    have hexp : CG * r ^ (n + 3) = (CG * r) * r ^ (n + 2) := by rw [pow_succ]; ring
    rw [hexp] at hNsub
    have hstep : (CG * r) * r ^ (n + 2) ≤ (c₀ * h / 2) * r ^ (n + 2) :=
      mul_le_mul_of_nonneg_right hCGr (by positivity)
    have hlow : r ^ (n + 2) * (c₀ * h) ≤ ‖a‖ := by
      rw [han]
      exact mul_le_mul_of_nonneg_left hGlo (by positivity)
    nlinarith [hrev, hNsub, hstep, hlow]
  have hNhi : ‖Ntil f y‖ ≤ r ^ (n + 2) * (2 * C₀ * h) := by
    have hCGr : CG * r ≤ C₀ * h := by
      have h1 : (CG / C₀) * r ≤ M₁ * r := by
        refine mul_le_mul_of_nonneg_right (le_trans ?_ hM₁G) hr.le
        have : (0:ℝ) ≤ 2 * CG / c₀ := by positivity
        linarith
      have h2 : (CG / C₀) * r ≤ h := le_trans h1 hthr
      rw [div_mul_eq_mul_div, div_le_iff₀ hC₀] at h2
      linarith [h2]
    have hexp : CG * r ^ (n + 3) = (CG * r) * r ^ (n + 2) := by rw [pow_succ]; ring
    rw [hexp] at hNsub
    have hstep : (CG * r) * r ^ (n + 2) ≤ (C₀ * h) * r ^ (n + 2) :=
      mul_le_mul_of_nonneg_right hCGr (by positivity)
    have hupper : ‖a‖ ≤ r ^ (n + 2) * (C₀ * h) := by
      rw [han]
      exact mul_le_mul_of_nonneg_left hGhi (by positivity)
    have htri : ‖Ntil f y‖ ≤ ‖a‖ + ‖Ntil f y - a‖ := by
      have := norm_add_le a (Ntil f y - a)
      simpa using this
    nlinarith [htri, hNsub, hstep, hupper]
  -- the cycle map
  have hScalc : ‖cycS f y‖ = ‖Ntil f y‖ / |sigt f y| := by
    rw [cycS, norm_smul, norm_inv, Real.norm_eq_abs]
    ring
  have hSlo : c₀ / 4 * r ^ 2 ≤ ‖cycS f y‖ := by
    rw [hScalc, le_div_iff₀ hsigabs]
    have hstep : c₀ / 4 * r ^ 2 * |sigt f y| ≤ c₀ / 4 * r ^ 2 * (2 * (r ^ n * h)) :=
      mul_le_mul_of_nonneg_left hsighi (by positivity)
    refine le_trans hstep (le_trans (le_of_eq ?_) hNlo)
    rw [pow_add]; ring
  have hShi : ‖cycS f y‖ ≤ 4 * C₀ * r ^ 2 := by
    rw [hScalc, div_le_iff₀ hsigabs]
    refine le_trans hNhi (le_trans (le_of_eq ?_)
      (mul_le_mul_of_nonneg_left hsiglo (by positivity : (0:ℝ) ≤ 4 * C₀ * r ^ 2)))
    rw [pow_add]; ring
  have hSne : cycS f y ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hSlo
    have hpos : (0:ℝ) < c₀ / 4 * r ^ 2 := by
      have := pow_pos hr 2; positivity
    linarith [hSlo, hpos]
  -- (d)
  have hdet : cct f n y ≠ 0 := by
    refine hM₀v y (by rw [hyn]; exact hr) (by rw [hyn]; exact le_trans hrρ (min_le_right _ _)) ?_
    rw [hyn]
    have hstep : M₀ * r ^ (n + 1) ≤ (M₁ / 2) * r ^ (n + 1) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith [hM₁M₀]
    refine le_trans hstep (le_trans ?_ hsiglo)
    have hexp : r ^ (n + 1) = r ^ n * r := by rw [pow_succ]
    rw [hexp]
    nlinarith [mul_le_mul_of_nonneg_right hthr hrn0.le, hrn0]
  refine ⟨hsigne, hdet, hSlo, hShi, ?_⟩
  -- (c)
  intro hthr2
  set w : Fin n → ℝ := ‖Ntil f y‖⁻¹ • Ntil f y with hwdef
  set wh : Fin n → ℝ := ‖Glead D3 v‖⁻¹ • Glead D3 v with hwhdef
  have hNne : Ntil f y ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hNlo
    have hpos : (0:ℝ) < r ^ (n + 2) * (c₀ * h / 2) :=
      mul_pos (pow_pos hr _) (by linarith [mul_pos hc₀ hh0])
    linarith [hNlo, hpos]
  have hNpos : (0:ℝ) < ‖Ntil f y‖ := norm_pos_iff.mpr hNne
  -- the direction of the cycle is `±w`
  have hdir : ‖cycS f y‖⁻¹ • cycS f y = (|sigt f y| / sigt f y) • w := by
    rw [hScalc, cycS, hwdef, smul_smul, smul_smul]
    congr 1
    field_simp
  have hsg : |sigt f y| / sigt f y = 1 ∨ |sigt f y| / sigt f y = -1 := by
    rcases lt_or_gt_of_ne hsigne with hneg | hpos
    · right; rw [abs_of_neg hneg]; field_simp
    · left; rw [abs_of_pos hpos]; field_simp
  have habs_sgn : |(|sigt f y| / sigt f y) ^ n| = 1 := by
    rcases hsg with hh | hh <;> rw [hh] <;> simp [abs_pow]
  have hQdir : |QtR f (‖cycS f y‖⁻¹ • cycS f y)| = |QtR f w| := by
    rw [hdir, QtR_smul, abs_mul, habs_sgn, one_mul]
  rw [hQdir]
  -- `w` is close to `ŵ(v)`
  have hnormw : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hnormwh : ‖wh‖ = 1 := by
    rw [hwhdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hawh : ‖a‖⁻¹ • a = wh := by
    rw [hadef, hwhdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < r ^ (n+2)),
      smul_smul, mul_inv]
    congr 1
    field_simp
  have hclose : ‖w - wh‖ ≤ C₂ * r / h := by
    have hbound := norm_normalize_sub_le hane hNne
    rw [hawh] at hbound
    refine le_trans hbound ?_
    rw [han]
    have hden : (0:ℝ) < r ^ (n + 2) * ‖Glead D3 v‖ := by positivity
    rw [div_le_div_iff₀ hden (by positivity : (0:ℝ) < h)]
    have hC₂ge : 2 * CG / c₀ ≤ C₂ := by rw [hC₂def]; linarith
    have hC₂c₀ : 2 * CG ≤ C₂ * c₀ := by
      rw [div_le_iff₀ hc₀] at hC₂ge; linarith [hC₂ge]
    have hp2 : (0:ℝ) < r ^ (n + 2) := by positivity
    calc 2 * ‖Ntil f y - a‖ * h
        ≤ 2 * (CG * r ^ (n + 3)) * h := by
          have := mul_le_mul_of_nonneg_left hNsub (by norm_num : (0:ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_right this hh0.le
      _ = (2 * CG) * (r * (r ^ (n + 2) * h)) := by rw [pow_succ, pow_succ]; ring
      _ ≤ (C₂ * c₀) * (r * (r ^ (n + 2) * h)) :=
          mul_le_mul_of_nonneg_right hC₂c₀ (by positivity)
      _ = C₂ * r * (r ^ (n + 2) * (c₀ * h)) := by ring
      _ ≤ C₂ * r * (r ^ (n + 2) * ‖Glead D3 v‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hGlo hp2.le
  -- Hypothesis A3 and the Lipschitz bound
  have hQv : QtR f v ≠ 0 := by
    intro hz
    rw [hhdef, hz, abs_zero] at hh0
    exact lt_irrefl _ hh0
  have hA3v := hA3 v hv hQv
  rw [← hhdef, ← hwhdef] at hA3v
  have hlip := QtR_lipschitz D N (le_of_eq hnormw) (le_of_eq hnormwh)
  rw [← hLdef] at hlip
  have hkey : |QtR f wh| - L * ‖w - wh‖ ≤ |QtR f w| := by
    have := abs_sub_abs_le_abs_sub (QtR f wh) (QtR f w)
    have hswap : |QtR f wh - QtR f w| = |QtR f w - QtR f wh| := abs_sub_comm _ _
    rw [hswap] at this
    linarith [this, hlip]
  -- the threshold absorbs the Lipschitz term
  have hrh : L * C₂ * (r / h) ≤ c₃ / 2 * h ^ β := by
    have hβ1 : (0:ℝ) < β + 1 := by linarith
    have hrle : r ≤ (h / M₁) ^ (β + 1) := by
      have h1 : r ^ ((β + 1)⁻¹) ≤ h / M₁ := by
        rw [le_div_iff₀ hM₁0, mul_comm]; exact hthr2
      have h2 : (r ^ ((β + 1)⁻¹)) ^ (β + 1) ≤ (h / M₁) ^ (β + 1) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hr.le _) h1 hβ1.le
      rwa [← Real.rpow_mul hr.le, inv_mul_cancel₀ hβ1.ne', Real.rpow_one] at h2
    have hdivpow : (h / M₁) ^ (β + 1) = h ^ (β + 1) / M₁ ^ (β + 1) :=
      Real.div_rpow hh0.le hM₁0.le _
    have hM₁β : M₁ ≤ M₁ ^ (β + 1) := by
      have := Real.rpow_le_rpow_of_exponent_le hM₁1 (by linarith : (1:ℝ) ≤ β + 1)
      rwa [Real.rpow_one] at this
    have hhβ : h ^ (β + 1) / h = h ^ β := by
      rw [Real.rpow_add hh0, Real.rpow_one]
      field_simp
    have hrh1 : r / h ≤ h ^ β / M₁ ^ (β + 1) := by
      rw [div_le_div_iff₀ hh0 (Real.rpow_pos_of_pos hM₁0 _)]
      rw [hdivpow] at hrle
      have hMp : (0:ℝ) < M₁ ^ (β + 1) := Real.rpow_pos_of_pos hM₁0 _
      have : r * M₁ ^ (β + 1) ≤ h ^ (β + 1) := by
        rw [le_div_iff₀ hMp] at hrle; linarith [hrle]
      calc r * M₁ ^ (β + 1) ≤ h ^ (β + 1) := this
        _ = h ^ β * h := by rw [← hhβ]; field_simp
    have hLC : 0 ≤ L * C₂ := mul_nonneg hL0 hC₂0.le
    have hstep : L * C₂ * (r / h) ≤ L * C₂ * (h ^ β / M₁ ^ (β + 1)) :=
      mul_le_mul_of_nonneg_left hrh1 hLC
    refine le_trans hstep ?_
    have hMp : (0:ℝ) < M₁ ^ (β + 1) := Real.rpow_pos_of_pos hM₁0 _
    have hML : 2 * L * C₂ ≤ c₃ * M₁ ^ (β + 1) := by
      have h1 : 2 * L * C₂ / c₃ ≤ M₁ ^ (β + 1) := le_trans hM₁L hM₁β
      rw [div_le_iff₀ hc₃] at h1
      linarith [h1]
    have hhβ0 : (0:ℝ) ≤ h ^ β := Real.rpow_nonneg hh0.le β
    rw [mul_div_assoc', div_le_iff₀ hMp]
    nlinarith [mul_le_mul_of_nonneg_right hML hhβ0, hhβ0, hMp]
  have hfin : L * ‖w - wh‖ ≤ c₃ / 2 * h ^ β := by
    refine le_trans (mul_le_mul_of_nonneg_left hclose hL0) ?_
    have : L * (C₂ * r / h) = L * C₂ * (r / h) := by ring
    rw [this]; exact hrh
  linarith [hkey, hA3v, hfin]

end Per

end SmoothData3

end MPE
