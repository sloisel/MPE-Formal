import Mathlib
import Formal.SevenAnti
import Formal.Instantiate
import Formal.Psi

/-!
# Discharging the anticoncentration hypothesis of Theorem 4.7

Two steps.

*Ob off* (`margin_to_krylov_gen`) is the paper's Lemma 4.1(ii): the margin event
`τ(z) < s` forces the *leading form* to be small.  All it uses is a splitting
`σ̃ = lc·Δ_A + R` with `|R(y)| ≤ cR‖y‖^{n+1}` — so it applies verbatim to the polynomial
construction (via `Anticonc.eval_sigtPoly` and `LowDeg.abs_eval_le`) and to the smooth one
(via `CThree.sigt_split`, whose `Van` conclusion is exactly this bound).

*Assembly* (`hCA_gen`) feeds that into `SevenAnti.krylov_prob`.  The powers of `δ'` cancel
exactly: `ε ≍ (s' + δ')·δ'^n`, so `ε^{1/n}/δ' ≍ (s' + δ')^{1/n}`, which is the scale-free
shape `hPsiGen_of` consumes.
-/

namespace MPE

open MeasureTheory Matrix Poly
open scoped ENNReal

variable {M : ℕ}

private lemma abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc |a - b| = |a + -b| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by rw [abs_neg]

lemma krylov_zero {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : krylov A 0 = 0 := by
  ext i j
  simp [krylov_apply]

/-! ### Ob off: the margin controls the leading form -/

/-- **Ob off.**  On the margin event the leading form `Δ_A` is small.  This is the paper's
Lemma 4.1(ii), with the remainder absorbed into the `‖z‖` correction. -/
theorem margin_to_krylov_gen {C : CycleData (Fin (M + 2) → ℝ)} (hd : C.d = M + 2)
    {Amt : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ} {lc cR ρ₀ : ℝ} (_hcR : 0 ≤ cR)
    (hsplit : ∀ y : Fin (M + 2) → ℝ, ‖y‖ ≤ ρ₀ →
      |C.sigt y - lc * (krylov Amt y).det| ≤ cR * ‖y‖ ^ (M + 3))
    {z : Fin (M + 2) → ℝ} (hz : ‖z‖ ≤ ρ₀) {s' : ℝ} (_hs' : 0 ≤ s')
    (hτ : C.τ z < s') :
    |lc| * |(krylov Amt z).det| ≤ (s' + cR * ‖z‖) * ‖z‖ ^ (M + 2) := by
  rcases eq_or_lt_of_le (norm_nonneg z) with hz0 | hz0
  · -- `z = 0`: the Krylov matrix vanishes
    have hzz : z = 0 := norm_eq_zero.mp hz0.symm
    rw [hzz, krylov_zero]
    simp
  · -- `z ≠ 0`: split `σ̃` and bound each piece
    have hsig : |C.sigt z| ≤ s' * ‖z‖ ^ (M + 2) := by
      have habs : |C.sigt z| = C.τ z * ‖z‖ ^ C.d := C.sigt_abs z hz0
      rw [hd] at habs
      have hz2 : (0:ℝ) < ‖z‖ ^ (M + 2) := pow_pos hz0 _
      rw [habs]
      nlinarith [hτ, hz2]
    have hrem : |C.sigt z - lc * (krylov Amt z).det| ≤ cR * ‖z‖ * ‖z‖ ^ (M + 2) := by
      have h := hsplit z hz
      have hpow : ‖z‖ ^ (M + 3) = ‖z‖ * ‖z‖ ^ (M + 2) := by ring
      rw [hpow] at h
      linarith [h]
    calc |lc| * |(krylov Amt z).det|
        = |lc * (krylov Amt z).det| := (abs_mul _ _).symm
      _ = |C.sigt z - (C.sigt z - lc * (krylov Amt z).det)| := by
          congr 1; ring
      _ ≤ |C.sigt z| + |C.sigt z - lc * (krylov Amt z).det| := abs_sub_le_add _ _
      _ ≤ s' * ‖z‖ ^ (M + 2) + cR * ‖z‖ * ‖z‖ ^ (M + 2) := add_le_add hsig hrem
      _ = (s' + cR * ‖z‖) * ‖z‖ ^ (M + 2) := by ring

/-! ### Assembly -/

open Real in
/-- **The anticoncentration hypothesis of Theorem 4.7, discharged.**

Beyond the splitting, the only hypothesis is that `A` is nonderogatory (`Δ_A ≢ 0`), which
is the paper's Lemma 4.2(i).  In particular there is no simple-spectrum assumption, and no
logarithm in the bound. -/
theorem hCA_gen {C : CycleData (Fin (M + 2) → ℝ)} (hd : C.d = M + 2)
    {Amt : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ} {lc cR ρ₀ : ℝ}
    (hlc : lc ≠ 0) (hcR : 0 ≤ cR)
    (hsplit : ∀ y : Fin (M + 2) → ℝ, ‖y‖ ≤ ρ₀ →
      |C.sigt y - lc * (krylov Amt y).det| ≤ cR * ‖y‖ ^ (M + 3))
    (hnd : ∃ v : Fin (M + 2) → ℝ, (krylov Amt v).det ≠ 0) :
    ∃ Am : ℝ, 0 ≤ Am ∧ ∀ δ' s' : ℝ, 0 < δ' → 2 * δ' ≤ ρ₀ → 0 < s' → s' ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | C.τ (x + δ' • clamp b) < s'}
          ≤ ENNReal.ofReal (Am * (s' + δ') ^ (((M : ℝ) + 2)⁻¹)) := by
  classical
  obtain ⟨v, hv0, hv⟩ := exists_good_dir (n := M + 1) hnd
  obtain ⟨Cst, hCst0, hCst⟩ := krylov_prob (A := Amt) hv0 hv
  set p : ℝ := ((M : ℝ) + 2)⁻¹ with hpdef
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hlca : 0 < |lc| := abs_pos.mpr hlc
  set c₁ : ℝ := max (2 * cR) 1 with hc₁def
  have hc₁0 : 0 < c₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K₀ : ℝ := c₁ * (2 ^ (M + 2) / |lc|) with hK₀def
  have hK₀0 : 0 < K₀ := by rw [hK₀def]; positivity
  refine ⟨Cst * K₀ ^ p, by positivity, ?_⟩
  intro δ' s' hδ' h2δ' hs' hs1 x hx
  set ε : ℝ := (c₁ * (s' + δ')) * (2 ^ (M + 2) * δ' ^ (M + 2)) / |lc| with hεdef
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  -- Ob off: the margin event sits inside the sublevel set of `Δ_A`
  have hsub : {b : Fin (M + 2) → ℝ | C.τ (x + δ' • clamp b) < s'}
      ⊆ {b | |(krylov Amt (x + δ' • clamp b)).det| ≤ ε} := by
    intro b hb
    set z : Fin (M + 2) → ℝ := x + δ' • clamp b with hzdef
    have hzn : ‖z‖ ≤ 2 * δ' := by
      calc ‖z‖ ≤ ‖x‖ + ‖δ' • clamp b‖ := norm_add_le _ _
        _ ≤ δ' + δ' * 1 := by
            refine add_le_add hx ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ']
            exact mul_le_mul_of_nonneg_left (norm_clamp_le b) hδ'.le
        _ = 2 * δ' := by ring
    have hz1 : ‖z‖ ≤ ρ₀ := le_trans hzn h2δ'
    have hkey := margin_to_krylov_gen hd hcR hsplit hz1 hs'.le hb
    have hstep : (s' + cR * ‖z‖) * ‖z‖ ^ (M + 2)
        ≤ (c₁ * (s' + δ')) * (2 ^ (M + 2) * δ' ^ (M + 2)) := by
      have h1 : s' + cR * ‖z‖ ≤ c₁ * (s' + δ') := by
        have hcz : cR * ‖z‖ ≤ cR * (2 * δ') := mul_le_mul_of_nonneg_left hzn hcR
        have h1' : (1:ℝ) ≤ c₁ := le_max_right _ _
        have h2' : 2 * cR ≤ c₁ := le_max_left _ _
        nlinarith [hs'.le, hδ'.le, hcR]
      have h2 : ‖z‖ ^ (M + 2) ≤ 2 ^ (M + 2) * δ' ^ (M + 2) := by
        have := pow_le_pow_left₀ (norm_nonneg z) hzn (M + 2)
        rwa [mul_pow] at this
      have hA2 : (0:ℝ) ≤ ‖z‖ ^ (M + 2) := by positivity
      have hA3 : (0:ℝ) ≤ c₁ * (s' + δ') :=
        mul_nonneg hc₁0.le (by linarith [hs'.le, hδ'.le])
      exact mul_le_mul h1 h2 hA2 hA3
    have hfin : |lc| * |(krylov Amt z).det|
        ≤ (c₁ * (s' + δ')) * (2 ^ (M + 2) * δ' ^ (M + 2)) := le_trans hkey hstep
    rw [Set.mem_setOf_eq, ← hzdef, hεdef, le_div_iff₀ hlca, mul_comm]
    exact hfin
  refine le_trans (le_trans (measure_mono hsub) (hCst δ' ε hδ' hε0 x hx)) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  -- the exponent bookkeeping: `ε^p = (K₀(s'+δ'))^p · δ'`
  have hδpow : (δ' ^ (M + 2) : ℝ) ^ p = δ' := by
    rw [← Real.rpow_natCast δ' (M + 2), ← Real.rpow_mul hδ'.le, hpdef]
    push_cast
    rw [mul_inv_cancel₀ (by positivity), Real.rpow_one]
  have hεeq : ε = (K₀ * (s' + δ')) * δ' ^ (M + 2) := by
    rw [hεdef, hK₀def]; field_simp
  have hsd : (0:ℝ) ≤ K₀ * (s' + δ') :=
    mul_nonneg hK₀0.le (by linarith [hs'.le, hδ'.le])
  have hδne : δ' ≠ 0 := ne_of_gt hδ'
  refine le_of_eq ?_
  calc Cst * ε ^ p / δ'
      = Cst * ((K₀ * (s' + δ')) ^ p * (δ' ^ (M + 2)) ^ p) / δ' := by
        rw [hεeq, Real.mul_rpow hsd (by positivity)]
    _ = Cst * (K₀ * (s' + δ')) ^ p := by
        rw [hδpow]; field_simp
    _ = Cst * K₀ ^ p * (s' + δ') ^ p := by
        rw [Real.mul_rpow hK₀0.le (by positivity)]; ring

/-! ### The polynomial construction -/

section Polynomial

variable {A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
  {q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ}

/-- The coefficient sum of the remainder: the constant in `|R(z)| ≤ cRem ‖z‖^{n+1}`. -/
noncomputable def cRem (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ) : ℝ :=
  ∑ d ∈ (sigRem A q).support, |MvPolynomial.coeff d (sigRem A q)|

lemma cRem_nonneg (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ) : 0 ≤ cRem A q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The splitting hypothesis of `hCA_gen`, for the polynomial construction. -/
lemma split_poly (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) :
    ∀ y : Fin (M + 2) → ℝ, ‖y‖ ≤ 1 →
      |(cycleData hq hA).sigt y - leadConst A * (krylov A y).det|
        ≤ cRem A q * ‖y‖ ^ (M + 3) := by
  intro y hy
  have hsplit : (cycleData hq hA).sigt y - leadConst A * (krylov A y).det
      = MvPolynomial.eval y (sigRem A q) := by
    show MvPolynomial.eval y (sigtPoly A q) - leadConst A * (krylov A y).det = _
    rw [eval_sigtPoly]; ring
  rw [hsplit]
  exact (lowDeg_sigRem hq).abs_eval_le y hy

/-- **The anticoncentration hypothesis of Theorem 4.7, for the polynomial construction.** -/
theorem hCA_seven (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1))
    (hnd : ∃ v : Fin (M + 2) → ℝ, (krylov A v).det ≠ 0) :
    ∃ Am : ℝ, 0 ≤ Am ∧ ∀ δ' s' : ℝ, 0 < δ' → 2 * δ' ≤ 1 → 0 < s' → s' ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | (cycleData hq hA).τ (x + δ' • clamp b) < s'}
          ≤ ENNReal.ofReal (Am * (s' + δ') ^ (((M : ℝ) + 2)⁻¹)) :=
  hCA_gen rfl (leadConst_ne_zero hA) (cRem_nonneg A q) (split_poly hq hA) hnd

end Polynomial

end MPE
