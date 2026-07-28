import Mathlib
import Formal.SevenCA
import Formal.GramAnti
import Formal.Gram

/-!
# The anticoncentration hypothesis, at any window

`Formal/SevenCA.lean` discharges `hCA` for the full window, where the degeneracy form is
`det K_A` of degree `n`.  The argument there never uses anything about that form beyond
its degree and the probability bound it satisfies, so this file states it once, over an
abstract degree `dd` and an abstract form `Dl`, and then instantiates it at the general
window with `Dl = det(KᵀK)` and `dd = 2k`.

The exponent bookkeeping is the reason one statement covers both: the probability bound
always has the shape `Cst · ε^{1/dd} / δ'`, and `ε ≍ (s'+δ')·δ'^{dd}`, so the `δ'` cancels
whatever `dd` is.
-/

namespace MPE

open MeasureTheory Metric Set Real
open scoped ENNReal

variable {M : ℕ}

private lemma abs_sub_le_add' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases b with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rcases abs_cases (a - b) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith

/-- **From the margin event to a sublevel set of the leading form.**  Abstract in the
degree: if `σ̃ = lc·Dl + O(r^{dd+1})` and the margin drops below `s'`, then `Dl` is small. -/
theorem margin_to_form {C : CycleData (Fin (M + 2) → ℝ)} {dd : ℕ} (hd : C.d = dd)
    {Dl : (Fin (M + 2) → ℝ) → ℝ} (hDl0 : Dl 0 = 0)
    {lc cR ρ₀ : ℝ} (hcR : 0 ≤ cR)
    (hsplit : ∀ y : Fin (M + 2) → ℝ, ‖y‖ ≤ ρ₀ →
      |C.sigt y - lc * Dl y| ≤ cR * ‖y‖ ^ (dd + 1))
    {z : Fin (M + 2) → ℝ} (hz : ‖z‖ ≤ ρ₀) {s' : ℝ} (hs' : 0 ≤ s')
    (hτ : C.τ z < s') :
    |lc| * |Dl z| ≤ (s' + cR * ‖z‖) * ‖z‖ ^ dd := by
  rcases eq_or_lt_of_le (norm_nonneg z) with hz0 | hz0
  · have hzz : z = 0 := norm_eq_zero.mp hz0.symm
    rw [hzz, hDl0]
    simp only [abs_zero, mul_zero, norm_zero, add_zero]
    exact mul_nonneg hs' (pow_nonneg le_rfl dd)
  · have hsig : |C.sigt z| ≤ s' * ‖z‖ ^ dd := by
      have habs : |C.sigt z| = C.τ z * ‖z‖ ^ C.d := C.sigt_abs z hz0
      rw [hd] at habs
      have hz2 : (0:ℝ) < ‖z‖ ^ dd := pow_pos hz0 _
      rw [habs]
      nlinarith [hτ, hz2]
    have hrem : |C.sigt z - lc * Dl z| ≤ cR * ‖z‖ * ‖z‖ ^ dd := by
      have h := hsplit z hz
      have hpow : ‖z‖ ^ (dd + 1) = ‖z‖ * ‖z‖ ^ dd := by ring
      rw [hpow] at h
      linarith [h]
    calc |lc| * |Dl z|
        = |lc * Dl z| := (abs_mul _ _).symm
      _ = |C.sigt z - (C.sigt z - lc * Dl z)| := by congr 1; ring
      _ ≤ |C.sigt z| + |C.sigt z - lc * Dl z| := abs_sub_le_add' _ _
      _ ≤ s' * ‖z‖ ^ dd + cR * ‖z‖ * ‖z‖ ^ dd := add_le_add hsig hrem
      _ = (s' + cR * ‖z‖) * ‖z‖ ^ dd := by ring

/-- **The anticoncentration hypothesis, discharged at any window.**  The only inputs are the
splitting `σ̃ = lc·Dl + O(r^{dd+1})` and a probability bound of the shape
`Cst·ε^{1/dd}/δ'` for the sublevel sets of `Dl`. -/
theorem hCA_of_prob {C : CycleData (Fin (M + 2) → ℝ)} {dd : ℕ} (hdd : 0 < dd)
    (hd : C.d = dd) {Dl : (Fin (M + 2) → ℝ) → ℝ} (hDl0 : Dl 0 = 0)
    {lc cR ρ₀ : ℝ} (hlc : lc ≠ 0) (hcR : 0 ≤ cR)
    (hsplit : ∀ y : Fin (M + 2) → ℝ, ‖y‖ ≤ ρ₀ →
      |C.sigt y - lc * Dl y| ≤ cR * ‖y‖ ^ (dd + 1))
    {Cst : ℝ} (hCst0 : 0 < Cst)
    (hprob : ∀ δ' ε : ℝ, 0 < δ' → 0 ≤ ε → ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
      blockMeasure (M + 2) {b | |Dl (x + δ' • clamp b)| ≤ ε}
        ≤ ENNReal.ofReal (Cst * ε ^ ((dd : ℝ)⁻¹) / δ')) :
    ∃ Am : ℝ, 0 ≤ Am ∧ ∀ δ' s' : ℝ, 0 < δ' → 2 * δ' ≤ ρ₀ → 0 < s' → s' ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | C.τ (x + δ' • clamp b) < s'}
          ≤ ENNReal.ofReal (Am * (s' + δ') ^ ((dd : ℝ)⁻¹)) := by
  classical
  set p : ℝ := ((dd : ℝ))⁻¹ with hpdef
  have hddR : (0:ℝ) < (dd : ℝ) := by exact_mod_cast hdd
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hlca : 0 < |lc| := abs_pos.mpr hlc
  set c₁ : ℝ := max (2 * cR) 1 with hc₁def
  have hc₁0 : 0 < c₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set K₀ : ℝ := c₁ * (2 ^ dd / |lc|) with hK₀def
  have hK₀0 : 0 < K₀ := by rw [hK₀def]; positivity
  refine ⟨Cst * K₀ ^ p, by positivity, ?_⟩
  intro δ' s' hδ' h2δ' hs' hs1 x hx
  set ε : ℝ := (c₁ * (s' + δ')) * (2 ^ dd * δ' ^ dd) / |lc| with hεdef
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have hsub : {b : Fin (M + 2) → ℝ | C.τ (x + δ' • clamp b) < s'}
      ⊆ {b | |Dl (x + δ' • clamp b)| ≤ ε} := by
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
    have hkey := margin_to_form hd hDl0 hcR hsplit hz1 hs'.le hb
    have hstep : (s' + cR * ‖z‖) * ‖z‖ ^ dd
        ≤ (c₁ * (s' + δ')) * (2 ^ dd * δ' ^ dd) := by
      have h1 : s' + cR * ‖z‖ ≤ c₁ * (s' + δ') := by
        have hcz : cR * ‖z‖ ≤ cR * (2 * δ') := mul_le_mul_of_nonneg_left hzn hcR
        have h1' : (1:ℝ) ≤ c₁ := le_max_right _ _
        have h2' : 2 * cR ≤ c₁ := le_max_left _ _
        nlinarith [hs'.le, hδ'.le, hcR]
      have h2 : ‖z‖ ^ dd ≤ 2 ^ dd * δ' ^ dd := by
        have := pow_le_pow_left₀ (norm_nonneg z) hzn dd
        rwa [mul_pow] at this
      have hA2 : (0:ℝ) ≤ ‖z‖ ^ dd := by positivity
      have hA3 : (0:ℝ) ≤ c₁ * (s' + δ') :=
        mul_nonneg hc₁0.le (by linarith [hs'.le, hδ'.le])
      exact mul_le_mul h1 h2 hA2 hA3
    have hfin : |lc| * |Dl z| ≤ (c₁ * (s' + δ')) * (2 ^ dd * δ' ^ dd) := le_trans hkey hstep
    rw [Set.mem_setOf_eq, ← hzdef, hεdef, le_div_iff₀ hlca, mul_comm]
    exact hfin
  refine le_trans (le_trans (measure_mono hsub) (hprob δ' ε hδ' hε0 x hx)) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hδpow : (δ' ^ dd : ℝ) ^ p = δ' := by
    rw [← Real.rpow_natCast δ' dd, ← Real.rpow_mul hδ'.le, hpdef]
    rw [mul_inv_cancel₀ (ne_of_gt hddR), Real.rpow_one]
  have hεeq : ε = (K₀ * (s' + δ')) * δ' ^ dd := by
    rw [hεdef, hK₀def]; field_simp
  have hsd : (0:ℝ) ≤ K₀ * (s' + δ') :=
    mul_nonneg hK₀0.le (by linarith [hs'.le, hδ'.le])
  have hδne : δ' ≠ 0 := ne_of_gt hδ'
  refine le_of_eq ?_
  calc Cst * ε ^ p / δ'
      = Cst * ((K₀ * (s' + δ')) ^ p * (δ' ^ dd) ^ p) / δ' := by
        rw [hεeq, Real.mul_rpow hsd (by positivity)]
    _ = Cst * (K₀ * (s' + δ')) ^ p := by rw [hδpow]; field_simp
    _ = Cst * K₀ ^ p * (s' + δ') ^ p := by
        rw [Real.mul_rpow hK₀0.le (by positivity)]; ring

/-! ### The general window -/

section GramInst

variable {kk : ℕ} {f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ)}

lemma gramDelta_zero (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ) :
    gramDelta (k := kk + 1) A 0 = 0 := by
  have hz : gkry (k := kk + 1) A (0 : Fin (M + 2) → ℝ) = 0 := by
    ext i j; simp [gkry]
  rw [gramDelta, hz]
  simp

/-- **The anticoncentration hypothesis at the general window.** -/
theorem hCA_gram {C : CycleData (Fin (M + 2) → ℝ)}
    (hd : C.d = 2 * (kk + 1))
    {lc cR ρ₀ : ℝ} (hlc : lc ≠ 0) (hcR : 0 ≤ cR)
    (hsplit : ∀ y : Fin (M + 2) → ℝ, ‖y‖ ≤ ρ₀ →
      |C.sigt y - lc * gramDelta (k := kk + 1) (Amat f) y| ≤ cR * ‖y‖ ^ (2 * (kk + 1) + 1))
    (hnd : ∃ v : Fin (M + 2) → ℝ, gramDelta (k := kk + 1) (Amat f) v ≠ 0) :
    ∃ Am : ℝ, 0 ≤ Am ∧ ∀ δ' s' : ℝ, 0 < δ' → 2 * δ' ≤ ρ₀ → 0 < s' → s' ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | C.τ (x + δ' • clamp b) < s'}
          ≤ ENNReal.ofReal (Am * (s' + δ') ^ (((2 * (kk + 1) : ℕ) : ℝ)⁻¹)) := by
  obtain ⟨v, hv0, hv⟩ := exists_good_dir_gram (m := M + 1) hnd
  obtain ⟨Cst, hCst0, hCst⟩ := gram_prob (A := Amat f) (Nat.succ_pos kk) hv0 hv
  exact hCA_of_prob (by omega) hd (gramDelta_zero _) hlc hcR hsplit hCst0 hCst

end GramInst

end MPE
