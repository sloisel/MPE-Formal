import Mathlib
import Formal.Cubic
import Formal.KrylovSub
import Formal.Anticonc

/-!
# The excluded set

The whole probabilistic content of Theorem 5.5.  The starting point is drawn once, and the
orbit is deterministic, so the failure event sits inside a *single* set of starting points:

    E t = {x : |Q̃(x)| ≤ t ‖x‖ⁿ},

the directions too close to the degeneracy set.

Two observations do all the work, and together they replace the paper's Lemma 5.4 (angular
measure of a sublevel set on the sphere, proved there by Brudnyi–Ganzburg):

* **Scale invariance.**  `Q̃` is homogeneous of degree `n`, so `E t` is a cone: the
  preimage of `E t` under `b ↦ ρ • b` is `E t` itself.  The radius `ρ` therefore disappears
  *before any measure theory happens* — no polar decomposition, no surface measure.
* **Containment.**  On the unit cube `‖x‖ ≤ 1`, so `E t` meets it inside a plain sublevel
  set of `det K_A`, which is exactly `Sublevel.sublevel_krylov` at half-width `1`.
-/

namespace MPE

open MeasureTheory Metric Set Matrix
open scoped ENNReal

section Excluded

variable {m : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}

local notation "n" => m + 1

/-- **The excluded set.**  Written with the factor `‖x‖ⁿ` rather than through directions, so
that it is a cone containing `0` and no normalisation is needed. -/
def excl (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (t : ℝ) : Set (Fin n → ℝ) :=
  {x | |QtR f x| ≤ t * ‖x‖ ^ n}

/-- **Scale invariance.**  `E t` is a cone, so dilating the starting ball does not move it. -/
lemma preimage_smul_excl {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (fun b : Fin n → ℝ => r • b) ⁻¹' (excl f t) = excl f t := by
  ext b
  simp only [Set.mem_preimage, excl, Set.mem_setOf_eq, QtR_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, mul_pow, abs_mul, abs_pow, abs_of_pos hr]
  constructor
  · intro h
    have hrn : (0:ℝ) < r ^ n := pow_pos hr n
    nlinarith [h, hrn]
  · intro h
    have hrn : (0:ℝ) < r ^ n := pow_pos hr n
    nlinarith [h, hrn]

/-- **Ob measure.**  The excluded set has measure `O(t^{1/n})` under the uniform measure on
the cube — with no dependence on the radius, by `preimage_smul_excl`. -/
theorem blockMeasure_excl_le (hA : IsUnit (Amat f - 1))
    (hnd : ∃ v : Fin n → ℝ, (krylov (Amat f) v).det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      blockMeasure n (excl f t) ≤ ENNReal.ofReal (C * t ^ (((m : ℝ) + 1)⁻¹)) := by
  classical
  obtain ⟨v, hv0, hv⟩ := exists_good_dir hnd
  -- the two nonzero scalars relating `Q̃` to `det K_A`
  have hdet : IsUnit (Amat f - 1).det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hAI : (Amat f - 1).det ≠ 0 := isUnit_iff_ne_zero.mp hdet
  have hp1 : (Amat f).charpoly.eval 1 ≠ 0 := Poly.charpoly_eval_one_ne_zero hA
  set g : ℝ := |(Amat f).charpoly.eval 1| * |(Amat f - 1).det| with hgdef
  have hg0 : 0 < g := by rw [hgdef]; exact mul_pos (abs_pos.mpr hp1) (abs_pos.mpr hAI)
  set p : ℝ := ((m : ℝ) + 1)⁻¹ with hpdef
  have hp0 : 0 < p := by rw [hpdef]; positivity
  set cv : ℝ := |(krylov (Amat f) v).det| with hcvdef
  have hcv0 : 0 < cv := abs_pos.mpr hv
  set C : ℝ := (2 * (1 + ‖v‖)) ^ m * (4 * ((m : ℝ) + 1)) / (g * cv) ^ p + 1 with hCdef
  have hgcv : (0:ℝ) < (g * cv) ^ p := Real.rpow_pos_of_pos (mul_pos hg0 hcv0) p
  have hC0 : 0 < C := by
    have hvn : (0:ℝ) ≤ 1 + ‖v‖ := by positivity
    rw [hCdef]; positivity
  refine ⟨C, hC0, ?_⟩
  intro t ht
  -- on the cube the excluded set is a sublevel set of `det K_A`
  set T : Set (Fin n → ℝ) :=
    {y | |(krylov (Amat f) y).det| ≤ t / g ∧ ∀ i, |y i| ≤ 1} with hTdef
  have hsub : excl f t ∩ cube n ⊆ T := by
    rintro x ⟨hx, hxc⟩
    have hxn : ‖x‖ ≤ 1 := by rwa [← closedBall_eq_cube] at hxc
    have hpow : ‖x‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg x) hxn
    have hQ : |QtR f x| ≤ t := by
      refine le_trans hx ?_
      nlinarith [ht, hpow]
    have hfac : |QtR f x| = g * |(krylov (Amat f) x).det| := by
      rw [QtR, DeltaR_eq, hgdef, abs_mul, abs_mul]
      ring
    refine ⟨?_, fun i => ?_⟩
    · rw [le_div_iff₀ hg0, mul_comm]
      rw [hfac] at hQ
      linarith [hQ]
    · have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      linarith [this, hxn]
  -- `sublevel_krylov` at half-width `1`
  have hvol := sublevel_krylov (A := Amat f) hv0 hv
    (K := 1) (ε := t / g) (by norm_num) (by positivity)
  -- undo the normalisation of `blockMeasure`
  have hcube : volume (excl f t ∩ cube n) = ENNReal.ofReal ((2:ℝ) ^ n) *
      blockMeasure n (excl f t) := by
    have h1 := volume_restrict_cube n
    have h2 : (volume : Measure (Fin n → ℝ)).restrict (cube n) (excl f t)
        = volume (excl f t ∩ cube n) := by
      rw [Measure.restrict_apply']
      exact measurableSet_cube _
    rw [← h2, h1, Measure.smul_apply, smul_eq_mul]
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2:ℝ) ^ n) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num))
  -- the arithmetic
  have harith : (2 * (1 * (1 + ‖v‖))) ^ m * (4 * ((m : ℝ) + 1) * (t / g / cv) ^ p)
      ≤ C * t ^ p := by
    have hdiv : (t / g / cv) ^ p = t ^ p / (g * cv) ^ p := by
      rw [show t / g / cv = t / (g * cv) by field_simp]
      exact Real.div_rpow ht (mul_pos hg0 hcv0).le p
    rw [hdiv, hCdef]
    have htp : (0:ℝ) ≤ t ^ p := Real.rpow_nonneg ht p
    have hkey : (2 * (1 * (1 + ‖v‖))) ^ m * (4 * ((m : ℝ) + 1) * (t ^ p / (g * cv) ^ p))
        = ((2 * (1 + ‖v‖)) ^ m * (4 * ((m : ℝ) + 1)) / (g * cv) ^ p) * t ^ p := by
      rw [one_mul]; field_simp
    rw [hkey]
    nlinarith [htp, hC0]
  calc blockMeasure n (excl f t)
      ≤ ENNReal.ofReal ((2:ℝ) ^ n) * blockMeasure n (excl f t) :=
        le_mul_of_one_le_left zero_le hone
    _ = volume (excl f t ∩ cube n) := hcube.symm
    _ ≤ volume T := measure_mono hsub
    _ ≤ ENNReal.ofReal ((2 * (1 * (1 + ‖v‖))) ^ m) *
          ENNReal.ofReal (4 * ((m : ℝ) + 1) * (t / g / cv) ^ p) := hvol
    _ = ENNReal.ofReal ((2 * (1 * (1 + ‖v‖))) ^ m *
          (4 * ((m : ℝ) + 1) * (t / g / cv) ^ p)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (C * t ^ p) := ENNReal.ofReal_le_ofReal harith

end Excluded

end MPE
