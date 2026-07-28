import Mathlib
import Formal.KrylovSub
import Formal.Anticonc
import Formal.Psi

/-!
# The anticoncentration bound of Theorem 4.7, in probability form

`Sublevel.sublevel_krylov` is a statement about Lebesgue measure on a box.  Here it is
transported to the dither: `b` uniform on the cube, `y = x + δ' b`.  The two Jacobians —
`δ'^{-(M+2)}` from the affine pullback and `δ'^{M+1}` from the box in the sublevel bound —
leave exactly one power of `δ'` in the denominator, which is what makes the final bound
`A (s' + δ')^{1/d}` scale-free.  This is the paper's Lemma 4.6.
-/

namespace MPE

open MeasureTheory Matrix Set
open scoped ENNReal

variable {M : ℕ}

/-- **The anticoncentration bound for `Δ_A = det K_A`, in probability form.** -/
theorem krylov_prob {A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
    {v : Fin (M + 2) → ℝ} (hv0 : v 0 = 1) (hv : (krylov A v).det ≠ 0) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ δ' ε : ℝ, 0 < δ' → 0 ≤ ε →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | |(krylov A (x + δ' • clamp b)).det| ≤ ε}
          ≤ ENNReal.ofReal (Cst * ε ^ (((M : ℝ) + 2)⁻¹) / δ') := by
  classical
  set c : ℝ := (krylov A v).det with hcdef
  have hc0 : 0 < |c| := abs_pos.mpr hv
  set p : ℝ := ((M : ℝ) + 2)⁻¹ with hpdef
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hcp : (0:ℝ) < |c| ^ p := Real.rpow_pos_of_pos hc0 p
  set Cst : ℝ :=
    4 ^ (M + 1) * (1 + ‖v‖) ^ (M + 1) * (4 * ((M : ℝ) + 2)) / |c| ^ p with hCdef
  have hCst0 : 0 < Cst := by
    rw [hCdef]
    have hvn : (0:ℝ) ≤ 1 + ‖v‖ := by positivity
    positivity
  refine ⟨Cst, hCst0, ?_⟩
  intro δ' ε hδ' hε x hx
  set S : Set (Fin (M + 2) → ℝ) :=
    {b | |(krylov A (x + δ' • clamp b)).det| ≤ ε} with hSdef
  set T : Set (Fin (M + 2) → ℝ) :=
    {y | |(krylov A y).det| ≤ ε ∧ ∀ i, |y i| ≤ 2 * δ'} with hTdef
  -- the cube maps into the box of half-width `2δ'`
  have hsub : S ∩ cube (M + 2) ⊆ (fun b => x + δ' • b) ⁻¹' T := by
    rintro b ⟨hb, hbc⟩
    have hbn : ‖b‖ ≤ 1 := by rwa [← closedBall_eq_cube] at hbc
    have hcl : clamp b = b := clamp_eq_self hbn
    have hb' : |(krylov A (x + δ' • b)).det| ≤ ε := by
      have := hb
      rw [hSdef, Set.mem_setOf_eq, hcl] at this
      exact this
    refine ⟨hb', fun i => ?_⟩
    have h1 : |x i| ≤ δ' :=
      le_trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i) hx
    have h2 : |b i| ≤ 1 :=
      le_trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm b i) hbn
    calc |(x + δ' • b) i| = |x i + δ' * b i| := by simp
      _ ≤ |x i| + |δ' * b i| := abs_add_le _ _
      _ ≤ δ' + δ' * 1 := by
          refine add_le_add h1 ?_
          rw [abs_mul, abs_of_pos hδ']
          exact mul_le_mul_of_nonneg_left h2 hδ'.le
      _ = 2 * δ' := by ring
  -- the sublevel bound on that box
  have hvolT := sublevel_krylov (n := M + 1) (A := A) hv0 hv
    (K := 2 * δ') (ε := ε) (by linarith) hε
  have hcast : ((M + 1 : ℕ) : ℝ) + 1 = (M : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hvolT
  -- the affine pullback
  have hpre : volume ((fun b => x + δ' • b) ⁻¹' T)
      = ENNReal.ofReal (δ'⁻¹ ^ (M + 2)) * volume T := volume_preimage_affine hδ' x T
  -- undo the normalisation of `blockMeasure`
  have hcube : volume (S ∩ cube (M + 2)) = ENNReal.ofReal ((2:ℝ) ^ (M + 2)) *
      blockMeasure (M + 2) S := by
    have h1 := volume_restrict_cube (M + 2)
    have h2 : (volume : Measure (Fin (M + 2) → ℝ)).restrict (cube (M + 2)) S
        = volume (S ∩ cube (M + 2)) := by
      rw [Measure.restrict_apply']
      exact measurableSet_cube _
    rw [← h2, h1, Measure.smul_apply, smul_eq_mul]
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2:ℝ) ^ (M + 2)) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num))
  -- the arithmetic: the two Jacobians leave one power of `δ'`
  have hδne : δ' ≠ 0 := ne_of_gt hδ'
  have hcpne : |c| ^ p ≠ 0 := ne_of_gt hcp
  have hjac : δ'⁻¹ ^ (M + 2) * δ' ^ (M + 1) = δ'⁻¹ := by
    have hsplit : δ' ^ (M + 2) = δ' ^ (M + 1) * δ' := by ring
    rw [inv_pow, hsplit]
    field_simp
  have harith : δ'⁻¹ ^ (M + 2) *
      ((2 * (2 * δ' * (1 + ‖v‖))) ^ (M + 1) *
        (4 * ((M : ℝ) + 2) * (ε / |c|) ^ p)) = Cst * ε ^ p / δ' := by
    calc δ'⁻¹ ^ (M + 2) *
          ((2 * (2 * δ' * (1 + ‖v‖))) ^ (M + 1) *
            (4 * ((M : ℝ) + 2) * (ε / |c|) ^ p))
        = (δ'⁻¹ ^ (M + 2) * δ' ^ (M + 1)) *
            (4 ^ (M + 1) * (1 + ‖v‖) ^ (M + 1) * (4 * ((M : ℝ) + 2)) *
              (ε ^ p / |c| ^ p)) := by
          rw [Real.div_rpow hε (abs_nonneg c),
            show (2 : ℝ) * (2 * δ' * (1 + ‖v‖)) = 4 * δ' * (1 + ‖v‖) by ring,
            mul_pow, mul_pow]
          ring
      _ = Cst * ε ^ p / δ' := by rw [hjac, hCdef]; field_simp
  calc blockMeasure (M + 2) S
      ≤ ENNReal.ofReal ((2:ℝ) ^ (M + 2)) * blockMeasure (M + 2) S :=
        le_mul_of_one_le_left zero_le hone
    _ = volume (S ∩ cube (M + 2)) := hcube.symm
    _ ≤ volume ((fun b => x + δ' • b) ⁻¹' T) := measure_mono hsub
    _ = ENNReal.ofReal (δ'⁻¹ ^ (M + 2)) * volume T := hpre
    _ ≤ ENNReal.ofReal (δ'⁻¹ ^ (M + 2)) *
          (ENNReal.ofReal ((2 * (2 * δ' * (1 + ‖v‖))) ^ (M + 1)) *
            ENNReal.ofReal (4 * ((M : ℝ) + 2) * (ε / |c|) ^ p)) := by
        exact mul_le_mul_right hvolT _

    _ = ENNReal.ofReal (Cst * ε ^ p / δ') := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          harith]

end MPE
