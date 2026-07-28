import Mathlib
import Formal.GramCA
import Formal.Seven

/-!
# Theorem 4.7 at the general window

The upper layers — the cycle analysis (`Formal/Cycle.lean`), the schedule induction
(`Formal/Gen.lean`) and the series summation (`Formal/Seven.lean`) — are stated for an
abstract `CycleData` and an abstract degree `dQ`.  So once the general-window construction
supplies a `CycleData` of order `d = 2k` (`Formal/Gram.lean`) and the anticoncentration
hypothesis is discharged at that degree (`Formal/GramCA.lean`), Theorem 4.7 follows by
instantiation, with failure probability `C δ^{(2-θ)/(2k)}` — the paper's
`C δ^{(2-θ)/d}` with `d = deg Q̃ = 2k`.

No spectral hypothesis is used beyond `I - A` invertible: in particular `A` may be
derogatory, and the window is then `k = deg m_A < n`.
-/

namespace MPE

open MeasureTheory Metric Set

/-- `m_A(1) ≠ 0` whenever `I - A` is invertible: otherwise `X - 1` divides `m_A`, and
cancelling the invertible factor `A - I` leaves a smaller annihilating polynomial. -/
theorem minpoly_eval_one_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit (A - 1)) : (minpoly ℝ A).eval 1 ≠ 0 := by
  intro h
  obtain ⟨s, hs⟩ := Polynomial.dvd_iff_isRoot.mpr (show (minpoly ℝ A).IsRoot 1 from h)
  have hmp0 : minpoly ℝ A ≠ 0 := minpoly.ne_zero (Matrix.isIntegral _)
  have hs0 : s ≠ 0 := fun h0 => hmp0 (by rw [hs, h0, mul_zero])
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℝ, B * (A - 1) = 1 :=
    ⟨↑hA.unit⁻¹, by have h := hA.unit.inv_mul; rwa [hA.unit_spec] at h⟩
  have haev : (A - 1) * (Polynomial.aeval A) s = 0 := by
    have h2 : (Polynomial.aeval A) (minpoly ℝ A) = 0 := minpoly.aeval ℝ A
    rw [hs, map_mul] at h2
    simpa only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_one] using h2
  have hsz : (Polynomial.aeval A) s = 0 := by
    have h3 := congrArg (fun N => B * N) haev
    simpa only [← Matrix.mul_assoc, hB, Matrix.one_mul, Matrix.mul_zero] using h3
  have h1 := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℝ A hsz) hs0
  have h2 : (minpoly ℝ A).natDegree = 1 + s.natDegree := by
    rw [hs, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero 1) hs0,
      Polynomial.natDegree_X_sub_C]
  omega
open scoped ENNReal

namespace SmoothData

section GramSeven

variable {M kk : ℕ} {f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ)} (D : SmoothData f)

/-! ### Measurability -/

lemma measurable_cctG (hf : Measurable f) (j : ℕ) : Measurable (cctG (kk := kk) f j) := by
  classical
  have hu : ∀ (i : ℕ) (l : Fin (M + 2)), Measurable (fun y => uu f i y l) :=
    fun i l => measurable_uu hf i l
  have hU : ∀ (l : Fin (M + 2)) (i : Fin (kk + 1)),
      Measurable (fun y => UevalG (kk := kk) f y l i) := fun l i => hu (i : ℕ) l
  have hGam : ∀ i l : Fin (kk + 1),
      Measurable (fun y => GamG (kk := kk) f y i l) := by
    intro i l
    have : (fun y => GamG (kk := kk) f y i l)
        = fun y => ∑ p : Fin (M + 2),
            UevalG (kk := kk) f y p i * UevalG (kk := kk) f y p l := by
      funext y; exact GamG_apply y i l
    rw [this]
    exact Finset.measurable_sum _ fun p _ => (hU p i).mul (hU p l)
  have hb : ∀ i : Fin (kk + 1), Measurable (fun y => bG (kk := kk) f y i) := by
    intro i
    have : (fun y => bG (kk := kk) f y i)
        = fun y => -∑ p : Fin (M + 2),
            UevalG (kk := kk) f y p i * uu f (kk + 1) y p := by
      funext y; exact bG_apply y i
    rw [this]
    exact (Finset.measurable_sum _ fun p _ => (hU p i).mul (hu (kk + 1) p)).neg
  by_cases hj : j < kk + 1
  · have hfun : cctG (kk := kk) f j
        = fun y => Matrix.det (fun i l => GcolF (kk := kk) f ⟨j, hj⟩ i l y) := by
      funext y; rw [GcolF_det, cctG, dif_pos hj]
    rw [hfun]
    refine measurable_det_of_entries fun i l => ?_
    rw [GcolF]
    by_cases h : l = (⟨j, hj⟩ : Fin (kk + 1))
    · rw [if_pos h]; exact hb i
    · rw [if_neg h]; exact hGam i l
  · have hfun : cctG (kk := kk) f j = fun y => Matrix.det (fun i l => GamG (kk := kk) f y i l) := by
      funext y; rw [cctG, dif_neg hj]
    rw [hfun]
    exact measurable_det_of_entries fun i l => hGam i l

lemma measurable_sigtG (hf : Measurable f) : Measurable (sigtG (kk := kk) f) :=
  Finset.measurable_sum _ fun j _ => measurable_cctG hf j

lemma measurable_NtilG (hf : Measurable f) : Measurable (NtilG (kk := kk) f) := by
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_cctG hf j).smul (hf.iterate j)

/-! ### The `CycleData` of the general window -/

/-- **The general-window `CycleData`**, of order `d = 2k`.  Its `hN` field is Lemma 4.1(iii),
`van_NtilG`. -/
theorem nonempty_cycleDataG (hkn : kk + 1 ≤ M + 2)
    (cz : ℕ → ℝ) (hann : ∑ i ∈ Finset.range (kk + 2), cz i • ((Amat f) ^ i) = 0)
    (htop : cz (kk + 1) = 1) :
    ∃ C : CycleData (Fin (M + 2) → ℝ),
      C.d = 2 * (kk + 1) ∧ C.Ntil = NtilG (kk := kk) f ∧ C.sigt = sigtG (kk := kk) f
        ∧ C.ρ₁ = D.rad (kk + 2) := by
  obtain ⟨Cn, hCn0, hCnv⟩ := D.van_NtilG (N := kk + 2) (le_refl _) hkn cz hann htop
  refine ⟨{ d := 2 * (kk + 1)
            Ntil := NtilG (kk := kk) f
            sigt := sigtG (kk := kk) f
            M := max Cn 1
            ρ₁ := D.rad (kk + 2)
            hd := by omega
            hM := le_max_right _ _
            hρ₁ := D.rad_pos _
            hN := ?_ }, rfl, rfl, rfl, rfl⟩
  intro y hy
  have hmem : y ∈ closedBall (0 : Fin (M + 2) → ℝ) (D.rad (kk + 2)) := by
    rw [mem_closedBall, dist_zero_right]; exact hy
  have h := hCnv.val y hmem
  have hpow : kk * 2 + 3 + 1 = 2 * (kk + 1) + 2 := by ring
  rw [hpow] at h
  exact le_trans h (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-! ### Theorem 4.7, general window -/

include D in
open Real in
/-- **Theorem 4.7 at the general window.**  `C²` smoothness, `I - A` invertible, window
`k = deg m_A` (carried as a monic annihilating polynomial `cz` of degree `k`), and the
degeneracy form `Δ = det(KᵀK)` not identically zero — which is the paper's Lemma 4.2(i),
automatic at that window.  No nonderogatory hypothesis. -/
theorem theorem47_gram (hkn : kk + 1 ≤ M + 2) (hA : IsUnit (Amat f - 1))
    (cz : ℕ → ℝ) (hann : ∑ i ∈ Finset.range (kk + 2), cz i • ((Amat f) ^ i) = 0)
    (htop : cz (kk + 1) = 1) (hlc : (∑ i ∈ Finset.range (kk + 2), cz i) ≠ 0)
    (hnd : ∃ v : Fin (M + 2) → ℝ, gramDelta (k := kk + 1) (Amat f) v ≠ 0)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ (C : CycleData (Fin (M + 2) → ℝ)) (Cst : ℝ),
      C.Ntil = NtilG (kk := kk) f ∧ C.sigt = sigtG (kk := kk) f ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ C.ρ₁ →
        (∀ i, hSched C.M δ θ i ≤ 1) →
        ((δ ^ ((2 - θ) / ((2 * (kk + 1) : ℕ) : ℝ))) ^ (θ - 1) ≤ 1 / 2) →
        ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
          (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
              {ω | ∃ i, ¬ ‖xProcG C x₀ (sched δ θ) i ω‖ ≤ sched δ θ i
                    ∨ C.sigt (yProcG C x₀ (sched δ θ) i ω) = 0}
            ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / ((2 * (kk + 1) : ℕ) : ℝ))) := by
  classical
  obtain ⟨C, hCd, hCN, hCs, hCρ⟩ := D.nonempty_cycleDataG hkn cz hann htop
  obtain ⟨cR, hcR0, hcRv⟩ := D.sigtG_split (N := kk + 2) (le_refl _) hkn cz hann htop
  -- measurability
  have hSmeas : Measurable C.S := by
    have h1 : C.S = fun y => (sigtG (kk := kk) f y)⁻¹ • NtilG (kk := kk) f y := by
      funext y
      show (C.sigt y)⁻¹ • C.Ntil y = _
      rw [hCs, hCN]
    rw [h1]
    exact ((measurable_sigtG D.hmeas).inv).smul (measurable_NtilG D.hmeas)
  have hτmeas : Measurable C.τ := by
    have h1 : C.τ = fun y => |sigtG (kk := kk) f y| / ‖y‖ ^ C.d := by
      funext y; show |C.sigt y| / ‖y‖ ^ C.d = _; rw [hCs]
    rw [h1]
    exact ((measurable_sigtG D.hmeas).abs).div (measurable_norm.pow_const _)
  -- the splitting, in the shape `hCA_gram` consumes
  have hsplit : ∀ y : Fin (M + 2) → ℝ, ‖y‖ ≤ D.rad (kk + 2) →
      |C.sigt y - (∑ i ∈ Finset.range (kk + 2), cz i)
          * gramDelta (k := kk + 1) (Amat f) y|
        ≤ cR * ‖y‖ ^ (2 * (kk + 1) + 1) := by
    intro y hy
    have hmem : y ∈ closedBall (0 : Fin (M + 2) → ℝ) (D.rad (kk + 2)) := by
      rw [mem_closedBall, dist_zero_right]; exact hy
    have h := hcRv.val y hmem
    rw [Real.norm_eq_abs] at h
    rw [hCs]
    have hpow : kk * 2 + 2 + 1 = 2 * (kk + 1) + 1 := by ring
    rwa [hpow] at h
  obtain ⟨Am, hAm0, hAmv⟩ := hCA_gram (kk := kk) (f := f) hCd hlc hcR0 hsplit hnd
  obtain ⟨Cst, hCst0, hmain⟩ := theorem47 C hSmeas hτmeas
    (dQ := 2 * (kk + 1)) (by omega) hAm0 hAmv hθ1 hθ2
  exact ⟨C, Cst, hCN, hCs, hCst0, fun δ hδ hδ1 h2δ hs1 hratio x₀ hx₀ =>
    hmain δ hδ hδ1 (hCρ ▸ h2δ) h2δ hs1 hratio x₀ hx₀⟩

/-! ### Theorem 4.7 as the paper states it -/

include D in
open Real in
/-- **Theorem 4.7.**  `f` is `C²` with `f 0 = 0`, `I - A` is invertible where `A = Df(0)`, and
the window is the paper's: `k = deg m_A`.  That is the whole hypothesis list — in particular
`A` need not be nonderogatory, and when it is derogatory `k < n`.

The monic annihilating polynomial, the nonvanishing `m_A(1) ≠ 0`, and the paper's
Lemma 4.2(i) (`Δ ≢ 0`) are all *derived* here from `hk` and `hA`. -/
theorem theorem47_general (hkn : kk + 1 ≤ M + 2) (hA : IsUnit (Amat f - 1))
    (hk : kk + 1 = (minpoly ℝ (Amat f)).natDegree)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ (C : CycleData (Fin (M + 2) → ℝ)) (Cst : ℝ),
      C.Ntil = NtilG (kk := kk) f ∧ C.sigt = sigtG (kk := kk) f ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ C.ρ₁ →
        (∀ i, hSched C.M δ θ i ≤ 1) →
        ((δ ^ ((2 - θ) / ((2 * (kk + 1) : ℕ) : ℝ))) ^ (θ - 1) ≤ 1 / 2) →
        ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
          (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
              {ω | ∃ i, ¬ ‖xProcG C x₀ (sched δ θ) i ω‖ ≤ sched δ θ i
                    ∨ C.sigt (yProcG C x₀ (sched δ θ) i ω) = 0}
            ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / ((2 * (kk + 1) : ℕ) : ℝ))) := by
  classical
  set mp : Polynomial ℝ := minpoly ℝ (Amat f) with hmpdef
  have hdeg : mp.natDegree < kk + 2 := by omega
  -- the coefficients of `m_A` are a monic annihilating polynomial of degree `k`
  set cz : ℕ → ℝ := fun i => mp.coeff i with hczdef
  have hann : ∑ i ∈ Finset.range (kk + 2), cz i • ((Amat f) ^ i) = 0 := by
    have h := minpoly.aeval ℝ (Amat f)
    rwa [← hmpdef, Polynomial.aeval_eq_sum_range' hdeg] at h
  have htop : cz (kk + 1) = 1 := by
    rw [hczdef, hk]
    exact (minpoly.monic (Matrix.isIntegral _)).coeff_natDegree
  -- `m_A(1) ≠ 0`, from `I - A` invertible
  have hlc : (∑ i ∈ Finset.range (kk + 2), cz i) ≠ 0 := by
    have h := Polynomial.eval_eq_sum_range' (p := mp) (x := (1 : ℝ)) hdeg
    simp only [one_pow, mul_one] at h
    rw [hczdef, ← h]
    exact minpoly_eval_one_ne_zero hA
  -- Lemma 4.2(i): the degeneracy form is not identically zero at this window
  have hnd : ∃ v : Fin (M + 2) → ℝ, gramDelta (k := kk + 1) (Amat f) v ≠ 0 :=
    exists_gramDelta_ne (m := M + 1) hA hk
  exact D.theorem47_gram hkn hA cz hann htop hlc hnd hθ1 hθ2

end GramSeven

end SmoothData

end MPE
