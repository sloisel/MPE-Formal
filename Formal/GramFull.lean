import Mathlib
import Formal.GramSeven
import Formal.SevenFull

/-!
# Theorem 4.7 at the general window, with every object given by a defining equation

`GramSeven.theorem47_general` is the theorem; this file is the bridge to the self-contained
form in `Formal/Statement.lean`, mirroring `SevenFull.mpe_dithered_C2_stmt`.  `U`, `Γ`, `b`,
`c̃`, `σ̃`, `Ñ` are supplied as data satisfying their paper definitions, the dithered process
by its two recursions, and all the smallness conditions are collapsed into `δ ≤ δ_*`.

The window is `k = deg m_A`, so `A` may be derogatory; `k ≤ n` is derived from
`m_A ∣ χ_A` rather than assumed.
-/

namespace MPE

open MeasureTheory Metric Set Matrix
open scoped ENNReal

namespace Smooth

variable {M kk : ℕ}

/-- `deg m_A ≤ n`, since `m_A ∣ χ_A`. -/
theorem natDegree_minpoly_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (minpoly ℝ A).natDegree ≤ n := by
  have hdvd : minpoly ℝ A ∣ A.charpoly := Matrix.minpoly_dvd_charpoly A
  have hne : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  have := Polynomial.natDegree_le_of_dvd hdvd hne
  rwa [A.charpoly_natDegree_eq_dim, Fintype.card_fin] at this

/-- **Theorem 4.7 at the general window, fully unfolded.** -/
theorem mpe_dithered_gram_stmt
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 2 f (Metric.ball 0 R))
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1))
    (hk : kk + 1 = (minpoly ℝ A).natDegree)
    (U : (Fin (M + 2) → ℝ) → Matrix (Fin (M + 2)) (Fin (kk + 1)) ℝ)
    (hU : ∀ y i j, U y i j = f^[(j : ℕ) + 1] y i - f^[(j : ℕ)] y i)
    (Gm : (Fin (M + 2) → ℝ) → Matrix (Fin (kk + 1)) (Fin (kk + 1)) ℝ)
    (hGm : ∀ y, Gm y = (U y)ᵀ * U y)
    (b : (Fin (M + 2) → ℝ) → Fin (kk + 1) → ℝ)
    (hb : ∀ y j, b y j
      = -∑ l : Fin (M + 2), U y l j * (f^[kk + 2] y l - f^[kk + 1] y l))
    (c : ℕ → (Fin (M + 2) → ℝ) → ℝ)
    (hcCramer : ∀ (j : Fin (kk + 1)) y, c (j : ℕ) y = (Gm y).cramer (b y) j)
    (hcDet : ∀ y, c (kk + 1) y = (Gm y).det)
    (sg : (Fin (M + 2) → ℝ) → ℝ) (Nt : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hsg : ∀ y, sg y = ∑ j ∈ Finset.range (kk + 2), c j y)
    (hNt : ∀ y, Nt y = ∑ j ∈ Finset.range (kk + 2), c j y • f^[j] y)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ dstar Cst : ℝ, 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
      ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
        (∀ ω, x 0 ω = x₀) →
        (∀ m ω, x (m + 1) ω
          = (sg (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i))))⁻¹
            • Nt (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i)))) →
        (Measure.infinitePi fun _ : ℕ =>
            Measure.pi fun _ : Fin (M + 2) =>
              ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
            {ω | ∃ m, δ ^ (θ ^ m) < ‖x m ω‖
                  ∨ sg (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i))) = 0}
          ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / (2 * (kk : ℝ) + 2))) := by
  classical
  obtain ⟨D⟩ := nonempty_smoothData hR hf0 hmeas hf
  have hAeq : A = Amat f := by rw [hAdef, Amat]
  subst hAeq
  have hkn : kk + 1 ≤ M + 2 := by
    have := natDegree_minpoly_le (Amat f); omega
  -- the supplied data are the definitions
  have hUeq : ∀ y, U y = UevalG (kk := kk) f y := by
    intro y; funext i j; rw [hU y i j]; rfl
  have hGmeq : ∀ y, Gm y = GamG (kk := kk) f y := by
    intro y; rw [hGm y, hUeq y]; rfl
  have hbeq : ∀ y, b y = bG (kk := kk) f y := by
    intro y; funext j; rw [hb y j, SmoothData.bG_apply, hUeq y]; rfl
  have hceq : ∀ j ∈ Finset.range (kk + 2), ∀ y, c j y = cctG (kk := kk) f j y := by
    intro j hj y
    rw [Finset.mem_range] at hj
    rcases Nat.lt_or_ge j (kk + 1) with hlt | hge
    · rw [cctG, dif_pos hlt, hcCramer ⟨j, hlt⟩ y, hGmeq y, hbeq y]
    · have hjeq : j = kk + 1 := by omega
      subst hjeq
      rw [hcDet y, cctG, dif_neg (by omega), hGmeq y]
  have hsgeq : ∀ y, sg y = sigtG (kk := kk) f y := by
    intro y; rw [hsg y, sigtG]
    exact Finset.sum_congr rfl fun j hj => hceq j hj y
  have hNteq : ∀ y, Nt y = NtilG (kk := kk) f y := by
    intro y; rw [hNt y, NtilG]
    exact Finset.sum_congr rfl fun j hj => by rw [hceq j hj y]
  obtain ⟨C, Cst, hNtC, hsigC, hCst0, hmain⟩ := D.theorem47_general hkn hA hk hθ1 hθ2
  -- the exponent, in the two shapes
  have hcast : (((2 * (kk + 1) : ℕ)) : ℝ) = 2 * (kk : ℝ) + 2 := by push_cast; ring
  set p : ℝ := (2 - θ) / (2 * (kk : ℝ) + 2) with hpdef
  have hp0 : 0 < p := by
    rw [hpdef]
    have : (0:ℝ) < 2 - θ := by linarith
    positivity
  -- collapse the smallness conditions
  have hM0 : (0:ℝ) < 4 * C.M := by have := C.hM; linarith
  have h2θ : (0:ℝ) < 2 - θ := by linarith
  obtain ⟨d₁, hd₁0, hd₁1, hd₁⟩ := exists_rpow_thresh h2θ (by positivity : (0:ℝ) < 1 / (4 * C.M))
  have hpθ : 0 < p * (θ - 1) := by
    have : (0:ℝ) < θ - 1 := by linarith
    positivity
  obtain ⟨d₂, hd₂0, hd₂1, hd₂⟩ := exists_rpow_thresh hpθ (by norm_num : (0:ℝ) < 1 / 2)
  set dstar : ℝ := min (min 1 (C.ρ₁ / 2)) (min d₁ d₂) with hdstar
  have hdstar0 : 0 < dstar := lt_min (lt_min one_pos (by linarith [C.hρ₁])) (lt_min hd₁0 hd₂0)
  refine ⟨dstar, Cst, hdstar0, hCst0, ?_⟩
  intro δ hδ hδd x₀ hx₀ x hx0 hxs
  have hδ1 : δ ≤ 1 := le_trans hδd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδρ : 2 * δ ≤ C.ρ₁ := by
    have := le_trans hδd (le_trans (min_le_left _ _) (min_le_right _ _))
    linarith [this]
  have hδd₁ : δ ≤ d₁ := le_trans hδd (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδd₂ : δ ≤ d₂ := le_trans hδd (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsch : ∀ m, hSched C.M δ θ m ≤ 1 := by
    intro m
    have hsk : sched δ θ m ≤ δ := sched_le hδ hδ1 hθ1.le m
    have hsk0 : 0 < sched δ θ m := sched_pos hδ θ m
    have hmono : (sched δ θ m) ^ (2 - θ) ≤ δ ^ (2 - θ) :=
      Real.rpow_le_rpow hsk0.le hsk h2θ.le
    have hbd : δ ^ (2 - θ) ≤ 1 / (4 * C.M) := hd₁ δ hδ hδd₁
    rw [hSched]
    calc 4 * C.M * (sched δ θ m) ^ (2 - θ) ≤ 4 * C.M * δ ^ (2 - θ) :=
          mul_le_mul_of_nonneg_left hmono hM0.le
      _ ≤ 4 * C.M * (1 / (4 * C.M)) := mul_le_mul_of_nonneg_left hbd hM0.le
      _ = 1 := by
          have hne : (C.M : ℝ) ≠ 0 := by have := C.hM; linarith
          field_simp
  have hratio : (δ ^ p) ^ (θ - 1) ≤ 1 / 2 := by
    rw [← Real.rpow_mul hδ.le]
    exact hd₂ δ hδ hδd₂
  have hxeq : ∀ m ω, x m ω = xProcG C x₀ (sched δ θ) m ω := by
    intro m
    induction m with
    | zero => intro ω; rw [hx0 ω]; rfl
    | succ m ih =>
        intro ω
        rw [hxs m ω, xProcG_succ, yProcG, ih ω, hsgeq, hNteq]
        show _ = (C.sigt _)⁻¹ • C.Ntil _
        rw [hsigC, hNtC]
        rfl
  have hyeq : ∀ m (ω : ℕ → Fin (M + 2) → ℝ),
      sg (xProcG C x₀ (sched δ θ) m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i)))
        = C.sigt (yProcG C x₀ (sched δ θ) m ω) := by
    intro m ω
    rw [hsgeq, hsigC]
    rfl
  have hset : {ω : ℕ → Fin (M + 2) → ℝ | ∃ m, δ ^ (θ ^ m) < ‖x m ω‖
        ∨ sg (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i))) = 0}
      = {ω | ∃ m, ¬ ‖xProcG C x₀ (sched δ θ) m ω‖ ≤ sched δ θ m
        ∨ C.sigt (yProcG C x₀ (sched δ θ) m ω) = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, sched, not_le, hxeq, hyeq]
  rw [hset]
  have := hmain δ hδ hδ1 hδρ hsch (by rw [hcast]; exact hratio) x₀ hx₀
  rwa [hcast] at this

end Smooth

end MPE
