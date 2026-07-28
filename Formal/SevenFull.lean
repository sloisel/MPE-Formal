import Mathlib
import Formal.Seven
import Formal.SevenCA
import Formal.CThree

/-!
# Theorem 4.7, with no anticoncentration hypothesis

`Seven.theorem47` carried the paper's Lemma 4.6 as a named hypothesis `hCA`.
`SevenCA.hCA_seven` proves it, so here it is discharged: the only hypotheses left are the
paper's own — `f` polynomial of the standing form (`hq`), `I - A` invertible (`hA`), `A`
nonderogatory (`hnd`, the paper's Lemma 4.2(i)), and `θ ∈ (1,2)`.
-/

namespace MPE

open MeasureTheory Matrix Poly
open scoped ENNReal

variable {M : ℕ} {A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
  {q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ}

/-- **Theorem 4.7.**  Dithered restarts with the schedule `δ_m = δ^(θ^m)`: from *every*
starting point with `‖x₀‖ ≤ δ`, with probability at least `1 - C δ^((2-θ)/d)` over the
dither, every cycle is defined and `‖x_m‖ ≤ δ_m` for all `m`.

No spectral hypothesis beyond `I - A` invertible and `A` nonderogatory; in particular no
simple spectrum, and no logarithms in the bound. -/
theorem theorem47_poly (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1))
    (hnd : ∃ v : Fin (M + 2) → ℝ, (krylov A v).det ≠ 0)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ Cst : ℝ, 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ 1 →
        (∀ m, hSched (cycleData hq hA).M δ θ m ≤ 1) →
        ((δ ^ ((2 - θ) / ((M : ℝ) + 2))) ^ (θ - 1) ≤ 1 / 2) →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
            {ω | ∃ m, ¬ ‖xProcG (cycleData hq hA) x₀ (sched δ θ) m ω‖ ≤ sched δ θ m}
          ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / ((M : ℝ) + 2))) := by
  classical
  obtain ⟨Am, hAm0, hAm⟩ := hCA_seven hq hA hnd
  have hcast : (((M + 2 : ℕ) : ℝ))⁻¹ = ((M : ℝ) + 2)⁻¹ := by push_cast; ring_nf
  have hcast2 : ((M + 2 : ℕ) : ℝ) = (M : ℝ) + 2 := by push_cast; ring
  -- the hypothesis of `theorem47`, in its exact shape
  have hCA' : ∀ δ' s' : ℝ, 0 < δ' → 2 * δ' ≤ 1 → 0 < s' → s' ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | (cycleData hq hA).τ (x + δ' • clamp b) < s'}
          ≤ ENNReal.ofReal (Am * (s' + δ') ^ (((M + 2 : ℕ) : ℝ)⁻¹)) := by
    intro δ' s' hδ' h2δ' hs' hs1 x hx
    rw [hcast]
    exact hAm δ' s' hδ' h2δ' hs' hs1 x hx
  obtain ⟨Cst, hCst0, hmain⟩ := theorem47 (cycleData hq hA)
    (measurable_cycleData_S hq hA) (measurable_cycleData_tau hq hA)
    (dQ := M + 2) (Nat.succ_pos _) hAm0 hCA' hθ1 hθ2
  refine ⟨Cst, hCst0, ?_⟩
  intro δ hδ hδ1 h2δ hs1 hratio x₀ hx₀
  have hrw : (2 - θ) / ((M + 2 : ℕ) : ℝ) = (2 - θ) / ((M : ℝ) + 2) := by rw [hcast2]
  have := hmain δ hδ hδ1 h2δ h2δ hs1 (by rw [hrw]; exact hratio) x₀ hx₀
  rwa [hrw] at this

/-! ### The smooth case

`CThree.lean`'s `SmoothData` is a `C²` structure — differentiability, `‖Df‖ ≤ L`, and
`‖Df z - Df 0‖ ≤ K‖z‖` — and `nonempty_smoothData` builds one from `ContDiffOn ℝ 2`.  Its
`sigt_split` supplies the splitting `σ̃ = p_A(1)·Δ + R` with `|R| = O(‖y‖^{n+1})`, which is
exactly the hypothesis of `hCA_gen`.  So the smooth case runs through the same discharge as
the polynomial one, with no extra work beyond translating `Δ` into `det K_A`. -/

/-- `δ^a ≤ c` holds for all small `δ`, when `a, c > 0`.  The collapse of the smallness
conditions of Theorem 4.7 into a single `δ ≤ δ_*`. -/
lemma exists_rpow_thresh {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d → δ ^ a ≤ c := by
  have hcp : (0:ℝ) < c ^ a⁻¹ := Real.rpow_pos_of_pos hc _
  refine ⟨min 1 (c ^ a⁻¹), lt_min one_pos hcp, min_le_left _ _, ?_⟩
  intro δ hδ hδd
  calc δ ^ a ≤ (min 1 (c ^ a⁻¹)) ^ a := Real.rpow_le_rpow hδ.le hδd ha.le
    _ ≤ (c ^ a⁻¹) ^ a :=
        Real.rpow_le_rpow (le_of_lt (lt_min one_pos hcp)) (min_le_right _ _) ha.le
    _ = c := by rw [← Real.rpow_mul hc.le, inv_mul_cancel₀ ha.ne', Real.rpow_one]

section Smooth

open Metric

variable {f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ)}

/-- **Theorem 4.7 for a `C²` iteration.**  From every starting point with `‖x₀‖ ≤ δ`, with
probability at least `1 - Cst·δ^((2-θ)/d)` over the dither, every cycle is defined and
`‖x_m‖ ≤ δ^(θ^m)` for all `m`.

The hypotheses are the paper's: `f` is `C²` near its fixed point (packaged as `SmoothData`,
which `nonempty_smoothData` produces from `ContDiffOn ℝ 2`), `I - A` is invertible, and `A`
is nonderogatory.  No simple spectrum, and no logarithms. -/
theorem theorem47_C2 (D : SmoothData f) (hA : IsUnit (Amat f - 1))
    (hnd : ∃ v : Fin (M + 2) → ℝ, (krylov (Amat f) v).det ≠ 0)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ (C : CycleData (Fin (M + 2) → ℝ)) (Cst : ℝ),
      C.Ntil = Ntil f ∧ C.sigt = sigt f ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ C.ρ₁ →
        (∀ k, hSched C.M δ θ k ≤ 1) →
        ((δ ^ ((2 - θ) / ((M : ℝ) + 2))) ^ (θ - 1) ≤ 1 / 2) →
        ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
          (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
              {ω | ∃ k, ¬ ‖xProcG C x₀ (sched δ θ) k ω‖ ≤ sched δ θ k}
            ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / ((M : ℝ) + 2))) := by
  classical
  obtain ⟨C, hd, hNt, hsigC, hρ₁, -⟩ :=
    D.nonempty_cycleData_sharpBound (N := M + 3) (le_refl _) hA
  obtain ⟨cRm, hcRm0, hcRmv⟩ := D.sigt_split (N := M + 3) (le_refl _)
  -- measurability of the cycle map and the margin
  have hSmeas : Measurable C.S := by
    have h1 : C.S = fun y => (sigt f y)⁻¹ • Ntil f y := by
      funext y
      show (C.sigt y)⁻¹ • C.Ntil y = _
      rw [hsigC, hNt]
    rw [h1]
    exact ((measurable_sigt D.hmeas).inv).smul (measurable_Ntil D.hmeas)
  have hτmeas : Measurable C.τ := by
    have h1 : C.τ = fun y => |sigt f y| / ‖y‖ ^ C.d := by
      funext y
      show |C.sigt y| / ‖y‖ ^ C.d = _
      rw [hsigC]
    rw [h1]
    exact ((measurable_sigt D.hmeas).abs).div (measurable_norm.pow_const _)
  -- the splitting, in the shape `hCA_gen` consumes
  have hsplit : ∀ y : Fin (M + 2) → ℝ, ‖y‖ ≤ C.ρ₁ →
      |C.sigt y - Poly.leadConst (Amat f) * (krylov (Amat f) y).det|
        ≤ cRm * ‖y‖ ^ (M + 3) := by
    intro y hy
    have hmem : y ∈ closedBall (0 : Fin (M + 2) → ℝ) (D.rad (M + 3)) := by
      rw [mem_closedBall, dist_zero_right, ← hρ₁]; exact hy
    have h := hcRmv.val y hmem
    have heq : C.sigt y - Poly.leadConst (Amat f) * (krylov (Amat f) y).det
        = sigt f y - (Amat f).charpoly.eval 1 * DeltaR f y := by
      rw [hsigC, DeltaR_eq, Poly.leadConst]; ring
    rw [heq, ← Real.norm_eq_abs]
    exact h
  obtain ⟨Am, hAm0, hAm⟩ :=
    hCA_gen hd (Poly.leadConst_ne_zero hA) hcRm0 hsplit hnd
  have hcast : (((M + 2 : ℕ) : ℝ))⁻¹ = ((M : ℝ) + 2)⁻¹ := by push_cast; ring_nf
  have hcast2 : ((M + 2 : ℕ) : ℝ) = (M : ℝ) + 2 := by push_cast; ring
  have hCA' : ∀ δ' s' : ℝ, 0 < δ' → 2 * δ' ≤ C.ρ₁ → 0 < s' → s' ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | C.τ (x + δ' • clamp b) < s'}
          ≤ ENNReal.ofReal (Am * (s' + δ') ^ (((M + 2 : ℕ) : ℝ)⁻¹)) := by
    intro δ' s' hδ' h2δ' hs' hs1 x hx
    rw [hcast]
    exact hAm δ' s' hδ' h2δ' hs' hs1 x hx
  obtain ⟨Cst, hCst0, hmain⟩ := theorem47 C hSmeas hτmeas
    (dQ := M + 2) (Nat.succ_pos _) hAm0 hCA' hθ1 hθ2
  refine ⟨C, Cst, hNt, hsigC, hCst0, ?_⟩
  intro δ hδ hδ1 h2δ hs1 hratio x₀ hx₀
  have hrw : (2 - θ) / ((M + 2 : ℕ) : ℝ) = (2 - θ) / ((M : ℝ) + 2) := by rw [hcast2]
  have := hmain δ hδ hδ1 h2δ h2δ hs1 (by rw [hrw]; exact hratio) x₀ hx₀
  rwa [hrw] at this

/-! ### The paper's statement

`theorem47_C2` phrased with the smoothness hypothesis as the paper writes it: `f` is `C²`
on a ball around its fixed point.  Everything else is unchanged. -/

/-- **Theorem 4.7.**  Let `f` be `C²` near the fixed point `0`, with `I - A` invertible and
`A` nonderogatory, where `A = Df(0)`.  Fix a schedule exponent `θ ∈ (1,2)`.  Then for every
small `δ` and *every* starting point with `‖x₀‖ ≤ δ` — the starting point may be chosen
adversarially, and may lie on the breakdown set — dithered restarted MPE with the schedule
`δ_m = δ^(θ^m)` satisfies, with probability at least `1 - C δ^((2-θ)/d)` over the dither:
every cycle is defined and `‖x_m‖ ≤ δ_m` for all `m`. -/
theorem mpe_dithered_C2
    -- the iteration: `C²` near its fixed point `0`, and measurable elsewhere
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 2 f (Metric.ball 0 R))
    -- the linear part `A = Df(0)`, invertible at `1` and nonderogatory
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1)) (hnd : ∃ v : Fin (M + 2) → ℝ, (krylov A v).det ≠ 0)
    -- the schedule exponent
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ (C : CycleData (Fin (M + 2) → ℝ)) (Cst : ℝ),
      C.Ntil = Ntil f ∧ C.sigt = sigt f ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ C.ρ₁ →
        (∀ k, hSched C.M δ θ k ≤ 1) →
        ((δ ^ ((2 - θ) / ((M : ℝ) + 2))) ^ (θ - 1) ≤ 1 / 2) →
        ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
          (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
              {ω | ∃ k, ¬ ‖xProcG C x₀ (sched δ θ) k ω‖ ≤ sched δ θ k}
            ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / ((M : ℝ) + 2))) := by
  obtain ⟨D⟩ := nonempty_smoothData hR hf0 hmeas hf
  subst hAdef
  exact theorem47_C2 D hA hnd hθ1 hθ2

/-- **Theorem 4.7, with every object given by a defining equation.**  The bridging lemma
behind `Formal/Statement.lean`'s self-contained statement: `U`, `c`, `σ̃`, `Ñ` are supplied
as data satisfying their paper definitions, the dithered process by its two recursions, and
all smallness conditions are collapsed into a single `δ ≤ δ_*`. -/
theorem mpe_dithered_C2_stmt
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 2 f (Metric.ball 0 R))
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
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ dstar Cst : ℝ, 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
      ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
        (∀ ω, x 0 ω = x₀) →
        (∀ k ω, x (k + 1) ω
          = (sg (x k ω + (δ ^ (θ ^ k)) • fun i => max (-1) (min 1 (ω k i))))⁻¹
            • Nt (x k ω + (δ ^ (θ ^ k)) • fun i => max (-1) (min 1 (ω k i)))) →
        (Measure.infinitePi fun _ : ℕ =>
            Measure.pi fun _ : Fin (M + 2) =>
              ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
            {ω | ∃ k, δ ^ (θ ^ k) < ‖x k ω‖}
          ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / ((M : ℝ) + 2))) := by
  classical
  obtain ⟨D⟩ := nonempty_smoothData hR hf0 hmeas hf
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
  have hnd' : ∃ v : Fin (M + 2) → ℝ, (krylov (Amat f) v).det ≠ 0 := hnd
  obtain ⟨C, Cst, hNtC, hsigC, hCst0, hmain⟩ := theorem47_C2 D hA hnd' hθ1 hθ2
  -- collapse the smallness conditions
  have hM0 : (0:ℝ) < 4 * C.M := by have := C.hM; linarith
  have h2θ : (0:ℝ) < 2 - θ := by linarith
  obtain ⟨d₁, hd₁0, hd₁1, hd₁⟩ := exists_rpow_thresh h2θ (by positivity : (0:ℝ) < 1 / (4 * C.M))
  set p : ℝ := (2 - θ) / ((M : ℝ) + 2) with hpdef
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hpθ : 0 < p * (θ - 1) := by have : (0:ℝ) < θ - 1 := by linarith
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
  -- the threshold conditions
  have hsch : ∀ k, hSched C.M δ θ k ≤ 1 := by
    intro k
    have hsk : sched δ θ k ≤ δ := sched_le hδ hδ1 hθ1.le k
    have hsk0 : 0 < sched δ θ k := sched_pos hδ θ k
    have hmono : (sched δ θ k) ^ (2 - θ) ≤ δ ^ (2 - θ) :=
      Real.rpow_le_rpow hsk0.le hsk h2θ.le
    have hbd : δ ^ (2 - θ) ≤ 1 / (4 * C.M) := hd₁ δ hδ hδd₁
    rw [hSched]
    calc 4 * C.M * (sched δ θ k) ^ (2 - θ) ≤ 4 * C.M * δ ^ (2 - θ) :=
          mul_le_mul_of_nonneg_left hmono hM0.le
      _ ≤ 4 * C.M * (1 / (4 * C.M)) := mul_le_mul_of_nonneg_left hbd hM0.le
      _ = 1 := by
          have hne : (C.M : ℝ) ≠ 0 := by have := C.hM; linarith
          field_simp
  have hratio : (δ ^ p) ^ (θ - 1) ≤ 1 / 2 := by
    rw [← Real.rpow_mul hδ.le]
    exact hd₂ δ hδ hδd₂
  -- the process agrees with `xProcG`
  have hxeq : ∀ k ω, x k ω = xProcG C x₀ (sched δ θ) k ω := by
    intro k
    induction k with
    | zero => intro ω; rw [hx0 ω]; rfl
    | succ k ih =>
        intro ω
        rw [hxs k ω, xProcG_succ, yProcG, ih ω, hsgeq, hNteq]
        show _ = (C.sigt _)⁻¹ • C.Ntil _
        rw [hsigC, hNtC]
        rfl
  have hset : {ω : ℕ → Fin (M + 2) → ℝ | ∃ k, δ ^ (θ ^ k) < ‖x k ω‖}
      = {ω | ∃ k, ¬ ‖xProcG C x₀ (sched δ θ) k ω‖ ≤ sched δ θ k} := by
    ext ω
    simp only [Set.mem_setOf_eq, sched, not_le, hxeq]
  rw [hset]
  exact hmain δ hδ hδ1 hδρ hsch hratio x₀ hx₀

end Smooth

end MPE
