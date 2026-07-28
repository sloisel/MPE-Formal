import Mathlib
import Formal.Weight
import Formal.OneDim
import Formal.Dyadic
import Formal.Blocks
import Formal.DeltaFactor
import Formal.Annulus
import Formal.PolyDeriv
import Formal.Instantiate

/-!
# Lemma 4.8: anticoncentration of the denominator

Appendix Obligations 7–9.  This file connects the polynomial construction of
`Formal/Instantiate.lean` to the geometry of `Formal/Annulus.lean`.

The bridge is short.  The cleared denominator splits as `σ̃ = c·Δ + R` with `Δ` the
degeneracy polynomial and every monomial of `R` of degree `≥ n+1`
(`lowDeg_sigt_remainder`, proved).  Evaluating, `Δ(z) = det(A-I)·det K_A(z)`, and the
Krylov matrix scales, `K_A(rz) = r·K_A(z)`, so `Δ(rz) = rⁿΔ(z)` with no polynomial
homogeneity machinery at all — just `Matrix.det_smul`.
-/

namespace MPE

set_option maxHeartbeats 1000000

open MeasureTheory Set Finset MvPolynomial
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ### The Krylov matrix scales -/

lemma krylov_smul (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (z : Fin n → ℝ) :
    krylov A (r • z) = r • krylov A z := by
  ext i j
  simp only [krylov_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.mulVec_smul]
  rfl

lemma det_krylov_smul (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (z : Fin n → ℝ) :
    (krylov A (r • z)).det = r ^ n * (krylov A z).det := by
  rw [krylov_smul, Matrix.det_smul, Fintype.card_fin]

/-! ### `Δ` in terms of the Krylov determinant -/

namespace Poly

open Finset

variable {m : ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
  {q : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℝ}

local notation "n" => m + 1

lemma eval_lin (M : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) (i : Fin n) :
    MvPolynomial.eval z (lin M i) = (M.mulVec z) i := by
  rw [lin, map_sum]
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rfl

/-- The evaluated Krylov matrix of the construction is `(A - I) · K_A(z)`. -/
lemma map_Kmat (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    (Kmat A).map (MvPolynomial.eval z) = (A - 1) * krylov A z := by
  ext i j
  rw [Matrix.map_apply, Kmat, eval_lin]
  show (((A - 1) * A ^ (j : ℕ)).mulVec z) i = ((A - 1) * krylov A z) i j
  rw [← Matrix.mulVec_mulVec]
  simp only [Matrix.mul_apply, krylov_apply]
  rfl

/-- **`Δ` is the Krylov determinant, up to the constant `det(A - I)`.** -/
theorem eval_Delta (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    MvPolynomial.eval z (Delta A) = (A - 1).det * (krylov A z).det := by
  rw [Delta, ← Matrix.det_mul]
  have := RingHom.map_det (MvPolynomial.eval z) (Kmat A)
  rw [this, ← map_Kmat A z]
  rfl

/-- `Δ` scales like a form of degree `n`. -/
lemma eval_Delta_smul (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (z : Fin n → ℝ) :
    MvPolynomial.eval (r • z) (Delta A) = r ^ n * MvPolynomial.eval z (Delta A) := by
  rw [eval_Delta, eval_Delta, det_krylov_smul]
  ring

/-! ### The splitting of `σ̃`

`σ̃ = c·Δ + R`, and after rescaling by `r` the remainder contributes `O(r)` in `C¹`. -/

variable (A q)

/-- The leading constant: `p_A(1)·det(A-I)`, nonzero when `A - I` is invertible. -/
noncomputable def leadConst : ℝ := A.charpoly.eval 1 * (A - 1).det

/-- The remainder `R = σ̃ - p_A(1)·Δ`. -/
noncomputable def sigRem : MvPolynomial (Fin n) ℝ :=
  sigtPoly A q - C (A.charpoly.eval 1) * Delta A

variable {A q}

lemma lowDeg_sigRem (hq : ∀ i, LowDeg 2 (q i)) : LowDeg (n + 1) (sigRem A q) :=
  lowDeg_sigt_remainder hq

lemma leadConst_ne_zero (hA : IsUnit (A - 1)) : leadConst A ≠ 0 := by
  refine mul_ne_zero (charpoly_eval_one_ne_zero hA) ?_
  exact isUnit_iff_ne_zero.mp (Matrix.isUnit_iff_isUnit_det (A - 1) |>.mp hA)

/-- **The splitting.**  `σ̃(z) = leadConst · det K_A(z) + R(z)`. -/
theorem eval_sigtPoly (z : Fin n → ℝ) :
    MvPolynomial.eval z (sigtPoly A q)
      = leadConst A * (krylov A z).det + MvPolynomial.eval z (sigRem A q) := by
  rw [sigRem, map_sub, map_mul, MvPolynomial.eval_C, eval_Delta, leadConst]
  ring

/-- **The rescaled splitting**, in the shape `Formal/Annulus.lean` consumes:
`σ̃(rz) = rⁿ (Q(z) + E_r(z))` with `Q(z) = leadConst · det K_A(z)` and
`E_r(z) = R(rz)/rⁿ`. -/
theorem eval_sigtPoly_smul {r : ℝ} (hr : 0 < r) (z : Fin n → ℝ) :
    MvPolynomial.eval (r • z) (sigtPoly A q)
      = r ^ n * (leadConst A * (krylov A z).det
          + MvPolynomial.eval (r • z) (sigRem A q) / r ^ n) := by
  have hrn : (r : ℝ) ^ n ≠ 0 := by positivity
  rw [eval_sigtPoly, det_krylov_smul]
  field_simp

/-! ### Passing to eigencoordinates

Everything is transported to the coordinates `w` in which the leading part is literally
`γ ∏ wᵢ`, *before* any analysis.  Composing with the linear substitution `z = P w` is
`bind₁ (lin P ·)`, which preserves `LowDeg` (`LowDeg.bind₁`), so the remainder stays of
degree `≥ n+1` and `PolyDeriv`'s estimates apply verbatim.  The matrix `P` then enters the
analysis only through the Jacobian `|det P|` and the containment `P⁻¹(cube) ⊆ cube`. -/

variable (A q)

/-- The construction read in eigencoordinates: `σ̂(w) = σ̃(Pw)`. -/
noncomputable def sigHat (P : Matrix (Fin n) (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.bind₁ (fun i => lin P i) (sigtPoly A q)

/-- Its remainder above the leading form. -/
noncomputable def remHat (P : Matrix (Fin n) (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.bind₁ (fun i => lin P i) (sigRem A q)

variable {A q}

lemma lowDeg_remHat (hq : ∀ i, LowDeg 2 (q i)) (P : Matrix (Fin n) (Fin n) ℝ) :
    LowDeg (n + 1) (remHat A q P) :=
  (lowDeg_sigRem hq).bind₁ (fun i => lowDeg_lin P i)

lemma eval_bind₁_lin (P : Matrix (Fin n) (Fin n) ℝ) (p : MvPolynomial (Fin n) ℝ)
    (w : Fin n → ℝ) :
    MvPolynomial.eval w (MvPolynomial.bind₁ (fun i => lin P i) p)
      = MvPolynomial.eval (P.mulVec w) p := by
  have hfun : (fun i => MvPolynomial.eval w (lin P i)) = P.mulVec w := by
    funext i; exact eval_lin P w i
  show MvPolynomial.eval₂Hom (RingHom.id ℝ) w _ = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  show MvPolynomial.eval (fun i => MvPolynomial.eval w (lin P i)) p
      = MvPolynomial.eval (P.mulVec w) p
  rw [hfun]

/-- **The splitting in eigencoordinates.**  If the columns of `P` are eigenvectors of `A`
with eigenvalues `lam`, then

    σ̂(w) = γ · ∏ᵢ wᵢ + R̂(w),     γ = leadConst · det P · ∏_{i<j}(lamⱼ - lamᵢ),

with every monomial of `R̂` of degree `≥ n+1`. -/
theorem eval_sigHat {P : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hAP : A * P = P * Matrix.diagonal lam) (w : Fin n → ℝ) :
    MvPolynomial.eval w (sigHat A q P)
      = (leadConst A * (P.det * ∏ i : Fin n, ∏ j ∈ Ioi i, (lam j - lam i))) * (∏ k, w k)
        + MvPolynomial.eval w (remHat A q P) := by
  rw [sigHat, remHat, eval_bind₁_lin, eval_bind₁_lin, eval_sigtPoly,
    det_krylov_of_eigen hAP w]
  ring

end Poly

/-! ### The per-shell estimate

Everything composes here.  On the shell of outer radius `r` the substitution `y = r z`
turns the margin event into a plain sublevel set on the cube (`tau_preimage_subset`), the
substitution `z = P w` turns the leading part into `γ ∏ wᵢ` at the cost of the Jacobian
`|det P|` (`volume_preimage_mulVec`), and the cube estimate finishes.
-/

open Poly

variable {M : ℕ} {A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
  {q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ}

/-- The rescaled remainder, read in eigencoordinates. -/
noncomputable def remScaled (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ)
    (P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ) (r : ℝ) (w : Fin (M + 2) → ℝ) : ℝ :=
  MvPolynomial.eval (r • w) (remHat A q P) / r ^ (M + 2)

/-- The leading constant in eigencoordinates. -/
noncomputable def gammaHat (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ) (lam : Fin (M + 2) → ℝ) : ℝ :=
  leadConst A * (P.det * ∏ i : Fin (M + 2), ∏ j ∈ Finset.Ioi i, (lam j - lam i))

lemma gammaHat_ne_zero {P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ} {lam : Fin (M + 2) → ℝ}
    (hA : IsUnit (A - 1)) (hP : IsUnit P.det) (hlam : Function.Injective lam) :
    gammaHat A P lam ≠ 0 := by
  refine mul_ne_zero (leadConst_ne_zero hA) (mul_ne_zero (isUnit_iff_ne_zero.mp hP) ?_)
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
  exact sub_ne_zero_of_ne fun hc => hij (hlam hc.symm)

/-- **The margin event, rescaled and in eigencoordinates.** -/
lemma sublevel_eq_gammaProd {P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
    {lam : Fin (M + 2) → ℝ} (hAP : A * P = P * Matrix.diagonal lam)
    {r : ℝ} (hr : 0 < r) (w : Fin (M + 2) → ℝ) :
    MvPolynomial.eval (r • (P.mulVec w)) (sigtPoly A q) / r ^ (M + 2)
      = gammaHat A P lam * (∏ k, w k) + remScaled A q P r w := by
  have hrn : (r : ℝ) ^ (M + 2) ≠ 0 := by positivity
  have hsmul : r • (P.mulVec w) = P.mulVec (r • w) := (Matrix.mulVec_smul P r w).symm
  have hprod : ∏ k, (r • w) k = r ^ (M + 2) * ∏ k, w k := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hsmul, remScaled, ← eval_bind₁_lin,
    show MvPolynomial.bind₁ (fun i => lin P i) (sigtPoly A q) = sigHat A q P from rfl,
    eval_sigHat hAP, gammaHat]
  field_simp
  rw [hprod]
  ring

/-- The perturbation `Ê_r` is measurable. -/
lemma measurable_remScaled (P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ) (r : ℝ) :
    Measurable (remScaled A q P r) := by
  unfold remScaled
  refine Measurable.div_const ?_ _
  exact (MvPolynomial.continuous_eval _).measurable.comp (measurable_const_smul r)

/-- Its derivative along the first coordinate, from `PolyDeriv`. -/
lemma hasDerivAt_remScaled (P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ) (r : ℝ)
    (u' : Fin (M + 1) → ℝ) (t : ℝ) :
    HasDerivAt (fun t => remScaled A q P r (Fin.cons t u'))
      ((∑ d ∈ (remHat A q P).support,
          frozenCoeff (remHat A q P) (r • u') d * ((d 0 : ℝ) * (r * t) ^ (d 0 - 1)))
        * r / r ^ (M + 2)) t := by
  have h := hasDerivAt_eval_cons_scaled (remHat A q P) (M + 2) r u' t
  have hfun : (fun t => remScaled A q P r (Fin.cons t u'))
      = fun t => MvPolynomial.eval (Fin.cons (r * t) (r • u')) (remHat A q P) / r ^ (M + 2) := by
    funext t
    rw [remScaled, cons_smul]
  rw [hfun]
  exact h

/-- And the bound `|∂ₜ Ê_r| ≤ derivBound(R̂)·r` on the cube. -/
lemma abs_deriv_remScaled_le (hq : ∀ i, LowDeg 2 (q i))
    (P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (u' : Fin (M + 1) → ℝ) (t : ℝ)
    (hz : ‖(Fin.cons t u' : Fin (M + 2) → ℝ)‖ ≤ 1) :
    |(∑ d ∈ (remHat A q P).support,
        frozenCoeff (remHat A q P) (r • u') d * ((d 0 : ℝ) * (r * t) ^ (d 0 - 1)))
      * r / r ^ (M + 2)|
      ≤ derivBound (remHat A q P) * r :=
  LowDeg.abs_deriv_scaled_le (lowDeg_remHat hq P) hr hr1 u' t hz

lemma norm_cons_le {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) {u' : Fin (M + 1) → ℝ}
    (hu : u' ∈ cube (M + 1)) : ‖(Fin.cons t u' : Fin (M + 2) → ℝ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [Real.norm_eq_abs, abs_le] using ht
  · have := hu j (Set.mem_univ j)
    simp only [Fin.cons_succ, Real.norm_eq_abs]
    rw [abs_le]
    exact this

/-- **The perturbation size on the shell of radius `r`.** -/
noncomputable def etaOf (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ)
    (P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ) (r : ℝ) : ℝ :=
  (derivBound (remHat A q P) + 1) * r

lemma etaOf_pos (P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ) {r : ℝ} (hr : 0 < r) :
    0 < etaOf A q P r := by
  have := derivBound_nonneg (remHat A q P)
  unfold etaOf
  positivity

/-- **The rescaled shell estimate.**  After rescaling by `r` and passing to
eigencoordinates, the margin event on the cube obeys the all-lines cube estimate. -/
theorem shell_cube_bound (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1))
    {P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ} {lam : Fin (M + 2) → ℝ}
    (hP : IsUnit P.det) (hlam : Function.Injective lam)
    (hAP : A * P = P * Matrix.diagonal lam)
    (hcontr : ∀ z : Fin (M + 2) → ℝ, ‖P⁻¹.mulVec z‖ ≤ ‖z‖)
    {r s : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s) :
    volume ({z : Fin (M + 2) → ℝ |
        |MvPolynomial.eval (r • z) (sigtPoly A q)| ≤ s * r ^ (M + 2)} ∩ cube (M + 2))
      ≤ ENNReal.ofReal |P.det| *
          (ENNReal.ofReal (4 * (4 * gammaConst M (gammaHat A P lam) + 2 ^ (M + 1)) * s
              * Lam s ^ (M + 1))
            + ENNReal.ofReal (2 * (gammaConst M (gammaHat A P lam) * (2 * etaOf A q P r)
              * Lam (2 * etaOf A q P r) ^ M))) := by
  classical
  set γ := gammaHat A P lam with hγdef
  set η := etaOf A q P r with hηdef
  have hγ : γ ≠ 0 := gammaHat_ne_zero hA hP hlam
  have hη : 0 < η := etaOf_pos P hr
  have hrn : (0:ℝ) < r ^ (M + 2) := by positivity
  -- the target set in `w`-coordinates
  set T : Set (Fin (M + 2) → ℝ) :=
    {w | |γ * (∏ i, w i) + remScaled A q P r w| ≤ s} ∩ cube (M + 2) with hT
  -- step 1: the source set is carried into `T`
  have hsub : ({z : Fin (M + 2) → ℝ |
      |MvPolynomial.eval (r • z) (sigtPoly A q)| ≤ s * r ^ (M + 2)} ∩ cube (M + 2))
      ⊆ (fun z => P⁻¹.mulVec z) ⁻¹' T := by
    rintro z ⟨hz, hzc⟩
    have hzn : ‖z‖ ≤ 1 := by rwa [← closedBall_eq_cube] at hzc
    have hw : P.mulVec (P⁻¹.mulVec z) = z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
    refine ⟨?_, ?_⟩
    · show |γ * (∏ i, (P⁻¹.mulVec z) i) + remScaled A q P r (P⁻¹.mulVec z)| ≤ s
      rw [← sublevel_eq_gammaProd hAP hr, hw]
      rw [abs_div, abs_of_pos hrn, div_le_iff₀ hrn]
      simpa [mul_comm] using hz
    · rw [← closedBall_eq_cube]
      exact le_trans (hcontr z) hzn
  -- step 2: transport, step 3: the cube estimate
  calc volume ({z : Fin (M + 2) → ℝ |
        |MvPolynomial.eval (r • z) (sigtPoly A q)| ≤ s * r ^ (M + 2)} ∩ cube (M + 2))
      ≤ volume ((fun z => P⁻¹.mulVec z) ⁻¹' T) := measure_mono hsub
    _ = ENNReal.ofReal |P.det| * volume T := volume_preimage_mulVec hP T
    _ ≤ _ := by
        refine mul_le_mul_right ?_ _
        refine measure_sublevel_cube_le M hγ hη hs (measurable_remScaled P r)
          (fun u' t => hasDerivAt_remScaled P r u' t) ?_
        intro u' hu t ht
        refine le_trans (abs_deriv_remScaled_le hq P hr hr1 u' t (norm_cons_le ht hu)) ?_
        have := derivBound_nonneg (remHat A q P)
        rw [hηdef, etaOf]
        nlinarith

/-! ### Lemma 4.8

Summing the shells.  The `s`-term carries the geometric weight `2^{-nj}` alone; the
`η`-term carries an extra `2^{-j}` from `ηⱼ ≍ 2^{-j}R` and a factor `(1+j)^M` from
`Λ(a2^{-j}) ≤ Λ(a)(1+j)`, so both sums are dominated by `dyadicConst`. -/

/-- **Lemma 4.8**, in Lebesgue form: the margin event inside the ball of radius `R`. -/
theorem lemma7_volume (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1))
    {P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ} {lam : Fin (M + 2) → ℝ}
    (hP : IsUnit P.det) (hlam : Function.Injective lam)
    (hAP : A * P = P * Matrix.diagonal lam)
    (hcontr : ∀ z : Fin (M + 2) → ℝ, ‖P⁻¹.mulVec z‖ ≤ ‖z‖) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ R s : ℝ, 0 < R → R ≤ 1 → 0 < s → s ≤ 1 →
      volume ({y : Fin (M + 2) → ℝ |
          |MvPolynomial.eval y (sigtPoly A q)| ≤ s * ‖y‖ ^ (M + 2)} ∩ {y | ‖y‖ ≤ R})
        ≤ ENNReal.ofReal (CA * R ^ (M + 2) *
            (s * Lam s ^ (M + 1) + R * Lam R ^ M)) := by
  classical
  set γ := gammaHat A P lam with hγdef
  set Γ := gammaConst M γ with hΓdef
  set c : ℝ := derivBound (remHat A q P) + 1 with hcdef
  have hc1 : (1:ℝ) ≤ c := by
    have := derivBound_nonneg (remHat A q P); rw [hcdef]; linarith
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le one_pos hc1
  have hΓ0 : (0:ℝ) ≤ Γ := gammaConst_nonneg M γ
  have hdP : (0:ℝ) < |P.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp hP)
  -- the two *constants* (independent of `R`, `s`, `j`)
  set D₁ : ℝ := |P.det| * (4 * (4 * Γ + 2 ^ (M + 1))) with hD₁
  set D₂ : ℝ := |P.det| * (4 * Γ * c) with hD₂
  have hD₁0 : 0 < D₁ := by rw [hD₁]; positivity
  have hD₂0 : 0 ≤ D₂ := by rw [hD₂]; positivity
  refine ⟨D₁ * dyadicConst (M + 2) 0
      + D₂ * Lam (2 * c) ^ M * dyadicConst (M + 3) M + 1, ?_, ?_⟩
  · have h1 := dyadicConst_nonneg (M + 2) 0
    have h2 := dyadicConst_nonneg (M + 3) M
    have h3 := (Lam_pow_pos (2 * c) M).le
    positivity
  intro R s hR hR1 hs hs1
  -- the `R`,`s`-dependent coefficients of the two dyadic series
  set a : ℝ := D₁ * (R ^ (M + 2) * (s * Lam s ^ (M + 1))) with hadef
  set b : ℝ := D₂ * (R ^ (M + 3) * Lam (2 * c * R) ^ M) with hbdef
  have hLamsp : (0:ℝ) < Lam s ^ (M + 1) := Lam_pow_pos s (M + 1)
  have hLamcR : (0:ℝ) < Lam (2 * c * R) ^ M := Lam_pow_pos _ M
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  -- shell sum
  refine le_trans (volume_inter_ball_le (by omega) hR _) ?_
  -- bound each shell
  have hshell : ∀ j : ℕ,
      ENNReal.ofReal (((1/2 : ℝ) ^ j * R) ^ (M + 2)) *
        volume ((fun z => ((1/2 : ℝ) ^ j * R) • z) ⁻¹'
          {y : Fin (M + 2) → ℝ |
            |MvPolynomial.eval y (sigtPoly A q)| ≤ s * ‖y‖ ^ (M + 2)} ∩ cube (M + 2))
      ≤ ENNReal.ofReal
          (a * (((1:ℝ)/2) ^ ((M + 2) * j) * (1 + j) ^ 0)
            + b * (((1:ℝ)/2) ^ ((M + 3) * j) * (1 + j) ^ M)) := by
    intro j
    set r : ℝ := (1/2 : ℝ) ^ j * R with hrdef
    have hr : 0 < r := by rw [hrdef]; positivity
    have hr1 : r ≤ 1 := by
      rw [hrdef]
      have : ((1:ℝ)/2) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    -- the preimage sits inside the shell-cube set
    have hsub : (fun z => r • z) ⁻¹'
        {y : Fin (M + 2) → ℝ | |MvPolynomial.eval y (sigtPoly A q)| ≤ s * ‖y‖ ^ (M + 2)}
        ∩ cube (M + 2)
        ⊆ {z : Fin (M + 2) → ℝ |
            |MvPolynomial.eval (r • z) (sigtPoly A q)| ≤ s * r ^ (M + 2)} ∩ cube (M + 2) := by
      rintro z ⟨hz, hzc⟩
      refine ⟨?_, hzc⟩
      have hzn : ‖z‖ ≤ 1 := by rwa [← closedBall_eq_cube] at hzc
      have hz' : |MvPolynomial.eval (r • z) (sigtPoly A q)| ≤ s * ‖r • z‖ ^ (M + 2) := hz
      refine le_trans hz' ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
      have hzp : ‖z‖ ^ (M + 2) ≤ 1 := pow_le_one₀ (norm_nonneg z) hzn
      have hr0 : (0:ℝ) ≤ r ^ (M + 2) := by positivity
      calc s * (r ^ (M + 2) * ‖z‖ ^ (M + 2)) ≤ s * (r ^ (M + 2) * 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hs.le
            exact mul_le_mul_of_nonneg_left hzp hr0
        _ = s * r ^ (M + 2) := by ring
    refine le_trans (mul_le_mul_right (measure_mono hsub) _) ?_
    refine le_trans (mul_le_mul_right
      (shell_cube_bound hq hA hP hlam hAP hcontr hr hr1 hs) _) ?_
    set X₁ : ℝ := 4 * (4 * Γ + 2 ^ (M + 1)) * s * Lam s ^ (M + 1) with hX₁
    set X₂ : ℝ := 2 * (Γ * (2 * etaOf A q P r) * Lam (2 * etaOf A q P r) ^ M) with hX₂
    have hη0 : 0 < etaOf A q P r := etaOf_pos P hr
    have hX₁0 : 0 ≤ X₁ := by rw [hX₁]; positivity
    have hX₂0 : 0 ≤ X₂ := by
      rw [hX₂]; have := (Lam_pow_pos (2 * etaOf A q P r) M).le; positivity
    -- collapse the right-hand side to a single `ofReal`
    have hcollapse : ENNReal.ofReal (r ^ (M + 2)) *
        (ENNReal.ofReal |P.det| * (ENNReal.ofReal X₁ + ENNReal.ofReal X₂))
        = ENNReal.ofReal (r ^ (M + 2) * (|P.det| * (X₁ + X₂))) := by
      rw [← ENNReal.ofReal_add hX₁0 hX₂0, ← ENNReal.ofReal_mul hdP.le,
        ← ENNReal.ofReal_mul (by positivity)]
    rw [hcollapse]
    refine ENNReal.ofReal_le_ofReal ?_
    -- the two elementary identities
    have hrpow : r ^ (M + 2) = R ^ (M + 2) * ((1:ℝ)/2) ^ ((M + 2) * j) := by
      rw [hrdef, mul_pow, ← pow_mul, mul_comm j (M + 2)]; ring
    have hetar : 2 * etaOf A q P r = (2 * c * R) * ((1:ℝ)/2) ^ j := by
      rw [etaOf, hcdef, hrdef]; ring
    have hsplit : ((1:ℝ)/2 : ℝ) ^ ((M + 3) * j)
        = ((1:ℝ)/2) ^ ((M + 2) * j) * ((1:ℝ)/2) ^ j := by
      rw [← pow_add]; ring_nf
    -- the `s`-term is an exact match
    have hi : r ^ (M + 2) * (|P.det| * X₁) = a * (((1:ℝ)/2) ^ ((M + 2) * j) * (1 + j) ^ 0) := by
      rw [hadef, hD₁, hrpow, hX₁]; ring
    -- the `η`-term, after `Λ(a2⁻ʲ) ≤ Λ(a)(1+j)`
    have hLamη : Lam (2 * etaOf A q P r) ^ M ≤ Lam (2 * c * R) ^ M * (1 + j) ^ M := by
      rw [hetar, ← mul_pow]
      exact pow_le_pow_left₀ (Lam_nonneg _) (Lam_mul_half_pow_le (by positivity) j) M
    have hii : r ^ (M + 2) * (|P.det| * X₂)
        ≤ b * (((1:ℝ)/2) ^ ((M + 3) * j) * (1 + j) ^ M) := by
      have hstep : X₂ ≤ 2 * Γ * ((2 * c * R) * ((1:ℝ)/2) ^ j)
          * (Lam (2 * c * R) ^ M * (1 + j) ^ M) := by
        rw [hX₂, hetar]
        have h1 : (0:ℝ) ≤ 2 * Γ * ((2 * c * R) * ((1:ℝ)/2) ^ j) := by positivity
        calc 2 * (Γ * ((2 * c * R) * ((1:ℝ)/2) ^ j)
              * Lam ((2 * c * R) * ((1:ℝ)/2) ^ j) ^ M)
            = (2 * Γ * ((2 * c * R) * ((1:ℝ)/2) ^ j))
              * Lam ((2 * c * R) * ((1:ℝ)/2) ^ j) ^ M := by ring
          _ ≤ (2 * Γ * ((2 * c * R) * ((1:ℝ)/2) ^ j))
              * (Lam (2 * c * R) ^ M * (1 + j) ^ M) := by
              refine mul_le_mul_of_nonneg_left ?_ h1
              rw [← mul_pow]
              exact pow_le_pow_left₀ (Lam_nonneg _)
                (Lam_mul_half_pow_le (by positivity) j) M
      calc r ^ (M + 2) * (|P.det| * X₂)
          ≤ r ^ (M + 2) * (|P.det| * (2 * Γ * ((2 * c * R) * ((1:ℝ)/2) ^ j)
              * (Lam (2 * c * R) ^ M * (1 + j) ^ M))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hstep hdP.le
        _ = b * (((1:ℝ)/2) ^ ((M + 3) * j) * (1 + j) ^ M) := by
            rw [hbdef, hD₂, hrpow, hsplit]; ring
    have hexpand : r ^ (M + 2) * (|P.det| * (X₁ + X₂))
        = r ^ (M + 2) * (|P.det| * X₁) + r ^ (M + 2) * (|P.det| * X₂) := by ring
    rw [hexpand]
    linarith [hi.le, hii]
  refine le_trans (ENNReal.tsum_le_tsum hshell) ?_
  -- sum the two dyadic series
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    (summable_dyadic_pair (n := M + 2) (p := M) (by omega) a b)]
  rw [tsum_dyadic_pair (by omega) a b]
  refine ENNReal.ofReal_le_ofReal ?_
  -- finally, absorb `Λ(2cR) ≤ Λ(2c)Λ(R)` and compare with the stated constant
  set CA : ℝ := D₁ * dyadicConst (M + 2) 0
      + D₂ * Lam (2 * c) ^ M * dyadicConst (M + 3) M + 1 with hCAdef
  have hdc1 : (0:ℝ) ≤ dyadicConst (M + 2) 0 := dyadicConst_nonneg _ _
  have hdc2 : (0:ℝ) ≤ dyadicConst (M + 3) M := dyadicConst_nonneg _ _
  have hL2c : (0:ℝ) ≤ Lam (2 * c) ^ M := (Lam_pow_pos (2 * c) M).le
  set P₁ : ℝ := R ^ (M + 2) * (s * Lam s ^ (M + 1)) with hP₁
  set P₂ : ℝ := R ^ (M + 2) * (R * Lam R ^ M) with hP₂
  have hP₁0 : (0:ℝ) ≤ P₁ := by
    rw [hP₁]
    exact mul_nonneg (by positivity) (mul_nonneg hs.le (Lam_pow_pos s (M + 1)).le)
  have hP₂0 : (0:ℝ) ≤ P₂ := by
    rw [hP₂]
    exact mul_nonneg (by positivity) (mul_nonneg hR.le (Lam_pow_pos R M).le)
  have hnn2 : (0:ℝ) ≤ D₂ * Lam (2 * c) ^ M * dyadicConst (M + 3) M :=
    mul_nonneg (mul_nonneg hD₂0 hL2c) hdc2
  have hnn1 : (0:ℝ) ≤ D₁ * dyadicConst (M + 2) 0 := mul_nonneg hD₁0.le hdc1
  have hCA1 : D₁ * dyadicConst (M + 2) 0 ≤ CA := by rw [hCAdef]; linarith
  have hCA2 : D₂ * Lam (2 * c) ^ M * dyadicConst (M + 3) M ≤ CA := by rw [hCAdef]; linarith
  -- the `s`-term
  have h1 : a * dyadicConst (M + 2) 0 ≤ CA * P₁ := by
    have : a * dyadicConst (M + 2) 0 = (D₁ * dyadicConst (M + 2) 0) * P₁ := by
      rw [hadef, hP₁]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hCA1 hP₁0
  -- the `η`-term
  have h2 : b * dyadicConst (M + 3) M ≤ CA * P₂ := by
    have hLamcR : Lam (2 * c * R) ^ M ≤ Lam (2 * c) ^ M * Lam R ^ M := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Lam_nonneg _) (Lam_mul_le_of_pos (by positivity) hR) M
    have hb : b * dyadicConst (M + 3) M
        ≤ (D₂ * Lam (2 * c) ^ M * dyadicConst (M + 3) M) * P₂ := by
      rw [hbdef, hP₂]
      have hfac : D₂ * (R ^ (M + 3) * Lam (2 * c * R) ^ M) * dyadicConst (M + 3) M
          = (D₂ * (R ^ (M + 2) * R) * dyadicConst (M + 3) M) * Lam (2 * c * R) ^ M := by
        ring
      have hfac' : D₂ * Lam (2 * c) ^ M * dyadicConst (M + 3) M
            * (R ^ (M + 2) * (R * Lam R ^ M))
          = (D₂ * (R ^ (M + 2) * R) * dyadicConst (M + 3) M)
            * (Lam (2 * c) ^ M * Lam R ^ M) := by ring
      rw [hfac, hfac']
      exact mul_le_mul_of_nonneg_left hLamcR (by positivity)
    exact le_trans hb (mul_le_mul_of_nonneg_right hCA2 hP₂0)
  have hfinal : CA * R ^ (M + 2) * (s * Lam s ^ (M + 1) + R * Lam R ^ M)
      = CA * P₁ + CA * P₂ := by rw [hP₁, hP₂]; ring
  rw [hfinal]
  linarith

/-! ### Lemma 4.8 in probability form

The dither is uniform on the sup-norm ball `B(x,δ)`, which is the cube `x + δ·[-1,1]ⁿ`.
Pulling back along `b ↦ x + δb` — a scaling and a translation — turns the uniform measure on
the unit cube into the uniform measure on `B(x,δ)`, and the two Jacobians `δⁿ` and `2ⁿ`
cancel against the `Rⁿ = (2δ)ⁿ` of `lemma7_volume`. -/

/-- The affine pullback of Lebesgue measure. -/
lemma volume_preimage_affine {δ : ℝ} (hδ : 0 < δ) (x : Fin (M + 2) → ℝ)
    (T : Set (Fin (M + 2) → ℝ)) :
    volume ((fun b => x + δ • b) ⁻¹' T)
      = ENNReal.ofReal (δ⁻¹ ^ (M + 2)) * volume T := by
  have hstep : (fun b : Fin (M + 2) → ℝ => x + δ • b) ⁻¹' T
      = (fun b : Fin (M + 2) → ℝ => δ • b) ⁻¹' ((fun y => x + y) ⁻¹' T) := rfl
  rw [hstep, Measure.addHaar_preimage_smul volume hδ.ne', measure_preimage_add]
  congr 1
  rw [Module.finrank_fin_fun, abs_of_nonneg (by positivity), inv_pow]

/-- **Lemma 4.8, probability form.**  For `y` uniform on the sup-norm ball `B(x,δ)` with
`‖x‖ ≤ δ`, the margin event has probability at most
`C_A (s Λ(s)^{n-1} + δ Λ(δ)^{n-2})`. -/
theorem lemma7_prob {Sig : (Fin (M + 2) → ℝ) → ℝ} {ρ : ℝ}
    (hvol : ∃ CA : ℝ, 0 < CA ∧ ∀ R s : ℝ, 0 < R → R ≤ ρ → 0 < s → s ≤ 1 →
      volume ({y : Fin (M + 2) → ℝ |
          |Sig y| ≤ s * ‖y‖ ^ (M + 2)} ∩ {y | ‖y‖ ≤ R})
        ≤ ENNReal.ofReal (CA * R ^ (M + 2) *
            (s * Lam s ^ (M + 1) + R * Lam R ^ M))) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ δ s : ℝ, 0 < δ → 2 * δ ≤ ρ → 0 < s → s ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ →
        blockMeasure (M + 2)
            {b | |Sig (x + δ • b)|
                ≤ s * ‖x + δ • b‖ ^ (M + 2)}
          ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
              (s * Lam s ^ (M + 1) + δ * Lam δ ^ M)) := by
  obtain ⟨CA, hCA0, hCA⟩ := hvol
  refine ⟨CA, hCA0, ?_⟩
  intro δ s hδ hδ1 hs hs1 x hx
  set S : Set (Fin (M + 2) → ℝ) :=
    {b | |Sig (x + δ • b)| ≤ s * ‖x + δ • b‖ ^ (M + 2)} with hS
  set T : Set (Fin (M + 2) → ℝ) :=
    {y | |Sig y| ≤ s * ‖y‖ ^ (M + 2)} ∩ {y | ‖y‖ ≤ 2 * δ}
    with hT
  have h2δ : (0:ℝ) < 2 * δ := by linarith
  -- `S ∩ cube` pulls back from `T`
  have hsub : S ∩ cube (M + 2) ⊆ (fun b => x + δ • b) ⁻¹' T := by
    rintro b ⟨hb, hbc⟩
    have hbn : ‖b‖ ≤ 1 := by rwa [← closedBall_eq_cube] at hbc
    refine ⟨hb, ?_⟩
    calc ‖x + δ • b‖ ≤ ‖x‖ + ‖δ • b‖ := norm_add_le _ _
      _ ≤ δ + δ * 1 := by
          refine add_le_add hx ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
          exact mul_le_mul_of_nonneg_left hbn hδ.le
      _ = 2 * δ := by ring
  -- transport, then `lemma7_volume`
  have hvol : volume (S ∩ cube (M + 2))
      ≤ ENNReal.ofReal (δ⁻¹ ^ (M + 2)) *
        ENNReal.ofReal (CA * (2 * δ) ^ (M + 2) *
          (s * Lam s ^ (M + 1) + (2 * δ) * Lam (2 * δ) ^ M)) := by
    refine le_trans (measure_mono hsub) ?_
    rw [volume_preimage_affine hδ x T]
    exact mul_le_mul_right (hCA (2 * δ) s h2δ hδ1 hs hs1) _
  -- undo the normalization of `blockMeasure`
  have hcube : volume (S ∩ cube (M + 2)) = ENNReal.ofReal ((2:ℝ) ^ (M + 2)) *
      blockMeasure (M + 2) S := by
    have := volume_restrict_cube (M + 2)
    have h2 : (volume : Measure (Fin (M + 2) → ℝ)).restrict (cube (M + 2)) S
        = volume (S ∩ cube (M + 2)) := by
      rw [Measure.restrict_apply']
      exact measurableSet_cube _
    rw [← h2, this, Measure.smul_apply, smul_eq_mul]
  -- `2^(M+2) ≥ 1`, so no cancellation is needed: absorb the factor into the constant
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2:ℝ) ^ (M + 2)) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num))
  calc blockMeasure (M + 2) S
      ≤ ENNReal.ofReal ((2:ℝ) ^ (M + 2)) * blockMeasure (M + 2) S :=
        le_mul_of_one_le_left zero_le hone
    _ = volume (S ∩ cube (M + 2)) := hcube.symm
    _ ≤ _ := by
        refine le_trans hvol ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hLam2δ : Lam (2 * δ) ^ M ≤ Lam δ ^ M :=
          pow_le_pow_left₀ (Lam_nonneg _) (Lam_le_Lam hδ (by linarith)) M
        have hinvδ : δ⁻¹ ^ (M + 2) * (2 * δ) ^ (M + 2) = 2 ^ (M + 2) := by
          rw [mul_pow, ← mul_assoc, mul_comm (δ⁻¹ ^ (M + 2)) ((2:ℝ) ^ (M + 2)), mul_assoc,
            ← mul_pow, inv_mul_cancel₀ hδ.ne', one_pow, mul_one]
        have hLs : (0:ℝ) ≤ s * Lam s ^ (M + 1) :=
          mul_nonneg hs.le (Lam_pow_pos s (M + 1)).le
        have hstep : (2 * δ) * Lam (2 * δ) ^ M ≤ 2 * (δ * Lam δ ^ M) := by
          have h := mul_le_mul_of_nonneg_left hLam2δ (by linarith : (0:ℝ) ≤ 2 * δ)
          linarith
        calc δ⁻¹ ^ (M + 2) * (CA * (2 * δ) ^ (M + 2)
              * (s * Lam s ^ (M + 1) + 2 * δ * Lam (2 * δ) ^ M))
            = (δ⁻¹ ^ (M + 2) * (2 * δ) ^ (M + 2)) * CA
              * (s * Lam s ^ (M + 1) + 2 * δ * Lam (2 * δ) ^ M) := by ring
          _ = 2 ^ (M + 2) * CA * (s * Lam s ^ (M + 1) + 2 * δ * Lam (2 * δ) ^ M) := by
              rw [hinvδ]
          _ ≤ 2 ^ (M + 2) * CA * (2 * (s * Lam s ^ (M + 1) + δ * Lam δ ^ M)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              linarith
          _ = CA * 2 ^ (M + 3) * (s * Lam s ^ (M + 1) + δ * Lam δ ^ M) := by
              rw [pow_succ]; ring

end MPE
