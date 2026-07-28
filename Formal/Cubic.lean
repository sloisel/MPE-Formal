import Mathlib
import Formal.CThree

/-!
# The cubic Taylor input, and the leading form `G`

Theorem 5.5 is the one place where `C³` is genuinely used: the quadratic Taylor coefficient
`q₂` of `f` is *part of the statement*, because it builds the leading form `G` on which
Hypotheses A2 and A3 are conditions.

Following the pattern of `SmoothData` — which carries the `C²` data as fields and leaves
`nonempty_smoothData` to produce it from `ContDiffOn ℝ 2` — `SmoothData3` carries `q₂` with
exactly the three properties the argument uses:

* homogeneity `q₂ (t • x) = t² • q₂ x`,
* the bilinear Lipschitz bound `‖q₂ a - q₂ b‖ ≤ K₂ (‖a‖+‖b‖) ‖a-b‖`,
* the cubic remainder `‖q x - q₂ x‖ ≤ K₃ ‖x‖³`, where `q = f - Df(0)` is `nonlin f`.

All three hold for `q₂ x = ½ (W x) x` with `W = D²f(0)`, and *no symmetry of `W` is needed*.

The main result is `van_Ntil_sub_lead`: with

    N² v := -(A-I)⁻¹ ∑_j c⁰_j q₂(Aʲ v),    G := Δ · N²,

one has `‖Ñ(y) - Δ(y) • N²(y)‖ ≤ C ‖y‖^(n+3)`.  This single estimate replaces *both* the
`C³` clause of the paper's Lemma 4.1 (which extracts the degree-`n+2` homogeneous part of
`Ñ`) and its Lemma 4.3 (`G = Δ·N²`): here `G` is *defined* as `Δ·N²`, so Lemma 4.3 is
definitional, and Lemma 4.1's clause is this estimate read on the sphere.

The proof is the exact identity `(A-I)Ñ = -∑_j c̃_j q(fʲ)` of `mulVec_Ntil` — the same
identity that reproved Lemma 4.4(iii) at `C²` — with one extra Taylor order.
-/

namespace MPE

open Metric Set

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G]

/-- **The `C³` data.**  `SmoothData` plus the quadratic Taylor coefficient of `f` at `0`,
with a cubic remainder.  Only *values* are constrained: no derivative of `q₂` is ever
taken. -/
structure SmoothData3 (f : G → G) extends SmoothData f where
  /-- the quadratic Taylor coefficient of `f` at `0` -/
  q₂ : G → G
  /-- the bilinearity constant -/
  K₂ : ℝ
  /-- the cubic remainder constant -/
  K₃ : ℝ
  hK₂ : 0 ≤ K₂
  hK₃ : 0 ≤ K₃
  hq₂smul : ∀ (t : ℝ) (x : G), q₂ (t • x) = (t ^ 2) • q₂ x
  hq₂lip : ∀ a b : G, ‖a‖ ≤ R → ‖b‖ ≤ R → ‖q₂ a - q₂ b‖ ≤ K₂ * (‖a‖ + ‖b‖) * ‖a - b‖
  hq₂rem : ∀ x : G, ‖x‖ ≤ R → ‖nonlin f x - q₂ x‖ ≤ K₃ * ‖x‖ ^ 3

/-! ### The constructor

`q₂ x = ½ (D²f(0) x) x`.  Homogeneity and the bilinear Lipschitz bound are immediate from
bilinearity of `D²f(0)`.  For the cubic remainder, symmetry of the second derivative
(`ContDiffAt.isSymmSndFDerivAt`) gives `D q₂ x = D²f(0) x`, after which the workhorse
`norm_le_of_fderiv_le` is applied three times — to `D²f - D²f(0)`, then to
`Df - Df(0) - D²f(0)·`, then to `f - Df(0)· - q₂` — exactly as `Smooth.lean`'s header
describes.  The number of derivatives used is three, independent of the dimension. -/

/-- **The `C³` data exists.** -/
theorem nonempty_smoothData3 [FiniteDimensional ℝ G] {f : G → G} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 3 f (ball (0 : G) R₀)) :
    ∃ D3 : SmoothData3 f,
      ∀ x : G, D3.q₂ x = (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ f) 0) x) x := by
  classical
  set R := R₀ / 2 with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  have hopen : IsOpen (ball (0 : G) R₀) := isOpen_ball
  have hsub : closedBall (0 : G) R ⊆ ball (0 : G) R₀ := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]
    rw [hRdef] at hz
    linarith
  -- the three levels of differentiability
  have hdiff : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ f z := fun z hz =>
    (hf.contDiffAt (hopen.mem_nhds (hsub hz))).differentiableAt (by norm_num)
  have hfd : ContDiffOn ℝ 2 (fderiv ℝ f) (ball (0 : G) R₀) :=
    hf.fderiv_of_isOpen hopen (by norm_num)
  have hfdd : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ f)) (ball (0 : G) R₀) :=
    hfd.fderiv_of_isOpen hopen (by norm_num)
  have hdiff2 : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ (fderiv ℝ f) z := fun z hz =>
    (hfd.contDiffAt (hopen.mem_nhds (hsub hz))).differentiableAt (by norm_num)
  have hdiff3 : ∀ z ∈ closedBall (0 : G) R,
      DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) z := fun z hz =>
    (hfdd.contDiffAt (hopen.mem_nhds (hsub hz))).differentiableAt (by norm_num)
  -- the compactness bounds
  obtain ⟨L₀, hL₀0, hL₀⟩ := exists_fderiv_bound_of_contDiffOn (g := f) hR.le
    ((hf.mono hsub).of_le (by norm_num)) hdiff
    ((hf.continuousOn_fderiv_of_isOpen hopen (by norm_num)).mono hsub)
  obtain ⟨K, hK0, hK⟩ := exists_fderiv_bound_of_contDiffOn (g := fderiv ℝ f) hR.le
    ((hfd.mono hsub).of_le (by norm_num)) hdiff2
    (((hfd.fderiv_of_isOpen hopen (by norm_num)).continuousOn (n := 0)).mono hsub)
  obtain ⟨KW, hKW0, hKW⟩ :=
    exists_fderiv_bound_of_contDiffOn (g := fderiv ℝ (fderiv ℝ f)) hR.le
      ((hfdd.mono hsub).of_le (by norm_num)) hdiff3
      (((hfdd.fderiv_of_isOpen hopen (by norm_num)).continuousOn (n := 0)).mono hsub)
  -- the `C²` fields, as in `nonempty_smoothData`
  have hlip : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ f z - fderiv ℝ f 0‖ ≤ K * ‖z‖ := by
    intro z hz
    refine norm_le_of_fderiv_le_const (g := fun w => fderiv ℝ f w - fderiv ℝ f 0) hK0
      (by simp) (fun w hw => (hdiff2 w hw).sub_const _) (fun w hw => ?_) ?_
    · have hd : HasFDerivAt (fun w => fderiv ℝ f w - fderiv ℝ f 0)
          (fderiv ℝ (fderiv ℝ f) w) w := (hdiff2 w hw).hasFDerivAt.sub_const _
      rw [hd.fderiv]
      exact hK w hw
    · rw [mem_closedBall, dist_zero_right] at hz; exact hz
  -- the second derivative at the origin, and `q₂`
  set B : G →L[ℝ] (G →L[ℝ] G) := fderiv ℝ (fderiv ℝ f) 0 with hBdef
  set q₂ : G → G := fun x => (1/2 : ℝ) • ((B x) x) with hq₂def
  have hsymm : IsSymmSndFDerivAt ℝ f 0 := by
    have h0 : (0 : G) ∈ closedBall (0 : G) R := by
      rw [mem_closedBall, dist_self]; exact hR.le
    refine (hf.contDiffAt (hopen.mem_nhds (hsub h0))).isSymmSndFDerivAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_num
  -- step 1: `‖D²f z - D²f 0‖ ≤ KW ‖z‖`
  have hWlip : ∀ z ∈ closedBall (0 : G) R,
      ‖fderiv ℝ (fderiv ℝ f) z - B‖ ≤ KW * ‖z‖ := by
    intro z hz
    rw [hBdef]
    refine norm_le_of_fderiv_le_const
      (g := fun w => fderiv ℝ (fderiv ℝ f) w - fderiv ℝ (fderiv ℝ f) 0) hKW0
      (by simp) (fun w hw => (hdiff3 w hw).sub_const _) (fun w hw => ?_) ?_
    · have hd : HasFDerivAt (fun w => fderiv ℝ (fderiv ℝ f) w - fderiv ℝ (fderiv ℝ f) 0)
          (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) w) w := (hdiff3 w hw).hasFDerivAt.sub_const _
      rw [hd.fderiv]
      exact hKW w hw
    · rw [mem_closedBall, dist_zero_right] at hz; exact hz
  -- step 2: `‖Df z - Df 0 - B z‖ ≤ KW ‖z‖²`
  have hu : ∀ z ∈ closedBall (0 : G) R,
      ‖fderiv ℝ f z - fderiv ℝ f 0 - B z‖ ≤ KW * ‖z‖ ^ 2 := by
    intro z hz
    have hz' : ‖z‖ ≤ R := by rwa [mem_closedBall, dist_zero_right] at hz
    refine norm_le_of_fderiv_le (p := 1) (g := fun w => fderiv ℝ f w - fderiv ℝ f 0 - B w)
      hKW0 (by simp) (fun w hw => ((hdiff2 w hw).sub_const _).sub (B.differentiableAt))
      (fun w hw => ?_) hz'
    have hd : HasFDerivAt (fun w => fderiv ℝ f w - fderiv ℝ f 0 - B w)
        (fderiv ℝ (fderiv ℝ f) w - B) w := by
      exact ((hdiff2 w hw).hasFDerivAt.sub_const (fderiv ℝ f 0)).sub B.hasFDerivAt
    rw [hd.fderiv]
    simpa using hWlip w hw
  -- `D q₂ x = B x`, using symmetry
  have hq₂deriv : ∀ x : G, HasFDerivAt q₂ (B x) x := by
    intro x
    have hΦ : HasFDerivAt (fun y : G => (B y) y)
        ((B x).comp (ContinuousLinearMap.id ℝ G) + B.flip x) x :=
      (B.hasFDerivAt).clm_apply (hasFDerivAt_id x)
    have hsm := hΦ.const_smul (1/2 : ℝ)
    have heq : (1/2 : ℝ) • ((B x).comp (ContinuousLinearMap.id ℝ G) + B.flip x) = B x := by
      ext v
      simp only [smul_apply, add_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.flip_apply]
      have := hsymm v x
      rw [← hBdef] at this
      rw [this]
      module
    rw [hq₂def]
    rw [← heq]
    exact hsm
  -- step 3: the cubic remainder
  have hrem : ∀ x ∈ closedBall (0 : G) R, ‖nonlin f x - q₂ x‖ ≤ KW * ‖x‖ ^ 3 := by
    intro x hx
    have hx' : ‖x‖ ≤ R := by rwa [mem_closedBall, dist_zero_right] at hx
    refine norm_le_of_fderiv_le (p := 2) (g := fun w => nonlin f w - q₂ w) hKW0 ?_
      (fun w hw => ((hdiff w hw).sub (linPart f).differentiableAt).sub
        (hq₂deriv w).differentiableAt)
      (fun w hw => ?_) hx'
    · show f 0 - linPart f 0 - q₂ 0 = 0
      rw [hf0, hq₂def]
      simp
    · have hd : HasFDerivAt (fun w => nonlin f w - q₂ w)
          (fderiv ℝ f w - linPart f - B w) w := by
        have h1 : HasFDerivAt (nonlin f) (fderiv ℝ f w - linPart f) w :=
          ((hdiff w hw).hasFDerivAt).sub (linPart f).hasFDerivAt
        exact h1.sub (hq₂deriv w)
      rw [hd.fderiv]
      have := hu w hw
      rw [linPart]
      exact this
  exact ⟨{ R := R, L := max L₀ 1, K := K, hR := hR, hL := le_max_right _ _, hK := hK0,
           hf0 := hf0, hmeas := hmeas, hdiff := hdiff,
           hbd := fun z hz => le_trans (hL₀ z hz) (le_max_left _ _), hlip := hlip,
           q₂ := q₂, K₂ := ‖B‖ / 2, K₃ := KW,
           hK₂ := by positivity, hK₃ := hKW0,
           hq₂smul := by
             intro t x
             rw [hq₂def]
             simp only [map_smul, smul_apply, smul_smul]
             congr 1
             ring
           hq₂lip := by
             intro a b _ _
             rw [hq₂def]
             have hsplit : (B a) a - (B b) b = (B a) (a - b) + (B (a - b)) b := by
               rw [map_sub, map_sub]
               simp only [sub_apply]
               abel
             rw [← smul_sub, norm_smul, Real.norm_eq_abs, hsplit]
             have h1 : ‖(B a) (a - b)‖ ≤ ‖B‖ * ‖a‖ * ‖a - b‖ :=
               le_trans ((B a).le_opNorm _)
                 (mul_le_mul_of_nonneg_right (B.le_opNorm a) (norm_nonneg _))
             have h2 : ‖(B (a - b)) b‖ ≤ ‖B‖ * ‖a - b‖ * ‖b‖ :=
               le_trans ((B (a - b)).le_opNorm _)
                 (mul_le_mul_of_nonneg_right (B.le_opNorm (a - b)) (norm_nonneg _))
             have h3 := norm_add_le ((B a) (a - b)) ((B (a - b)) b)
             have habs : |(1/2 : ℝ)| = 1/2 := by norm_num
             rw [habs]
             nlinarith [h1, h2, h3, norm_nonneg ((B a) (a - b) + (B (a - b)) b)]
           hq₂rem := fun x hx => hrem x (by rwa [mem_closedBall, dist_zero_right]) },
    fun x => rfl⟩

namespace SmoothData3

variable {f : G → G} (D3 : SmoothData3 f)

@[simp] lemma q₂_zero : D3.q₂ 0 = 0 := by
  have h := D3.hq₂smul 0 0
  simpa using h

/-- `‖q₂ x‖ ≤ K₂ ‖x‖²`, from the Lipschitz bound at `b = 0`. -/
lemma norm_q₂_le {x : G} (hx : ‖x‖ ≤ D3.R) : ‖D3.q₂ x‖ ≤ D3.K₂ * ‖x‖ ^ 2 := by
  have h0 : ‖(0 : G)‖ ≤ D3.R := by simpa using D3.hR.le
  have h := D3.hq₂lip x 0 hx h0
  simp only [q₂_zero, sub_zero, norm_zero, add_zero] at h
  calc ‖D3.q₂ x‖ ≤ D3.K₂ * ‖x‖ * ‖x‖ := h
    _ = D3.K₂ * ‖x‖ ^ 2 := by ring

end SmoothData3

/-! ### The leading form -/

section Lead

variable {m : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}

local notation "n" => m + 1

/-- `N^{[2]}(v) = -(A-I)⁻¹ ∑_{j≤n} c⁰_j q₂(Aʲ v)`, the explicit quadratic vector of the
paper's Lemma 4.3.  Here `c⁰_j = p_A.coeff j` (with `c⁰_n = 1`, the polynomial being
monic), matching the convention of `cct_sub_leading`. -/
noncomputable def NtwoR (D3 : SmoothData3 f) (v : Fin n → ℝ) : Fin n → ℝ :=
  (Amat f - 1)⁻¹.mulVec
    (-∑ j ∈ Finset.range (n + 1),
      (Amat f).charpoly.coeff j • D3.q₂ (((Amat f) ^ j).mulVec v))

/-- The leading form `G = Δ · N^{[2]}`.  The paper's Lemma 4.3 is this definition. -/
noncomputable def Glead (D3 : SmoothData3 f) (v : Fin n → ℝ) : Fin n → ℝ :=
  DeltaR f v • NtwoR D3 v

/-- `Q̃ = p_A(1) · Δ`, the paper's degree-`n` form at the full nonderogatory window. -/
noncomputable def QtR (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (v : Fin n → ℝ) : ℝ :=
  (Amat f).charpoly.eval 1 * DeltaR f v

/-- `Q̃` is homogeneous of degree `n`. -/
lemma QtR_smul (r : ℝ) (v : Fin n → ℝ) : QtR f (r • v) = r ^ n * QtR f v := by
  rw [QtR, QtR, DeltaR_eq, DeltaR_eq, det_krylov_smul]
  ring

/-- The cleared cycle map `S = Ñ/σ̃`. -/
noncomputable def cycS (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (y : Fin n → ℝ) :
    Fin n → ℝ := (sigt f y)⁻¹ • Ntil f y

/-- `N^{[2]}` is homogeneous of degree `2`. -/
lemma NtwoR_smul (D3 : SmoothData3 f) (r : ℝ) (v : Fin n → ℝ) :
    NtwoR D3 (r • v) = r ^ 2 • NtwoR D3 v := by
  rw [NtwoR, NtwoR, ← Matrix.mulVec_smul]
  congr 1
  rw [smul_neg, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_smul, D3.hq₂smul, smul_comm]

/-- Hence the leading form `G = Δ·N^{[2]}` is homogeneous of degree `n+2`. -/
lemma Glead_smul (D3 : SmoothData3 f) (r : ℝ) (v : Fin n → ℝ) :
    Glead D3 (r • v) = r ^ (n + 2) • Glead D3 v := by
  rw [Glead, Glead, NtwoR_smul, DeltaR_eq, det_krylov_smul, smul_smul, smul_smul]
  congr 1
  rw [DeltaR_eq]
  ring

/-- `(A-I) · N^{[2]}(v) = -∑_j c⁰_j q₂(Aʲ v)`: the defining property, with the inverse
cleared. -/
lemma mulVec_NtwoR (D3 : SmoothData3 f) (hA : IsUnit (Amat f - 1)) (v : Fin n → ℝ) :
    (Amat f - 1).mulVec (NtwoR D3 v)
      = -∑ j ∈ Finset.range (n + 1),
          (Amat f).charpoly.coeff j • D3.q₂ (((Amat f) ^ j).mulVec v) := by
  have hdet : IsUnit (Amat f - 1).det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  rw [NtwoR, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

end Lead

/-! ### `Δ` vanishes to order `n` -/

namespace SmoothData

section Estimates3

variable {m : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)} (D : SmoothData f)

local notation "n" => m + 1

/-- **`Δ` vanishes to order `n`.**  `Van.det` applied to the linear model `K`, whose entries
are linear in `y`. -/
theorem van_DeltaR (N : ℕ) :
    Van (D.rad N) m
      ((m + 1).factorial * (1 * (2 ^ m * (D.CB N) ^ (m + 1)))) (DeltaR f) := by
  have h := Van.det (ρ := D.rad N) (C := D.CB N) (D.CB_nonneg N)
    (fun i k => D.van_Kmat_entry' (N := N) i k)
  have hfun : (fun y => Matrix.det (fun i k => Kmat f i k y)) = DeltaR f := by
    funext y; exact det_Kmat y
  rwa [hfun] at h

/-- The constant in `|Δ(y)| ≤ CΔ ‖y‖ⁿ`. -/
noncomputable def CDelta (N : ℕ) : ℝ :=
  (m + 1).factorial * (1 * (2 ^ m * (D.CB N) ^ (m + 1)))

lemma CDelta_nonneg (N : ℕ) : 0 ≤ D.CDelta N := by
  have := D.CB_nonneg N
  rw [CDelta]; positivity

lemma abs_DeltaR_le {N : ℕ} {y : Fin n → ℝ} (hy : y ∈ closedBall (0 : Fin n → ℝ) (D.rad N)) :
    |DeltaR f y| ≤ D.CDelta N * ‖y‖ ^ n := by
  have h := (D.van_DeltaR N).val y hy
  rwa [Real.norm_eq_abs] at h

end Estimates3

end SmoothData

/-! ### The leading-form estimate (the paper's Lemma 4.1 `C³` clause and Lemma 4.3) -/

namespace SmoothData3

section Lead3

variable {m : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)} (D3 : SmoothData3 f)

local notation "n" => m + 1

/-- The pointwise algebraic identity behind the estimate: after clearing `(A-I)`, the
difference `Ñ - Δ·N²` is a sum of `n+1` terms, each carrying either the correction
`E_j = c̃_j - c⁰_j Δ` (of order `n+1`) against the quadratic `q(fʲ)`, or `Δ` (of order `n`)
against the *cubic* discrepancy `q(fʲ y) - q₂(Aʲ y)`. -/
lemma mulVec_Ntil_sub_lead (hA : IsUnit (Amat f - 1)) (y : Fin n → ℝ) :
    (Amat f - 1).mulVec (Ntil f y - DeltaR f y • NtwoR D3 y)
      = -∑ j ∈ Finset.range (n + 1),
          ((cct f j y - (Amat f).charpoly.coeff j * DeltaR f y) • nonlin f (f^[j] y)
            + ((Amat f).charpoly.coeff j * DeltaR f y) •
                (nonlin f (f^[j] y) - D3.q₂ (((linPart f) ^ j) y))) := by
  classical
  rw [Matrix.mulVec_sub, mulVec_Ntil, Matrix.mulVec_smul, mulVec_NtwoR D3 hA,
    smul_neg, sub_neg_eq_add, Finset.smul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Amat_pow_mulVec, smul_smul]
  module

/-- **Ob `G`.**  `‖Ñ(y) - Δ(y)·N²(y)‖ ≤ C‖y‖^{n+3}`. -/
theorem exists_lead_bound {N : ℕ} (hN : n + 1 ≤ N) (hA : IsUnit (Amat f - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ closedBall (0 : Fin n → ℝ) (D3.toSmoothData.rad N),
      ‖Ntil f y - DeltaR f y • NtwoR D3 y‖ ≤ C * ‖y‖ ^ (n + 3) := by
  classical
  set D : SmoothData f := D3.toSmoothData with hDdef
  -- (a) clearing `(A - I)`
  have hdet : IsUnit (Amat f - 1).det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hmul : (Amat f - 1)⁻¹ * (Amat f - 1) = 1 := Matrix.nonsing_inv_mul _ hdet
  set B : ℝ := ‖(mulVecCLM ((Amat f - 1)⁻¹) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ with hBdef
  have hB0 : 0 ≤ B := norm_nonneg _
  have hinv : ∀ w : Fin n → ℝ, ‖w‖ ≤ B * ‖(Amat f - 1).mulVec w‖ := by
    intro w
    have hw : (mulVecCLM ((Amat f - 1)⁻¹) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        ((Amat f - 1).mulVec w) = w := by
      rw [mulVecCLM_apply, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
    calc ‖w‖ = ‖(mulVecCLM ((Amat f - 1)⁻¹) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
              ((Amat f - 1).mulVec w)‖ := by rw [hw]
      _ ≤ B * ‖(Amat f - 1).mulVec w‖ := ContinuousLinearMap.le_opNorm _ _
  -- (b) the ingredients
  choose CE hCE0 hCEv using fun j : Fin (n + 1) =>
    D.cct_sub_leading hN (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)
  set Etot : ℝ := ∑ j : Fin (n + 1), CE j with hEtot
  have hEtot0 : 0 ≤ Etot := Finset.sum_nonneg fun j _ => hCE0 j
  set Cq : ℝ := D.K * (D.L ^ N) ^ 2 with hCq
  have hCq0 : (0:ℝ) ≤ Cq := mul_nonneg D.hK (sq_nonneg _)
  set Cs : ℝ := (D.K * (D.L ^ N) ^ 2) *
    ∑ i ∈ Finset.range (N + 1), (max ‖linPart f‖ 1) ^ i with hCs
  have hCs0 : (0:ℝ) ≤ Cs := by
    refine mul_nonneg hCq0 (Finset.sum_nonneg fun i _ => ?_)
    exact pow_nonneg (le_trans zero_le_one (le_max_right _ _)) i
  set Cc : ℝ := ∑ j ∈ Finset.range (n + 1), |(Amat f).charpoly.coeff j| with hCc
  have hCc0 : 0 ≤ Cc := Finset.sum_nonneg fun j _ => abs_nonneg _
  set LN : ℝ := D.L ^ N with hLN
  have hLN0 : (0:ℝ) ≤ LN := by rw [hLN]; exact pow_nonneg D.L_pos.le N
  -- powers of the linear part
  have hpowbd : ∀ (j : ℕ) (y : Fin n → ℝ), ‖((linPart f) ^ j) y‖ ≤ D.L ^ j * ‖y‖ := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
        intro y
        have hstep : ((linPart f) ^ (j + 1)) y = linPart f (((linPart f) ^ j) y) := by
          rw [pow_succ']; rfl
        rw [hstep]
        calc ‖linPart f (((linPart f) ^ j) y)‖
            ≤ ‖linPart f‖ * ‖((linPart f) ^ j) y‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ D.L * (D.L ^ j * ‖y‖) :=
              mul_le_mul D.norm_linPart_le (ih y) (norm_nonneg _) D.L_pos.le
          _ = D.L ^ (j + 1) * ‖y‖ := by rw [pow_succ]; ring
  have hpowN : ∀ (j : ℕ), j ≤ N → ∀ y : Fin n → ℝ, ‖((linPart f) ^ j) y‖ ≤ LN * ‖y‖ := by
    intro j hj y
    refine le_trans (hpowbd j y) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg y))
    rw [hLN]; exact pow_le_pow_right₀ D.hL hj
  have hpowR : ∀ (j : ℕ), j ≤ N → ∀ y ∈ closedBall (0 : Fin n → ℝ) (D.rad N),
      ‖((linPart f) ^ j) y‖ ≤ D.R := by
    intro j hj y hy
    rw [mem_closedBall, dist_zero_right] at hy
    refine le_trans (hpowN j hj y) ?_
    calc LN * ‖y‖ ≤ LN * D.rad N := mul_le_mul_of_nonneg_left hy hLN0
      _ ≤ D.R := by
          have hLne : D.L ≠ 0 := D.L_pos.ne'
          have heq : D.L ^ N * (D.R / D.L ^ (N + 1)) = D.R / D.L := by
            rw [pow_succ]; field_simp
          rw [hLN, SmoothData.rad, heq, div_le_iff₀ D.L_pos]
          nlinarith [D.hR.le, D.hL]
  -- the three pointwise ingredients
  have hEbd : ∀ j ∈ Finset.range (n + 1), ∀ y ∈ closedBall (0 : Fin n → ℝ) (D.rad N),
      |cct f j y - (Amat f).charpoly.coeff j * DeltaR f y| ≤ Etot * ‖y‖ ^ (n + 1) := by
    intro j hj y hy
    have hjlt : j < n + 1 := Finset.mem_range.mp hj
    set jf : Fin (n + 1) := ⟨j, hjlt⟩ with hjf
    have h := (hCEv jf).val y hy
    rw [Real.norm_eq_abs] at h
    refine le_trans h (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact Finset.single_le_sum (f := CE) (fun k _ => hCE0 k) (Finset.mem_univ jf)
  have hqbd : ∀ j ∈ Finset.range (n + 1), ∀ y ∈ closedBall (0 : Fin n → ℝ) (D.rad N),
      ‖nonlin f (f^[j] y)‖ ≤ Cq * ‖y‖ ^ 2 := by
    intro j hj y hy
    have hjN : j ≤ N := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) (by omega)
    exact (D.van_nonlin_comp_iter hjN).val y hy
  set Ccub : ℝ := D3.K₃ * LN ^ 3 + D3.K₂ * (LN + LN) * Cs with hCcub
  have hCcub0 : 0 ≤ Ccub := by
    have := D3.hK₃; have := D3.hK₂
    rw [hCcub]; positivity
  have hcub : ∀ j ∈ Finset.range (n + 1), ∀ y ∈ closedBall (0 : Fin n → ℝ) (D.rad N),
      ‖nonlin f (f^[j] y) - D3.q₂ (((linPart f) ^ j) y)‖ ≤ Ccub * ‖y‖ ^ 3 := by
    intro j hj y hy
    have hjN : j ≤ N := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) (by omega)
    have hyn : ‖y‖ ≤ D.rad N := by rwa [mem_closedBall, dist_zero_right] at hy
    have hy0 : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
    -- `f^j y` is in the ball, and its norm is at most `LN‖y‖`
    have hfj : ‖f^[j] y‖ ≤ D.R := by
      have := D.iter_mem hjN hy
      rwa [mem_closedBall, dist_zero_right] at this
    have hfjn : ‖f^[j] y‖ ≤ LN * ‖y‖ := D.iter_norm_le hjN hy
    have hAj : ‖((linPart f) ^ j) y‖ ≤ D.R := hpowR j hjN y hy
    have hAjn : ‖((linPart f) ^ j) y‖ ≤ LN * ‖y‖ := hpowN j hjN y
    -- the cubic remainder
    have h1 : ‖nonlin f (f^[j] y) - D3.q₂ (f^[j] y)‖ ≤ D3.K₃ * LN ^ 3 * ‖y‖ ^ 3 := by
      refine le_trans (D3.hq₂rem _ hfj) ?_
      have : ‖f^[j] y‖ ^ 3 ≤ (LN * ‖y‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hfjn 3
      calc D3.K₃ * ‖f^[j] y‖ ^ 3 ≤ D3.K₃ * (LN * ‖y‖) ^ 3 :=
            mul_le_mul_of_nonneg_left this D3.hK₃
        _ = D3.K₃ * LN ^ 3 * ‖y‖ ^ 3 := by ring
    -- the bilinear comparison
    have h2 : ‖D3.q₂ (f^[j] y) - D3.q₂ (((linPart f) ^ j) y)‖
        ≤ D3.K₂ * (LN + LN) * Cs * ‖y‖ ^ 3 := by
      have hlip := D3.hq₂lip (f^[j] y) (((linPart f) ^ j) y) hfj hAj
      have hsub : ‖f^[j] y - ((linPart f) ^ j) y‖ ≤ Cs * ‖y‖ ^ 2 :=
        (D.van_iter_sub_pow N j hjN).val y hy
      refine le_trans hlip ?_
      have hsum : ‖f^[j] y‖ + ‖((linPart f) ^ j) y‖ ≤ LN * ‖y‖ + LN * ‖y‖ :=
        add_le_add hfjn hAjn
      calc D3.K₂ * (‖f^[j] y‖ + ‖((linPart f) ^ j) y‖) * ‖f^[j] y - ((linPart f) ^ j) y‖
          ≤ D3.K₂ * (LN * ‖y‖ + LN * ‖y‖) * (Cs * ‖y‖ ^ 2) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hsum D3.hK₂) hsub
              (norm_nonneg _) (mul_nonneg D3.hK₂ (by positivity))
        _ = D3.K₂ * (LN + LN) * Cs * ‖y‖ ^ 3 := by ring
    calc ‖nonlin f (f^[j] y) - D3.q₂ (((linPart f) ^ j) y)‖
        ≤ ‖nonlin f (f^[j] y) - D3.q₂ (f^[j] y)‖
            + ‖D3.q₂ (f^[j] y) - D3.q₂ (((linPart f) ^ j) y)‖ := by
          have := norm_add_le (nonlin f (f^[j] y) - D3.q₂ (f^[j] y))
            (D3.q₂ (f^[j] y) - D3.q₂ (((linPart f) ^ j) y))
          simpa using this
      _ ≤ D3.K₃ * LN ^ 3 * ‖y‖ ^ 3 + D3.K₂ * (LN + LN) * Cs * ‖y‖ ^ 3 := add_le_add h1 h2
      _ = Ccub * ‖y‖ ^ 3 := by rw [hCcub]; ring
  -- assemble
  refine ⟨B * ((n + 1) * (Etot * Cq) + Cc * (D.CDelta N * Ccub)), ?_, ?_⟩
  · have := D.CDelta_nonneg N
    positivity
  intro y hy
  have hy0 : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
  have hterm : ∀ j ∈ Finset.range (n + 1),
      ‖(cct f j y - (Amat f).charpoly.coeff j * DeltaR f y) • nonlin f (f^[j] y)
        + ((Amat f).charpoly.coeff j * DeltaR f y) •
            (nonlin f (f^[j] y) - D3.q₂ (((linPart f) ^ j) y))‖
      ≤ (Etot * Cq + |(Amat f).charpoly.coeff j| * (D.CDelta N * Ccub)) * ‖y‖ ^ (n + 3) := by
    intro j hj
    have hE := hEbd j hj y hy
    have hq := hqbd j hj y hy
    have hc := hcub j hj y hy
    have hΔ := D.abs_DeltaR_le hy
    have hA1 : ‖(cct f j y - (Amat f).charpoly.coeff j * DeltaR f y) • nonlin f (f^[j] y)‖
        ≤ (Etot * Cq) * ‖y‖ ^ (n + 3) := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |cct f j y - (Amat f).charpoly.coeff j * DeltaR f y| * ‖nonlin f (f^[j] y)‖
          ≤ (Etot * ‖y‖ ^ (n + 1)) * (Cq * ‖y‖ ^ 2) :=
            mul_le_mul hE hq (norm_nonneg _) (by positivity)
        _ = (Etot * Cq) * ‖y‖ ^ (n + 3) := by ring
    have hA2 : ‖((Amat f).charpoly.coeff j * DeltaR f y) •
          (nonlin f (f^[j] y) - D3.q₂ (((linPart f) ^ j) y))‖
        ≤ (|(Amat f).charpoly.coeff j| * (D.CDelta N * Ccub)) * ‖y‖ ^ (n + 3) := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
      calc |(Amat f).charpoly.coeff j| * |DeltaR f y|
              * ‖nonlin f (f^[j] y) - D3.q₂ (((linPart f) ^ j) y)‖
          ≤ |(Amat f).charpoly.coeff j| * (D.CDelta N * ‖y‖ ^ n) * (Ccub * ‖y‖ ^ 3) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hΔ (abs_nonneg _)) hc
              (norm_nonneg _)
              (mul_nonneg (abs_nonneg _) (mul_nonneg (D.CDelta_nonneg N) (by positivity)))
        _ = (|(Amat f).charpoly.coeff j| * (D.CDelta N * Ccub)) * ‖y‖ ^ (n + 3) := by ring
    exact le_trans (norm_add_le _ _) (by linarith [hA1, hA2])
  have hsum : ‖-∑ j ∈ Finset.range (n + 1),
      ((cct f j y - (Amat f).charpoly.coeff j * DeltaR f y) • nonlin f (f^[j] y)
        + ((Amat f).charpoly.coeff j * DeltaR f y) •
            (nonlin f (f^[j] y) - D3.q₂ (((linPart f) ^ j) y)))‖
      ≤ ((n + 1) * (Etot * Cq) + Cc * (D.CDelta N * Ccub)) * ‖y‖ ^ (n + 3) := by
    rw [norm_neg]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right (le_of_eq ?_) (by positivity)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_mul, ← hCc]
    push_cast
    ring
  calc ‖Ntil f y - DeltaR f y • NtwoR D3 y‖
      ≤ B * ‖(Amat f - 1).mulVec (Ntil f y - DeltaR f y • NtwoR D3 y)‖ := hinv _
    _ = B * ‖-∑ j ∈ Finset.range (n + 1),
          ((cct f j y - (Amat f).charpoly.coeff j * DeltaR f y) • nonlin f (f^[j] y)
            + ((Amat f).charpoly.coeff j * DeltaR f y) •
                (nonlin f (f^[j] y) - D3.q₂ (((linPart f) ^ j) y)))‖ := by
        rw [D3.mulVec_Ntil_sub_lead hA y]
    _ ≤ B * (((n + 1) * (Etot * Cq) + Cc * (D.CDelta N * Ccub)) * ‖y‖ ^ (n + 3)) :=
        mul_le_mul_of_nonneg_left hsum hB0
    _ = B * ((n + 1) * (Etot * Cq) + Cc * (D.CDelta N * Ccub)) * ‖y‖ ^ (n + 3) := by ring

end Lead3

end SmoothData3

end MPE