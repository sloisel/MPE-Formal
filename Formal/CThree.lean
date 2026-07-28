import Mathlib
import Formal.Smooth
import Formal.Algebra
import Formal.Main
import Formal.General
import Formal.Reduce
import Formal.Corollary

/-!
# The `C³` iteration

The polynomial development assumes `f x = A x + q x` with `q` a polynomial map, and extracts
every estimate by counting degrees.  This file replaces the degree count by an analytic one,
so that Theorem 4.9 applies to an arbitrary map that is `C³` near its fixed point.

The plan is `../../appendix.tex` §11, Remark `rem:noquad`.  Two facts carry the whole
argument, and neither needs a Taylor expansion:

* the **exact** identity `(A - I) Ñ = -∑_j c̃_j q(f^j)` where `q = f - A`, which comes from
  `adj(U) U = (det U) I` and holds pointwise for any map at all;
* the **one** structural estimate `c̃_j = p_j Δ + r_j` with `r_j` vanishing to order `n+1`,
  which comes from Cramer's rule, `Van.det_sub`, and Cayley–Hamilton.

This file supplies the analytic input to the second: a bundle of constants extracted once
from the `C³` hypothesis, and the propagation of `Van` through the iterates `f^j`.
-/

set_option maxHeartbeats 1000000

namespace MPE

open Metric Set MeasureTheory

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G]

/-! ### The analytic data

Every constant the `C³` argument needs, extracted once.  The last field — `Df` is Lipschitz
at `0` — is the *only* smoothness used beyond `C¹`; it is what puts `q = f - Df 0` in
`Van 1`.  In particular `C^{1,1}` would suffice, and `C³` is assumed only to match the
paper. -/
structure SmoothData (f : G → G) : Type where
  /-- the radius on which every estimate holds -/
  R : ℝ
  /-- a Lipschitz constant for `f`, at least `1` so that powers are monotone -/
  L : ℝ
  /-- a Lipschitz constant for `Df` at the origin -/
  K : ℝ
  hR : 0 < R
  hL : 1 ≤ L
  hK : 0 ≤ K
  hf0 : f 0 = 0
  /-- `f` is measurable.  This is *not* part of "`f` is `C³` near `0`": it is needed only
  because the dithered process is defined by the global map, and a `C³`-on-a-ball hypothesis
  says nothing about `f` elsewhere.  Any continuous iteration satisfies it. -/
  hmeas : Measurable f
  hdiff : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ f z
  hbd : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ f z‖ ≤ L
  hlip : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ f z - fderiv ℝ f 0‖ ≤ K * ‖z‖

/-- **The analytic data exists.**  A map that is `C²` on a ball around a fixed point admits a
`SmoothData`: the bounds come from continuity of `Df` and `D²f` on a compact sub-ball, and
the Lipschitz bound on `Df` from the mean value inequality applied to `z ↦ Df z - Df 0`.
`C²` is exactly what the paper's Theorem 4.7 assumes, and it is all the development ever
uses: no third derivative appears anywhere downstream of this proof. -/
theorem nonempty_smoothData [FiniteDimensional ℝ G] {f : G → G} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 2 f (ball (0 : G) R₀)) :
    Nonempty (SmoothData f) := by
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
  -- `f` is differentiable on the closed ball
  have hdiff : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ f z := fun z hz =>
    (hf.contDiffAt (hopen.mem_nhds (hsub hz))).differentiableAt (by norm_num)
  -- `Df` is `C¹` on the open ball, hence differentiable and continuous on the closed one
  have hfd : ContDiffOn ℝ 1 (fderiv ℝ f) (ball (0 : G) R₀) := hf.fderiv_of_isOpen hopen (by
    norm_num)
  have hdiff2 : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ (fderiv ℝ f) z := fun z hz =>
    (hfd.contDiffAt (hopen.mem_nhds (hsub hz))).differentiableAt (by norm_num)
  -- the two compactness bounds
  obtain ⟨L₀, hL₀0, hL₀⟩ := exists_fderiv_bound_of_contDiffOn (g := f) hR.le
    ((hf.mono hsub).of_le (by norm_num)) hdiff
    ((hf.continuousOn_fderiv_of_isOpen hopen (by norm_num)).mono hsub)
  obtain ⟨K, hK0, hK⟩ := exists_fderiv_bound_of_contDiffOn (g := fderiv ℝ f) hR.le
    ((hfd.mono hsub).of_le (by norm_num)) hdiff2
    (((hfd.fderiv_of_isOpen hopen (by norm_num)).continuousOn (n := 0)).mono hsub)
  -- the Lipschitz bound on `Df`, by the mean value inequality
  have hlip : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ f z - fderiv ℝ f 0‖ ≤ K * ‖z‖ := by
    intro z hz
    refine norm_le_of_fderiv_le_const (g := fun w => fderiv ℝ f w - fderiv ℝ f 0) hK0
      (by simp) (fun w hw => (hdiff2 w hw).sub_const _) (fun w hw => ?_) ?_
    · have hd : HasFDerivAt (fun w => fderiv ℝ f w - fderiv ℝ f 0)
          (fderiv ℝ (fderiv ℝ f) w) w := (hdiff2 w hw).hasFDerivAt.sub_const _
      rw [hd.fderiv]
      exact hK w hw
    · rw [mem_closedBall, dist_zero_right] at hz; exact hz
  exact ⟨{ R := R, L := max L₀ 1, K := K, hR := hR, hL := le_max_right _ _, hK := hK0,
           hf0 := hf0, hmeas := hmeas, hdiff := hdiff,
           hbd := fun z hz => le_trans (hL₀ z hz) (le_max_left _ _), hlip := hlip }⟩

/-- The linear part `A = Df(0)`, as a continuous linear map. -/
noncomputable def linPart (f : G → G) : G →L[ℝ] G := fderiv ℝ f 0

/-- The nonlinear part `q = f - A`.  It vanishes to order `2`: this is the *only* consequence
of smoothness the whole `C³` argument uses. -/
noncomputable def nonlin (f : G → G) (x : G) : G := f x - linPart f x

namespace SmoothData

variable {f : G → G} (D : SmoothData f)

lemma norm_linPart_le : ‖linPart f‖ ≤ D.L := by
  have h0 : (0 : G) ∈ closedBall (0 : G) D.R := by
    rw [mem_closedBall, dist_self]; exact D.hR.le
  exact D.hbd 0 h0

/-- **`q` vanishes to order `2`.**  This is `van_sub_fderiv` applied to `f`. -/
theorem van_nonlin : Van D.R 1 D.K (nonlin f) :=
  van_sub_fderiv D.hK D.hf0 D.hdiff D.hlip

/-! ### The iterates

All of `f^0,…,f^N` are controlled on the shrunken ball of radius `R/L^(N+1)`, and each
differs from the corresponding power of `A` by something vanishing to order `2`.  That last
fact is the analytic content of the whole file: it is what turns the columns of the MPE
matrix into "linear part plus `Van 1`". -/

/-- The radius on which `f^0,…,f^N` are all controlled. -/
noncomputable def rad (N : ℕ) : ℝ := D.R / D.L ^ (N + 1)

lemma L_pos : (0:ℝ) < D.L := lt_of_lt_of_le one_pos D.hL

lemma rad_pos (N : ℕ) : 0 < D.rad N := div_pos D.hR (pow_pos D.L_pos _)

lemma rad_le (N : ℕ) : D.rad N ≤ D.R := by
  rw [rad, div_le_iff₀ (pow_pos D.L_pos _)]
  nlinarith [D.hR.le, one_le_pow₀ D.hL (n := N + 1)]

lemma norm_le_of_mem_rad {N : ℕ} {y : G} (hy : y ∈ closedBall (0 : G) (D.rad N)) {j : ℕ}
    (hj : j ≤ N + 1) : ‖y‖ ≤ D.R / D.L ^ j := by
  rw [mem_closedBall, dist_zero_right, rad] at hy
  exact hy.trans (div_le_div_of_nonneg_left D.hR.le (pow_pos D.L_pos j)
    (pow_le_pow_right₀ D.hL hj))

lemma iter_norm_le {N j : ℕ} (hj : j ≤ N) {y : G} (hy : y ∈ closedBall (0 : G) (D.rad N)) :
    ‖f^[j] y‖ ≤ D.L ^ N * ‖y‖ := by
  refine (norm_iter_le D.hR.le D.hL D.hf0 D.hdiff D.hbd j y
    (D.norm_le_of_mem_rad hy (le_trans hj (Nat.le_succ N)))).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ D.hL hj) (norm_nonneg y)

lemma iter_mem {N j : ℕ} (hj : j ≤ N) {y : G} (hy : y ∈ closedBall (0 : G) (D.rad N)) :
    f^[j] y ∈ closedBall (0 : G) D.R :=
  iter_mem_closedBall D.hR.le D.hL D.hf0 D.hdiff D.hbd
    (D.norm_le_of_mem_rad hy (Nat.succ_le_succ hj))

lemma iter_diff {N j : ℕ} (hj : j ≤ N) {y : G} (hy : y ∈ closedBall (0 : G) (D.rad N)) :
    DifferentiableAt ℝ (f^[j]) y :=
  (iter_differentiableAt D.hR.le D.hL D.hf0 D.hdiff D.hbd j y
    (D.norm_le_of_mem_rad hy (le_trans hj (Nat.le_succ N)))).1

lemma iter_fderiv_le {N j : ℕ} (hj : j ≤ N) {y : G} (hy : y ∈ closedBall (0 : G) (D.rad N)) :
    ‖fderiv ℝ (f^[j]) y‖ ≤ D.L ^ N :=
  ((iter_differentiableAt D.hR.le D.hL D.hf0 D.hdiff D.hbd j y
    (D.norm_le_of_mem_rad hy (le_trans hj (Nat.le_succ N)))).2).trans
      (pow_le_pow_right₀ D.hL hj)

/-- `q ∘ f^j` vanishes to order `2`, uniformly for `j ≤ N`. -/
theorem van_nonlin_comp_iter {N j : ℕ} (hj : j ≤ N) :
    Van (D.rad N) 1 (D.K * (D.L ^ N) ^ 2) (fun y => nonlin f (f^[j] y)) :=
  Van.comp (pow_nonneg D.L_pos.le N) D.hK D.van_nonlin
    (fun _ hy => D.iter_mem hj hy) (fun _ hy => D.iter_diff hj hy)
    (fun _ hy => D.iter_norm_le hj hy) (fun _ hy => D.iter_fderiv_le hj hy)

/-- **The iterates are linear to second order.**  `f^j(y) - A^j y` vanishes to order `2`,
uniformly for `j ≤ N`.  Induction on `j` through
`f^{j+1} - A^{j+1} = q∘f^j + A·(f^j - A^j)`. -/
theorem van_iter_sub_pow (N : ℕ) :
    ∀ j ≤ N, Van (D.rad N)
      (1 : ℕ)
      ((D.K * (D.L ^ N) ^ 2) * ∑ i ∈ Finset.range (N + 1), (max ‖linPart f‖ 1) ^ i)
      (fun y => f^[j] y - (linPart f ^ j) y) := by
  set M : ℝ := max ‖linPart f‖ 1 with hM
  have hM1 : (1:ℝ) ≤ M := le_max_right _ _
  have hM0 : (0:ℝ) ≤ M := le_trans zero_le_one hM1
  set c : ℝ := D.K * (D.L ^ N) ^ 2 with hc
  have hc0 : (0:ℝ) ≤ c := mul_nonneg D.hK (by positivity)
  have hCj : ∀ j : ℕ, (0:ℝ) ≤ c * ∑ i ∈ Finset.range j, M ^ i := fun j =>
    mul_nonneg hc0 (Finset.sum_nonneg fun i _ => pow_nonneg hM0 i)
  have hpow : ∀ (j : ℕ) (y : G), (linPart f ^ (j + 1)) y = (linPart f) ((linPart f ^ j) y) := by
    intro j y
    rw [pow_succ']
    rfl
  -- the running constants
  have key : ∀ j ≤ N, Van (D.rad N) 1 (c * ∑ i ∈ Finset.range j, M ^ i)
      (fun y => f^[j] y - (linPart f ^ j) y) := by
    intro j
    induction j with
    | zero =>
        intro _
        have hfun : (fun y => f^[0] y - (linPart f ^ 0) y) = fun _ : G => (0 : G) := by
          funext y; simp
        rw [hfun]
        simpa using (Van.zero_van (ρ := D.rad N) (k := 1) (E := G) (F := G))
    | succ j ih =>
        intro hj
        have hjN : j ≤ N := le_trans (Nat.le_succ j) hj
        have h1 := D.van_nonlin_comp_iter hjN
        have h2 := Van.clm_comp (linPart f) (hCj j) (ih hjN)
        have h2' : Van (D.rad N) 1 (M * (c * ∑ i ∈ Finset.range j, M ^ i))
            (fun y => (linPart f) (f^[j] y - (linPart f ^ j) y)) :=
          h2.mono_const (mul_le_mul_of_nonneg_right (le_max_left _ _) (hCj j))
        have hsum := h1.add h2'
        have hfun : (fun y => f^[j + 1] y - (linPart f ^ (j + 1)) y)
            = fun y => nonlin f (f^[j] y)
                + (linPart f) (f^[j] y - (linPart f ^ j) y) := by
          funext y
          rw [Function.iterate_succ_apply', hpow j y]
          simp only [nonlin, map_sub]
          abel
        rw [hfun]
        refine hsum.mono_const (le_of_eq ?_)
        rw [geom_sum_succ, hc]
        ring
  intro j hj
  refine (key j hj).mono_const ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hc0
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro i _ _; exact pow_nonneg hM0 i

/-- The iterates themselves vanish linearly. -/
theorem van_iter {N j : ℕ} (hj : j ≤ N) : Van (D.rad N) 0 (D.L ^ N) (f^[j]) where
  diff := fun _ hy => D.iter_diff hj hy
  val := fun _ hy => by simpa using D.iter_norm_le hj hy
  der := fun _ hy => by simpa using D.iter_fderiv_le hj hy

end SmoothData

/-! ### The MPE cycle for a smooth map

Everything below is defined pointwise, exactly as in the polynomial development but with
`MvPolynomial` replaced by "function of `y`".  Two things make the analytic argument work:

* Cramer's rule turns every cleared coefficient into a *determinant* of a matrix whose entries
  vanish linearly, which is what `Van.det` and `Van.det_sub` want (no adjugate, hence no row
  of constants);
* the self-consistency relation `∑_j c̃_j u_j = 0` is `U · adj U = (det U)·I`, so it is already
  available for an arbitrary commutative ring — `MPE.selfConsistency`. -/

section Construction

variable {m : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}

local notation "n" => m + 1

/-- `u_j = f^{j+1} - f^j`. -/
noncomputable def uu (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (j : ℕ) (y : Fin n → ℝ) :
    Fin n → ℝ := f^[j + 1] y - f^[j] y

/-- The linear part of the iteration, as a matrix — this is the `A` of the paper, and the
only thing about `f` that the leading-order analysis sees. -/
noncomputable def Amat (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix' (fderiv ℝ f 0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).toLinearMap

lemma Amat_mulVec (y : Fin n → ℝ) : (Amat f).mulVec y = fderiv ℝ f 0 y :=
  LinearMap.toMatrix'_mulVec _ _

lemma Amat_pow_mulVec (j : ℕ) (y : Fin n → ℝ) :
    ((Amat f) ^ j).mulVec y = ((linPart f) ^ j) y := by
  induction j generalizing y with
  | zero => simp [Matrix.one_mulVec]
  | succ j ih =>
      have hcomm : ((Amat f) ^ (j + 1)) = (Amat f) * (Amat f) ^ j := by rw [pow_succ']
      rw [hcomm, ← Matrix.mulVec_mulVec, ih, pow_succ' (linPart f)]
      exact Amat_mulVec _

/-- `u_j`'s linear part, `A^j (A - I) y`. -/
noncomputable def uuLin (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (j : ℕ) (y : Fin n → ℝ) :
    Fin n → ℝ := ((Amat f - 1) * (Amat f) ^ j).mulVec y

lemma uuLin_eq (j : ℕ) (y : Fin n → ℝ) :
    uuLin f j y = ((linPart f) ^ (j + 1)) y - ((linPart f) ^ j) y := by
  have hexp : (Amat f - 1) * (Amat f) ^ j = (Amat f) ^ (j + 1) - (Amat f) ^ j := by
    rw [sub_mul, one_mul, pow_succ']
  rw [uuLin, hexp, Matrix.sub_mulVec, Amat_pow_mulVec, Amat_pow_mulVec]

/-- Multiplication by a matrix, as a continuous linear map. -/
noncomputable def mulVecCLM (M : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap M.mulVecLin

lemma mulVecCLM_apply (M : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    mulVecCLM M y = M.mulVec y := rfl

/-! #### The four matrices

`U` has columns `u_0,…,u_{n-1}`; `K` has their linear parts.  `Ucol j` and `Kcol j` are the
same with column `j` replaced by `-u_n` — by Cramer's rule these are exactly the matrices
whose determinants are the cleared coefficients. -/

/-- The MPE matrix at `y`. -/
noncomputable def Ueval (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i k => uu f (k : ℕ) y i

/-- The Krylov matrix at `y`; its determinant is `Δ`. -/
noncomputable def Keval (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i k => uuLin f (k : ℕ) y i

/-- `Δ(y) = det [(A-I)y, (A-I)Ay, …, (A-I)A^{n-1}y]`.  Depends on `A` alone. -/
noncomputable def DeltaR (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (y : Fin n → ℝ) : ℝ :=
  (Keval f y).det

/-- The MPE matrix as a matrix of *functions*, with column `j` replaced by `-u_n`. -/
noncomputable def Ucol (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin n) :
    Matrix (Fin n) (Fin n) ((Fin n → ℝ) → ℝ) :=
  fun i k => if k = j then (fun y => -(uu f n y i)) else (fun y => uu f (k : ℕ) y i)

/-- The same for the linear model. -/
noncomputable def Kcol (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin n) :
    Matrix (Fin n) (Fin n) ((Fin n → ℝ) → ℝ) :=
  fun i k => if k = j then (fun y => -(uuLin f n y i)) else (fun y => uuLin f (k : ℕ) y i)

/-- The MPE matrix and its model, as matrices of functions. -/
noncomputable def Umat (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) :
    Matrix (Fin n) (Fin n) ((Fin n → ℝ) → ℝ) := fun i k => fun y => uu f (k : ℕ) y i

noncomputable def Kmat (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) :
    Matrix (Fin n) (Fin n) ((Fin n → ℝ) → ℝ) := fun i k => fun y => uuLin f (k : ℕ) y i

lemma Ucol_eval (j : Fin n) (y : Fin n → ℝ) :
    (fun i k => Ucol f j i k y) = (Ueval f y).updateCol j (fun i => -(uu f n y i)) := by
  funext i k
  rw [Matrix.updateCol_apply, Ucol]
  by_cases h : k = j <;> simp [h, Ueval]

lemma Kcol_eval (j : Fin n) (y : Fin n → ℝ) :
    (fun i k => Kcol f j i k y) = (Keval f y).updateCol j (fun i => -(uuLin f n y i)) := by
  funext i k
  rw [Matrix.updateCol_apply, Kcol]
  by_cases h : k = j <;> simp [h, Keval]

lemma Umat_eval (y : Fin n → ℝ) : (fun i k => Umat f i k y) = Ueval f y := rfl

lemma Kmat_eval (y : Fin n → ℝ) : (fun i k => Kmat f i k y) = Keval f y := rfl

/-- **The cleared coefficients.**  For `j < n`, Cramer's rule; `c̃_n = det U`. -/
noncomputable def cct (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (j : ℕ) (y : Fin n → ℝ) :
    ℝ :=
  if h : j < n then (Ueval f y).adjugate.mulVec (fun i => -(uu f n y i)) ⟨j, h⟩
  else (Ueval f y).det

lemma cct_eq_det (j : Fin n) (y : Fin n → ℝ) :
    cct f (j : ℕ) y = Matrix.det (fun i k => Ucol f j i k y) := by
  rw [cct, dif_pos j.isLt, Ucol_eval, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec,
    Fin.eta]

lemma cct_top (y : Fin n → ℝ) : cct f n y = Matrix.det (fun i k => Umat f i k y) := by
  rw [cct, dif_neg (lt_irrefl n), Umat_eval]

/-! #### The linear determinants, in closed form

Cayley–Hamilton says `-u_n^{lin} = K·p` with `p` the characteristic-polynomial coefficients;
Cramer then gives `det(K[col j ← K p]) = (det K)·p_j`. -/

lemma Keval_mulVec_charpoly (y : Fin n → ℝ) :
    (Keval f y).mulVec (fun k => (Amat f).charpoly.coeff (k : ℕ))
      = fun i => -(uuLin f n y i) := by
  funext i
  have hcomb := congrFun (krylov_charpoly_combination (Amat f) y) i
  have hmv : (Keval f y).mulVec (fun k => (Amat f).charpoly.coeff (k : ℕ)) i
      = ∑ k : Fin n, uuLin f (k : ℕ) y i * (Amat f).charpoly.coeff (k : ℕ) := rfl
  rw [hmv]
  have hsum : ∑ k : Fin n, uuLin f (k : ℕ) y i * (Amat f).charpoly.coeff (k : ℕ)
      = ∑ k ∈ Finset.range n, (Amat f).charpoly.coeff k • (uuLin f k y i) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => (Amat f).charpoly.coeff k • (uuLin f k y i)) n]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul]; ring
  rw [hsum]
  have hpi : ∀ k : ℕ, (Amat f).charpoly.coeff k • (uuLin f k y i)
      = ((Amat f).charpoly.coeff k • (((Amat f - 1) * (Amat f) ^ k).mulVec y)) i := fun k => rfl
  simp only [hpi]
  rw [← Finset.sum_apply]
  rw [hcomb]
  rfl

/-- **The linear determinant, evaluated.**  This is `(★)`'s leading term. -/
theorem det_Kcol (j : Fin n) (y : Fin n → ℝ) :
    Matrix.det (fun i k => Kcol f j i k y)
      = (Amat f).charpoly.coeff (j : ℕ) * DeltaR f y := by
  rw [Kcol_eval, ← Keval_mulVec_charpoly, ← Matrix.cramer_apply,
    Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [DeltaR, smul_eq_mul, mul_comm]

theorem det_Kmat (y : Fin n → ℝ) : Matrix.det (fun i k => Kmat f i k y) = DeltaR f y := rfl

/-- The Krylov matrix of `Δ` is `(A - I)` times the plain Krylov matrix. -/
lemma Keval_eq (y : Fin n → ℝ) : Keval f y = (Amat f - 1) * krylov (Amat f) y := by
  funext i k
  have h1 : uuLin f (k : ℕ) y
      = Matrix.mulVec (Amat f - 1) (Matrix.mulVec ((Amat f) ^ (k : ℕ)) y) := by
    rw [uuLin, Matrix.mulVec_mulVec]
  show uuLin f (k : ℕ) y i = _
  rw [h1, Matrix.mul_apply]
  rfl

/-- Hence `Δ = det(A - I) · det K_A`, and `leadConst A · det K_A = p_A(1) · Δ`. -/
lemma DeltaR_eq (y : Fin n → ℝ) :
    DeltaR f y = (Amat f - 1).det * (krylov (Amat f) y).det := by
  rw [DeltaR, Keval_eq, Matrix.det_mul]

/-- A uniform bound for the entries of the linear model `K`. -/
noncomputable def normCol (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (k : ℕ) : ℝ :=
  ‖(mulVecCLM ((Amat f - 1) * (Amat f) ^ k) : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ))‖

noncomputable def CKb (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), normCol f k

lemma normCol_nonneg (k : ℕ) : 0 ≤ normCol f k := norm_nonneg _

lemma CKb_nonneg : 0 ≤ CKb f :=
  Finset.sum_nonneg fun _ _ => normCol_nonneg _

lemma van_uuLin {ρ : ℝ} (k : ℕ) (i : Fin n) :
    Van ρ 0 (normCol f k) (fun y => uuLin f k y i) := by
  have h : Van ρ 0 (normCol f k)
      (fun y => (mulVecCLM ((Amat f - 1) * (Amat f) ^ k) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) y) :=
    Van.of_clm _
  have h2 := Van.pi_apply (normCol_nonneg k) h i
  have hfun : (fun y => ((mulVecCLM ((Amat f - 1) * (Amat f) ^ k) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) y) i) = fun y => uuLin f k y i := by
    funext y
    rw [mulVecCLM_apply, uuLin]
  rw [hfun] at h2
  exact h2

lemma van_uuLin' {ρ : ℝ} {k : ℕ} (hk : k ≤ n) (i : Fin n) :
    Van ρ 0 (CKb f) (fun y => uuLin f k y i) :=
  (van_uuLin k i).mono_const
    (Finset.single_le_sum (f := fun k => normCol f k)
      (fun _ _ => normCol_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))

/-- The entries of the linear model vanish linearly. -/
theorem van_Kcol_entry {ρ : ℝ} (j i k : Fin n) : Van ρ 0 (CKb f) (Kcol f j i k) := by
  rw [Kcol]
  by_cases h : k = j
  · simp only [h, if_pos]
    exact (van_uuLin' (le_refl _) i).neg
  · simp only [if_neg h]
    exact van_uuLin' (le_of_lt k.isLt) i

theorem van_Kmat_entry {ρ : ℝ} (i k : Fin n) : Van ρ 0 (CKb f) (Kmat f i k) :=
  van_uuLin' (le_of_lt k.isLt) i

/-! #### Measurability

The `hΨ` chain needs `σ̃` and `Ñ` measurable *globally* — the dithered process is defined by
the global map, so this cannot come from smoothness on a ball.  It comes from
`SmoothData.hmeas` instead. -/

lemma measurable_uu (hf : Measurable f) (j : ℕ) (i : Fin n) :
    Measurable (fun y => uu f j y i) := by
  have h1 : Measurable (fun y : Fin n → ℝ => f^[j + 1] y) := hf.iterate (j + 1)
  have h2 : Measurable (fun y : Fin n → ℝ => f^[j] y) := hf.iterate j
  exact (measurable_pi_apply i).comp (h1.sub h2)

lemma measurable_det_of_entries {N : ℕ} {E : Type*} [MeasurableSpace E]
    {Mm : Matrix (Fin N) (Fin N) (E → ℝ)} (h : ∀ i k, Measurable (Mm i k)) :
    Measurable (fun y => Matrix.det (fun i k => Mm i k y)) := by
  classical
  have hfun : (fun y => Matrix.det (fun i k => Mm i k y))
      = fun y => ∑ σ : Equiv.Perm (Fin N),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, Mm (σ i) i y := by
    funext y
    rw [Matrix.det_apply']
  rw [hfun]
  refine Finset.measurable_sum _ fun σ _ => measurable_const.mul ?_
  exact Finset.measurable_prod _ fun i _ => h (σ i) i

lemma measurable_cct (hf : Measurable f) (j : ℕ) : Measurable (cct f j) := by
  classical
  by_cases hj : j < n
  · have hfun : cct f j = fun y => Matrix.det (fun i k => Ucol f ⟨j, hj⟩ i k y) := by
      funext y; rw [← cct_eq_det ⟨j, hj⟩ y]
    rw [hfun]
    refine measurable_det_of_entries fun i k => ?_
    rw [Ucol]
    by_cases h : k = (⟨j, hj⟩ : Fin n)
    · rw [if_pos h]
      exact (measurable_uu hf (m + 1) i).neg
    · rw [if_neg h]
      exact measurable_uu hf (k : ℕ) i
  · have hfun : cct f j = fun y => Matrix.det (fun i k => Umat f i k y) := by
      funext y; rw [cct, dif_neg hj, Umat_eval]
    rw [hfun]
    exact measurable_det_of_entries fun i k => measurable_uu hf (k : ℕ) i

/-! #### `Ñ`, `σ̃`, and the exact identity

`selfConsistency` — `U · adj U = (det U)·I`, valid over any commutative ring — gives
`∑_j c̃_j u_j = 0` pointwise.  Substituting `u_j = (A-I)f^j + q(f^j)` turns it into an exact
expression for `(A-I)Ñ`, with no estimates and no smoothness at all. -/

/-- `Ñ = ∑_{j≤n} c̃_j f^j`. -/
noncomputable def Ntil (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (y : Fin n → ℝ) :
    Fin n → ℝ := ∑ j ∈ Finset.range (n + 1), cct f j y • (f^[j] y)

/-- `σ̃ = ∑_{j≤n} c̃_j`. -/
noncomputable def sigt (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (y : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), cct f j y

lemma measurable_sigt (hf : Measurable f) : Measurable (sigt f) :=
  Finset.measurable_sum _ fun j _ => measurable_cct hf j

lemma measurable_Ntil (hf : Measurable f) : Measurable (Ntil f) := by
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_cct hf j).smul (hf.iterate j)

/-- **The self-consistency relation `∑_{j≤n} c̃_j u_j = 0`**, pointwise. -/
theorem sum_cct_uu (y : Fin n → ℝ) :
    ∑ j ∈ Finset.range (n + 1), cct f j y • (uu f j y) = (0 : Fin n → ℝ) := by
  classical
  have hself := selfConsistency (Ueval f y) (fun i => uu f (m + 1) y i)
  have hcoe : ∀ k : Fin n, cct f (k : ℕ) y
      = (Ueval f y).adjugate.mulVec (fun i => -(uu f (m + 1) y i)) k := by
    intro k
    rw [cct, dif_pos k.isLt, Fin.eta]
  have hmv : (Ueval f y).mulVec ((Ueval f y).adjugate.mulVec
      (fun i => -(uu f (m + 1) y i))) = ∑ k : Fin n, cct f (k : ℕ) y • (uu f (k : ℕ) y) := by
    funext i
    rw [Finset.sum_apply]
    have : (Ueval f y).mulVec ((Ueval f y).adjugate.mulVec
        (fun i => -(uu f (m + 1) y i))) i
        = ∑ k : Fin n, uu f (k : ℕ) y i
            * ((Ueval f y).adjugate.mulVec (fun i => -(uu f (m + 1) y i)) k) := rfl
    rw [this]
    exact Finset.sum_congr rfl fun k _ => by rw [← hcoe k]; simp [mul_comm]
  have hdet : (Ueval f y).det • (fun i => uu f (m + 1) y i)
      = cct f (m + 1) y • (uu f (m + 1) y) := by
    rw [cct, dif_neg (lt_irrefl (m + 1))]
  have hneg : (fun i => -(uu f (m + 1) y i)) = -(fun i => uu f (m + 1) y i) := rfl
  rw [hneg] at hmv
  rw [hmv, hdet] at hself
  rw [Finset.sum_range_succ,
    ← Fin.sum_univ_eq_sum_range (fun k => cct f k y • (uu f k y)) (m + 1)]
  exact hself

/-- **The exact identity.**  `(A - I)Ñ = -∑_j c̃_j q(f^j)`, with `q = f - Df(0)`.  No
smoothness, no degrees, no truncation: this is `U · adj U = (det U)·I` rearranged. -/
theorem mulVec_Ntil (y : Fin n → ℝ) :
    (Amat f - 1).mulVec (Ntil f y)
      = -∑ j ∈ Finset.range (n + 1), cct f j y • (nonlin f (f^[j] y)) := by
  have hu : ∀ j : ℕ, uu f j y
      = nonlin f (f^[j] y) + (Amat f - 1).mulVec (f^[j] y) := by
    intro j
    funext i
    have hAf : (Amat f).mulVec (f^[j] y) = linPart f (f^[j] y) := Amat_mulVec _
    have hstep : f^[j + 1] y = f (f^[j] y) := Function.iterate_succ_apply' f j y
    simp only [uu, hstep, nonlin, Matrix.sub_mulVec, hAf, Matrix.one_mulVec, Pi.sub_apply,
      Pi.add_apply, linPart]
    abel
  have hlin : (Amat f - 1).mulVec (Ntil f y)
      = ∑ j ∈ Finset.range (n + 1), cct f j y • ((Amat f - 1).mulVec (f^[j] y)) := by
    have := map_sum (Matrix.mulVecLin (Amat f - 1))
      (fun j => cct f j y • (f^[j] y)) (Finset.range (n + 1))
    simp only [Matrix.mulVecLin_apply] at this
    rw [Ntil, this]
    exact Finset.sum_congr rfl fun j _ => by
      simpa using (Matrix.mulVec_smul (Amat f - 1) (cct f j y) (f^[j] y))
  have hzero := sum_cct_uu (f := f) y
  simp only [hu] at hzero
  have hsplit : ∑ j ∈ Finset.range (n + 1), cct f j y • (nonlin f (f^[j] y)
        + (Amat f - 1).mulVec (f^[j] y))
      = (∑ j ∈ Finset.range (n + 1), cct f j y • (nonlin f (f^[j] y)))
        + ∑ j ∈ Finset.range (n + 1), cct f j y • ((Amat f - 1).mulVec (f^[j] y)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => smul_add _ _ _
  have hzero' : (∑ j ∈ Finset.range (n + 1), cct f j y • (nonlin f (f^[j] y)))
      + ∑ j ∈ Finset.range (n + 1), cct f j y • ((Amat f - 1).mulVec (f^[j] y))
      = (0 : Fin n → ℝ) := by
    rw [← hsplit]; exact hzero
  rw [hlin]
  exact eq_neg_of_add_eq_zero_right hzero'

end Construction

namespace SmoothData

section Estimates

variable {m : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)} (D : SmoothData f)

local notation "n" => m + 1

/-- **The columns of the MPE matrix vanish linearly.** -/
theorem van_uu {N j : ℕ} (hj : j + 1 ≤ N) : Van (D.rad N) 0 (D.L ^ N + D.L ^ N) (uu f j) :=
  (D.van_iter hj).sub (D.van_iter (le_trans (Nat.le_succ j) hj))

/-- **The columns are linear to second order.**  This is the structural input to `(★)`. -/
theorem van_uu_sub_lin {N j : ℕ} (hj : j + 1 ≤ N) :
    Van (D.rad N) 1
      (2 * ((D.K * (D.L ^ N) ^ 2) * ∑ i ∈ Finset.range (N + 1), (max ‖linPart f‖ 1) ^ i))
      (fun y => uu f j y - uuLin f j y) := by
  have h1 := D.van_iter_sub_pow N (j + 1) hj
  have h2 := D.van_iter_sub_pow N j (le_trans (Nat.le_succ j) hj)
  have hsub := h1.sub h2
  have hfun : (fun y => uu f j y - uuLin f j y)
      = fun y => (f^[j + 1] y - ((linPart f) ^ (j + 1)) y)
          - (f^[j] y - ((linPart f) ^ j) y) := by
    funext y
    rw [uu, uuLin_eq]
    abel
  rw [hfun]
  refine hsub.mono_const (le_of_eq ?_)
  ring

/-! #### The entries of the MPE matrix

Both `U` and its linear model `K` have entries in `Van 0`, and corresponding entries differ
by something in `Van 1`.  These are the three hypotheses of `Van.det_sub`. -/

/-- A constant bounding the entries of both `U` and `K`. -/
noncomputable def CB (N : ℕ) : ℝ := max (D.L ^ N + D.L ^ N) (CKb f)

lemma CB_nonneg (N : ℕ) : 0 ≤ D.CB N :=
  le_trans CKb_nonneg (le_max_right _ _)

/-- A constant bounding the differences. -/
noncomputable def CD (N : ℕ) : ℝ :=
  2 * ((D.K * (D.L ^ N) ^ 2) * ∑ i ∈ Finset.range (N + 1), (max ‖linPart f‖ 1) ^ i)

lemma CD_nonneg (N : ℕ) : 0 ≤ D.CD N := by
  refine mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg D.hK (by positivity)) ?_)
  exact Finset.sum_nonneg fun i _ => pow_nonneg (le_trans zero_le_one (le_max_right _ _)) i

theorem van_Ucol_entry {N : ℕ} (hN : n + 1 ≤ N) (j i k : Fin n) :
    Van (D.rad N) 0 (D.CB N) (Ucol f j i k) := by
  have hpos : (0:ℝ) ≤ D.L ^ N + D.L ^ N := by
    have := pow_nonneg D.L_pos.le N; linarith
  rw [Ucol]
  by_cases h : k = j
  · simp only [h, if_pos]
    exact (((Van.pi_apply hpos (D.van_uu hN) i).neg).mono_const (le_max_left _ _))
  · simp only [if_neg h]
    have hk : (k : ℕ) + 1 ≤ N := by have := k.isLt; omega
    exact ((Van.pi_apply hpos (D.van_uu hk) i).mono_const (le_max_left _ _))

theorem van_Umat_entry {N : ℕ} (hN : n + 1 ≤ N) (i k : Fin n) :
    Van (D.rad N) 0 (D.CB N) (Umat f i k) := by
  have hpos : (0:ℝ) ≤ D.L ^ N + D.L ^ N := by
    have := pow_nonneg D.L_pos.le N; linarith
  have hk : (k : ℕ) + 1 ≤ N := by have := k.isLt; omega
  exact ((Van.pi_apply hpos (D.van_uu hk) i).mono_const (le_max_left _ _))

theorem van_Kcol_entry' {N : ℕ} (j i k : Fin n) :
    Van (D.rad N) 0 (D.CB N) (Kcol f j i k) :=
  (van_Kcol_entry j i k).mono_const (le_max_right _ _)

theorem van_Kmat_entry' {N : ℕ} (i k : Fin n) :
    Van (D.rad N) 0 (D.CB N) (Kmat f i k) :=
  (van_Kmat_entry i k).mono_const (le_max_right _ _)

theorem van_Ucol_sub {N : ℕ} (hN : n + 1 ≤ N) (j i k : Fin n) :
    Van (D.rad N) 1 (D.CD N) (fun y => Ucol f j i k y - Kcol f j i k y) := by
  rw [Ucol, Kcol]
  by_cases h : k = j
  · simp only [h, if_pos]
    have hfun : (fun y => -(uu f (m + 1) y i) - -(uuLin f (m + 1) y i))
        = fun y => -(uu f (m + 1) y i - uuLin f (m + 1) y i) := by funext y; ring
    rw [hfun]
    exact (Van.pi_apply (D.CD_nonneg N) (D.van_uu_sub_lin hN) i).neg
  · simp only [if_neg h]
    have hk : (k : ℕ) + 1 ≤ N := by have := k.isLt; omega
    exact Van.pi_apply (D.CD_nonneg N) (D.van_uu_sub_lin hk) i

theorem van_Umat_sub {N : ℕ} (hN : n + 1 ≤ N) (i k : Fin n) :
    Van (D.rad N) 1 (D.CD N) (fun y => Umat f i k y - Kmat f i k y) := by
  have hk : (k : ℕ) + 1 ≤ N := by have := k.isLt; omega
  exact Van.pi_apply (D.CD_nonneg N) (D.van_uu_sub_lin hk) i

/-- **The cleared coefficients vanish to order `n`.**  A determinant of `n` entries each in
`Van 0`. -/
theorem van_cct {N : ℕ} (hN : n + 1 ≤ N) (j : ℕ) (hj : j ≤ n) :
    Van (D.rad N) m
      ((m + 1).factorial * (1 * (2 ^ m * (D.CB N) ^ (m + 1)))) (cct f j) := by
  rcases lt_or_eq_of_le hj with hlt | rfl
  · have h := Van.det (M := Ucol f ⟨j, hlt⟩) (D.CB_nonneg N)
      (fun i k => D.van_Ucol_entry hN _ i k)
    have hfun : (fun y => Matrix.det (fun i k => Ucol f ⟨j, hlt⟩ i k y)) = cct f j := by
      funext y; rw [← cct_eq_det ⟨j, hlt⟩ y]
    rwa [hfun] at h
  · have h := Van.det (M := Umat f) (D.CB_nonneg N) (fun i k => D.van_Umat_entry hN i k)
    have hfun : (fun y => Matrix.det (fun i k => Umat f i k y)) = cct f (m + 1) := by
      funext y; rw [← cct_top y]
    rwa [hfun] at h

/-! #### `(★)`: the cleared coefficients split

`c̃_j = p_j·Δ + r_j` with `r_j` vanishing to order `n+1`.  This is the only place where any
structure of `f` beyond `f(0)=0` is used, and it is where the `C³` hypothesis is spent. -/

/-- **`(★)`.**  Each cleared coefficient is `p_j·Δ` plus a remainder of order `n+1`. -/
theorem cct_sub_leading {N : ℕ} (hN : n + 1 ≤ N) (j : ℕ) (hj : j ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ Van (D.rad N) n C
      (fun y => cct f j y - (Amat f).charpoly.coeff j * DeltaR f y) := by
  rcases lt_or_eq_of_le hj with hlt | rfl
  · obtain ⟨Kc, hKc0, hKcv⟩ := Van.det_sub (d := 1) (M := Ucol f ⟨j, hlt⟩)
      (N := Kcol f ⟨j, hlt⟩) (D.CB_nonneg N) (D.CD_nonneg N)
      (fun i k => D.van_Ucol_entry hN _ i k) (fun i k => D.van_Kcol_entry' _ i k)
      (fun i k => D.van_Ucol_sub hN _ i k)
    refine ⟨Kc, hKc0, ?_⟩
    have hfun : (fun y => cct f j y - (Amat f).charpoly.coeff j * DeltaR f y)
        = fun y => Matrix.det (fun i k => Ucol f ⟨j, hlt⟩ i k y)
            - Matrix.det (fun i k => Kcol f ⟨j, hlt⟩ i k y) := by
      funext y
      rw [det_Kcol ⟨j, hlt⟩ y, cct_eq_det ⟨j, hlt⟩ y]
    rw [hfun]
    exact hKcv
  · obtain ⟨Kc, hKc0, hKcv⟩ := Van.det_sub (d := 1) (M := Umat f) (N := Kmat f)
      (D.CB_nonneg N) (D.CD_nonneg N)
      (fun i k => D.van_Umat_entry hN i k) (fun i k => D.van_Kmat_entry' i k)
      (fun i k => D.van_Umat_sub hN i k)
    refine ⟨Kc, hKc0, ?_⟩
    have hmonic : (Amat f).charpoly.coeff (m + 1) = 1 := by
      have h := (Amat f).charpoly_monic.coeff_natDegree
      have hdeg : (Amat f).charpoly.natDegree = m + 1 := by simp
      rwa [hdeg] at h
    have hfun : (fun y => cct f (m + 1) y - (Amat f).charpoly.coeff (m + 1) * DeltaR f y)
        = fun y => Matrix.det (fun i k => Umat f i k y)
            - Matrix.det (fun i k => Kmat f i k y) := by
      funext y
      rw [hmonic, one_mul, cct_top, det_Kmat]
    rw [hfun]
    exact hKcv

/-! #### The `σ̃` splitting

Summing `(★)` over `j ≤ n` collects the characteristic-polynomial coefficients, whose sum is
`p_A(1)`.  This is Ob.`split`/Ob.`pert` of the appendix: `σ̃ = p_A(1)·Δ + R` with
`|R| = O(‖y‖^{n+1})` and `|∂R| = O(‖y‖^n)`, which is exactly what the `Van (m+1)` conclusion
says. -/

/-- **`σ̃ = p_A(1)·Δ + R` with `R` of order `n+1`.** -/
theorem sigt_split {N : ℕ} (hN : n + 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ Van (D.rad N) (m + 1) C
      (fun y => sigt f y - (Amat f).charpoly.eval 1 * DeltaR f y) := by
  classical
  choose Cj hCj0 hCjv using fun j : Fin (n + 1) =>
    D.cct_sub_leading hN (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)
  set Ctot : ℝ := ∑ j : Fin (n + 1), Cj j with hCtot
  have hCtot0 : 0 ≤ Ctot := Finset.sum_nonneg fun j _ => hCj0 j
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))), Van (D.rad N) (m + 1) Ctot
      (fun y => cct f (j : ℕ) y - (Amat f).charpoly.coeff (j : ℕ) * DeltaR f y) := fun j _ =>
    (hCjv j).mono_const (Finset.single_le_sum (f := Cj) (fun k _ => hCj0 k) (Finset.mem_univ j))
  have hsum := Van.sum (ρ := D.rad N) (k := m + 1) (Finset.univ : Finset (Fin (n + 1)))
    hCtot0 hterm
  refine ⟨(Finset.univ : Finset (Fin (n + 1))).card * Ctot,
    mul_nonneg (by positivity) hCtot0, ?_⟩
  have hfun : (fun y => ∑ j : Fin (n + 1),
        (cct f (j : ℕ) y - (Amat f).charpoly.coeff (j : ℕ) * DeltaR f y))
      = fun y => sigt f y - (Amat f).charpoly.eval 1 * DeltaR f y := by
    funext y
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    congr 1
    · rw [sigt, Fin.sum_univ_eq_sum_range (fun j => cct f j y) (n + 1)]
    · congr 1
      rw [Fin.sum_univ_eq_sum_range (fun j => (Amat f).charpoly.coeff j) (n + 1)]
      have hdeg : (Amat f).charpoly.natDegree = n := by simp
      rw [Polynomial.eval_eq_sum_range, hdeg]
      exact Finset.sum_congr rfl fun j _ => by simp
  rw [← hfun]
  exact hsum

/-! #### Lemma 4.1(iii)

`‖Ñ(y)‖ ≤ M‖y‖^{n+2}` — the `hN` field of `CycleData`.  In the polynomial development this
took the `T`-decomposition and Cayley–Hamilton; here it is one line of `Van` arithmetic on
the exact identity, because `c̃_j` already vanishes to order `n` and `q∘f^j` to order `2`. -/

/-- The right-hand side of the exact identity vanishes to order `n+2`. -/
theorem van_sum_cct_nonlin {N : ℕ} (hN : n + 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ Van (D.rad N) (m + 2) C
      (fun y => ∑ j ∈ Finset.range (n + 1), cct f j y • (nonlin f (f^[j] y))) := by
  classical
  set Cc : ℝ := ((m + 1).factorial : ℝ) * (1 * (2 ^ m * (D.CB N) ^ (m + 1))) with hCc
  have hCc0 : 0 ≤ Cc := by
    rw [hCc]
    exact mul_nonneg (by positivity)
      (mul_nonneg zero_le_one (mul_nonneg (by positivity) (pow_nonneg (D.CB_nonneg N) _)))
  have hCq0 : (0:ℝ) ≤ D.K * (D.L ^ N) ^ 2 := mul_nonneg D.hK (by positivity)
  have hterm : ∀ j ∈ Finset.range (n + 1),
      Van (D.rad N) (m + 2) (2 * (Cc * (D.K * (D.L ^ N) ^ 2)))
        (fun y => cct f j y • (nonlin f (f^[j] y))) := by
    intro j hj
    have hjn : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact Van.smul hCc0 hCq0 (D.van_cct hN j hjn)
      (D.van_nonlin_comp_iter (le_trans hjn (by omega)))
  refine ⟨(Finset.range (n + 1)).card * (2 * (Cc * (D.K * (D.L ^ N) ^ 2))), ?_,
    Van.sum (ρ := D.rad N) (k := m + 2) (Finset.range (n + 1)) ?_ hterm⟩
  · exact mul_nonneg (by positivity) (by positivity)
  · positivity

/-- **Lemma 4.1(iii) for a `C³` map.**  `Ñ` vanishes to order `n+2`. -/
theorem van_Ntil {N : ℕ} (hN : n + 1 ≤ N) (hA : IsUnit (Amat f - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ Van (D.rad N) (m + 2) C (Ntil f) := by
  classical
  obtain ⟨C, hC0, hCv⟩ := D.van_sum_cct_nonlin hN
  have hdet : IsUnit (Amat f - 1).det := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hmul : (Amat f - 1)⁻¹ * (Amat f - 1) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hNt : (fun y => (mulVecCLM ((Amat f - 1)⁻¹) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (-∑ j ∈ Finset.range (n + 1), cct f j y • (nonlin f (f^[j] y))))
      = Ntil f := by
    funext y
    rw [mulVecCLM_apply, ← mulVec_Ntil, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  have h := Van.clm_comp (mulVecCLM ((Amat f - 1)⁻¹) :
      (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) hC0 hCv.neg
  rw [hNt] at h
  exact ⟨_, mul_nonneg (norm_nonneg _) hC0, h⟩

/-! #### Lemma 4.4(iii)

Substituting `(★)` into the exact identity splits the right-hand side into `Δ·W` with
`‖W‖ = O(‖y‖²)` and a remainder of order `n+3`.  Dividing by `|σ̃|` — which controls `|Δ|`
by the `σ̃` splitting — this is `‖S(y)‖ ≤ C₁‖y‖² + C₂‖y‖³/τ(y)`. -/

/-- **Lemma 4.4(iii) for a `C³` map.**
`‖Ñ(y)‖ ≤ C₁|σ̃(y)|‖y‖² + C₂‖y‖^{n+3}`. -/
theorem sharp_estimate {N : ℕ} (hN : n + 1 ≤ N) (hA : IsUnit (Amat f - 1)) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ y ∈ closedBall (0 : Fin n → ℝ) (D.rad N),
        ‖Ntil f y‖ ≤ C₁ * |sigt f y| * ‖y‖ ^ 2 + C₂ * ‖y‖ ^ (m + 4) := by
  classical
  -- (a) the inverse of `A - I`
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
  -- (b) `p_A(1) ≠ 0`
  have hp1 : (Amat f).charpoly.eval 1 ≠ 0 := by
    rw [Matrix.eval_charpoly]
    have hscal : (Matrix.scalar (Fin n)) (1 : ℝ) - Amat f = -(Amat f - 1) := by
      have h1 : (Matrix.scalar (Fin n)) (1 : ℝ) = 1 := by simp
      rw [h1, neg_sub]
    rw [hscal, Matrix.det_neg]
    simpa using hdet.ne_zero
  have hp1abs : 0 < |(Amat f).charpoly.eval 1| := abs_pos.mpr hp1
  -- (c) `W`, the quadratic factor
  set Cq : ℝ := D.K * (D.L ^ N) ^ 2 with hCqdef
  have hCq0 : (0:ℝ) ≤ Cq := mul_nonneg D.hK (by positivity)
  set CW : ℝ := (∑ j ∈ Finset.range (n + 1), |(Amat f).charpoly.coeff j|) * Cq + 1 with hCWdef
  have hCW0 : (0:ℝ) < CW := by
    have : (0:ℝ) ≤ (∑ j ∈ Finset.range (n + 1), |(Amat f).charpoly.coeff j|) * Cq :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hCq0
    rw [hCWdef]; linarith
  have hW : ∀ y ∈ closedBall (0 : Fin n → ℝ) (D.rad N),
      ‖∑ j ∈ Finset.range (n + 1), (Amat f).charpoly.coeff j • (nonlin f (f^[j] y))‖
        ≤ CW * ‖y‖ ^ 2 := by
    intro y hy
    have hbd : ∀ j ∈ Finset.range (n + 1),
        ‖(Amat f).charpoly.coeff j • (nonlin f (f^[j] y))‖
          ≤ |(Amat f).charpoly.coeff j| * (Cq * ‖y‖ ^ 2) := by
      intro j hj
      have hjn : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        ((D.van_nonlin_comp_iter (le_trans hjn (by omega))).val y hy) (abs_nonneg _)
    calc ‖∑ j ∈ Finset.range (n + 1), (Amat f).charpoly.coeff j • (nonlin f (f^[j] y))‖
        ≤ ∑ j ∈ Finset.range (n + 1), ‖(Amat f).charpoly.coeff j • (nonlin f (f^[j] y))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range (n + 1), |(Amat f).charpoly.coeff j| * (Cq * ‖y‖ ^ 2) :=
          Finset.sum_le_sum hbd
      _ = ((∑ j ∈ Finset.range (n + 1), |(Amat f).charpoly.coeff j|) * Cq) * ‖y‖ ^ 2 := by
          rw [← Finset.sum_mul]; ring
      _ ≤ CW * ‖y‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hCWdef]; linarith
  -- (d) the remainder, of order `n+3`
  obtain ⟨CR, hCR0, hCRv⟩ : ∃ C : ℝ, 0 ≤ C ∧ Van (D.rad N) (m + 3) C
      (fun y => ∑ j : Fin (n + 1),
        (cct f (j : ℕ) y - (Amat f).charpoly.coeff (j : ℕ) * DeltaR f y)
          • (nonlin f (f^[(j : ℕ)] y))) := by
    choose Cj hCj0 hCjv using fun j : Fin (n + 1) =>
      D.cct_sub_leading hN (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)
    have hCtot0 : (0:ℝ) ≤ ∑ j : Fin (n + 1), Cj j := Finset.sum_nonneg fun j _ => hCj0 j
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))),
        Van (D.rad N) (m + 3) (2 * ((∑ k : Fin (n + 1), Cj k) * Cq))
          (fun y => (cct f (j : ℕ) y - (Amat f).charpoly.coeff (j : ℕ) * DeltaR f y)
            • (nonlin f (f^[(j : ℕ)] y))) := by
      intro j _
      have hjle : (j : ℕ) ≤ N := by have := j.isLt; omega
      have hprod := Van.smul (hCj0 j) hCq0 (hCjv j) (D.van_nonlin_comp_iter hjle)
      refine hprod.mono_const ?_
      have hle : Cj j ≤ ∑ k : Fin (n + 1), Cj k :=
        Finset.single_le_sum (f := Cj) (fun k _ => hCj0 k) (Finset.mem_univ j)
      nlinarith [hCq0, hCj0 j]
    exact ⟨_, by positivity, Van.sum (ρ := D.rad N) (k := m + 3)
      (Finset.univ : Finset (Fin (n + 1))) (by positivity) hterm⟩
  -- (e) the `σ̃` splitting
  obtain ⟨CS, hCS0, hCSv⟩ := D.sigt_split hN
  -- (f) the decomposition
  have hdecomp : ∀ y : Fin n → ℝ,
      ∑ j ∈ Finset.range (n + 1), cct f j y • (nonlin f (f^[j] y))
        = (DeltaR f y) • (∑ j ∈ Finset.range (n + 1),
              (Amat f).charpoly.coeff j • (nonlin f (f^[j] y)))
          + ∑ j : Fin (n + 1),
              (cct f (j : ℕ) y - (Amat f).charpoly.coeff (j : ℕ) * DeltaR f y)
                • (nonlin f (f^[(j : ℕ)] y)) := by
    intro y
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      (cct f j y - (Amat f).charpoly.coeff j * DeltaR f y) • (nonlin f (f^[j] y))) (n + 1),
      Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [smul_smul, ← add_smul]; congr 1; ring
  -- (g) assemble
  refine ⟨B * CW / |(Amat f).charpoly.eval 1| + 1,
    B * CW * CS / |(Amat f).charpoly.eval 1| + B * CR + 1, ?_, ?_, ?_⟩
  · have : 0 ≤ B * CW / |(Amat f).charpoly.eval 1| := by positivity
    linarith
  · have h1 : 0 ≤ B * CW * CS / |(Amat f).charpoly.eval 1| := by positivity
    have h2 : 0 ≤ B * CR := mul_nonneg hB0 hCR0
    linarith
  intro y hy
  have hy0 : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
  have hWb := hW y hy
  have hRb : ‖∑ j : Fin (n + 1),
      (cct f (j : ℕ) y - (Amat f).charpoly.coeff (j : ℕ) * DeltaR f y)
        • (nonlin f (f^[(j : ℕ)] y))‖ ≤ CR * ‖y‖ ^ (m + 4) := hCRv.val y hy
  have hSb : |sigt f y - (Amat f).charpoly.eval 1 * DeltaR f y| ≤ CS * ‖y‖ ^ (m + 2) := by
    simpa [Real.norm_eq_abs] using hCSv.val y hy
  -- `|Δ|` is controlled by `|σ̃|`
  have hDb : |DeltaR f y| * |(Amat f).charpoly.eval 1|
      ≤ |sigt f y| + CS * ‖y‖ ^ (m + 2) := by
    have hsub : sigt f y - (sigt f y - (Amat f).charpoly.eval 1 * DeltaR f y)
        = (Amat f).charpoly.eval 1 * DeltaR f y := by ring
    have habs : |(Amat f).charpoly.eval 1 * DeltaR f y|
        ≤ |sigt f y| + |sigt f y - (Amat f).charpoly.eval 1 * DeltaR f y| := by
      have h := norm_add_le (sigt f y) (-(sigt f y - (Amat f).charpoly.eval 1 * DeltaR f y))
      simp only [Real.norm_eq_abs, abs_neg] at h
      rwa [show sigt f y + -(sigt f y - (Amat f).charpoly.eval 1 * DeltaR f y)
        = (Amat f).charpoly.eval 1 * DeltaR f y from by ring] at h
    rw [abs_mul, mul_comm] at habs
    linarith
  -- the main chain
  have hkey : ‖Ntil f y‖
      ≤ B * (|DeltaR f y| * (CW * ‖y‖ ^ 2) + CR * ‖y‖ ^ (m + 4)) := by
    refine le_trans (hinv (Ntil f y)) ?_
    rw [mulVec_Ntil, norm_neg, hdecomp y]
    refine mul_le_mul_of_nonneg_left ?_ hB0
    refine le_trans (norm_add_le _ _) (add_le_add ?_ hRb)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hWb (abs_nonneg _)
  have hDle : |DeltaR f y| ≤ (|sigt f y| + CS * ‖y‖ ^ (m + 2)) / |(Amat f).charpoly.eval 1| := by
    rw [le_div_iff₀ hp1abs]; exact hDb
  have hpw : ‖y‖ ^ 2 * ‖y‖ ^ (m + 2) = ‖y‖ ^ (m + 4) := by rw [← pow_add]; congr 1; omega
  have hfinal : B * (|DeltaR f y| * (CW * ‖y‖ ^ 2) + CR * ‖y‖ ^ (m + 4))
      ≤ (B * CW / |(Amat f).charpoly.eval 1|) * |sigt f y| * ‖y‖ ^ 2
        + (B * CW * CS / |(Amat f).charpoly.eval 1| + B * CR) * ‖y‖ ^ (m + 4) := by
    have hstep : |DeltaR f y| * (CW * ‖y‖ ^ 2)
        ≤ ((|sigt f y| + CS * ‖y‖ ^ (m + 2)) / |(Amat f).charpoly.eval 1|) * (CW * ‖y‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hDle (by positivity)
    have heq : ((|sigt f y| + CS * ‖y‖ ^ (m + 2)) / |(Amat f).charpoly.eval 1|) * (CW * ‖y‖ ^ 2)
        = (CW / |(Amat f).charpoly.eval 1|) * |sigt f y| * ‖y‖ ^ 2
          + (CW * CS / |(Amat f).charpoly.eval 1|) * ‖y‖ ^ (m + 4) := by
      rw [← hpw]; field_simp
    rw [heq] at hstep
    calc B * (|DeltaR f y| * (CW * ‖y‖ ^ 2) + CR * ‖y‖ ^ (m + 4))
        ≤ B * (((CW / |(Amat f).charpoly.eval 1|) * |sigt f y| * ‖y‖ ^ 2
            + (CW * CS / |(Amat f).charpoly.eval 1|) * ‖y‖ ^ (m + 4))
            + CR * ‖y‖ ^ (m + 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ hB0
          linarith [hstep]
      _ = (B * CW / |(Amat f).charpoly.eval 1|) * |sigt f y| * ‖y‖ ^ 2
            + (B * CW * CS / |(Amat f).charpoly.eval 1| + B * CR) * ‖y‖ ^ (m + 4) := by
          field_simp; ring
  refine le_trans hkey (le_trans hfinal ?_)
  have hs : (0:ℝ) ≤ |sigt f y| := abs_nonneg _
  have hyp : (0:ℝ) ≤ ‖y‖ ^ 2 := by positivity
  have hyq : (0:ℝ) ≤ ‖y‖ ^ (m + 4) := by positivity
  nlinarith [mul_nonneg hs hyp]

/-! #### The remainder, in the shape `theorem3_gen` wants

`Rm = σ̃ - leadConst A · det K_A` vanishes to order `n+1`, and its rescaled coordinate
derivatives are `O(r)` on the unit cube — the two facts the shell estimate consumes. -/

include D in
/-- `σ̃` vanishes at the origin. -/
lemma cct_zero {N : ℕ} (hN : n + 1 ≤ N) (j : ℕ) (hj : j ≤ n) : cct f j 0 = 0 := by
  have h0 : (0 : Fin n → ℝ) ∈ closedBall (0 : Fin n → ℝ) (D.rad N) := by
    rw [mem_closedBall, dist_self]; exact (D.rad_pos N).le
  have h := (D.van_cct hN j hj).val 0 h0
  rw [norm_zero, zero_pow (by omega), mul_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

include D in
lemma sigt_zero {N : ℕ} (hN : n + 1 ≤ N) : sigt f 0 = 0 := by
  rw [sigt]
  exact Finset.sum_eq_zero fun j hj =>
    D.cct_zero hN j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

/-- **The splitting in `theorem3_gen`'s shape.** -/
theorem sigt_split_lead {N : ℕ} (hN : n + 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ Van (D.rad N) (m + 1) C
      (fun y => sigt f y - Poly.leadConst (Amat f) * (krylov (Amat f) y).det) := by
  obtain ⟨C, hC0, hCv⟩ := D.sigt_split hN
  refine ⟨C, hC0, ?_⟩
  have hfun : (fun y => sigt f y - Poly.leadConst (Amat f) * (krylov (Amat f) y).det)
      = fun y => sigt f y - (Amat f).charpoly.eval 1 * DeltaR f y := by
    funext y
    rw [DeltaR_eq, Poly.leadConst]
    ring
  rw [hfun]
  exact hCv

include D in
/-- **Lemma 4.4(ii) for the `C³` construction.**  The least-squares determinant is nonzero
whenever the margin clears `M₀‖y‖`.

Both `c̃_n` and `σ̃` split off the *same* `Δ`: by `(★)` with `p_n = 1`, `c̃_n = Δ + r`, and by
`sigt_split`, `σ̃ = p_A(1)Δ + R`, with `r` and `R` of order `n+1`.  Eliminating `Δ` turns a
lower bound on `|σ̃|` into one on `|c̃_n| = |det U|`, provided `M₀` is chosen large enough
relative to the two remainder constants.  That choice is what the paper's `M₀` is for. -/
theorem exists_M0_det_ne_zero {N : ℕ} (hN : n + 1 ≤ N) (hA : IsUnit (Amat f - 1)) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ y : Fin n → ℝ, 0 < ‖y‖ → ‖y‖ ≤ D.rad N →
      M₀ * ‖y‖ ^ (n + 1) ≤ |sigt f y| → cct f n y ≠ 0 := by
  classical
  obtain ⟨Cc, hCc0, hCcv⟩ := D.cct_sub_leading hN n (le_refl n)
  obtain ⟨Cs, hCs0, hCsv⟩ := D.sigt_split hN
  set p1 : ℝ := (Amat f).charpoly.eval 1 with hp1def
  have hp1 : p1 ≠ 0 := Poly.charpoly_eval_one_ne_zero hA
  have hp1abs : 0 < |p1| := abs_pos.mpr hp1
  have hmonic : (Amat f).charpoly.coeff n = 1 := by
    have h := (Amat f).charpoly_monic.coeff_natDegree
    have hdeg : (Amat f).charpoly.natDegree = n := by simp
    rwa [hdeg] at h
  refine ⟨Cs + |p1| * (Cc + 1), by positivity, ?_⟩
  intro y hy0 hyR hmarg
  have hmem : y ∈ closedBall (0 : Fin n → ℝ) (D.rad N) := by
    rw [mem_closedBall, dist_zero_right]; exact hyR
  have hyn : (0:ℝ) < ‖y‖ ^ (n + 1) := pow_pos hy0 _
  -- the two remainders
  have hr : |cct f n y - DeltaR f y| ≤ Cc * ‖y‖ ^ (n + 1) := by
    have h := hCcv.val y hmem
    rw [Real.norm_eq_abs] at h
    rwa [hmonic, one_mul] at h
  have hR : |sigt f y - p1 * DeltaR f y| ≤ Cs * ‖y‖ ^ (n + 1) := by
    have h := hCsv.val y hmem
    rwa [Real.norm_eq_abs] at h
  -- eliminate Δ
  have hDlow : (Cc + 1) * ‖y‖ ^ (n + 1) ≤ |DeltaR f y| := by
    have habs : |p1| * |DeltaR f y| = |p1 * DeltaR f y| := (abs_mul _ _).symm
    have h2 : |sigt f y| - |sigt f y - p1 * DeltaR f y| ≤ |p1 * DeltaR f y| := by
      have h := abs_sub_abs_le_abs_sub (sigt f y) (sigt f y - p1 * DeltaR f y)
      have heq : sigt f y - (sigt f y - p1 * DeltaR f y) = p1 * DeltaR f y := by ring
      rw [heq] at h
      exact h
    have h3 : |p1| * ((Cc + 1) * ‖y‖ ^ (n + 1)) ≤ |p1| * |DeltaR f y| := by
      rw [habs]
      nlinarith [hmarg, hR, h2]
    exact le_of_mul_le_mul_left h3 hp1abs
  have hfin : ‖y‖ ^ (n + 1) ≤ |cct f n y| := by
    have h := abs_sub_abs_le_abs_sub (DeltaR f y) (cct f n y)
    have hcomm : |DeltaR f y - cct f n y| = |cct f n y - DeltaR f y| := abs_sub_comm _ _
    rw [hcomm] at h
    nlinarith [hDlow, hr, h]
  intro hzero
  rw [hzero, abs_zero] at hfin
  linarith

include D in
/-- **Lemma 4.4(ii) in the shape `quad_nonsingular` consumes.**  Converting the margin
`τ(z) ≥ M₀‖z‖` into `|σ̃(z)| ≥ M₀‖z‖^(n+1)` is the only step. -/
theorem exists_M0_hDne {N : ℕ} (hN : n + 1 ≤ N) (hA : IsUnit (Amat f - 1))
    (C : CycleData (Fin n → ℝ)) (hd : C.d = m + 1) (hsigC : C.sigt = sigt f)
    (hρ : C.ρ₁ = D.rad N) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ z : Fin n → ℝ, 0 < ‖z‖ → ‖z‖ ≤ C.ρ₁ →
      M₀ * ‖z‖ ≤ C.τ z → cct f n z ≠ 0 := by
  obtain ⟨M₀, hM₀, hmain⟩ := D.exists_M0_det_ne_zero hN hA
  refine ⟨M₀, hM₀, ?_⟩
  intro z hz0 hzρ hτ
  refine hmain z hz0 (by rwa [hρ] at hzρ) ?_
  have hτeq : C.τ z = |sigt f z| / ‖z‖ ^ n := by
    show |C.sigt z| / ‖z‖ ^ C.d = _
    rw [hsigC, hd]
  rw [hτeq, le_div_iff₀ (pow_pos hz0 n)] at hτ
  calc M₀ * ‖z‖ ^ (n + 1) = M₀ * ‖z‖ * ‖z‖ ^ n := by rw [pow_succ']; ring
    _ ≤ |sigt f z| := hτ

/-- Updating one coordinate is an affine path with derivative `Pi.single κ 1`. -/
lemma hasDerivAt_update (v : Fin n → ℝ) (κ : Fin n) (t : ℝ) :
    HasDerivAt (fun t => (Function.update v κ t : Fin n → ℝ)) (Pi.single κ (1:ℝ)) t := by
  rw [hasDerivAt_pi]
  intro i
  by_cases h : i = κ
  · subst h
    simp only [Function.update_self, Pi.single_eq_same]
    exact hasDerivAt_id t
  · simp only [Function.update_of_ne h, Pi.single_eq_of_ne h]
    exact hasDerivAt_const t (v i)

/-- **The rescaled coordinate derivatives of the remainder are `O(r)`.**  This is the last
hypothesis of `theorem3_gen`; it is the `C³` counterpart of `LowDeg.exists_deriv_update`. -/
theorem exists_deriv_update_van {ρ cRm : ℝ} {Rm : (Fin n → ℝ) → ℝ}
    (hcRm : 0 ≤ cRm) (hRm : Van ρ (m + 1) cRm Rm)
    (P : Matrix (Fin n) (Fin n) ℝ) {r : ℝ} (hr : 0 < r)
    (hrρ : r * (‖(mulVecCLM P : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ + 1) ≤ ρ)
    (κ : Fin n) :
    ∃ g : ℝ → (Fin n → ℝ) → ℝ,
      (∀ v t, ‖(Function.update v κ t : Fin n → ℝ)‖ ≤ 1 →
          HasDerivAt (fun t => Rm (P.mulVec (r • Function.update v κ t)) / r ^ (m + 1))
            (g t v) t)
        ∧ ∀ v t, ‖(Function.update v κ t : Fin n → ℝ)‖ ≤ 1 →
            |g t v| ≤ (cRm * (‖(mulVecCLM P : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ + 1) ^ (m + 2))
              * r := by
  classical
  set L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := mulVecCLM P with hL
  set NL : ℝ := ‖L‖ + 1 with hNL
  have hNL1 : (1:ℝ) ≤ NL := by rw [hNL]; linarith [norm_nonneg L]
  have hNL0 : (0:ℝ) < NL := lt_of_lt_of_le one_pos hNL1
  -- the point where the derivative is taken stays in the ball
  have hmem : ∀ (v : Fin n → ℝ) (t : ℝ), ‖(Function.update v κ t : Fin n → ℝ)‖ ≤ 1 →
      ‖L (r • Function.update v κ t)‖ ≤ ρ ∧
        L (r • Function.update v κ t) ∈ closedBall (0 : Fin n → ℝ) ρ := by
    intro v t hv
    have h1 : ‖L (r • Function.update v κ t)‖ ≤ ‖L‖ * (r * 1) := by
      refine le_trans (L.le_opNorm _) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg L))
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hv hr.le
    have h2 : ‖L‖ * (r * 1) ≤ ρ := by nlinarith [norm_nonneg L, hr.le]
    exact ⟨le_trans h1 h2, by rw [mem_closedBall, dist_zero_right]; exact le_trans h1 h2⟩
  refine ⟨fun t v => (fderiv ℝ Rm (L (r • Function.update v κ t)))
      (r • L (Pi.single κ (1:ℝ))) / r ^ (m + 1), ?_, ?_⟩
  · intro v t hv
    have hpath : HasDerivAt (fun t => L (r • Function.update v κ t))
        (r • L (Pi.single κ (1:ℝ))) t := by
      have h1 : HasDerivAt (fun t => (r : ℝ) • (Function.update v κ t : Fin n → ℝ))
          (r • Pi.single κ (1:ℝ)) t := (hasDerivAt_update v κ t).const_smul r
      have h2 := L.hasFDerivAt.comp_hasDerivAt t h1
      rw [map_smul] at h2
      exact h2
    have hfd : HasFDerivAt Rm (fderiv ℝ Rm (L (r • Function.update v κ t)))
        (L (r • Function.update v κ t)) :=
      (hRm.diff _ (hmem v t hv).2).hasFDerivAt
    have hcomp := hfd.comp_hasDerivAt t hpath
    exact hcomp.div_const _
  · intro v t hv
    have hsingle : ‖(Pi.single κ (1:ℝ) : Fin n → ℝ)‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
      by_cases h : i = κ
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    have hz : ‖L (r • Function.update v κ t)‖ ≤ ‖L‖ * r := by
      refine le_trans (L.le_opNorm _) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg L))
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      calc r * ‖(Function.update v κ t : Fin n → ℝ)‖ ≤ r * 1 :=
            mul_le_mul_of_nonneg_left hv hr.le
        _ = r := by ring
    have hder := hRm.der _ (hmem v t hv).2
    have hnum : ‖(fderiv ℝ Rm (L (r • Function.update v κ t))) (r • L (Pi.single κ (1:ℝ)))‖
        ≤ (cRm * ‖L (r • Function.update v κ t)‖ ^ (m + 1)) * (r * ‖L‖) := by
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul hder ?_ (norm_nonneg _)
        (by positivity))
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      refine mul_le_mul_of_nonneg_left ?_ hr.le
      refine le_trans (L.le_opNorm _) ?_
      simpa using mul_le_mul_of_nonneg_left hsingle (norm_nonneg L)
    have hpow : ‖L (r • Function.update v κ t)‖ ^ (m + 1) ≤ (‖L‖ * r) ^ (m + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hz _
    have hLNL : ‖L‖ ≤ NL := by rw [hNL]; linarith
    have hL0 : (0:ℝ) ≤ ‖L‖ := norm_nonneg L
    have hstep : (cRm * ‖L (r • Function.update v κ t)‖ ^ (m + 1)) * (r * ‖L‖)
        ≤ (cRm * NL ^ (m + 2)) * r ^ (m + 2) := by
      have h1 : (cRm * ‖L (r • Function.update v κ t)‖ ^ (m + 1)) * (r * ‖L‖)
          ≤ (cRm * (‖L‖ * r) ^ (m + 1)) * (r * ‖L‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hcRm) (by positivity)
      have heq : (cRm * (‖L‖ * r) ^ (m + 1)) * (r * ‖L‖)
          = (cRm * ‖L‖ ^ (m + 2)) * r ^ (m + 2) := by
        rw [mul_pow]; ring
      rw [heq] at h1
      refine le_trans h1 ?_
      have h2 : ‖L‖ ^ (m + 2) ≤ NL ^ (m + 2) := pow_le_pow_left₀ hL0 hLNL _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hcRm) (by positivity)
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < r ^ (m + 1)), div_le_iff₀ (by positivity)]
    calc |(fderiv ℝ Rm (L (r • Function.update v κ t))) (r • L (Pi.single κ (1:ℝ)))|
        ≤ (cRm * ‖L (r • Function.update v κ t)‖ ^ (m + 1)) * (r * ‖L‖) := by
          simpa [Real.norm_eq_abs] using hnum
      _ ≤ (cRm * NL ^ (m + 2)) * r ^ (m + 2) := hstep
      _ = cRm * NL ^ (m + 2) * r * r ^ (m + 1) := by rw [pow_succ']; ring

/-! #### The interface terms

`CycleData` and `SharpBound` are exactly the two structural hypotheses of `MPE.dither_sharp`.
For a `C³` map both are now theorems, as they were for a polynomial one. -/

/-- **Both structural hypotheses of Theorem 4.9, for a `C³` map.**  The `CycleData` exists with
`hN` (Lemma 4.1(iii)) proved, and it carries a `SharpBound` with `bound` (Lemma 4.4(iii)) proved.
The field equations are carried along because `hΨ` needs to know that `sigt` really is `σ̃`. -/
theorem nonempty_cycleData_sharpBound {N : ℕ} (hN : n + 1 ≤ N) (hA : IsUnit (Amat f - 1)) :
    ∃ C : CycleData (Fin n → ℝ),
      C.d = m + 1 ∧ C.Ntil = Ntil f ∧ C.sigt = sigt f ∧ C.ρ₁ = D.rad N
        ∧ Nonempty (SharpBound C) := by
  classical
  obtain ⟨CN, hCN0, hCNv⟩ := D.van_Ntil hN hA
  obtain ⟨C₁, C₂, hC₁, hC₂, hbd⟩ := D.sharp_estimate hN hA
  -- Lemma 4.1(iii), in the shape `CycleData.hN` wants
  have hNfield : ∀ y : Fin n → ℝ, ‖y‖ ≤ D.rad N →
      ‖Ntil f y‖ ≤ (1 + CN) * ‖y‖ ^ (m + 1 + 2) := by
    intro y hy
    have h := hCNv.val y (by rwa [mem_closedBall, dist_zero_right])
    have hpow : (m + 2 + 1) = (m + 1 + 2) := by omega
    rw [hpow] at h
    nlinarith [pow_nonneg (norm_nonneg y) (m + 1 + 2)]
  -- Lemma 4.4(iii), in the shape `SharpBound.bound` wants
  have hbound : ∀ y : Fin n → ℝ, 0 < ‖y‖ → ‖y‖ ≤ D.rad N → sigt f y ≠ 0 →
      ‖(sigt f y)⁻¹ • Ntil f y‖
        ≤ C₁ * ‖y‖ ^ 2 + C₂ * ‖y‖ ^ 3 / (|sigt f y| / ‖y‖ ^ (m + 1)) := by
    intro y hy0 hy1 hσ
    have hσabs : (0:ℝ) < |sigt f y| := abs_pos.mpr hσ
    have hest := hbd y (by rw [mem_closedBall, dist_zero_right]; exact hy1)
    have hS : ‖(sigt f y)⁻¹ • Ntil f y‖ = ‖Ntil f y‖ / |sigt f y| := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs]; ring
    rw [hS, div_le_iff₀ hσabs]
    have hpow : ‖y‖ ^ (2:ℕ) * ‖y‖ ^ (m + 1) * ‖y‖ = ‖y‖ ^ (m + 4) := by
      rw [← pow_add, ← pow_succ]; congr 1; omega
    have hrhs : (C₁ * ‖y‖ ^ 2 + C₂ * ‖y‖ ^ 3 / (|sigt f y| / ‖y‖ ^ (m + 1))) * |sigt f y|
        = C₁ * |sigt f y| * ‖y‖ ^ 2 + C₂ * ‖y‖ ^ (m + 4) := by
      field_simp
      rw [← hpow]
      ring
    rw [hrhs]
    exact hest
  exact ⟨{ d := m + 1
           Ntil := Ntil f
           sigt := sigt f
           M := 1 + CN
           ρ₁ := D.rad N
           hd := Nat.succ_pos m
           hM := by linarith
           hρ₁ := D.rad_pos N
           hN := hNfield },
         rfl, rfl, rfl, rfl,
         ⟨{ C₁ := C₁, C₂ := C₂, hC₁ := hC₁, hC₂ := hC₂,
            bound := fun y h1 h2 h3 => hbound y h1 h2 h3 }⟩⟩

end Estimates

section TopLevel

/-! ### Theorem 4.9 for a `C³` iteration

Every hypothesis of `theorem3_gen` is now available, so Theorem 4.9 holds for a map that is
`C³` near its fixed point, with no polynomial assumption anywhere. -/

variable {M : ℕ} {f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ)} (D : SmoothData f)

include D in
/-- **Theorem 4.9 for a `C³` iteration.** -/
theorem theorem3_C3 (hA : IsUnit (Amat f - 1)) (hsq : Squarefree (Amat f).charpoly)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ (C : CycleData (Fin (M + 2) → ℝ)) (B : SharpBound C) (Cst ρ : ℝ),
      C.Ntil = Ntil f ∧ C.sigt = sigt f ∧ 0 < Cst ∧ 0 < ρ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ 1 → 2 * δ ≤ ρ → 2 * δ ≤ C.ρ₁ →
        (∀ k, 8 * B.C₁ * (sched δ θ k) ^ (2 - θ) ≤ 1) →
        (∀ k, 16 * B.C₂ * (sched δ θ k) ^ (3 - θ) ≤ 1) →
        ((δ ^ (1:ℝ)) ^ (θ - 1) * θ ^ (M + 1) ≤ 1 / 2) →
        ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
          (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
              {ω | ∃ k, ¬ ‖xProc C x₀ δ θ k ω‖ ≤ sched δ θ k}
            ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) := by
  classical
  obtain ⟨C, hd, hNt, hsigC, hρ₁, ⟨B⟩⟩ :=
    D.nonempty_cycleData_sharpBound (N := M + 3) (le_refl _) hA
  obtain ⟨Dsh⟩ := nonempty_shellData (Nat.succ_pos (M + 1)) (Amat f) hsq
  obtain ⟨cRm, hcRm0, hcRmv⟩ := D.sigt_split_lead (N := M + 3) (le_refl _)
  set NL : ℝ := ‖(mulVecCLM Dsh.Pm : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ))‖ + 1
    with hNLdef
  have hNL0 : (0:ℝ) < NL := by
    rw [hNLdef]
    linarith [norm_nonneg (mulVecCLM Dsh.Pm :
      (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ))]
  set ρ : ℝ := D.rad (M + 3) / NL with hρdef
  have hρ0 : 0 < ρ := div_pos (D.rad_pos _) hNL0
  set Rmf : (Fin (M + 2) → ℝ) → ℝ :=
    fun y => Poly.leadConst (Amat f) * (krylov (Amat f) y).det with hRmfdef
  have hz : sigt f 0 = 0 := D.sigt_zero (N := M + 3) (le_refl _)
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
  have hlead : Poly.leadConst (Amat f) ≠ 0 := Poly.leadConst_ne_zero hA
  have hkry : Measurable fun y : Fin (M + 2) → ℝ => (krylov (Amat f) y).det := by
    refine measurable_det_of_entries
      (Mm := fun i k => fun y : Fin (M + 2) → ℝ => (krylov (Amat f) y) i k) fun i k => ?_
    show Measurable fun y : Fin (M + 2) → ℝ => ((Amat f) ^ (k : ℕ)).mulVec y i
    exact (measurable_pi_apply i).comp
      ((Matrix.mulVecLin ((Amat f) ^ (k:ℕ))).continuous_of_finiteDimensional.measurable)
  have hRmeas : Measurable (fun y => sigt f y - Rmf y) := by
    rw [hRmfdef]
    exact (measurable_sigt D.hmeas).sub (measurable_const.mul hkry)
  have hRderiv : ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ κ : Fin (M + 2),
      ∃ g : ℝ → (Fin (M + 2) → ℝ) → ℝ,
        (∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 →
            HasDerivAt (fun t => (fun y => sigt f y - Rmf y)
              (Dsh.Pm.mulVec (r • Function.update v κ t)) / r ^ (M + 2)) (g t v) t)
          ∧ ∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 →
              |g t v| ≤ (cRm * NL ^ (M + 3)) * r := by
    intro r hr hrρ κ
    refine exists_deriv_update_van hcRm0 hcRmv Dsh.Pm hr ?_ κ
    rw [← hNLdef]
    rw [hρdef, le_div_iff₀ hNL0] at hrρ
    exact hrρ
  obtain ⟨Cst, hCst, hmain⟩ := theorem3_gen (A := Amat f) (Sig := sigt f)
    (Rm := fun y => sigt f y - Rmf y) hρ0 Dsh C hd (fun y => by rw [hsigC]) hz hSmeas hτmeas
    hlead (fun y => by rw [hRmfdef]; ring) hRmeas
    (by positivity : (0:ℝ) ≤ cRm * NL ^ (M + 3)) hRderiv B hθ1 hθ2
  exact ⟨C, B, Cst, ρ, hNt, hsigC, hCst, hρ0, hmain⟩

/-! ### The smallness conditions, collapsed

`theorem3_C3` carries five technical inequalities relating `δ`, `θ`, the Lemma 4.4 constants and
the two radii.  All are monotone in `δ`, so they collapse to `δ ≤ δ_*` — which is how the
paper states them, and what makes the statement non-vacuous: the constants are no longer
buried inside the hypotheses. -/

include D in
/-- **Theorem 4.9 for a `C³` iteration, with the smallness conditions collapsed to `δ ≤ δ_*`.**

The process is pinned down by its two defining equations rather than by a `CycleData`, so the
statement mentions only `σ̃` and `Ñ`. -/
theorem theorem3_small_C3 (hA : IsUnit (Amat f - 1)) (hsq : Squarefree (Amat f).charpoly)
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ dstar Cst : ℝ, 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar → ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
          (∀ ω, x 0 ω = x₀) →
          (∀ k ω, x (k + 1) ω
            = (sigt f (x k ω + (sched δ θ k) • clamp (ω k)))⁻¹
              • Ntil f (x k ω + (sched δ θ k) • clamp (ω k))) →
          (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
              {ω | ∃ k, ¬ ‖x k ω‖ ≤ sched δ θ k}
            ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) := by
  classical
  obtain ⟨C, B, Cst, ρ, hNt, hsigC, hCst, hρ0, hmain⟩ := D.theorem3_C3 hA hsq hθ1 hθ2
  obtain ⟨t₁, ht₁, -, h₁⟩ := exists_thresh (a := 8 * B.C₁) (p := 2 - θ)
    (by have := B.hC₁; positivity) (by linarith)
  obtain ⟨t₂, ht₂, -, h₂⟩ := exists_thresh (a := 16 * B.C₂) (p := 3 - θ)
    (by have := B.hC₂; positivity) (by linarith)
  obtain ⟨t₃, ht₃, -, h₃⟩ := exists_thresh (a := 2 * θ ^ (M + 1)) (p := θ - 1)
    (by have : (0:ℝ) < θ := by linarith
        positivity) (by linarith)
  refine ⟨min (min (min t₁ t₂) (min t₃ (1/2))) (min (ρ/2) (C.ρ₁/2)), Cst,
    lt_min (lt_min (lt_min ht₁ ht₂) (lt_min ht₃ (by norm_num)))
      (lt_min (by linarith) (by have := C.hρ₁; linarith)), hCst, ?_⟩
  intro δ hδ hδt x₀ hx₀ x hx0 hxs
  -- unpack the threshold
  have hA1 : δ ≤ min (min t₁ t₂) (min t₃ (1/2)) := le_trans hδt (min_le_left _ _)
  have hA2 : δ ≤ min (ρ/2) (C.ρ₁/2) := le_trans hδt (min_le_right _ _)
  have hδ2 : δ ≤ 1/2 := le_trans hA1 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ1 : δ ≤ 1 := by linarith
  have h2δ : 2 * δ ≤ 1 := by linarith
  have h2δρ : 2 * δ ≤ ρ := by
    have := le_trans hA2 (min_le_left _ _); linarith
  have h2δC : 2 * δ ≤ C.ρ₁ := by
    have := le_trans hA2 (min_le_right _ _); linarith
  have hsch : ∀ k, sched δ θ k ≤ δ := fun k => sched_le hδ hδ1 hθ1.le k
  have hschpos : ∀ k, 0 < sched δ θ k := fun k => sched_pos hδ θ k
  -- the process is the one `theorem3_C3` speaks about
  have hSeq : ∀ y, C.S y = (sigt f y)⁻¹ • Ntil f y := by
    intro y
    show (C.sigt y)⁻¹ • C.Ntil y = _
    rw [hsigC, hNt]
  have hxeq : ∀ k ω, x k ω = xProc C x₀ δ θ k ω := by
    intro k
    induction k with
    | zero => intro ω; rw [hx0]; rfl
    | succ k ih =>
        intro ω
        rw [hxs k ω, ih ω, ← hSeq, xProc_succ]
        rfl
  have hset : {ω : ℕ → Fin (M + 2) → ℝ | ∃ k, ¬ ‖x k ω‖ ≤ sched δ θ k}
      = {ω | ∃ k, ¬ ‖xProc C x₀ δ θ k ω‖ ≤ sched δ θ k} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [← hxeq k ω]; exact hk⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [hxeq k ω]; exact hk⟩
  rw [hset]
  refine hmain δ hδ hδ1 h2δ h2δρ h2δC (fun k => ?_) (fun k => ?_) ?_ x₀ hx₀
  · refine le_trans ?_ (h₁ δ hδ (le_trans hA1 (le_trans (min_le_left _ _) (min_le_left _ _))))
    refine mul_le_mul_of_nonneg_left ?_ (by have := B.hC₁; positivity)
    exact Real.rpow_le_rpow (hschpos k).le (hsch k) (by linarith)
  · refine le_trans ?_ (h₂ δ hδ (le_trans hA1 (le_trans (min_le_left _ _) (min_le_right _ _))))
    refine mul_le_mul_of_nonneg_left ?_ (by have := B.hC₂; positivity)
    exact Real.rpow_le_rpow (hschpos k).le (hsch k) (by linarith)
  · have h := h₃ δ hδ (le_trans hA1 (le_trans (min_le_right _ _) (min_le_left _ _)))
    rw [Real.rpow_one]
    linarith

/-! ### The self-contained statement

Everything is spelled out by defining equations in mathlib terms, so that the audit file
`Formal/Statement.lean` mentions no definition of this development. -/

include D in
/-- **The theorem.**  Minimal polynomial extrapolation with dithered restarts, for a map that
is `C³` near its fixed point. -/
theorem mpe_dithered_sharp_C3_proof
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1)) (hsq : Squarefree A.charpoly)
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
          ≤ ENNReal.ofReal (Cst * δ * (1 + max 0 (-Real.log δ)) ^ (M + 1)) := by
  classical
  -- identify the data with the construction of this file
  have hAeq : A = Amat f := by rw [hAdef, Amat]
  subst hAeq
  have hUeq : ∀ y, U y = Ueval f y := by
    intro y
    funext i j
    rw [hU y i j]
    rfl
  have hceq : ∀ j ∈ Finset.range (M + 3), ∀ y, c j y = cct f j y := by
    intro j hj y
    rw [Finset.mem_range] at hj
    rcases Nat.lt_or_ge j (M + 2) with hlt | hge
    · rw [cct, dif_pos hlt, ← hUeq y]
      have h := hcAdj ⟨j, hlt⟩ y
      rw [h]
      rfl
    · have hjeq : j = M + 2 := by omega
      subst hjeq
      rw [hcDet y, cct, dif_neg (by omega), hUeq y]
  have hsgeq : ∀ y, sg y = sigt f y := by
    intro y
    rw [hsg y, sigt]
    exact Finset.sum_congr rfl fun j hj => hceq j hj y
  have hNteq : ∀ y, Nt y = Ntil f y := by
    intro y
    rw [hNt y, Ntil]
    exact Finset.sum_congr rfl fun j hj => by rw [hceq j hj y]
  obtain ⟨dstar, Cst, hd0, hC0, hmain⟩ := D.theorem3_small_C3 hA hsq hθ1 hθ2
  refine ⟨dstar, Cst, hd0, hC0, ?_⟩
  intro δ hδ hδt x₀ hx₀ x hx0 hxs
  have hset : {ω : ℕ → Fin (M + 2) → ℝ | ∃ k, δ ^ (θ ^ k) < ‖x k ω‖}
      = {ω | ∃ k, ¬ ‖x k ω‖ ≤ sched δ θ k} := by
    ext ω
    simp only [Set.mem_setOf_eq, sched, not_le]
  rw [hset]
  refine hmain δ hδ hδt x₀ hx₀ x hx0 ?_
  intro k ω
  rw [hxs k ω, hsgeq, hNteq]
  rfl

include D in
/-- **Theorem 4.9 for a `C³` iteration.** -/
theorem corollary_C3 (hA : IsUnit (Amat f - 1)) (hsq : Squarefree (Amat f).charpoly)
 :
    ∃ (C : CycleData (Fin (M + 2) → ℝ)) (B : SharpBound C) (Cst ρ cth : ℝ),
      C.Ntil = Ntil f ∧ C.sigt = sigt f ∧ 0 < Cst ∧ 0 < ρ ∧ 0 < cth ∧
      -- the threshold is large enough that the good event also forces `det U ≠ 0`
      (∀ z : Fin (M + 2) → ℝ, 0 < ‖z‖ → ‖z‖ ≤ C.ρ₁ →
          cth * (2 : ℝ)⁻¹ * ‖z‖ ≤ C.τ z → cct f (M + 2) z ≠ 0) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        max (8 * B.C₁) 1 * δ * 2 ^ (M + 1) ≤ 1 / 2 →
        cth * δ ≤ 1 →
        2 * δ ≤ ρ → 2 * δ ≤ C.ρ₁ →
        ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
          (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
              {ω | ∃ k, ¬ ‖xProcG C x₀ (qsched (max (8 * B.C₁) 1) δ) k ω‖
                    ≤ qsched (max (8 * B.C₁) 1) δ k
                  ∨ cct f (M + 2) (yProcG C x₀ (qsched (max (8 * B.C₁) 1) δ) k ω) = 0}
            ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) := by
  classical
  obtain ⟨C, hd, hNt, hsigC, hρ₁, ⟨B⟩⟩ :=
    D.nonempty_cycleData_sharpBound (N := M + 3) (le_refl _) hA
  obtain ⟨Dsh⟩ := nonempty_shellData (Nat.succ_pos (M + 1)) (Amat f) hsq
  obtain ⟨cRm, hcRm0, hcRmv⟩ := D.sigt_split_lead (N := M + 3) (le_refl _)
  set NL : ℝ := ‖(mulVecCLM Dsh.Pm : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ))‖ + 1
    with hNLdef
  have hNL0 : (0:ℝ) < NL := by
    rw [hNLdef]
    linarith [norm_nonneg (mulVecCLM Dsh.Pm :
      (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ))]
  set ρ : ℝ := D.rad (M + 3) / NL with hρdef
  have hρ0 : 0 < ρ := div_pos (D.rad_pos _) hNL0
  set Rmf : (Fin (M + 2) → ℝ) → ℝ :=
    fun y => Poly.leadConst (Amat f) * (krylov (Amat f) y).det with hRmfdef
  have hz : sigt f 0 = 0 := D.sigt_zero (N := M + 3) (le_refl _)
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
  have hlead : Poly.leadConst (Amat f) ≠ 0 := Poly.leadConst_ne_zero hA
  have hkry : Measurable fun y : Fin (M + 2) → ℝ => (krylov (Amat f) y).det := by
    refine measurable_det_of_entries
      (Mm := fun i k => fun y : Fin (M + 2) → ℝ => (krylov (Amat f) y) i k) fun i k => ?_
    show Measurable fun y : Fin (M + 2) → ℝ => ((Amat f) ^ (k : ℕ)).mulVec y i
    exact (measurable_pi_apply i).comp
      ((Matrix.mulVecLin ((Amat f) ^ (k:ℕ))).continuous_of_finiteDimensional.measurable)
  have hRmeas : Measurable (fun y => sigt f y - Rmf y) := by
    rw [hRmfdef]
    exact (measurable_sigt D.hmeas).sub (measurable_const.mul hkry)
  have hRderiv : ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ κ : Fin (M + 2),
      ∃ g : ℝ → (Fin (M + 2) → ℝ) → ℝ,
        (∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 →
            HasDerivAt (fun t => (fun y => sigt f y - Rmf y)
              (Dsh.Pm.mulVec (r • Function.update v κ t)) / r ^ (M + 2)) (g t v) t)
          ∧ ∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 →
              |g t v| ≤ (cRm * NL ^ (M + 3)) * r := by
    intro r hr hrρ κ
    refine exists_deriv_update_van hcRm0 hcRmv Dsh.Pm hr ?_ κ
    rw [← hNLdef]
    rw [hρdef, le_div_iff₀ hNL0] at hrρ
    exact hrρ
  obtain ⟨M₀, hM₀0, hM₀⟩ := D.exists_M0_hDne (N := M + 3) (le_refl _) hA C hd hsigC hρ₁
  set cth : ℝ := max (16 * B.C₂ / max (8 * B.C₁) 1) (2 * M₀) with hcthdef
  have hcth0 : 0 < cth := lt_of_lt_of_le (by have := B.hC₂; positivity) (le_max_left _ _)
  have hcthge : 16 * B.C₂ / max (8 * B.C₁) 1 ≤ cth := le_max_left _ _
  have hDne : ∀ z : Fin (M + 2) → ℝ, 0 < ‖z‖ → ‖z‖ ≤ C.ρ₁ →
      cth * (2 : ℝ)⁻¹ * ‖z‖ ≤ C.τ z → cct f (M + 2) z ≠ 0 := by
    intro z hz0 hzρ hτ
    refine hM₀ z hz0 hzρ (le_trans ?_ hτ)
    have h2 : 2 * M₀ ≤ cth := le_max_right _ _
    have : M₀ ≤ cth * (2:ℝ)⁻¹ := by linarith
    exact mul_le_mul_of_nonneg_right this (norm_nonneg z)
  obtain ⟨Cst, hCst, hmain⟩ := corollary_quad_gen (A := Amat f) (Sig := sigt f)
    (Rm := fun y => sigt f y - Rmf y) hρ0 Dsh C hd (fun y => by rw [hsigC]) hz hSmeas hτmeas
    hlead (fun y => by rw [hRmfdef]; ring) hRmeas
    (by positivity : (0:ℝ) ≤ cRm * NL ^ (M + 3)) hRderiv B hcth0 hcthge
    (fun z => cct f (M + 2) z ≠ 0) hDne
  refine ⟨C, B, Cst, ρ, cth, hNt, hsigC, hCst, hρ0, hcth0, hDne, ?_⟩
  intro δ hδ hδ1 h1 h2 h3 h4 x₀ hx₀
  refine le_trans (measure_mono ?_) (hmain δ hδ hδ1 h1 h2 h3 h4 x₀ hx₀)
  rintro ω ⟨k, hk | hk⟩
  · exact ⟨k, Or.inl hk⟩
  · exact ⟨k, Or.inr (by simpa using hk)⟩

include D in
/-- **Theorem 4.9 for a `C³` iteration, with the smallness conditions collapsed to
`δ ≤ δ_*`.**  The schedule is pinned by its two defining equations `δ₀ = δ`,
`δₘ₊₁ = Kδₘ²`, and the process by its own, so the statement mentions neither `qsched` nor
`xProcG`. -/
theorem corollary_small_C3 (hA : IsUnit (Amat f - 1))
    (hsq : Squarefree (Amat f).charpoly) :
    ∃ K dstar Cst : ℝ, 1 ≤ K ∧ 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar → ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        ∀ dl : ℕ → ℝ, dl 0 = δ → (∀ k, dl (k + 1) = K * (dl k) ^ 2) →
        ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
          (∀ ω, x 0 ω = x₀) →
          (∀ k ω, x (k + 1) ω
            = (sigt f (x k ω + (dl k) • clamp (ω k)))⁻¹
              • Ntil f (x k ω + (dl k) • clamp (ω k))) →
          (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
              {ω | ∃ k, ¬ ‖x k ω‖ ≤ dl k
                    ∨ Matrix.det (fun i j => Umat f i j (x k ω + dl k • clamp (ω k))) = 0}
            ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) := by
  classical
  obtain ⟨C, B, Cst, ρ, cth, hNt, hsigC, hCst, hρ0, hcth0, hDne, hmain⟩ :=
    D.corollary_C3 hA hsq
  set K : ℝ := max (8 * B.C₁) 1 with hKdef
  have hK1 : (1:ℝ) ≤ K := le_max_right _ _
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hC₂ := B.hC₂
  have hρ₁ := C.hρ₁
  -- the four smallness conditions are each of the form `δ ≤ const`
  set t₁ : ℝ := 1 / (2 * K * 2 ^ (M + 1)) with ht₁def
  set t₂ : ℝ := 1 / cth with ht₂def
  have ht₁ : 0 < t₁ := by rw [ht₁def]; positivity
  have ht₂ : 0 < t₂ := by rw [ht₂def]; positivity
  refine ⟨K, min (min 1 t₁) (min t₂ (min (ρ / 2) (C.ρ₁ / 2))), Cst, hK1,
    lt_min (lt_min one_pos ht₁) (lt_min ht₂ (lt_min (by linarith) (by linarith))), hCst, ?_⟩
  intro δ hδ hδt x₀ hx₀ dl hdl0 hdls x hx0 hxs
  have hδ1 : δ ≤ 1 := le_trans hδt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδt₁ : δ ≤ t₁ := le_trans hδt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδt₂ : δ ≤ t₂ := le_trans hδt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδρ : δ ≤ ρ / 2 :=
    le_trans hδt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδρ₁ : δ ≤ C.ρ₁ / 2 :=
    le_trans hδt (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hcond1 : K * δ * 2 ^ (M + 1) ≤ 1 / 2 := by
    rw [ht₁def, le_div_iff₀ (by positivity)] at hδt₁
    nlinarith [hδt₁]
  have hcond2 : cth * δ ≤ 1 := by
    rw [ht₂def, le_div_iff₀ hcth0] at hδt₂
    linarith [hδt₂]
  -- the schedule is the quadratic one
  have hdleq : ∀ k, dl k = qsched K δ k := by
    intro k
    induction k with
    | zero => rw [hdl0, qsched_zero hK0.ne']
    | succ k ih => rw [hdls k, ih, qsched_succ hK0.ne']
  -- the process is the one `corollary_C3` speaks about
  have hSeq : ∀ y, C.S y = (sigt f y)⁻¹ • Ntil f y := by
    intro y
    show (C.sigt y)⁻¹ • C.Ntil y = _
    rw [hsigC, hNt]
  have hxeq : ∀ k ω, x k ω = xProcG C x₀ (qsched K δ) k ω := by
    intro k
    induction k with
    | zero => intro ω; rw [hx0]; rfl
    | succ k ih =>
        intro ω
        rw [hxs k ω, ih ω, ← hSeq, hdleq k, xProcG_succ]
        rfl
  have hyeq : ∀ k ω, x k ω + dl k • clamp (ω k)
      = yProcG C x₀ (qsched K δ) k ω := by
    intro k ω
    rw [hxeq k ω, hdleq k, yProcG]
  refine le_trans (measure_mono ?_)
    (hmain δ hδ hδ1 hcond1 hcond2 (by linarith) (by linarith) x₀ hx₀)
  rintro ω ⟨k, hk | hk⟩
  · exact ⟨k, Or.inl (by rw [← hxeq k ω, ← hdleq k]; exact hk)⟩
  · refine ⟨k, Or.inr ?_⟩
    rw [cct_top, ← hyeq k ω]
    exact hk

include D in
/-- **Theorem 4.9**, self-contained. -/
theorem mpe_quadratic_C3_proof
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1)) (hsq : Squarefree A.charpoly)
    (U : (Fin (M + 2) → ℝ) → Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hU : ∀ y i j, U y i j = f^[(j : ℕ) + 1] y i - f^[(j : ℕ)] y i)
    (c : ℕ → (Fin (M + 2) → ℝ) → ℝ)
    (hcAdj : ∀ (j : Fin (M + 2)) y,
      c (j : ℕ) y = (U y).adjugate.mulVec (fun i => -(f^[M + 3] y i - f^[M + 2] y i)) j)
    (hcDet : ∀ y, c (M + 2) y = (U y).det)
    (sg : (Fin (M + 2) → ℝ) → ℝ) (Nt : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hsg : ∀ y, sg y = ∑ j ∈ Finset.range (M + 3), c j y)
    (hNt : ∀ y, Nt y = ∑ j ∈ Finset.range (M + 3), c j y • f^[j] y)
 :
    ∃ K dstar Cst : ℝ, 1 ≤ K ∧ 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
      ∀ dl : ℕ → ℝ, dl 0 = δ → (∀ k, dl (k + 1) = K * (dl k) ^ 2) →
      ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
        (∀ ω, x 0 ω = x₀) →
        (∀ k ω, x (k + 1) ω
          = (sg (x k ω + (dl k) • fun i => max (-1) (min 1 (ω k i))))⁻¹
            • Nt (x k ω + (dl k) • fun i => max (-1) (min 1 (ω k i)))) →
        (Measure.infinitePi fun _ : ℕ =>
            Measure.pi fun _ : Fin (M + 2) =>
              ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
            {ω | ∃ k, dl k < ‖x k ω‖
                  ∨ Matrix.det (U (x k ω + dl k • fun i => max (-1) (min 1 (ω k i)))) = 0}
          ≤ ENNReal.ofReal (Cst * δ * (1 + max 0 (-Real.log δ)) ^ (M + 1)) := by
  classical
  -- identify the data with the construction of this file
  have hAeq : A = Amat f := by rw [hAdef, Amat]
  subst hAeq
  have hUeq : ∀ y, U y = Ueval f y := by
    intro y
    funext i j
    rw [hU y i j]
    rfl
  have hceq : ∀ j ∈ Finset.range (M + 3), ∀ y, c j y = cct f j y := by
    intro j hj y
    rw [Finset.mem_range] at hj
    rcases Nat.lt_or_ge j (M + 2) with hlt | hge
    · rw [cct, dif_pos hlt, ← hUeq y]
      have h := hcAdj ⟨j, hlt⟩ y
      rw [h]
      rfl
    · have hjeq : j = M + 2 := by omega
      subst hjeq
      rw [hcDet y, cct, dif_neg (by omega), hUeq y]
  have hsgeq : ∀ y, sg y = sigt f y := by
    intro y
    rw [hsg y, sigt]
    exact Finset.sum_congr rfl fun j hj => hceq j hj y
  have hNteq : ∀ y, Nt y = Ntil f y := by
    intro y
    rw [hNt y, Ntil]
    exact Finset.sum_congr rfl fun j hj => by rw [hceq j hj y]
  obtain ⟨K, dstar, Cst, hK1, hd0, hC0, hmain⟩ := D.corollary_small_C3 hA hsq
  refine ⟨K, dstar, Cst, hK1, hd0, hC0, ?_⟩
  intro δ hδ hδt x₀ hx₀ dl hdl0 hdls x hx0 hxs
  have hset : {ω : ℕ → Fin (M + 2) → ℝ | ∃ k, dl k < ‖x k ω‖
        ∨ Matrix.det (U (x k ω + dl k • fun i => max (-1) (min 1 (ω k i)))) = 0}
      = {ω | ∃ k, ¬ ‖x k ω‖ ≤ dl k
          ∨ Matrix.det (fun i j => Umat f i j (x k ω + dl k • clamp (ω k))) = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, not_le]
    constructor
    · rintro ⟨k, hk | hk⟩
      · exact ⟨k, Or.inl hk⟩
      · exact ⟨k, Or.inr (by rw [Umat_eval, ← hUeq]; exact hk)⟩
    · rintro ⟨k, hk | hk⟩
      · exact ⟨k, Or.inl hk⟩
      · exact ⟨k, Or.inr (by rw [Umat_eval, ← hUeq] at hk; exact hk)⟩
  rw [hset]
  refine hmain δ hδ hδt x₀ hx₀ dl hdl0 hdls x hx0 ?_
  intro k ω
  rw [hxs k ω, hsgeq, hNteq]
  rfl


end TopLevel



end SmoothData

end MPE
