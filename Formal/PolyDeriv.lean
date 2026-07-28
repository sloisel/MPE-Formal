import Mathlib
import Formal.Degree

/-!
# Differentiating a polynomial along one coordinate

Appendix §9 needs a `C¹` bound on the remainder `R = σ̃ - Q̃`, and `Formal/Annulus.lean` asks
for it in the form `HasDerivAt (fun t => E (Fin.cons t u')) _ t` with an explicit bound on
the derivative.

Mathlib has `MvPolynomial.pderiv`, but that is the *formal* derivative and there is no
bridge from it to `fderiv`/`HasDerivAt` of the evaluation map.  Rather than build that
bridge, we differentiate the monomial expansion directly: fixing all but the first
coordinate turns

    eval (Fin.cons t u') P  =  ∑_{d ∈ supp P} (coeff d P · ∏_j u'ⱼ^{d(j+1)}) · t^{d 0},

a finite sum of monomials in `t`, whose derivative is immediate.  The same expansion gives
the bound, with the explicit constant `∑ |coeff d P| · deg d`.
-/

namespace MPE

open MvPolynomial Finset

variable {m : ℕ}

/-- The coefficient of `t^{d 0}` when all but the first coordinate is frozen at `u'`. -/
noncomputable def frozenCoeff (P : MvPolynomial (Fin (m + 1)) ℝ) (u' : Fin m → ℝ)
    (d : Fin (m + 1) →₀ ℕ) : ℝ :=
  MvPolynomial.coeff d P * ∏ j : Fin m, u' j ^ d j.succ

/-- **The expansion.**  Freezing all but the first coordinate exhibits the evaluation as a
polynomial in `t`. -/
lemma eval_cons_eq (P : MvPolynomial (Fin (m + 1)) ℝ) (u' : Fin m → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.cons t u') P
      = ∑ d ∈ P.support, frozenCoeff P u' d * t ^ d 0 := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fin.prod_univ_succ, frozenCoeff]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- **The derivative.**  Differentiating the expansion term by term. -/
theorem hasDerivAt_eval_cons (P : MvPolynomial (Fin (m + 1)) ℝ) (u' : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (fun t => MvPolynomial.eval (Fin.cons t u') P)
      (∑ d ∈ P.support, frozenCoeff P u' d * ((d 0 : ℝ) * t ^ (d 0 - 1))) t := by
  have hfun : (fun t => MvPolynomial.eval (Fin.cons t u') P)
      = fun t => ∑ d ∈ P.support, frozenCoeff P u' d * t ^ d 0 := by
    funext t; exact eval_cons_eq P u' t
  rw [hfun]
  refine HasDerivAt.fun_sum fun d _ => ?_
  exact (hasDerivAt_pow (d 0) t).const_mul (frozenCoeff P u' d)

/-- The explicit constant in the derivative bound. -/
noncomputable def derivBound (P : MvPolynomial (Fin (m + 1)) ℝ) : ℝ :=
  ∑ d ∈ P.support, |MvPolynomial.coeff d P| * (d.degree : ℝ)

lemma derivBound_nonneg (P : MvPolynomial (Fin (m + 1)) ℝ) : 0 ≤ derivBound P :=
  Finset.sum_nonneg fun d _ => by positivity

/-- The total degree of an exponent vector on `Fin (m+1)` is the sum over all coordinates. -/
lemma degree_eq_sum_univ (d : Fin (m + 1) →₀ ℕ) : d.degree = ∑ i : Fin (m + 1), d i := by
  rw [Finsupp.degree_apply]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  simpa using hi

/-- **The derivative bound.**  If every monomial of `P` has degree at least `k+1`, then the
derivative along the first coordinate is `O(‖y‖^k)` on the unit ball, with constant
`∑ |coeff| · deg`. -/
theorem LowDeg.abs_deriv_cons_le {k : ℕ} {P : MvPolynomial (Fin (m + 1)) ℝ}
    (hP : LowDeg (k + 1) P) (u' : Fin m → ℝ) (t : ℝ)
    (hy : ‖(Fin.cons t u' : Fin (m + 1) → ℝ)‖ ≤ 1) :
    |∑ d ∈ P.support, frozenCoeff P u' d * ((d 0 : ℝ) * t ^ (d 0 - 1))|
      ≤ derivBound P * ‖(Fin.cons t u' : Fin (m + 1) → ℝ)‖ ^ k := by
  classical
  set y : Fin (m + 1) → ℝ := Fin.cons t u' with hydef
  have hy0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  have hcoord : ∀ i : Fin (m + 1), |y i| ≤ ‖y‖ := fun i => by
    simpa using norm_le_pi_norm y i
  have hterm : ∀ d ∈ P.support,
      |frozenCoeff P u' d * ((d 0 : ℝ) * t ^ (d 0 - 1))|
        ≤ |MvPolynomial.coeff d P| * (d.degree : ℝ) * ‖y‖ ^ k := by
    intro d hd
    rcases Nat.eq_zero_or_pos (d 0) with h0 | h0
    · simp [h0]
      positivity
    -- `d 0 ≥ 1`
    have hdeg : k + 1 ≤ d.degree := hP d hd
    have hsplit : d.degree = d 0 + ∑ j : Fin m, d j.succ := by
      rw [degree_eq_sum_univ, Fin.sum_univ_succ]
    -- bound the frozen coefficient
    have hfz : |frozenCoeff P u' d| ≤ |MvPolynomial.coeff d P| * ‖y‖ ^ (∑ j : Fin m, d j.succ) := by
      rw [frozenCoeff, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |∏ j : Fin m, u' j ^ d j.succ| = ∏ j : Fin m, |u' j| ^ d j.succ := by
            rw [Finset.abs_prod]
            exact Finset.prod_congr rfl fun j _ => abs_pow _ _
        _ ≤ ∏ j : Fin m, ‖y‖ ^ d j.succ := by
            refine Finset.prod_le_prod (fun j _ => by positivity) fun j _ => ?_
            refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
            have : u' j = y j.succ := by rw [hydef, Fin.cons_succ]
            rw [this]; exact hcoord _
        _ = ‖y‖ ^ (∑ j : Fin m, d j.succ) := Finset.prod_pow_eq_pow_sum _ _ _
    -- bound the `t` factor
    have ht : |(d 0 : ℝ) * t ^ (d 0 - 1)| ≤ (d 0 : ℝ) * ‖y‖ ^ (d 0 - 1) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (d 0))]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
      have : t = y 0 := by rw [hydef, Fin.cons_zero]
      rw [this]; exact hcoord _
    -- combine
    have hexp : (d 0 - 1) + (∑ j : Fin m, d j.succ) = d.degree - 1 := by omega
    calc |frozenCoeff P u' d * ((d 0 : ℝ) * t ^ (d 0 - 1))|
        = |frozenCoeff P u' d| * |(d 0 : ℝ) * t ^ (d 0 - 1)| := abs_mul _ _
      _ ≤ (|MvPolynomial.coeff d P| * ‖y‖ ^ (∑ j : Fin m, d j.succ)) *
            ((d 0 : ℝ) * ‖y‖ ^ (d 0 - 1)) :=
          mul_le_mul hfz ht (abs_nonneg _) (by positivity)
      _ = |MvPolynomial.coeff d P| * (d 0 : ℝ) * ‖y‖ ^ (d.degree - 1) := by
          rw [← hexp, pow_add]; ring
      _ ≤ |MvPolynomial.coeff d P| * (d.degree : ℝ) * ‖y‖ ^ k := by
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            exact_mod_cast (by omega : d 0 ≤ d.degree)
          · exact pow_le_pow_of_le_one hy0 hy (by omega)
  calc |∑ d ∈ P.support, frozenCoeff P u' d * ((d 0 : ℝ) * t ^ (d 0 - 1))|
      ≤ ∑ d ∈ P.support, |frozenCoeff P u' d * ((d 0 : ℝ) * t ^ (d 0 - 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.support, |MvPolynomial.coeff d P| * (d.degree : ℝ) * ‖y‖ ^ k :=
        Finset.sum_le_sum hterm
    _ = derivBound P * ‖y‖ ^ k := by rw [derivBound, ← Finset.sum_mul]

/-- **Homogeneous scaling.**  A form of degree `k` scales by `r^k`.  Mathlib has the
`IsHomogeneous` predicate but not this, its defining analytic property. -/
theorem IsHomogeneous.eval_smul {k : ℕ} {P : MvPolynomial (Fin (m + 1)) ℝ}
    (hP : P.IsHomogeneous k) (r : ℝ) (z : Fin (m + 1) → ℝ) :
    MvPolynomial.eval (r • z) P = r ^ k * MvPolynomial.eval z P := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = k := by
    have h := hP (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
    exact h
  have hprod : ∏ i, (r • z) i ^ d i = r ^ k * ∏ i, z i ^ d i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    congr 2
    rw [← hdeg, degree_eq_sum_univ]
  rw [hprod]; ring

/-! ### Rescaling

The annuli of §9 are handled by rescaling: on the annulus of radius `≍ r` one studies
`E_r(z) = R(r z) / r^k`.  If every monomial of `R` has degree at least `k+1` then the
derivative of `E_r` along a coordinate is `O(r)` on the unit ball — the perturbation is
small *because* the remainder has one more degree than the leading form. -/

lemma cons_smul (r t : ℝ) (u' : Fin m → ℝ) :
    (Fin.cons (r * t) (r • u') : Fin (m + 1) → ℝ) = r • (Fin.cons t u' : Fin (m + 1) → ℝ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Pi.smul_apply]

lemma norm_cons_smul (r : ℝ) (hr : 0 ≤ r) (t : ℝ) (u' : Fin m → ℝ) :
    ‖(Fin.cons (r * t) (r • u') : Fin (m + 1) → ℝ)‖
      = r * ‖(Fin.cons t u' : Fin (m + 1) → ℝ)‖ := by
  rw [cons_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]

/-- The derivative of the rescaled polynomial along the first coordinate. -/
theorem hasDerivAt_eval_cons_scaled (R : MvPolynomial (Fin (m + 1)) ℝ) (k : ℕ) (r : ℝ)
    (u' : Fin m → ℝ) (t : ℝ) :
    HasDerivAt (fun t => MvPolynomial.eval (Fin.cons (r * t) (r • u')) R / r ^ k)
      ((∑ d ∈ R.support,
          frozenCoeff R (r • u') d * ((d 0 : ℝ) * (r * t) ^ (d 0 - 1))) * r / r ^ k) t := by
  have h1 : HasDerivAt (fun t : ℝ => r * t) r t := by
    simpa using (hasDerivAt_id t).const_mul r
  have h2 := (hasDerivAt_eval_cons R (r • u') (r * t)).comp t h1
  exact h2.div_const (r ^ k)

/-- **The rescaled derivative is `O(r)`.**  If every monomial of `R` has degree at least
`k+1`, the derivative of `z ↦ R(rz)/r^k` along the first coordinate is at most
`derivBound R · r` on the unit ball. -/
theorem LowDeg.abs_deriv_scaled_le {k : ℕ} {R : MvPolynomial (Fin (m + 1)) ℝ}
    (hR : LowDeg (k + 1) R) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (u' : Fin m → ℝ) (t : ℝ)
    (hz : ‖(Fin.cons t u' : Fin (m + 1) → ℝ)‖ ≤ 1) :
    |(∑ d ∈ R.support,
        frozenCoeff R (r • u') d * ((d 0 : ℝ) * (r * t) ^ (d 0 - 1))) * r / r ^ k|
      ≤ derivBound R * r := by
  have hnorm : ‖(Fin.cons (r * t) (r • u') : Fin (m + 1) → ℝ)‖
      = r * ‖(Fin.cons t u' : Fin (m + 1) → ℝ)‖ := norm_cons_smul r hr.le t u'
  have hle1 : ‖(Fin.cons (r * t) (r • u') : Fin (m + 1) → ℝ)‖ ≤ 1 := by
    rw [hnorm]
    calc r * ‖(Fin.cons t u' : Fin (m + 1) → ℝ)‖ ≤ r * 1 :=
          mul_le_mul_of_nonneg_left hz hr.le
      _ ≤ 1 := by linarith
  -- the inner derivative is `O((r‖z‖)^k)`
  have hinner := hR.abs_deriv_cons_le (r • u') (r * t) hle1
  have hrk : (0:ℝ) < r ^ k := pow_pos hr k
  rw [abs_div, abs_mul, abs_of_pos hr, abs_of_pos hrk, div_le_iff₀ hrk]
  have hstep : |∑ d ∈ R.support,
      frozenCoeff R (r • u') d * ((d 0 : ℝ) * (r * t) ^ (d 0 - 1))|
      ≤ derivBound R * r ^ k := by
    refine le_trans hinner ?_
    rw [hnorm]
    have : (r * ‖(Fin.cons t u' : Fin (m + 1) → ℝ)‖) ^ k ≤ r ^ k := by
      rw [mul_pow]
      have hzk : ‖(Fin.cons t u' : Fin (m + 1) → ℝ)‖ ^ k ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) hz
      nlinarith [pow_pos hr k, pow_nonneg (norm_nonneg (Fin.cons t u' : Fin (m+1) → ℝ)) k]
    exact mul_le_mul_of_nonneg_left this (derivBound_nonneg R)
  calc |∑ d ∈ R.support, frozenCoeff R (r • u') d * ((d 0 : ℝ) * (r * t) ^ (d 0 - 1))| * r
      ≤ (derivBound R * r ^ k) * r := mul_le_mul_of_nonneg_right hstep hr.le
    _ = derivBound R * r * r ^ k := by ring

/-! ### An arbitrary coordinate

The chart cover of `Formal/Annulus.lean` fibres in *every* coordinate, not just the first, so
the bounds above are needed for each `κ : Fin (m+1)`.  Rather than redo the expansion, rename
along `Equiv.swap 0 κ`: that changes neither `LowDeg` (degrees of exponent vectors are
permutation-invariant) nor `derivBound` (which involves only `|coeff|` and the *total* degree),
and it turns `Function.update v κ ·` into `Fin.cons · ·`. -/

lemma cons_eq_update (t : ℝ) (w : Fin (m + 1) → ℝ) :
    (Fin.cons t (fun j : Fin m => w j.succ) : Fin (m + 1) → ℝ) = Function.update w 0 t := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.succ_ne_zero]

lemma swap_apply_eq_zero_iff (κ i : Fin (m + 1)) :
    Equiv.swap (0 : Fin (m + 1)) κ i = 0 ↔ i = κ := by
  constructor
  · intro hz
    have h1 := congrArg (Equiv.swap (0 : Fin (m + 1)) κ) hz
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at h1
  · intro h; rw [h, Equiv.swap_apply_right]

lemma update_comp_swap (κ : Fin (m + 1)) (v : Fin (m + 1) → ℝ) (t : ℝ) :
    (Function.update (fun i => v (Equiv.swap (0 : Fin (m + 1)) κ i)) 0 t)
        ∘ (Equiv.swap (0 : Fin (m + 1)) κ)
      = Function.update v κ t := by
  funext i
  by_cases hi : i = κ
  · subst hi
    simp [Equiv.swap_apply_right]
  · have hne : Equiv.swap (0 : Fin (m + 1)) κ i ≠ 0 := fun hz =>
      hi ((swap_apply_eq_zero_iff κ i).mp hz)
    simp only [Function.comp_apply, Function.update_of_ne hne, Function.update_of_ne hi]
    show v (Equiv.swap (0 : Fin (m + 1)) κ (Equiv.swap (0 : Fin (m + 1)) κ i)) = v i
    rw [Equiv.swap_apply_self]

/-- Freezing all but coordinate `κ` is freezing all but coordinate `0` of the renamed
polynomial. -/
theorem eval_update_eq_eval_cons (R : MvPolynomial (Fin (m + 1)) ℝ) (κ : Fin (m + 1))
    (v : Fin (m + 1) → ℝ) (t : ℝ) :
    MvPolynomial.eval (Function.update v κ t) R
      = MvPolynomial.eval
          (Fin.cons t (fun j : Fin m => v (Equiv.swap (0 : Fin (m + 1)) κ j.succ)))
          (MvPolynomial.rename (Equiv.swap (0 : Fin (m + 1)) κ) R) := by
  rw [MvPolynomial.eval_rename,
    show (Fin.cons t (fun j : Fin m => v (Equiv.swap (0 : Fin (m + 1)) κ j.succ)) :
        Fin (m + 1) → ℝ)
      = Function.update (fun i => v (Equiv.swap (0 : Fin (m + 1)) κ i)) 0 t from
      cons_eq_update t (fun i => v (Equiv.swap (0 : Fin (m + 1)) κ i)),
    update_comp_swap]

lemma lowDeg_rename {k : ℕ} {R : MvPolynomial (Fin (m + 1)) ℝ} (hR : LowDeg k R)
    (σ : Fin (m + 1) ≃ Fin (m + 1)) : LowDeg k (MvPolynomial.rename σ R) := by
  classical
  intro d hd
  rw [MvPolynomial.support_rename_of_injective σ.injective, Finset.mem_image] at hd
  obtain ⟨e, he, rfl⟩ := hd
  rw [Finsupp.degree_mapDomain]
  exact hR e he

lemma derivBound_rename (R : MvPolynomial (Fin (m + 1)) ℝ)
    (σ : Fin (m + 1) ≃ Fin (m + 1)) :
    derivBound (MvPolynomial.rename σ R) = derivBound R := by
  classical
  rw [derivBound, derivBound, MvPolynomial.support_rename_of_injective σ.injective,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective σ.injective h]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain _ σ.injective, Finsupp.degree_mapDomain]

lemma norm_comp_le {ι : Type*} [Fintype ι] (f : ι → ℝ) (σ : ι → ι) : ‖f ∘ σ‖ ≤ ‖f‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr fun i => norm_le_pi_norm f (σ i)

/-- **The rescaled derivative along an arbitrary coordinate.**  If every monomial of `R` has
degree at least `k+1`, then `v ↦ R(rv)/r^k` has, in each coordinate, a derivative bounded by
`derivBound R · r` on the unit ball. -/
theorem LowDeg.exists_deriv_update {k : ℕ} {R : MvPolynomial (Fin (m + 1)) ℝ}
    (hR : LowDeg (k + 1) R) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (κ : Fin (m + 1)) :
    ∃ g : ℝ → (Fin (m + 1) → ℝ) → ℝ,
      (∀ v t, HasDerivAt
          (fun t => MvPolynomial.eval (r • Function.update v κ t) R / r ^ k) (g t v) t)
        ∧ ∀ v t, ‖(Function.update v κ t : Fin (m + 1) → ℝ)‖ ≤ 1 →
            |g t v| ≤ derivBound R * r := by
  classical
  refine ⟨fun t v =>
    (∑ d ∈ (MvPolynomial.rename (Equiv.swap (0 : Fin (m + 1)) κ) R).support,
      frozenCoeff (MvPolynomial.rename (Equiv.swap (0 : Fin (m + 1)) κ) R)
          (r • fun j : Fin m => v (Equiv.swap (0 : Fin (m + 1)) κ j.succ)) d
        * ((d 0 : ℝ) * (r * t) ^ (d 0 - 1))) * r / r ^ k, ?_, ?_⟩
  · intro v t
    have hfun : (fun t => MvPolynomial.eval (r • Function.update v κ t) R / r ^ k)
        = fun t => MvPolynomial.eval
            (Fin.cons (r * t)
              (r • fun j : Fin m => v (Equiv.swap (0 : Fin (m + 1)) κ j.succ)))
            (MvPolynomial.rename (Equiv.swap (0 : Fin (m + 1)) κ) R) / r ^ k := by
      funext t
      have h1 : (r : ℝ) • (Function.update v κ t) = Function.update (r • v) κ (r * t) := by
        funext i
        by_cases hi : i = κ
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      have h2 : (fun j : Fin m => (r • v) (Equiv.swap (0 : Fin (m + 1)) κ j.succ))
          = (r • fun j : Fin m => v (Equiv.swap (0 : Fin (m + 1)) κ j.succ)) := by
        funext j; rfl
      rw [h1, eval_update_eq_eval_cons R κ (r • v) (r * t), h2]
    rw [hfun]
    exact hasDerivAt_eval_cons_scaled
      (MvPolynomial.rename (Equiv.swap (0 : Fin (m + 1)) κ) R) k r
      (fun j : Fin m => v (Equiv.swap (0 : Fin (m + 1)) κ j.succ)) t
  · intro v t hnorm
    have hz : ‖(Fin.cons t (fun j : Fin m => v (Equiv.swap (0 : Fin (m + 1)) κ j.succ)) :
        Fin (m + 1) → ℝ)‖ ≤ 1 := by
      have h3 : (Function.update (fun i => v (Equiv.swap (0 : Fin (m + 1)) κ i)) 0 t)
          = (Function.update v κ t) ∘ (Equiv.swap (0 : Fin (m + 1)) κ) := by
        rw [← update_comp_swap κ v t]
        funext i
        show Function.update (fun i => v (Equiv.swap (0 : Fin (m + 1)) κ i)) 0 t i
          = Function.update (fun i => v (Equiv.swap (0 : Fin (m + 1)) κ i)) 0 t
              (Equiv.swap (0 : Fin (m + 1)) κ (Equiv.swap (0 : Fin (m + 1)) κ i))
        rw [Equiv.swap_apply_self]
      rw [cons_eq_update t (fun i => v (Equiv.swap (0 : Fin (m + 1)) κ i)), h3]
      exact le_trans (norm_comp_le _ _) hnorm
    have hb := (lowDeg_rename hR (Equiv.swap (0 : Fin (m + 1)) κ)).abs_deriv_scaled_le hr hr1
      (fun j : Fin m => v (Equiv.swap (0 : Fin (m + 1)) κ j.succ)) t hz
    rwa [derivBound_rename R (Equiv.swap (0 : Fin (m + 1)) κ)] at hb

end MPE
