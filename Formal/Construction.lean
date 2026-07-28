import Formal.Degree

/-!
# The MPE construction as polynomials

Instantiating the degree machinery: for a polynomial map `f(x) = Ax + q(x)` with `q` of
degree `≥ 2`, the iterates `f^j` decompose as `A^j x + g_j` with `g_j` of degree `≥ 2`.
This is the last input `LowDeg.Ntilde` needs, and it discharges the degree side of
`CycleData.hN`.

Composition of polynomial maps is `MvPolynomial.bind₁`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace MPE

open MvPolynomial Finset

variable {σ τ : Type*} [DecidableEq σ] [DecidableEq τ] [Fintype σ] [Fintype τ]

/-! ### Composition preserves low degree -/

lemma bind₁_eq_sum (h : σ → MvPolynomial τ ℝ) (p : MvPolynomial σ ℝ) :
    bind₁ h p = ∑ d ∈ p.support, C (coeff d p) * ∏ i ∈ d.support, (h i) ^ (d i) :=
  MvPolynomial.eval₂_eq _ _ _

/-- Powers multiply degrees. -/
lemma LowDeg.pow {a : ℕ} {p : MvPolynomial σ ℝ} (hp : LowDeg a p) (m : ℕ) :
    LowDeg (m * a) (p ^ m) := by
  induction m with
  | zero => simpa using lowDeg_zero (p ^ 0)
  | succ k ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hp

/-- **Composition.**  Substituting maps that vanish at the origin into a polynomial of
degree `≥ k` gives a polynomial of degree `≥ k`.  This is what propagates the degree bound
along the iterates `f^j`. -/
theorem LowDeg.bind₁ {k : ℕ} {p : MvPolynomial σ ℝ} {h : σ → MvPolynomial τ ℝ}
    (hp : LowDeg k p) (hh : ∀ i, LowDeg 1 (h i)) :
    LowDeg k (MvPolynomial.bind₁ h p) := by
  classical
  rw [bind₁_eq_sum]
  refine LowDeg.sum (k := k) (f := fun d => C (coeff d p) * ∏ i ∈ d.support, (h i) ^ (d i)) ?_
  intro d hd
  have hprod : LowDeg (∑ i ∈ d.support, d i * 1) (∏ i ∈ d.support, (h i) ^ (d i)) :=
    LowDeg.prod (k := fun i => d i * 1) fun i _ => (hh i).pow (d i)
  have hdeg : (∑ i ∈ d.support, d i * 1) = d.degree := by
    simp [Finsupp.degree_apply]
  rw [hdeg] at hprod
  have : LowDeg (0 + k) (C (coeff d p) * ∏ i ∈ d.support, (h i) ^ (d i)) :=
    (lowDeg_zero _).mul (hprod.mono (hp d hd))
  simpa using this

/-! ### The polynomial map and its iterates -/

variable {n : ℕ}

/-- The linear polynomial map `x ↦ Mx`. -/
noncomputable def lin (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ k, C (M i k) * X k

lemma lowDeg_lin (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : LowDeg 1 (lin M i) := by
  refine LowDeg.sum (k := 1) (f := fun k => C (M i k) * X k) fun k _ => ?_
  have hX : LowDeg 1 (X k : MvPolynomial (Fin n) ℝ) := by
    intro d hd
    rw [MvPolynomial.support_X] at hd
    simp at hd
    subst hd
    simp [Finsupp.degree_apply]
  have := (lowDeg_zero (C (M i k))).mul hX
  simpa using this

/-- Substituting a map into a linear map composes the matrices. -/
lemma bind₁_lin (M : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → MvPolynomial (Fin n) ℝ)
    (i : Fin n) : MvPolynomial.bind₁ h (lin M i) = ∑ k, C (M i k) * h k := by
  rw [lin, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right]

/-- The iterates of the polynomial map `f`. -/
noncomputable def iter (f : Fin n → MvPolynomial (Fin n) ℝ) :
    ℕ → Fin n → MvPolynomial (Fin n) ℝ
  | 0 => fun i => X i
  | (j + 1) => fun i => MvPolynomial.bind₁ (iter f j) (f i)

lemma lowDeg_iter {f : Fin n → MvPolynomial (Fin n) ℝ} (hf : ∀ i, LowDeg 1 (f i)) :
    ∀ j i, LowDeg 1 (iter f j i) := by
  intro j
  induction j with
  | zero =>
      intro i
      show LowDeg 1 (X i)
      intro d hd
      rw [MvPolynomial.support_X] at hd
      simp at hd
      subst hd
      simp [Finsupp.degree_apply]
  | succ k ih => exact fun i => (hf i).bind₁ ih

/-- **The decomposition `f^j = A^j x + g_j`.**

For `f = lin A + q` with `q` of degree `≥ 2`, the iterate `f^j` differs from the linear
map `A^j x` by a polynomial of degree `≥ 2`.  This supplies the `g_j` that
`LowDeg.Ntilde` consumes. -/
theorem lowDeg_iter_sub_lin {A : Matrix (Fin n) (Fin n) ℝ}
    {q f : Fin n → MvPolynomial (Fin n) ℝ}
    (hq : ∀ i, LowDeg 2 (q i)) (hf : ∀ i, f i = lin A i + q i) :
    ∀ j i, LowDeg 2 (iter f j i - lin (A ^ j) i) := by
  have hf1 : ∀ i, LowDeg 1 (f i) := by
    intro i; rw [hf i]; exact (lowDeg_lin A i).add ((hq i).mono (by norm_num))
  intro j
  induction j with
  | zero =>
      intro i
      have : iter f 0 i - lin (A ^ 0) i = X i - lin 1 i := by simp [iter]
      rw [this, lin]
      have hone : ∑ k, C ((1 : Matrix (Fin n) (Fin n) ℝ) i k) * X k
          = (X i : MvPolynomial (Fin n) ℝ) := by
        rw [Finset.sum_eq_single i]
        · simp [Matrix.one_apply]
        · intro b _ hb; simp [Matrix.one_apply, Ne.symm hb]
        · intro h; simp at h
      rw [hone, sub_self]
      exact lowDeg_of_zero 2
  | succ j ih =>
      intro i
      -- f^{j+1} = ∑_k A i k · f^j_k + q(f^j), and f^j_k = (A^j x)_k + g_j k
      have hexp : iter f (j + 1) i
          = (∑ k, C (A i k) * iter f j k) + MvPolynomial.bind₁ (iter f j) (q i) := by
        show MvPolynomial.bind₁ (iter f j) (f i) = _
        rw [hf i, map_add, bind₁_lin]
      have hlin : lin (A ^ (j + 1)) i = ∑ k, C (A i k) * lin (A ^ j) k := by
        rw [pow_succ']
        simp only [lin, Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [← mul_assoc, ← map_mul]
      rw [hexp, hlin, add_sub_right_comm, ← Finset.sum_sub_distrib]
      refine LowDeg.add ?_ ((hq i).bind₁ (lowDeg_iter hf1 j))
      refine LowDeg.sum (k := 2)
        (f := fun k => C (A i k) * iter f j k - C (A i k) * lin (A ^ j) k) fun k _ => ?_
      rw [← mul_sub]
      have := (lowDeg_zero (C (A i k))).mul (ih k)
      simpa using this

end MPE
