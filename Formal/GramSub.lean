import Mathlib
import Formal.Sublevel
import Formal.MaxVector

/-!
# The sublevel bound at the general window

At the full window `k = n` the degeneracy form is `Δ = det K`, of degree `n`, and
`Formal/KrylovSub.lean` bounds its sublevel sets.  At the general window `k = deg m_A ≤ n`
the matrix `K(x) ∈ ℝ^{n×k}` is rectangular and the degeneracy form is the Gram determinant

    Δ(x) = det (K(x)ᵀ K(x)),

of degree `d = 2k`.  This file is the exact analogue of `KrylovSub.lean` for that form.

The structure is the same, and for the same reason: `K` is *linear* in `x`, so along a line
`K(a + t v) = K(a) + t K(v)`, the Gram matrix is quadratic in `t`, and
`Sublevel.detGramPencil` gives the restriction as a polynomial of degree `2k` whose top
coefficient is `det(K(v)ᵀ K(v)) = Δ(v)` — the same on every line, which is what
`Sublevel.sublevel_dir` needs.
-/

namespace MPE

open MeasureTheory Metric Set Matrix Polynomial

/-! ### The rectangular Krylov matrix -/

section Gram

variable {n k : ℕ}

/-- `K(x) = [(A-I)x, (A-I)Ax, …, (A-I)A^{k-1}x] ∈ ℝ^{n×k}`, the matrix of the general
window.  At `k = n` this is `(A - I)` times the plain Krylov matrix. -/
noncomputable def gkry (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => (((A - 1) * A ^ (j : ℕ)).mulVec x) i

/-- The degeneracy form of the general window, `Δ = det(KᵀK)`, of degree `2k`. -/
noncomputable def gramDelta (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  Matrix.det ((gkry (k := k) A x)ᵀ * (gkry (k := k) A x))

lemma gkry_add_smul (A : Matrix (Fin n) (Fin n) ℝ) (a v : Fin n → ℝ) (t : ℝ) :
    gkry (k := k) A (a + t • v) = gkry (k := k) A a + t • gkry (k := k) A v := by
  ext i j
  simp only [gkry, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec_add, Matrix.mulVec_smul]

lemma gkry_smul (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (x : Fin n → ℝ) :
    gkry (k := k) A (r • x) = r • gkry (k := k) A x := by
  ext i j
  simp only [gkry, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Matrix.mulVec_smul]
  rfl

/-- `Δ` is homogeneous of degree `2k`. -/
lemma gramDelta_smul (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (x : Fin n → ℝ) :
    gramDelta (k := k) A (r • x) = r ^ (2 * k) * gramDelta (k := k) A x := by
  rw [gramDelta, gramDelta, gkry_smul]
  have hT : ((r • gkry (k := k) A x)ᵀ * (r • gkry (k := k) A x))
      = (r ^ 2) • ((gkry (k := k) A x)ᵀ * (gkry (k := k) A x)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  rw [hT, Matrix.det_smul, Fintype.card_fin, ← pow_mul, mul_comm 2 k]

/-! ### The line restriction -/

/-- The restriction of `Δ` to the line `a + t v`, as a polynomial in `t`. -/
noncomputable def gramPoly (A : Matrix (Fin n) (Fin n) ℝ) (a v : Fin n → ℝ) :
    Polynomial ℝ :=
  detGramPencil (gkry (k := k) A a) (gkry (k := k) A v)

lemma gramPoly_eval (A : Matrix (Fin n) (Fin n) ℝ) (a v : Fin n → ℝ) (t : ℝ) :
    (gramPoly (k := k) A a v).eval t = gramDelta (k := k) A (a + t • v) := by
  rw [gramPoly, detGramPencil_eval, gramDelta, gkry_add_smul]

lemma gramPoly_natDegree_le (A : Matrix (Fin n) (Fin n) ℝ) (a v : Fin n → ℝ) :
    (gramPoly (k := k) A a v).natDegree ≤ 2 * k :=
  detGramPencil_natDegree_le _ _

/-- **The leading coefficient is `Δ(v)`, independent of the base point.** -/
lemma gramPoly_coeff (A : Matrix (Fin n) (Fin n) ℝ) (a v : Fin n → ℝ) :
    (gramPoly (k := k) A a v).coeff (2 * k) = gramDelta (k := k) A v :=
  detGramPencil_coeff _ _

/-! ### Continuity -/

lemma continuous_gramDelta (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun x : Fin n → ℝ => gramDelta (k := k) A x := by
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, gkry, Matrix.of_apply, Matrix.mulVec,
    dotProduct]
  refine continuous_finsetSum _ fun l _ => ?_
  exact (continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_apply m)).mul
    (continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_apply m))

lemma measurable_gramDelta (A : Matrix (Fin n) (Fin n) ℝ) :
    Measurable fun x : Fin n → ℝ => gramDelta (k := k) A x :=
  (continuous_gramDelta A).measurable

end Gram

/-! ### Normalising the direction -/

section GramDir

variable {m k : ℕ}

/-- **A good direction can be normalised to have first coordinate `1`.**  Same argument as
`exists_good_dir`: the line `v + t e₀` meets `{Δ ≠ 0}` off the finite root set of a
polynomial, and homogeneity rescales. -/
theorem exists_good_dir_gram {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hA : ∃ v : Fin (m + 1) → ℝ, gramDelta (k := k) A v ≠ 0) :
    ∃ w : Fin (m + 1) → ℝ, w 0 = 1 ∧ gramDelta (k := k) A w ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := hA
  set e : Fin (m + 1) → ℝ := Pi.single 0 1 with hedef
  set p : Polynomial ℝ := gramPoly (k := k) A v e with hpdef
  have hp0 : p.eval 0 = gramDelta (k := k) A v := by
    rw [hpdef, gramPoly_eval]; simp
  have hpne : p ≠ 0 := by
    intro h
    rw [h] at hp0
    simp at hp0
    exact hv hp0.symm
  have hfin : ({t : ℝ | p.IsRoot t} ∪ {-(v 0)}).Finite :=
    (Polynomial.finite_setOf_isRoot hpne).union (Set.finite_singleton _)
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff,
    not_or] at ht
  obtain ⟨hroot, hzero⟩ := ht
  set z : Fin (m + 1) → ℝ := v + t • e with hzdef
  have hz0 : z 0 = v 0 + t := by rw [hzdef]; simp [hedef]
  have hz0ne : z 0 ≠ 0 := by
    rw [hz0]; intro h; exact hzero (by linarith)
  have hzdet : gramDelta (k := k) A z ≠ 0 := by
    have hEq : gramDelta (k := k) A z = p.eval t := by rw [hpdef, gramPoly_eval, hzdef]
    rw [hEq]; exact hroot
  refine ⟨(z 0)⁻¹ • z, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hz0ne
  · rw [gramDelta_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hz0ne)) hzdet

/-- **The anticoncentration bound for the general-window degeneracy form.** -/
theorem sublevel_gram {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hk : 0 < k)
    {v : Fin (m + 1) → ℝ} (hv0 : v 0 = 1) (hv : gramDelta (k := k) A v ≠ 0)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    volume {y : Fin (m + 1) → ℝ |
        |gramDelta (k := k) A y| ≤ ε ∧ ∀ i, |y i| ≤ K}
      ≤ ENNReal.ofReal ((2 * (K * (1 + ‖v‖))) ^ m) *
        ENNReal.ofReal (4 * ((2 * k : ℕ) : ℝ) *
          (ε / |gramDelta (k := k) A v|) ^ (((2 * k : ℕ) : ℝ)⁻¹)) :=
  sublevel_dir (n := m) (d := 2 * k) (by omega) hv
    (measurable_gramDelta A) hv0 (fun a => gramPoly (k := k) A a v)
    (fun a => gramPoly_natDegree_le A a v)
    (fun a => gramPoly_coeff A a v)
    (fun a t => (gramPoly_eval A a v t).symm) hK hε

end GramDir

/-! ### `Δ ≢ 0` is exactly the window condition

`gramDelta A v ≠ 0` says the columns `(A-I)Aʲv` (`j < k`) are independent, i.e. `v` has
grade at least `k`.  Since every vector has grade at most `deg m_A`, this forces
`k ≤ deg m_A`; combined with a monic annihilating polynomial of degree `k` (which forces
`deg m_A ≤ k`) it says exactly `k = deg m_A`, the paper's standing window — so it is not an
extra hypothesis.

The converse — that `k = deg m_A` *produces* such a `v` — is the paper's Lemma 4.2(i), the
existence of a vector whose annihilator is the minimal polynomial.  mathlib does not carry
it; see `../../appendix2.tex` §Stage 2. -/

section WindowCond

variable {m kk : ℕ}

/-- **If the degeneracy form is somewhere nonzero, the window does not exceed `deg m_A`.** -/
theorem le_natDegree_minpoly_of_gramDelta_ne
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    {v : Fin (m + 1) → ℝ} (hv : gramDelta (k := kk + 1) A v ≠ 0) :
    kk + 1 ≤ (minpoly ℝ A).natDegree := by
  classical
  by_contra hcon
  push_neg at hcon
  have hdlt : (minpoly ℝ A).natDegree < kk + 1 := hcon
  set c : Fin (kk + 1) → ℝ := fun j => (minpoly ℝ A).coeff (j : ℕ) with hcdef
  -- `c ≠ 0`: the leading coefficient of a monic polynomial sits at an index `< k`
  have hmonic : (minpoly ℝ A).Monic := minpoly.monic (Matrix.isIntegral _)
  have hcne : c ≠ 0 := by
    intro h
    have h2 := congrFun h ⟨(minpoly ℝ A).natDegree, hdlt⟩
    rw [hcdef] at h2
    simp only [Pi.zero_apply] at h2
    rw [hmonic.coeff_natDegree] at h2
    exact one_ne_zero h2
  -- `K(v)` kills `c`, because `Σ_j c_j A^j = m_A(A) = 0`
  have hsum0 : ∑ j ∈ Finset.range (kk + 1), (minpoly ℝ A).coeff j • (A ^ j) = 0 := by
    rw [← Polynomial.aeval_eq_sum_range' hdlt]
    exact minpoly.aeval ℝ A
  have hK : (gkry (k := kk + 1) A v).mulVec c = 0 := by
    funext i
    have hlhs : (gkry (k := kk + 1) A v).mulVec c i
        = ∑ j ∈ Finset.range (kk + 1),
            (((A - 1) * ((minpoly ℝ A).coeff j • A ^ j)).mulVec v) i := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => (((A - 1) * ((minpoly ℝ A).coeff j • A ^ j)).mulVec v) i) (kk + 1)]
      simp only [Matrix.mulVec, dotProduct, gkry, Matrix.of_apply, hcdef]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hlhs]
    have hstep : ∑ j ∈ Finset.range (kk + 1),
          (((A - 1) * ((minpoly ℝ A).coeff j • A ^ j)).mulVec v) i
        = (((A - 1) * (∑ j ∈ Finset.range (kk + 1),
            (minpoly ℝ A).coeff j • (A ^ j))).mulVec v) i := by
      rw [Finset.mul_sum, Matrix.sum_mulVec, Finset.sum_apply]
    rw [hstep, hsum0, Matrix.mul_zero, Matrix.zero_mulVec]
  have hGram : ((gkry (k := kk + 1) A v)ᵀ * (gkry (k := kk + 1) A v)).mulVec c = 0 := by
    rw [← Matrix.mulVec_mulVec, hK, Matrix.mulVec_zero]
  exact hv (Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hcne, hGram⟩)

/-- **Lemma 4.2(i), the converse direction.**  At the paper's window `k = deg m_A` the
degeneracy form is not identically zero.  The witness is the vector of
`exists_ann_eq_minpoly`: `K(v)c = (A-I)·p(A)v` for `p = ∑cⱼXʲ`, so with `A - I` invertible
`K(v)c = 0` forces `m_A ∣ p`, and `deg p < k = deg m_A` then forces `p = 0`. -/
theorem exists_gramDelta_ne {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hA : IsUnit (A - 1)) (hk : kk + 1 = (minpoly ℝ A).natDegree) :
    ∃ v : Fin (m + 1) → ℝ, gramDelta (k := kk + 1) A v ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := MPE.exists_ann_eq_minpoly A
  refine ⟨v, fun hzero => ?_⟩
  obtain ⟨c, hc0, hcv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  -- over `ℝ`, `KᵀKc = 0` gives `Kc = 0`
  have hKc : (gkry (k := kk + 1) A v).mulVec c = 0 := by
    have h : c ⬝ᵥ ((gkry (k := kk + 1) A v)ᵀ * (gkry (k := kk + 1) A v)).mulVec c = 0 := by
      rw [hcv, dotProduct_zero]
    rwa [← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
      dotProduct_self_eq_zero] at h
  -- read `Kc` as `(A - I)·p(A)v`
  set p : Polynomial ℝ :=
    ∑ j : Fin (kk + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) with hpdef
  have hpcoeff : ∀ j : Fin (kk + 1), p.coeff (j : ℕ) = c j := by
    intro j
    rw [hpdef, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      have hne : (j : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have haev : (Polynomial.aeval A) p = ∑ j : Fin (kk + 1), c j • A ^ (j : ℕ) := by
    rw [hpdef, map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Algebra.smul_def]
  have hKeq : (gkry (k := kk + 1) A v).mulVec c
      = ((A - 1) * (Polynomial.aeval A) p).mulVec v := by
    rw [haev, Finset.mul_sum]
    funext i
    rw [Matrix.sum_mulVec, Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, gkry, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  -- `A - I` invertible strips it off, so `m_A ∣ p`
  have hpv : ((Polynomial.aeval A) p).mulVec v = 0 := by
    obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ, B * (A - 1) = 1 :=
      ⟨↑hA.unit⁻¹, by have h := hA.unit.inv_mul; rwa [hA.unit_spec] at h⟩
    have h0 : (A - 1).mulVec (((Polynomial.aeval A) p).mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec]; exact hKeq ▸ hKc
    have h1 := congrArg (fun w => B.mulVec w) h0
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hB, Matrix.one_mul,
      Matrix.one_mulVec, Matrix.mulVec_zero] using h1
  have hdvd : minpoly ℝ A ∣ p := hv p hpv
  -- but `deg p < deg m_A`, so `p = 0` and `c = 0`
  have hp0 : p = 0 := by
    by_contra hne
    have h1 : (minpoly ℝ A).natDegree ≤ p.natDegree := Polynomial.natDegree_le_of_dvd hdvd hne
    have h2 : p.natDegree ≤ kk := by
      rw [hpdef]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      rw [Polynomial.natDegree_X_pow]
      exact Nat.lt_succ_iff.mp j.2
    omega
  exact hc0 (funext fun j => by rw [← hpcoeff j, hp0, Polynomial.coeff_zero, Pi.zero_apply])

end WindowCond

end MPE
