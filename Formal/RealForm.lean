import Mathlib
import Formal.DeltaFactor
import Formal.Algebra

/-!
# The real form: factoring the characteristic polynomial

Appendix Obligation 1.  A monic squarefree real polynomial is the product of its *distinct*
monic irreducible factors, each of degree at most two, and they are pairwise coprime.

This is the first step of the CRT route to `RealBlockFactorization`, which replaces the
complex-eigenbasis argument of the earlier draft.  Nothing here mentions `ℂ`.
-/

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace MPE

open Polynomial UniqueFactorizationMonoid

/-- Distinct monic irreducible real polynomials are coprime. -/
lemma isCoprime_of_irreducible_of_ne {f g : ℝ[X]}
    (hf : Irreducible f) (hg : Irreducible g) (hfm : f.Monic) (hgm : g.Monic)
    (hne : f ≠ g) : IsCoprime f g := by
  rcases hf.isCoprime_or_dvd g with h | h
  · exact h
  · exfalso
    obtain ⟨c, hc⟩ := h
    have hcu : IsUnit c := (hg.isUnit_or_isUnit hc).resolve_left hf.not_isUnit
    refine hne (Polynomial.eq_of_monic_of_associated hfm hgm ⟨hcu.unit, ?_⟩)
    rw [IsUnit.unit_spec]
    exact hc.symm

/-- **Obligation 1.**  A monic squarefree real polynomial factors as a product over a finite
set of distinct monic irreducibles, each of degree at most two, pairwise coprime. -/
theorem exists_factorization {p : ℝ[X]} (hm : p.Monic) (hsq : Squarefree p) :
    ∃ S : Finset ℝ[X], (∀ f ∈ S, Irreducible f ∧ f.Monic ∧ f.natDegree ≤ 2) ∧
      (∏ f ∈ S, f) = p ∧ (S : Set ℝ[X]).Pairwise (Function.onFun IsCoprime id) := by
  classical
  have hp0 : p ≠ 0 := hm.ne_zero
  set S : Finset ℝ[X] := (normalizedFactors p).toFinset with hS
  have hnodup : (normalizedFactors p).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hp0).mp hsq
  -- each factor is irreducible, monic, of degree ≤ 2
  have hmem : ∀ f ∈ S, Irreducible f ∧ f.Monic ∧ f.natDegree ≤ 2 := by
    intro f hf
    rw [hS, Multiset.mem_toFinset] at hf
    have hirr : Irreducible f := irreducible_of_normalized_factor f hf
    have hmon : f.Monic := by
      have hnorm : normalize f = f := normalize_normalized_factor f hf
      rw [← hnorm]
      exact monic_normalize (hirr.ne_zero)
    exact ⟨hirr, hmon, hirr.natDegree_le_two⟩
  refine ⟨S, hmem, ?_, ?_⟩
  · -- the product over the finset is the multiset product, which is `p`
    have hprod : ∏ f ∈ S, f = (normalizedFactors p).prod := by
      rw [hS, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
        Multiset.dedup_eq_self.mpr hnodup]
      simp
    rw [hprod]
    -- the product of normalized factors is monic and associated to `p`
    have hassoc : Associated (normalizedFactors p).prod p := prod_normalizedFactors hp0
    have hmonprod : ((normalizedFactors p).prod).Monic := by
      have := Polynomial.monic_multiset_prod_of_monic (normalizedFactors p) id ?_
      · simpa using this
      · intro f hf
        exact (hmem f (by rw [hS, Multiset.mem_toFinset]; exact hf)).2.1
    exact Polynomial.eq_of_monic_of_associated hmonprod hm hassoc
  · intro f hf g hg hne
    have hf' := hmem f (by simpa using hf)
    have hg' := hmem g (by simpa using hg)
    exact isCoprime_of_irreducible_of_ne hf'.1 hg'.1 hf'.2.1 hg'.2.1 hne

/-! ### Obligation 2: the primary decomposition

`ℝⁿ` becomes an `ℝ[X]`-module with `X` acting as `A` (`Module.AEval'`).  Cayley–Hamilton
says the module is `charpoly`-torsion, and `charpoly = ∏ fᵢ` with the `fᵢ` pairwise coprime,
so `Submodule.torsionBy_isInternal` splits it. -/

variable {n : ℕ}

/-- The `ℝ[X]`-module structure on `ℝⁿ` in which `X` acts as `A`. -/
abbrev AMod (A : Matrix (Fin n) (Fin n) ℝ) := Module.AEval' (Matrix.mulVecLin A)

/-- Evaluating a polynomial at `A` commutes with `Matrix.mulVecLin`. -/
lemma aeval_mulVecLin (A : Matrix (Fin n) (Fin n) ℝ) (p : ℝ[X]) :
    (aeval (Matrix.mulVecLin A)) p = Matrix.mulVecLin (aeval A p) := by
  have h := Polynomial.aeval_algHom_apply
    (Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin n)).toAlgHom A p
  have hcoe : ∀ M : Matrix (Fin n) (Fin n) ℝ,
      (Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin n)).toAlgHom M = Matrix.mulVecLin M :=
    fun _ => rfl
  rw [hcoe, hcoe] at h
  exact h

/-- The `ℝ[X]`-action on `AMod A`, spelled out. -/
lemma smul_AEval_of (A : Matrix (Fin n) (Fin n) ℝ) (p : ℝ[X]) (v : Fin n → ℝ) :
    p • (Module.AEval'.of (Matrix.mulVecLin A)) v
      = (Module.AEval'.of (Matrix.mulVecLin A)) ((aeval A p).mulVec v) := by
  rw [← Module.AEval.of_aeval_smul, aeval_mulVecLin]
  rfl

/-- **Cayley–Hamilton, as torsion.**  The module is `charpoly`-torsion. -/
lemma isTorsionBy_charpoly (A : Matrix (Fin n) (Fin n) ℝ) :
    Module.IsTorsionBy ℝ[X] (AMod A) A.charpoly := by
  intro x
  obtain ⟨m, rfl⟩ := (Module.AEval'.of (Matrix.mulVecLin A)).surjective x
  rw [smul_AEval_of, Matrix.aeval_self_charpoly]
  show (Module.AEval'.of (Matrix.mulVecLin A)) ((0 : Matrix (Fin n) (Fin n) ℝ).mulVec m) = 0
  rw [Matrix.zero_mulVec, map_zero]

/-- **Obligation 2.**  With `charpoly` squarefree, `ℝⁿ` is the internal direct sum of the
`fᵢ`-torsion submodules, one for each distinct irreducible factor. -/
theorem isInternal_torsion (A : Matrix (Fin n) (Fin n) ℝ) (_hsq : Squarefree A.charpoly)
    {S : Finset ℝ[X]} (hprod : (∏ f ∈ S, f) = A.charpoly)
    (hcop : (S : Set ℝ[X]).Pairwise (Function.onFun IsCoprime id)) :
    DirectSum.IsInternal fun f : S => Submodule.torsionBy ℝ[X] (AMod A) (f : ℝ[X]) := by
  classical
  refine Submodule.torsionBy_isInternal (q := id) hcop ?_
  rw [show (∏ f ∈ S, id f) = A.charpoly by simpa using hprod]
  exact isTorsionBy_charpoly A

/-! ### Obligation 3b: each summand is nonzero

`ker (aeval A f) ≠ 0` for every irreducible factor `f` of `charpoly`.  The obvious route —
"every irreducible factor of `charpoly` divides `minpoly`" — is **not available**: mathlib
has only `minpoly_dvd_charpoly`, the other direction.

Instead `ℂ` is used, once, purely to manufacture a root of `f`; it is discarded again as
soon as the determinant is known to vanish.  No eigenbasis, no conjugation, nothing
normalized. -/

section Eigen

variable {K : Type*} [Field K] {N : ℕ}

/-- Powers act on an eigenvector by powers of the eigenvalue. -/
lemma pow_mulVec_of_eigen {M : Matrix (Fin N) (Fin N) K} {μ : K} {v : Fin N → K}
    (h : M.mulVec v = μ • v) (k : ℕ) : (M ^ k).mulVec v = (μ ^ k) • v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]

/-- Hence any polynomial in `M` acts by the value of that polynomial at the eigenvalue. -/
lemma aeval_mulVec_of_eigen {M : Matrix (Fin N) (Fin N) K} {μ : K} {v : Fin N → K}
    (h : M.mulVec v = μ • v) (p : K[X]) :
    (aeval M p).mulVec v = (p.eval μ) • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial k a =>
      rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, ← Algebra.smul_def,
        Matrix.smul_mulVec, pow_mulVec_of_eigen h k, smul_smul]

end Eigen

/-- **Obligation 3b.**  If `f` is a nonconstant real polynomial dividing `charpoly A`, then
`aeval A f` is singular. -/
theorem det_aeval_eq_zero_of_dvd_charpoly {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    {f : ℝ[X]} (hdeg : 0 < f.degree) (hdvd : f ∣ A.charpoly) :
    (aeval A f).det = 0 := by
  classical
  set φ : ℝ →+* ℂ := algebraMap ℝ ℂ with hφ
  set Ac : Matrix (Fin N) (Fin N) ℂ := A.map φ with hAc
  set fc : ℂ[X] := f.map φ with hfc
  -- (1) a complex root of `f`
  have hdegc : 0 < fc.degree := by
    rw [hfc, Polynomial.degree_map_eq_of_injective φ.injective]
    exact hdeg
  obtain ⟨μ, hμ⟩ := Complex.exists_root hdegc
  -- (2) it is a root of the complexified characteristic polynomial
  have hdvdc : fc ∣ Ac.charpoly := by
    rw [hAc, Matrix.charpoly_map, hfc]
    exact Polynomial.map_dvd _ hdvd
  have hroot : Ac.charpoly.IsRoot μ := hμ.dvd hdvdc
  -- (3)-(4) `μ` is an eigenvalue: some `v ≠ 0` has `Ac v = μ v`
  have hdet : (Matrix.scalar (Fin N) μ - Ac).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have heig : Ac.mulVec v = μ • v := by
    rw [Matrix.sub_mulVec] at hv
    have hsc : (Matrix.scalar (Fin N) μ).mulVec v = μ • v := by
      funext i
      simp [Matrix.scalar_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
        Finset.sum_ite_eq]
    rw [hsc] at hv
    exact (sub_eq_zero.mp hv).symm
  -- (5) so `aeval Ac fc` kills `v`, hence is singular
  have hker : (aeval Ac fc).mulVec v = 0 := by
    rw [aeval_mulVec_of_eigen heig fc, hμ, zero_smul]
  have hdetc : (aeval Ac fc).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hker⟩
  -- (6)-(7) descend to `ℝ`
  have hmapaeval : (φ.mapMatrix) (aeval A f) = aeval Ac fc := by
    rw [hAc, hfc]
    refine Polynomial.map_aeval_eq_aeval_map (φ := φ) (ψ := φ.mapMatrix) ?_ f A
    ext r i j
    simp [Matrix.algebraMap_matrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      apply_ite φ]
  rw [← hmapaeval, ← RingHom.map_det] at hdetc
  exact φ.injective (by simpa using hdetc)

/-- **Obligation 3b, as needed downstream.**  Each torsion summand belonging to an
irreducible factor of `charpoly` is nonzero.  This is what rules out `m_f = 0` in the
dimension count of Obligation 3c. -/
theorem torsionBy_ne_bot {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    {f : ℝ[X]} (hdeg : 0 < f.degree) (hdvd : f ∣ A.charpoly) :
    Submodule.torsionBy ℝ[X] (AMod A) f ≠ ⊥ := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (det_aeval_eq_zero_of_dvd_charpoly A hdeg hdvd)
  have hmem : (Module.AEval'.of (Matrix.mulVecLin A)) v
      ∈ Submodule.torsionBy ℝ[X] (AMod A) f := by
    rw [Submodule.mem_torsionBy_iff, smul_AEval_of, hv, map_zero]
  intro hbot
  rw [hbot, Submodule.mem_bot] at hmem
  exact hv0 ((Module.AEval'.of (Matrix.mulVecLin A)).map_eq_zero_iff.mp hmem)

/-! ### Obligation 3a: the residue field

`ℝ[X]/(f)` is `AdjoinRoot f`; for `f` irreducible it is a field of degree `deg f` over `ℝ`. -/

/-- **Obligation 3a.**  `dim_ℝ (ℝ[X]/(f)) = deg f`. -/
lemma finrank_adjoinRoot {f : ℝ[X]} (hf : Irreducible f) :
    Module.finrank ℝ (AdjoinRoot f) = f.natDegree := by
  haveI : Fact (Irreducible f) := ⟨hf⟩
  rw [(AdjoinRoot.powerBasis hf.ne_zero).finrank, AdjoinRoot.powerBasis_dim]

/-! ### Obligation 3c: each summand has dimension a multiple of `deg f`

The torsion summand `V_f` is a module over the residue field, so the tower formula makes its
real dimension `deg f` times its dimension over that field.  Combined with
`∑ dim V_f = n = ∑ deg f` and `V_f ≠ 0` (Obligation 3b), this forces the multiplier to be
`1` — which is what makes `V_f` a *line* over its residue field. -/

/-- **Obligation 3c.**  A module killed by an irreducible `f` has real dimension a multiple
of `deg f` — it is a vector space over the residue field.

Stated for an abstract `V` rather than for the submodule directly: the submodule's
`AddCommMonoid`/`Module` instance path does not unify with the one
`Module.IsTorsionBy.module` expects, and abstracting `V` sidesteps that entirely. -/
theorem finrank_of_isTorsionBy {V : Type*} [AddCommGroup V] [Module ℝ[X] V] [Module ℝ V]
    [IsScalarTower ℝ ℝ[X] V] {f : ℝ[X]} (hf : Irreducible f)
    (hV : Module.IsTorsionBy ℝ[X] V f) :
    ∃ m : ℕ, Module.finrank ℝ V = f.natDegree * m := by
  haveI : Fact (Irreducible f) := ⟨hf⟩
  haveI hmax : (Ideal.span {f}).IsMaximal := AdjoinRoot.span_maximal_of_irreducible
  letI : Field (ℝ[X] ⧸ Ideal.span {f}) := Ideal.Quotient.field _
  have hset : Module.IsTorsionBySet ℝ[X] V (Ideal.span {f}) := by
    rw [Ideal.submodule_span_eq.symm]
    exact (Module.isTorsionBySet_span_singleton_iff f).mpr hV
  letI : Module (ℝ[X] ⧸ Ideal.span {f}) V := hset.module
  haveI : IsScalarTower ℝ (ℝ[X] ⧸ Ideal.span {f}) V := hset.isScalarTower
  refine ⟨Module.finrank (ℝ[X] ⧸ Ideal.span {f}) V, ?_⟩
  have hdim : Module.finrank ℝ (ℝ[X] ⧸ Ideal.span {f}) = f.natDegree := finrank_adjoinRoot hf
  rw [← hdim]
  exact (Module.finrank_mul_finrank ℝ (ℝ[X] ⧸ Ideal.span {f}) V).symm

/-! ### Obligation 3d: the counting argument

`∑_f deg f · m_f = n = ∑_f deg f` with every `m_f ≥ 1` and `deg f > 0` forces every
`m_f = 1`.  Isolated here as pure arithmetic on a `Finset`, so it can be applied without
carrying any module structure. -/

/-- If `∑ d f * m f = ∑ d f` with every `d f > 0` and every `m f ≥ 1`, then `m ≡ 1`. -/
theorem eq_one_of_sum_mul_eq {ι : Type*} (S : Finset ι) (d m : ι → ℕ)
    (hd : ∀ i ∈ S, 0 < d i) (hm : ∀ i ∈ S, 1 ≤ m i)
    (hsum : ∑ i ∈ S, d i * m i = ∑ i ∈ S, d i) :
    ∀ i ∈ S, m i = 1 := by
  classical
  -- every term of the first sum dominates the corresponding term of the second
  have hterm : ∀ i ∈ S, d i ≤ d i * m i := fun i hi =>
    Nat.le_mul_of_pos_right _ (hm i hi)
  -- equality of the sums forces equality termwise
  have hEq : ∀ i ∈ S, d i = d i * m i :=
    (Finset.sum_eq_sum_iff_of_le hterm).mp hsum.symm
  intro i hi
  have hdi := hd i hi
  have h := (hEq i hi).symm
  nlinarith [h, hdi, hm i hi]

/-- **Obligation 3d, dimension form.**  Each summand has real dimension exactly `deg f`. -/
theorem finrank_eq_natDegree_of_counting {ι : Type*} (S : Finset ι) (d m : ι → ℕ)
    (hd : ∀ i ∈ S, 0 < d i) (hm : ∀ i ∈ S, 1 ≤ m i)
    (hsum : ∑ i ∈ S, d i * m i = ∑ i ∈ S, d i) :
    ∀ i ∈ S, d i * m i = d i := fun i hi => by
  rw [eq_one_of_sum_mul_eq S d m hd hm hsum i hi, mul_one]

/-- **Obligation 3d, degree side.**  The factor degrees sum to `n`. -/
theorem sum_natDegree_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) {S : Finset ℝ[X]}
    (hmon : ∀ f ∈ S, f.Monic) (hprod : (∏ f ∈ S, f) = A.charpoly) :
    ∑ f ∈ S, f.natDegree = N := by
  have hlead : (∏ f ∈ S, f.leadingCoeff) ≠ 0 := by
    have h1 : (∏ f ∈ S, f.leadingCoeff) = 1 :=
      Finset.prod_eq_one fun f hf => (hmon f hf).leadingCoeff
    rw [h1]; norm_num
  have hnd := Polynomial.natDegree_prod' (s := S) (f := id) hlead
  simp only [id] at hnd
  rw [hprod, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hnd
  exact hnd.symm

/-- **Obligation 3d, dimension side.**  An internal direct sum of `R`-submodules has
`K`-dimension the sum of the summands', for any base field `K` under `R`.

Stated abstractly, for the same reason as `finrank_of_isTorsionBy`: the concrete submodules
carry instance paths that do not unify with what the direct-sum lemmas expect. -/
theorem finrank_sum_of_isInternal {K R M : Type*} [Field K] [Ring R] [AddCommGroup M]
    [Algebra K R] [Module R M] [Module K M] [IsScalarTower K R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Submodule R M) (h : DirectSum.IsInternal V)
    [∀ i, Module.Finite K (V i)] [∀ i, Module.Free K (V i)] :
    ∑ i, Module.finrank K (V i) = Module.finrank K M := by
  classical
  have e : (DirectSum ι fun i => (V i)) ≃ₗ[R] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap V) h
  have eK : (DirectSum ι fun i => (V i)) ≃ₗ[K] M := e.restrictScalars K
  rw [← eK.finrank_eq, Module.finrank_directSum]

/-! ### Obligation 3e, step 1: the companion matrix

In the basis `v, Av, …, A^{n-1}v` supplied by a cyclic vector, `A` becomes the companion
matrix of its characteristic polynomial.  Stated multiplicatively, so that no inverse is
formed:

    A · K_A(v)  =  K_A(v) · C.

Column `j < n-1` of `C` is the unit vector at `j+1` (the shift `X · Xʲ = X^{j+1}`); the last
column holds the `charpoly` coefficients, which is exactly Cayley–Hamilton. -/

/-- The companion matrix of `A.charpoly`: multiplication by `X` on `ℝ[X]/(charpoly)` in the
monomial basis. -/
noncomputable def companionOf {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    if (j : ℕ) + 1 = N then -A.charpoly.coeff (i : ℕ)
    else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- **The companion relation.**  `A · K_A(v) = K_A(v) · C`, for every `v`. -/
theorem mul_krylov_eq_krylov_mul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) :
    A * krylov A v = krylov A v * companionOf A := by
  ext i j
  -- the left side is the next Krylov vector
  have hlhs : (A * krylov A v) i j = ((A ^ ((j : ℕ) + 1)).mulVec v) i := by
    have h1 : (A * krylov A v) i j = (A.mulVec ((A ^ (j : ℕ)).mulVec v)) i := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, krylov_apply]
    rw [h1, Matrix.mulVec_mulVec, ← pow_succ']
  rw [hlhs]
  by_cases hlast : (j : ℕ) + 1 = N
  · -- last column: Cayley–Hamilton
    have hrhs : (krylov A v * companionOf A) i j
        = ∑ l : Fin N, ((A ^ (l : ℕ)).mulVec v) i * (-A.charpoly.coeff (l : ℕ)) := by
      simp only [Matrix.mul_apply, krylov_apply, companionOf, Matrix.of_apply, if_pos hlast]
    rw [hrhs, hlast]
    -- evaluate Cayley–Hamilton at `v`, component `i`
    have hsm : ∀ l : ℕ, ((A.charpoly.coeff l • A ^ l).mulVec v) i
        = A.charpoly.coeff l * (((A ^ l).mulVec v) i) := by
      intro l
      rw [Matrix.smul_mulVec]
      rfl
    have hev : ∑ l ∈ Finset.range N, A.charpoly.coeff l * (((A ^ l).mulVec v) i)
        = -(((A ^ N).mulVec v) i) := by
      have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => (M.mulVec v) i)
        (charpoly_sum_eq_neg_pow A)
      simp only [Matrix.sum_mulVec, Matrix.neg_mulVec] at h
      rw [Finset.sum_apply] at h
      simpa only [hsm, Pi.neg_apply] using h
    have hfin : ∑ l : Fin N, A.charpoly.coeff (l : ℕ) * (((A ^ (l : ℕ)).mulVec v) i)
        = -(((A ^ N).mulVec v) i) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun l => A.charpoly.coeff l * (((A ^ l).mulVec v) i)) N]
      exact hev
    calc ((A ^ N).mulVec v) i
        = -(-(((A ^ N).mulVec v) i)) := by ring
      _ = -(∑ l : Fin N, A.charpoly.coeff (l : ℕ) * (((A ^ (l : ℕ)).mulVec v) i)) := by
          rw [hfin]
      _ = ∑ l : Fin N, ((A ^ (l : ℕ)).mulVec v) i * (-A.charpoly.coeff (l : ℕ)) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun l _ => by ring
  · -- interior column: a plain shift
    have hjlt : (j : ℕ) + 1 < N := lt_of_le_of_ne (Nat.succ_le_of_lt j.2) hlast
    have hrhs : (krylov A v * companionOf A) i j
        = ∑ l : Fin N, ((A ^ (l : ℕ)).mulVec v) i *
            (if (l : ℕ) = (j : ℕ) + 1 then 1 else 0) := by
      simp only [Matrix.mul_apply, krylov_apply, companionOf, Matrix.of_apply,
        if_neg hlast]
    rw [hrhs, Finset.sum_eq_single (⟨(j : ℕ) + 1, hjlt⟩ : Fin N)]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ (j : ℕ) + 1 := by
        intro hc
        exact hb (Fin.ext hc)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-! ### Obligation 3e, step 2: the norm of a product algebra

`N_{S×T}(x) = N_S(x.1) · N_T(x.2)`.  Not in mathlib, and needed because the Chinese-remainder
isomorphism presents `ℝ[X]/(p)` as a product.  In a product basis the multiplication matrix
is block diagonal, so this is `Matrix.det_fromBlocks_zero₁₂`.

Note `Matrix.det_blockDiagonal'` — the varying-block-size version — is *also* absent from
mathlib, which is why this is stated for two factors and iterated, rather than for a
`Finset`-indexed product in one go. -/

theorem norm_prod_eq {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Module.Free R S] [Module.Finite R S] [Module.Free R T] [Module.Finite R T]
    (x : S × T) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  classical
  set bS := Module.Free.chooseBasis R S with hbS
  set bT := Module.Free.chooseBasis R T with hbT
  rw [Algebra.norm_eq_matrix_det (bS.prod bT), Algebra.norm_eq_matrix_det bS,
    Algebra.norm_eq_matrix_det bT]
  have hM : Algebra.leftMulMatrix (bS.prod bT) x
      = Matrix.fromBlocks (Algebra.leftMulMatrix bS x.1) 0 0
          (Algebra.leftMulMatrix bT x.2) := by
    ext i j
    cases i <;> cases j <;>
      simp [Algebra.leftMulMatrix_eq_repr_mul, Prod.mul_def,
        
        ]
  rw [hM, Matrix.det_fromBlocks_zero₁₂]

/-! ### Obligation 3e, step 3: the Krylov determinant is a norm

The route here is shorter than the one planned in the appendix, and does **not** need the
companion matrix.  If `z = g(A)v` then

    K_A(z) = K_A(v) · leftMulMatrix (mk g),

because `Aʲ (g(A)v) = (Xʲ g)(A) v` and `Xʲ g` reduces modulo `charpoly` to its expansion in
the monomial basis.  Taking determinants,

    det K_A(z) = det K_A(v) · N(mk g),

so the whole block factorization is a statement about the *norm* on `ℝ[X]/(charpoly)`; the
similarity transport to a companion matrix is bypassed entirely. -/

section Cyclic

variable {N : ℕ}

/-- Cayley–Hamilton lets `aeval A` factor through `ℝ[X] ⧸ (charpoly)`, as an `ℝ`-algebra map.
`AdjoinRoot.lift` cannot be used here: it requires a *commutative* target. -/
noncomputable def aevalQuot (A : Matrix (Fin N) (Fin N) ℝ) :
    AdjoinRoot A.charpoly →ₐ[ℝ] Matrix (Fin N) (Fin N) ℝ :=
  Ideal.Quotient.liftₐ _ (Polynomial.aeval A) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul])

@[simp] lemma aevalQuot_mk (A : Matrix (Fin N) (Fin N) ℝ) (h : ℝ[X]) :
    aevalQuot A (AdjoinRoot.mk _ h) = aeval A h := rfl

lemma charpoly_natDegree (A : Matrix (Fin N) (Fin N) ℝ) : A.charpoly.natDegree = N := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- The monomial basis of `ℝ[X] ⧸ (charpoly)`, reindexed by `Fin N`. -/
noncomputable def charBasis (A : Matrix (Fin N) (Fin N) ℝ) :
    Module.Basis (Fin N) ℝ (AdjoinRoot A.charpoly) :=
  (AdjoinRoot.powerBasis' A.charpoly_monic).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis'_dim, charpoly_natDegree]))

@[simp] lemma charBasis_apply (A : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) :
    charBasis A j = AdjoinRoot.mk _ (X ^ (j : ℕ)) := by
  rw [charBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simp only [AdjoinRoot.powerBasis'_gen]
  rw [← AdjoinRoot.mk_X, ← map_pow]
  congr 1

lemma aevalQuot_charBasis (A : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) :
    aevalQuot A (charBasis A j) = A ^ (j : ℕ) := by
  rw [charBasis_apply, aevalQuot_mk, map_pow, Polynomial.aeval_X]

/-- **The key factorization.**  `K_A(g(A)v) = K_A(v) · leftMulMatrix (mk g)`.

Every `Aʲ(g(A)v)` is `(Xʲg)(A)v`, and `Xʲg` reduces modulo `charpoly` to its expansion in the
monomial basis — whose coefficients are precisely the `j`-th column of the multiplication
matrix of `mk g`. -/
theorem krylov_aeval_mulVec (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (g : ℝ[X]) :
    krylov A ((aeval A g).mulVec v)
      = krylov A v * Algebra.leftMulMatrix (charBasis A) (AdjoinRoot.mk _ g) := by
  set M := Algebra.leftMulMatrix (charBasis A) (AdjoinRoot.mk A.charpoly g) with hM
  have hexp : ∀ j : Fin N, aeval A (X ^ (j : ℕ) * g) = ∑ l : Fin N, M l j • A ^ (l : ℕ) := by
    intro j
    have hbase : AdjoinRoot.mk A.charpoly (X ^ (j : ℕ) * g)
        = ∑ l : Fin N, M l j • charBasis A l := by
      have hcomm : AdjoinRoot.mk A.charpoly (X ^ (j : ℕ) * g)
          = AdjoinRoot.mk A.charpoly g * charBasis A j := by
        rw [charBasis_apply, map_mul]; ring
      rw [hcomm, ← (charBasis A).sum_repr
        (AdjoinRoot.mk A.charpoly g * charBasis A j)]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      rw [hM, Algebra.leftMulMatrix_eq_repr_mul]
    calc aeval A (X ^ (j : ℕ) * g)
        = aevalQuot A (AdjoinRoot.mk A.charpoly (X ^ (j : ℕ) * g)) := rfl
      _ = aevalQuot A (∑ l : Fin N, M l j • charBasis A l) := by rw [hbase]
      _ = ∑ l : Fin N, M l j • A ^ (l : ℕ) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun l _ => by
            rw [map_smul, aevalQuot_charBasis]
  ext i j
  have hLHS : krylov A ((aeval A g).mulVec v) i j
      = ((aeval A (X ^ (j : ℕ) * g)).mulVec v) i := by
    show ((A ^ (j : ℕ)).mulVec ((aeval A g).mulVec v)) i = _
    rw [Matrix.mulVec_mulVec]
    congr 2
    rw [map_mul, map_pow, Polynomial.aeval_X]
  rw [hLHS, hexp j, Matrix.sum_mulVec, Matrix.mul_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_mulVec, krylov_apply]
  show M l j * ((A ^ (l : ℕ)).mulVec v) i = ((A ^ (l : ℕ)).mulVec v) i * M l j
  ring

/-- **The identity that replaces the whole norm apparatus.**  If `M` commutes with `A` then
`K_A(Mv) = M · K_A(v)`: column `j` of the left is `Aʲ(Mv) = M(Aʲv)`, which is column `j` of
the right.

Everything the block factorization needs follows from this and `Matrix.det_mul`.  In
particular the route through `ℝ[X] ⧸ (charpoly)`, `Algebra.norm`, and the Chinese remainder
theorem — including the `AdjoinRoot` transparency wall documented below — is unnecessary. -/
theorem krylov_mulVec_of_commute {N : ℕ} {A M : Matrix (Fin N) (Fin N) ℝ}
    (hc : Commute A M) (v : Fin N → ℝ) :
    krylov A (M.mulVec v) = M * krylov A v := by
  ext i j
  show ((A ^ (j : ℕ)).mulVec (M.mulVec v)) i = (M * krylov A v) i j
  rw [Matrix.mulVec_mulVec, (hc.pow_left (j : ℕ)).eq, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, krylov_apply]

/-- A polynomial in `A` commutes with `A`. -/
lemma commute_aeval {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (g : ℝ[X]) :
    Commute A (aeval A g) := by
  have h : Commute (X : ℝ[X]) g := Commute.all _ _
  have := h.map (Polynomial.aeval A)
  rwa [Polynomial.aeval_X] at this

/-- **The determinant form, stated with no quotient rings at all.** -/
theorem det_krylov_aeval_mulVec' {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (g : ℝ[X]) :
    (krylov A ((aeval A g).mulVec v)).det = (aeval A g).det * (krylov A v).det := by
  rw [krylov_mulVec_of_commute (commute_aeval A g), Matrix.det_mul]

/-- **The determinant form.**  `det K_A(g(A)v) = det K_A(v) · N(mk g)`. -/
theorem det_krylov_aeval_mulVec (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (g : ℝ[X]) :
    (krylov A ((aeval A g).mulVec v)).det
      = (krylov A v).det * Algebra.norm ℝ (AdjoinRoot.mk A.charpoly g) := by
  haveI := A.charpoly_monic.free_adjoinRoot (R := ℝ)
  haveI := A.charpoly_monic.finite_adjoinRoot (R := ℝ)
  rw [krylov_aeval_mulVec, Matrix.det_mul,
    Algebra.norm_eq_matrix_det (charBasis A)]

/-- A corollary worth recording: on `ℝ[X] ⧸ (charpoly)` the norm of `mk g` is `det g(A)`.
This falls out of comparing `det_krylov_aeval_mulVec'` with the norm route, and is the
statement the abandoned Chinese-remainder argument was trying to reach. -/
theorem norm_mk_eq_det_aeval {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (hv : (krylov A v).det ≠ 0) (g : ℝ[X]) :
    Algebra.norm ℝ (AdjoinRoot.mk A.charpoly g) = (aeval A g).det := by
  haveI := A.charpoly_monic.free_adjoinRoot (R := ℝ)
  haveI := A.charpoly_monic.finite_adjoinRoot (R := ℝ)
  have h1 := det_krylov_aeval_mulVec A v g
  have h2 := det_krylov_aeval_mulVec' A v g
  rw [h2] at h1
  field_simp at h1
  exact h1.symm

end Cyclic

/-! ### Obligation 3e, step 4: Chinese remainder, and the norm as a product

`N_{ℝ[X]/(∏f)}(g) = ∏_f N_{ℝ[X]/(f)}(g)`.  The two-factor CRT is an *isomorphism*, so its
contribution to any determinant is a unit and never has to be computed — this is what the
explicit-CRT-matrix route paid for with a separate `det C ≠ 0` theorem.

The splitting is done two factors at a time and iterated because
`Matrix.det_blockDiagonal'` (varying block sizes) is absent from mathlib. -/

section CRT

/-- For coprime `f, q`, `(f q) = (f) ⊓ (q)`. -/
lemma span_mul_eq_inf {f q : ℝ[X]} (h : IsCoprime f q) :
    Ideal.span {f * q} = Ideal.span {f} ⊓ Ideal.span {q} := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨Ideal.mem_span_singleton.mpr ⟨q, rfl⟩,
      Ideal.mem_span_singleton.mpr ⟨f, mul_comm f q⟩⟩
  · intro x hx
    have hxf : x ∈ Ideal.span {f} := hx.1
    have hxq : x ∈ Ideal.span {q} := hx.2
    rw [Ideal.mem_span_singleton] at hxf hxq
    rw [Ideal.mem_span_singleton]
    exact h.mul_dvd hxf hxq

/- **The Chinese-remainder step is blocked here, and the reason is worth recording.**

The plan was `AdjoinRoot (f*q) ≃ₐ[ℝ] AdjoinRoot f × AdjoinRoot q`, built from
`Ideal.quotientInfEquivQuotientProd` and `span_mul_eq_inf` above.  The *definition*
elaborates: with an explicit type ascription, `AdjoinRoot f` and `ℝ[X] ⧸ Ideal.span {f}`
unify at default transparency.

But every `rw`/`simp` on it fails, with
`the target expression is not type-correct under the instances transparency level`.
`AdjoinRoot` is a semireducible `def`, and tactics unify at `instances` transparency, where
`AdjoinRoot f` and `ℝ[X] ⧸ Ideal.span {f}` are *not* interchangeable — their `CommRing`
instances are found by different paths.  So the mk-formula
`crt (mk g) = (mk g, mk g)` cannot be proved by rewriting, and without it the norm
factorization cannot be stated.

Three ways out, none of them short:

1. Restate everything with the raw quotient and never mention `AdjoinRoot` — but
   `AdjoinRoot.powerBasis'` (needed for `charBasis`, and for the `Module.Free`/`Finite`
   instances that `Algebra.norm` requires) is only available for `AdjoinRoot`, so the same
   mismatch reappears at the other end.
2. Prove the norm factorization from a *filtration* instead of CRT:
   `0 → (q)/(fq) → ℝ[X]/(fq) → ℝ[X]/(q) → 0` with `(q)/(fq) ≅ ℝ[X]/(f)` via multiplication
   by `q`.  Multiplication by `g` is block *triangular* for the adapted basis
   `q, qX, …, qX^{d_f-1}, 1, X, …, X^{d_q-1}`, so
   `Matrix.det_fromBlocks_zero₂₁` applies.  This is **unconditional** — no coprimality at
   all — and is the mathematically better theorem; the cost is constructing the adapted
   basis and proving it is one.
3. Contribute `Matrix.det_blockDiagonal'` (varying block sizes, currently absent) and do the
   whole product in one step rather than two factors at a time.

Route 2 looks best: it needs no CRT, no coprimality, and no `AdjoinRoot`/quotient bridge.
-/

/-- `ℝ[X] ⧸ (1)` is trivial, so every norm there is `1`. -/
lemma norm_adjoinRoot_one (x : AdjoinRoot (1 : ℝ[X])) : Algebra.norm ℝ x = 1 := by
  haveI : Subsingleton (AdjoinRoot (1 : ℝ[X])) := by
    constructor
    intro a b
    obtain ⟨pa, rfl⟩ := AdjoinRoot.mk_surjective a
    obtain ⟨pb, rfl⟩ := AdjoinRoot.mk_surjective b
    rw [AdjoinRoot.mk_eq_mk]
    exact one_dvd _
  rw [Subsingleton.elim x 1, map_one]

end CRT

/-! ### Obligation 3e, step 5: the block-diagonal determinant

`det (⊕ᵢ fᵢ) = ∏ᵢ det fᵢ` for blocks of **varying** size.  This is the one thing the block
factorization still needed, and the matrix form of it —
`Matrix.det_blockDiagonal'` — is absent from mathlib (only the uniform-size
`Matrix.det_blockDiagonal` is there; and mathlib has no companion matrices either, so the
alternative route via `charpoly (companion p) = p` would be worse).

Stated for `LinearMap.det` instead of matrices, it is short: `LinearMap.det_prodMap` supplies
the two-block case basis-free, `Fin.consLinearEquiv` peels one factor off a `Fin (k+1)`-indexed
product, and `LinearMap.det_conj` transports along it. -/

section BlockDet

variable {R : Type*} [CommRing R]

/-- The block-diagonal endomorphism of a `Fin k`-indexed product. -/
def piMap {k : ℕ} {M : Fin k → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (f : ∀ i, M i →ₗ[R] M i) : (∀ i, M i) →ₗ[R] (∀ i, M i) :=
  LinearMap.pi fun i => (f i).comp (LinearMap.proj i)

@[simp] lemma piMap_apply {k : ℕ} {M : Fin k → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (f : ∀ i, M i →ₗ[R] M i) (x : ∀ i, M i) (i : Fin k) :
    piMap f x i = f i (x i) := rfl

/-- **The block-diagonal determinant, varying block sizes.** -/
theorem det_piMap :
    ∀ (k : ℕ) {M : Fin k → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
      (f : ∀ i, M i →ₗ[R] M i),
      LinearMap.det (piMap f) = ∏ i, LinearMap.det (f i) := by
  intro k
  induction k with
  | zero =>
      intro M _ _ _ _ f
      have : Subsingleton (∀ i : Fin 0, M i) := ⟨fun a b => _root_.funext fun i => i.elim0⟩
      simp [LinearMap.det_eq_one_of_subsingleton]
  | succ k ih =>
      intro M _ _ _ _ f
      set e := Fin.consLinearEquiv R M with he
      have hconj : piMap f
          = (e : (M 0 × ∀ i : Fin k, M i.succ) →ₗ[R] (∀ i, M i)) ∘ₗ
              (LinearMap.prodMap (f 0) (piMap fun i : Fin k => f i.succ)) ∘ₗ
              (e.symm : (∀ i, M i) →ₗ[R] (M 0 × ∀ i : Fin k, M i.succ)) := by
        apply LinearMap.ext
        intro x
        apply _root_.funext
        refine Fin.cases ?_ ?_
        · rfl
        · intro j; rfl
      rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, ih, Fin.prod_univ_succ]

end BlockDet

/-! ### Obligation 3c: the dimension of a torsion summand

`dim V_f = deg f`.  The route planned in the appendix used the tower formula
`dim_ℝ V_f = dim_ℝ F_f · dim_{F_f} V_f` with `F_f = ℝ[X] ⧸ (f)`.  That is **instance-hostile**:
`Module.IsTorsionBy.module` supplies the `F_f`-structure only up to an instance diamond
(`Ideal.Quotient.ring` versus `Ideal.Quotient.semiring`, and two different
`AddCommMonoid` paths), and mathlib's own comment on the neighbouring
`quotientAnnihilator` warns that this area causes "synthesis failures / timeouts".

The replacement uses `minpoly` instead, and touches no quotient module: the restriction of
`A` to `V_f` is killed by `f`, so its minimal polynomial *is* `f`; that divides its
characteristic polynomial, whose degree is `dim V_f`; hence `deg f ≤ dim V_f`, and summing
against `∑ deg f = n` forces equality. -/

section MinpolyBlock

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- **An endomorphism killed by a monic irreducible `f` on a nonzero space has `minpoly f`.** -/
theorem minpoly_eq_of_irreducible [FiniteDimensional ℝ M] [Nontrivial M]
    (φ : M →ₗ[ℝ] M) {f : ℝ[X]} (hirr : Irreducible f) (hmon : f.Monic)
    (hkill : aeval φ f = 0) :
    minpoly ℝ φ = f := by
  have hdvd : minpoly ℝ φ ∣ f := minpoly.dvd ℝ φ hkill
  have hmm : (minpoly ℝ φ).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral φ)
  have hne1 : minpoly ℝ φ ≠ 1 := by
    intro h
    have hdeg : (minpoly ℝ φ).degree = 0 := by rw [h]; simp
    exact (minpoly.degree_pos (Algebra.IsIntegral.isIntegral φ)).ne' hdeg
  -- an irreducible has only units and associates as divisors
  obtain ⟨c, hc⟩ := hdvd
  have hcu : IsUnit c := by
    rcases hirr.isUnit_or_isUnit hc with h | h
    · exact absurd (hmm.eq_one_of_isUnit h) hne1
    · exact h
  exact (Polynomial.eq_of_monic_of_associated hmm hmon ⟨hcu.unit, by
    rw [IsUnit.unit_spec]; exact hc.symm⟩)

/-- Hence `deg f ≤ dim M`: the minimal polynomial divides the characteristic polynomial,
whose degree is the dimension. -/
theorem natDegree_le_finrank_of_aeval_eq_zero [FiniteDimensional ℝ M] [Nontrivial M]
    (φ : M →ₗ[ℝ] M) {f : ℝ[X]} (hirr : Irreducible f) (hmon : f.Monic)
    (hkill : aeval φ f = 0) :
    f.natDegree ≤ Module.finrank ℝ M := by
  have hmin : minpoly ℝ φ = f := minpoly_eq_of_irreducible φ hirr hmon hkill
  have hdvd : minpoly ℝ φ ∣ φ.charpoly := φ.minpoly_dvd_charpoly
  rw [hmin] at hdvd
  have hchar : φ.charpoly.natDegree = Module.finrank ℝ M := φ.charpoly_natDegree
  rw [← hchar]
  exact Polynomial.natDegree_le_of_dvd hdvd φ.charpoly_monic.ne_zero

end MinpolyBlock

/-! ### Obligation 3c, continued: the restriction of `A` to `ker f(A)`

Working with `ker f(A)` as an `ℝ`-submodule of `ℝⁿ` rather than with `torsionBy` inside
`AMod A` keeps everything in plain `ℝ`-linear algebra — no transport across `AEval'.of`, and
none of the quotient-module instance trouble noted above. -/

section RestrictKer

variable {N : ℕ}

/-- `ker f(A)` is `A`-invariant, because `A` commutes with `f(A)`. -/
lemma mapsTo_ker_aeval (A : Matrix (Fin N) (Fin N) ℝ) (f : ℝ[X]) :
    ∀ x ∈ LinearMap.ker (Matrix.mulVecLin (aeval A f)),
      Matrix.mulVecLin A x ∈ LinearMap.ker (Matrix.mulVecLin (aeval A f)) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  show (aeval A f).mulVec (A.mulVec x) = 0
  rw [Matrix.mulVec_mulVec, ← (commute_aeval A f).eq, ← Matrix.mulVec_mulVec]
  show A.mulVec ((aeval A f).mulVec x) = 0
  rw [show (aeval A f).mulVec x = 0 from hx, Matrix.mulVec_zero]

/-- The restriction of `A` to `ker f(A)`. -/
noncomputable def restrictKer (A : Matrix (Fin N) (Fin N) ℝ) (f : ℝ[X]) :
    (LinearMap.ker (Matrix.mulVecLin (aeval A f))) →ₗ[ℝ]
      (LinearMap.ker (Matrix.mulVecLin (aeval A f))) :=
  (Matrix.mulVecLin A).restrict (mapsTo_ker_aeval A f)

lemma coe_restrictKer (A : Matrix (Fin N) (Fin N) ℝ) (f : ℝ[X])
    (x : LinearMap.ker (Matrix.mulVecLin (aeval A f))) :
    ((restrictKer A f x : Fin N → ℝ)) = A.mulVec (x : Fin N → ℝ) :=
  LinearMap.coe_restrict_apply _ _

lemma coe_pow_restrictKer (A : Matrix (Fin N) (Fin N) ℝ) (f : ℝ[X]) (k : ℕ)
    (x : LinearMap.ker (Matrix.mulVecLin (aeval A f))) :
    (((restrictKer A f) ^ k) x : Fin N → ℝ) = (A ^ k).mulVec (x : Fin N → ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, coe_restrictKer, ih, Matrix.mulVec_mulVec,
        ← pow_succ']

lemma coe_aeval_restrictKer (A : Matrix (Fin N) (Fin N) ℝ) (f g : ℝ[X])
    (x : LinearMap.ker (Matrix.mulVecLin (aeval A f))) :
    ((aeval (restrictKer A f) g) x : Fin N → ℝ) = (aeval A g).mulVec (x : Fin N → ℝ) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq,
        Matrix.add_mulVec]
  | monomial k a =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
        ← Algebra.smul_def, LinearMap.smul_apply, Submodule.coe_smul,
        coe_pow_restrictKer, Matrix.smul_mulVec]

/-- **`f` annihilates the restriction.** -/
theorem aeval_restrictKer_self (A : Matrix (Fin N) (Fin N) ℝ) (f : ℝ[X]) :
    aeval (restrictKer A f) f = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [coe_aeval_restrictKer]
  have hx : (aeval A f).mulVec (x : Fin N → ℝ) = 0 := by
    have := x.2
    rwa [LinearMap.mem_ker] at this
  rw [hx]
  rfl

/-- **Obligation 3c, the inequality.**  `deg f ≤ dim ker f(A)` for `f` monic irreducible,
provided the kernel is nonzero — which `torsionBy_ne_bot` supplies. -/
theorem natDegree_le_finrank_ker (A : Matrix (Fin N) (Fin N) ℝ) {f : ℝ[X]}
    (hirr : Irreducible f) (hmon : f.Monic)
    [Nontrivial (LinearMap.ker (Matrix.mulVecLin (aeval A f)))] :
    f.natDegree ≤ Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (aeval A f))) :=
  natDegree_le_finrank_of_aeval_eq_zero (restrictKer A f) hirr hmon
    (aeval_restrictKer_self A f)

end RestrictKer

/-! ### Obligations 4–5: the one-block factors

A `1×1` block contributes the coordinate itself.  A `2×2` block contributes the binary form
`det[z | Bz] = c x² + (d−a)xy − b y²`, whose discriminant is `tr² − 4 det`, negative exactly
when the block's characteristic polynomial is irreducible over `ℝ`.  A definite binary form
becomes `α‖Lu‖²` after an invertible linear change of variables — the `plane` block shape. -/

/-- The Krylov determinant of a `1×1` block. -/
lemma det_krylov_one (B : Matrix (Fin 1) (Fin 1) ℝ) (z : Fin 1 → ℝ) :
    (krylov B z).det = z 0 := by
  rw [Matrix.det_fin_one]
  show ((B ^ (0 : ℕ)).mulVec z) 0 = z 0
  simp

/-- **The binary form of a `2×2` block.** -/
lemma det_krylov_two (B : Matrix (Fin 2) (Fin 2) ℝ) (z : Fin 2 → ℝ) :
    (krylov B z).det
      = B 1 0 * (z 0) ^ 2 + (B 1 1 - B 0 0) * (z 0) * (z 1) - B 0 1 * (z 1) ^ 2 := by
  rw [Matrix.det_fin_two]
  show ((B ^ (0:ℕ)).mulVec z) 0 * ((B ^ (1:ℕ)).mulVec z) 1
    - ((B ^ (1:ℕ)).mulVec z) 0 * ((B ^ (0:ℕ)).mulVec z) 1 = _
  simp only [pow_zero, pow_one, Matrix.one_mulVec]
  show z 0 * (B.mulVec z) 1 - (B.mulVec z) 0 * z 1 = _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Its discriminant is `tr² − 4 det`. -/
lemma disc_eq (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (B 1 1 - B 0 0) ^ 2 - 4 * (B 1 0) * (-(B 0 1))
      = (B 0 0 + B 1 1) ^ 2 - 4 * B.det := by
  rw [Matrix.det_fin_two]
  ring

/-- **A definite binary form is `α‖Lu‖²`.**  This is what turns a `2×2` block into the
`plane` block shape `‖·‖²`. -/
theorem definite_binary_form {α β γ : ℝ} (hdisc : β ^ 2 - 4 * α * γ < 0) :
    ∃ L : Matrix (Fin 2) (Fin 2) ℝ, IsUnit L.det ∧ α ≠ 0 ∧
      ∀ x y : ℝ, α * x ^ 2 + β * x * y + γ * y ^ 2
        = α * (((L.mulVec ![x, y]) 0) ^ 2 + ((L.mulVec ![x, y]) 1) ^ 2) := by
  -- `α ≠ 0`: otherwise the discriminant is `β² ≥ 0`
  have hα : α ≠ 0 := by
    intro h
    rw [h] at hdisc
    nlinarith [sq_nonneg β]
  -- the completed square
  have hκ2 : 0 < (4 * α * γ - β ^ 2) / (4 * α ^ 2) := by
    have h4 : (0:ℝ) < 4 * α ^ 2 := by positivity
    exact div_pos (by linarith) h4
  set κ : ℝ := Real.sqrt ((4 * α * γ - β ^ 2) / (4 * α ^ 2)) with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.mpr hκ2
  have hκsq : κ ^ 2 = (4 * α * γ - β ^ 2) / (4 * α ^ 2) := Real.sq_sqrt hκ2.le
  refine ⟨!![1, β / (2 * α); 0, κ], ?_, hα, ?_⟩
  · rw [Matrix.det_fin_two_of]
    simpa using hκ0.ne'
  · intro x y
    have hL0 : (Matrix.mulVec !![1, β / (2 * α); 0, κ] ![x, y]) 0 = x + β / (2 * α) * y := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hL1 : (Matrix.mulVec !![1, β / (2 * α); 0, κ] ![x, y]) 1 = κ * y := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hL0, hL1, mul_pow, hκsq]
    field_simp
    ring

end MPE
