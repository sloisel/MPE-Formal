import Mathlib

/-!
# A vector whose annihilator is the minimal polynomial

This is the paper's Lemma 4.2(i) in the form the general window needs: for a real matrix `A`
there is a vector `v` annihilated by no polynomial that `m_A` does not already divide —
equivalently, `v, Av, …, A^{k-1}v` are independent for `k = deg m_A`.

mathlib does not carry this.  The usual proof factors `m_A` into coprime prime powers and
adds together vectors realising each; the proof here is shorter.  The annihilator of any `v`
divides `m_A`, so if no `v` realised `m_A` then every `v` would be killed by `m_A/q` for one
of the *finitely many* irreducible factors `q` of `m_A`.  That exhibits `ℝⁿ` as a finite
union of proper subspaces, which is impossible over an infinite field
(`Subspace.exists_eq_top_of_iUnion_eq_univ`).

The gcd is what keeps the argument finite: a vector killed by some `p` with `m_A ∤ p` is
killed by `gcd(p, m_A)`, which *does* divide `m_A`, so only divisors of `m_A` are ever in
play.
-/

namespace MPE

open Polynomial

variable {n : ℕ}

/-- `ker p(A)`, as a subspace. -/
noncomputable def kerAeval (A : Matrix (Fin n) (Fin n) ℝ) (p : ℝ[X]) :
    Subspace ℝ (Fin n → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin ((aeval A) p))

lemma mem_kerAeval {A : Matrix (Fin n) (Fin n) ℝ} {p : ℝ[X]} {v : Fin n → ℝ} :
    v ∈ kerAeval A p ↔ ((aeval A) p).mulVec v = 0 := Iff.rfl

/-- A matrix killing every vector is zero. -/
lemma matrix_eq_zero_of_mulVec_eq_zero {N : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ v, N.mulVec v = 0) : N = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using this

lemma kerAeval_ne_top {A : Matrix (Fin n) (Fin n) ℝ} {p : ℝ[X]}
    (hp : (aeval A) p ≠ 0) : kerAeval A p ≠ ⊤ := by
  intro h
  refine hp (matrix_eq_zero_of_mulVec_eq_zero fun v => ?_)
  have : v ∈ kerAeval A p := h ▸ Submodule.mem_top
  exact mem_kerAeval.mp this

/-- The annihilator of a *vector*: the polynomials `p` with `p(A)v = 0`.  An ideal of `ℝ[X]`,
hence principal, and it contains `m_A`; so its generator always divides `m_A`. -/
noncomputable def annIdealVec (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : Ideal ℝ[X] where
  carrier := {p : ℝ[X] | ((aeval A) p).mulVec v = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, Matrix.add_mulVec, ha, hb, add_zero]
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, Matrix.zero_mulVec]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [smul_eq_mul, map_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

lemma mem_annIdealVec {A : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {p : ℝ[X]} :
    p ∈ annIdealVec A v ↔ ((aeval A) p).mulVec v = 0 := Iff.rfl

/-- **Lemma 4.2(i).**  Some vector realises the minimal polynomial as its annihilator. -/
theorem exists_ann_eq_minpoly (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ v : Fin n → ℝ, ∀ p : ℝ[X], ((aeval A) p).mulVec v = 0 → minpoly ℝ A ∣ p := by
  classical
  set mp : ℝ[X] := minpoly ℝ A with hmpdef
  have hint : IsIntegral ℝ A := Matrix.isIntegral _
  have hmp0 : mp ≠ 0 := minpoly.ne_zero hint
  have hmpaev : (aeval A) mp = 0 := minpoly.aeval ℝ A
  by_contra hcon
  push_neg at hcon
  -- the finitely many irreducible factors of `m_A`, and a chosen cofactor for each
  set S : Finset ℝ[X] := (UniqueFactorizationMonoid.normalizedFactors mp).toFinset with hSdef
  set cof : ℝ[X] → ℝ[X] := fun q => if h : q ∣ mp then h.choose else 0 with hcofdef
  have hcof : ∀ q : ℝ[X], q ∣ mp → mp = q * cof q := by
    intro q hq
    rw [hcofdef]
    simp only [dif_pos hq]
    exact hq.choose_spec
  have hSdvd : ∀ q : ℝ[X], q ∈ S → q ∣ mp ∧ Irreducible q := by
    intro q hq
    rw [hSdef, Multiset.mem_toFinset] at hq
    exact ⟨UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq,
      UniqueFactorizationMonoid.irreducible_of_normalized_factor _ hq⟩
  -- every vector is killed by `m_A / q` for one of them
  have hcov : (⋃ q : {x // x ∈ S}, (kerAeval A (cof (q : ℝ[X])) : Set (Fin n → ℝ)))
      = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨p, hpv, hpd⟩ := hcon v
    -- the generator of the vector annihilator divides `m_A` but is not a multiple of it
    set I : Ideal ℝ[X] := annIdealVec A v with hIdef
    set g : ℝ[X] := Submodule.IsPrincipal.generator I with hgdef
    have hmpI : mp ∈ I :=
      show ((aeval A) mp).mulVec v = 0 by rw [hmpaev, Matrix.zero_mulVec]
    have hgmp : g ∣ mp := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hmpI
    have hgp : g ∣ p := (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hpv
    have hgnd : ¬ mp ∣ g := fun h => hpd (h.trans hgp)
    obtain ⟨c, hc⟩ := hgmp
    have hg0 : g ≠ 0 := fun h => hmp0 (by rw [hc, h, zero_mul])
    have hc0 : c ≠ 0 := fun h => hmp0 (by rw [hc, h, mul_zero])
    have hcnu : ¬ IsUnit c := by
      intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      refine hgnd ⟨b, ?_⟩
      rw [hc, mul_assoc, hb, mul_one]
    obtain ⟨q₀, hq₀irr, hq₀c⟩ := WfDvdMonoid.exists_irreducible_factor hcnu hc0
    have hq₀mp : q₀ ∣ mp := hq₀c.trans (Dvd.intro_left g hc.symm)
    obtain ⟨q, hqS, hqassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hmp0 hq₀irr hq₀mp
    have hqS' : q ∈ S := by rw [hSdef, Multiset.mem_toFinset]; exact hqS
    have hqmp : q ∣ mp := (hSdvd q hqS').1
    have hq0 : q ≠ 0 := (hSdvd q hqS').2.ne_zero
    refine Set.mem_iUnion.mpr ⟨⟨q, hqS'⟩, ?_⟩
    -- `g ∣ cof q`, by cancelling `q` from `m_A = q * cof q = q * (g * u * e)`
    obtain ⟨u, hu⟩ := hqassoc
    obtain ⟨e, he⟩ := hq₀c
    have huu : (u : ℝ[X]) * ((u⁻¹ : ℝ[X]ˣ) : ℝ[X]) = 1 := u.mul_inv
    have hcan : q * cof q = q * (g * (e * ((u⁻¹ : ℝ[X]ˣ) : ℝ[X]))) := by
      rw [← hcof q hqmp, hc, he, ← hu]
      calc g * (q₀ * e) = q₀ * g * e * 1 := by ring
        _ = q₀ * g * e * ((u : ℝ[X]) * ((u⁻¹ : ℝ[X]ˣ) : ℝ[X])) := by rw [huu]
        _ = q₀ * (u : ℝ[X]) * (g * (e * ((u⁻¹ : ℝ[X]ˣ) : ℝ[X]))) := by ring
    have hgcof : g ∣ cof q :=
      ⟨e * ((u⁻¹ : ℝ[X]ˣ) : ℝ[X]), mul_left_cancel₀ hq0 hcan⟩
    show ((aeval A) (cof q)).mulVec v = 0
    exact (Submodule.IsPrincipal.mem_iff_generator_dvd I).mpr hgcof
  obtain ⟨q, hq⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  -- but each of them is proper: `m_A ∤ m_A/q`, by degree
  refine kerAeval_ne_top (p := cof (q : ℝ[X])) ?_ hq
  intro hzero
  obtain ⟨hqmp, hqirr⟩ := hSdvd (q : ℝ[X]) q.2
  have heq : mp = (q : ℝ[X]) * cof (q : ℝ[X]) := hcof _ hqmp
  have hdvd : mp ∣ cof (q : ℝ[X]) := minpoly.dvd ℝ A hzero
  have hcf0 : cof (q : ℝ[X]) ≠ 0 := fun h => hmp0 (by rw [heq, h, mul_zero])
  have hle : mp.natDegree ≤ (cof (q : ℝ[X])).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hcf0
  have hlt : (cof (q : ℝ[X])).natDegree < mp.natDegree := by
    rw [heq, Polynomial.natDegree_mul hqirr.ne_zero hcf0]
    have := hqirr.natDegree_pos
    omega
  omega

end MPE
