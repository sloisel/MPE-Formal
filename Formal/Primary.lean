import Mathlib
import Formal.RealForm

/-!
# The real primary decomposition of `ℝⁿ`

Let `A` be a real `n × n` matrix whose characteristic polynomial is squarefree, and write
`charpoly A = ∏ᵢ fᵢ` with the `fᵢ` distinct monic irreducibles (so `deg fᵢ ≤ 2`).  Then

    ℝⁿ = ⨁ᵢ ker fᵢ(A).

This is Obligation 2 of `../appendix.tex`, but proved *directly for `ℝ`-submodules of `ℝⁿ`*
rather than through `Module.AEval'` and `Submodule.torsionBy_isInternal`.  The reason is
purely practical: the torsion route states the decomposition for `ℝ[X]`-submodules of a type
synonym, and transporting `DirectSum.IsInternal` back across `Module.AEval'.of` — through
`restrictScalars` and the `iSup` of two different lattices — costs more than reproving it.
The direct proof needs exactly two inputs:

* a Bézout identity for the *cofactors* `eᵢ = ∏_{j ≠ i} fⱼ`, which generate the unit ideal;
* `ker fᵢ(A) ⊓ ker eᵢ(A) = ⊥`, again by Bézout.

Nothing here mentions `ℂ`.
-/

set_option maxHeartbeats 1000000

namespace MPE

open Polynomial

/-! ### A Bézout identity for a pairwise-coprime family

If `f₁, …, f_N` are pairwise coprime then the cofactors `eᵢ = ∏_{j ≠ i} fⱼ` generate the unit
ideal.  Mathlib has `IsCoprime.prod_right`, i.e. `IsCoprime fᵢ eᵢ`, but not this. -/

/-- **The cofactors of a pairwise-coprime family generate the unit ideal.** -/
theorem exists_bezout_cofactors {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (ff : ι → R) (hpw : Pairwise fun i j => IsCoprime (ff i) (ff j)) :
    ∀ s : Finset ι, s.Nonempty → ∃ u : ι → R, ∑ i ∈ s, u i * ∏ j ∈ s.erase i, ff j = 1 := by
  classical
  intro s
  induction s using Finset.cons_induction with
  | empty => intro h; simp at h
  | cons a t ha ih =>
      intro _
      rw [Finset.cons_eq_insert]
      rcases t.eq_empty_or_nonempty with rfl | hne
      · exact ⟨fun _ => 1, by simp⟩
      obtain ⟨u, hu⟩ := ih hne
      obtain ⟨α, β, hαβ⟩ : IsCoprime (ff a) (∏ j ∈ t, ff j) :=
        IsCoprime.prod_right fun j hj => hpw fun hja => ha (hja ▸ hj)
      refine ⟨fun i => if i = a then β else α * u i, ?_⟩
      have key : ∀ i ∈ t, (if i = a then β else α * u i) * ∏ j ∈ (insert a t).erase i, ff j
          = (α * ff a) * (u i * ∏ j ∈ t.erase i, ff j) := by
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        rw [if_neg hia, Finset.erase_insert_of_ne (Ne.symm hia),
          Finset.prod_insert (fun hmem => ha (Finset.mem_of_mem_erase hmem))]
        ring
      have hval : (fun i => if i = a then β else α * u i) a = β := if_pos rfl
      rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.sum_congr rfl key,
        ← Finset.mul_sum, hu, hval]
      linear_combination hαβ

/-! ### The kernels `ker f(A)` -/

section Ker

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

/-- Membership in `ker f(A)`, spelled out. -/
lemma mem_ker_aeval {f : ℝ[X]} {x : Fin n → ℝ} :
    x ∈ LinearMap.ker (Matrix.mulVecLin (aeval A f)) ↔ (aeval A f).mulVec x = 0 := Iff.rfl

/-- `ker f(A)` grows with `f`. -/
lemma ker_aeval_mono {f g : ℝ[X]} (h : f ∣ g) :
    LinearMap.ker (Matrix.mulVecLin (aeval A f))
      ≤ LinearMap.ker (Matrix.mulVecLin (aeval A g)) := by
  intro x hx
  obtain ⟨c, rfl⟩ := h
  rw [mem_ker_aeval] at hx ⊢
  rw [show f * c = c * f from mul_comm f c, map_mul, ← Matrix.mulVec_mulVec, hx,
    Matrix.mulVec_zero]

/-- **Bézout kills the intersection.**  Coprime polynomials have disjoint kernels. -/
lemma ker_aeval_disjoint {f g : ℝ[X]} (h : IsCoprime f g) :
    Disjoint (LinearMap.ker (Matrix.mulVecLin (aeval A f)))
      (LinearMap.ker (Matrix.mulVecLin (aeval A g))) := by
  obtain ⟨a, b, hab⟩ := h
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hf, hg⟩ := hx
  rw [mem_ker_aeval] at hf hg
  have hxe : x = (aeval A (a * f)).mulVec x + (aeval A (b * g)).mulVec x := by
    rw [← Matrix.add_mulVec, ← map_add, hab, map_one, Matrix.one_mulVec]
  have h1 : (aeval A (a * f)).mulVec x = 0 := by
    rw [map_mul, ← Matrix.mulVec_mulVec, hf, Matrix.mulVec_zero]
  have h2 : (aeval A (b * g)).mulVec x = 0 := by
    rw [map_mul, ← Matrix.mulVec_mulVec, hg, Matrix.mulVec_zero]
  rw [Submodule.mem_bot, hxe, h1, h2, add_zero]

/-! ### The decomposition -/

variable {N : ℕ} (ff : Fin N → ℝ[X])

/-- **Independence of the primary components.**  The other components all lie in the kernel of
the cofactor `eᵢ`, which is coprime to `fᵢ`. -/
theorem iSupIndep_ker (hpw : Pairwise fun i j => IsCoprime (ff i) (ff j)) :
    iSupIndep fun i : Fin N => LinearMap.ker (Matrix.mulVecLin (aeval A (ff i))) := by
  classical
  intro i
  -- the cofactor
  set e : ℝ[X] := ∏ j ∈ Finset.univ.erase i, ff j with he
  have hcop : IsCoprime (ff i) e := by
    rw [he]
    exact IsCoprime.prod_right fun j hj => hpw (Finset.ne_of_mem_erase hj).symm
  refine (ker_aeval_disjoint A hcop).mono_right ?_
  refine iSup_le fun j => iSup_le fun hj => ?_
  refine ker_aeval_mono A ?_
  rw [he]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)

/-- **The primary components span.**  Immediately from the Bézout identity for the cofactors
and Cayley–Hamilton. -/
theorem iSup_ker_eq_top (hN : 0 < N) (hpw : Pairwise fun i j => IsCoprime (ff i) (ff j))
    (hprod : ∏ i, ff i = A.charpoly) :
    (⨆ i : Fin N, LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))) = ⊤ := by
  classical
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hN
  obtain ⟨u, hu⟩ := exists_bezout_cofactors ff hpw Finset.univ hne
  rw [Submodule.eq_top_iff']
  intro x
  -- `x = ∑ᵢ (uᵢ eᵢ)(A) x`, and the `i`-th term lies in `ker fᵢ(A)`
  have hsplit : x = ∑ i : Fin N,
      (aeval A (u i * ∏ j ∈ Finset.univ.erase i, ff j)).mulVec x := by
    have : ∑ i : Fin N, (aeval A (u i * ∏ j ∈ Finset.univ.erase i, ff j))
        = aeval A (1 : ℝ[X]) := by
      rw [← map_sum, hu]
    calc x = (aeval A (1 : ℝ[X])).mulVec x := by rw [map_one, Matrix.one_mulVec]
      _ = (∑ i : Fin N, (aeval A (u i * ∏ j ∈ Finset.univ.erase i, ff j))).mulVec x := by
            rw [this]
      _ = _ := by
            rw [Matrix.sum_mulVec]
  rw [hsplit]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine Submodule.mem_iSup_of_mem i ?_
  have hkey : ff i * (u i * ∏ j ∈ Finset.univ.erase i, ff j) = u i * A.charpoly := by
    rw [← hprod, ← Finset.mul_prod_erase Finset.univ ff (Finset.mem_univ i)]
    ring
  rw [mem_ker_aeval, Matrix.mulVec_mulVec, ← map_mul, hkey, map_mul,
    Matrix.aeval_self_charpoly, mul_zero, Matrix.zero_mulVec]

/-- **Obligation 2, restated for `ℝ`-submodules of `ℝⁿ`.** -/
theorem isInternal_ker (hN : 0 < N) (hpw : Pairwise fun i j => IsCoprime (ff i) (ff j))
    (hprod : ∏ i, ff i = A.charpoly) :
    DirectSum.IsInternal fun i : Fin N =>
      LinearMap.ker (Matrix.mulVecLin (aeval A (ff i))) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_ker A ff hpw, iSup_ker_eq_top A ff hN hpw hprod⟩

end Ker


/-! ### The determinant of an endomorphism respecting an internal direct sum

Mathlib has the corresponding statement for the *trace*
(`LinearMap.trace_eq_sum_trace_restrict`, via
`LinearMap.toMatrix_directSum_collectedBasis_eq_blockDiagonal'`) but not for the determinant,
and it has `Matrix.det_blockDiagonal` only for blocks of *constant* size.  Basis-free, the
proof is three lines on top of `det_piMap`. -/

section DetInternal

variable {M : Type} [AddCommGroup M] [Module ℝ M] {N : ℕ} (V : Fin N → Submodule ℝ M)

/-- Coordinates for an internal direct sum indexed by `Fin N`.  On elements it is
`x ↦ ∑ᵢ xᵢ` (`internalEquiv_apply`). -/
noncomputable def internalEquiv (h : DirectSum.IsInternal V) : (∀ i, V i) ≃ₗ[ℝ] M :=
  (DirectSum.linearEquivFunOnFintype ℝ (Fin N) fun i => V i).symm.trans
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap V) h)

@[simp] lemma internalEquiv_single (h : DirectSum.IsInternal V) (i : Fin N) (y : V i) :
    internalEquiv V h (Pi.single i y) = (y : M) := by
  simp [internalEquiv, DirectSum.linearEquivFunOnFintype_symm_single]

lemma internalEquiv_apply (h : DirectSum.IsInternal V) (x : ∀ i, V i) :
    internalEquiv V h x = ∑ i, (x i : M) := by
  have hx : ∑ i, Pi.single i (x i) = x := Finset.univ_sum_single x
  calc internalEquiv V h x
      = internalEquiv V h (∑ i, Pi.single i (x i)) := by rw [hx]
    _ = ∑ i, internalEquiv V h (Pi.single i (x i)) := map_sum _ _ _
    _ = ∑ i, (x i : M) := Finset.sum_congr rfl fun i _ => internalEquiv_single V h i (x i)

/-- **The determinant of an endomorphism respecting an internal direct sum** is the product of
the determinants of its restrictions. -/
theorem det_eq_prod_det_restrict [∀ i, Module.Free ℝ (V i)] [∀ i, Module.Finite ℝ (V i)]
    (h : DirectSum.IsInternal V) (f : M →ₗ[ℝ] M) (hf : ∀ i, ∀ x ∈ V i, f x ∈ V i) :
    LinearMap.det f = ∏ i, LinearMap.det (f.restrict (hf i)) := by
  set E := internalEquiv V h with hE
  have hcomp : ∀ x : ∀ i, V i, E (piMap (fun i => f.restrict (hf i)) x) = f (E x) := by
    intro x
    rw [hE, internalEquiv_apply, internalEquiv_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show ((f.restrict (hf i)) (x i) : M) = f (x i)
    exact LinearMap.coe_restrict_apply _ _
  have hconj : piMap (fun i => f.restrict (hf i))
      = (E.symm : M →ₗ[ℝ] (∀ i, V i)) ∘ₗ f ∘ₗ (E : (∀ i, V i) →ₗ[ℝ] M) := by
    apply LinearMap.ext
    intro x
    show piMap (fun i => f.restrict (hf i)) x = E.symm (f (E x))
    rw [← hcomp x, E.symm_apply_apply]
  rw [← det_piMap N (fun i => f.restrict (hf i)), hconj]
  simpa using (LinearMap.det_conj f E.symm).symm

end DetInternal

/-! ### Obligation 3: the dimension of each primary component

`dim ker fᵢ(A) = deg fᵢ`.  Only the *inequality* `deg fᵢ ≤ dim ker fᵢ(A)` is needed — from
`minpoly` — because `∑ dim = n = ∑ deg` then forces equality termwise.  In particular the
tower formula of the appendix, and with it the quotient-module instance trouble, is not
needed at all. -/

section Dim

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {N : ℕ} (ff : Fin N → ℝ[X])

/-- Each primary component is nonzero (Obligation 3b). -/
theorem ker_aeval_ne_bot {f : ℝ[X]} (hdeg : 0 < f.degree) (hdvd : f ∣ A.charpoly) :
    LinearMap.ker (Matrix.mulVecLin (aeval A f)) ≠ ⊥ := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (det_aeval_eq_zero_of_dvd_charpoly A hdeg hdvd)
  intro hbot
  have hmem : v ∈ LinearMap.ker (Matrix.mulVecLin (aeval A f)) := hv
  rw [hbot, Submodule.mem_bot] at hmem
  exact hv0 hmem

/-- A real irreducible polynomial has positive degree. -/
lemma natDegree_pos_of_irreducible {f : ℝ[X]} (hirr : Irreducible f) : 0 < f.natDegree :=
  Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr)

/-- **Obligation 3.**  Each primary component has real dimension exactly `deg fᵢ`. -/
theorem finrank_ker_eq_natDegree (hN : 0 < N)
    (hirr : ∀ i, Irreducible (ff i)) (hmon : ∀ i, (ff i).Monic)
    (hpw : Pairwise fun i j => IsCoprime (ff i) (ff j))
    (hprod : ∏ i, ff i = A.charpoly) (i : Fin N) :
    Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))) = (ff i).natDegree := by
  classical
  have hdvd : ∀ j, ff j ∣ A.charpoly := fun j => by
    rw [← hprod]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hdeg : ∀ j, 0 < (ff j).degree := fun j => Polynomial.degree_pos_of_irreducible (hirr j)
  -- `deg fⱼ ≤ dim ker fⱼ(A)`
  have hle : ∀ j, (ff j).natDegree
      ≤ Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (aeval A (ff j)))) := by
    intro j
    haveI : Nontrivial (LinearMap.ker (Matrix.mulVecLin (aeval A (ff j)))) :=
      Submodule.nontrivial_iff_ne_bot.mpr (ker_aeval_ne_bot A (hdeg j) (hdvd j))
    exact natDegree_le_finrank_ker A (hirr j) (hmon j)
  -- the two sums
  have hsum1 : ∑ j, Module.finrank ℝ
      (LinearMap.ker (Matrix.mulVecLin (aeval A (ff j)))) = n := by
    rw [finrank_sum_of_isInternal (K := ℝ) _ (isInternal_ker A ff hN hpw hprod)]
    simp
  have hsum2 : ∑ j, (ff j).natDegree = n := by
    have h1 : (∏ j, ff j).natDegree = ∑ j, (ff j).natDegree :=
      Polynomial.natDegree_prod _ _ fun j _ => (hmon j).ne_zero
    rw [hprod, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h1
    exact h1.symm
  have hEq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp (by rw [hsum2, hsum1])
  exact (hEq i (Finset.mem_univ i)).symm

end Dim

/-! ### A cyclic vector

`v = ∑ᵢ wᵢ` with every `wᵢ ≠ 0` is cyclic.  The proof is by *injectivity*: if
`g(A) v = 0` with `deg g < n`, then `g(φᵢ) wᵢ = 0` for each `i` (the components of a direct
sum vanish separately), hence `fᵢ ∣ g` by Bézout, hence `charpoly = ∏ fᵢ ∣ g` by pairwise
coprimality, hence `g = 0` by degrees.  So `K_A(v)` has trivial kernel, and being square it is
invertible.

No cyclicity of the individual blocks is needed, and no Cayley–Hamilton span argument. -/

section Cyclic

/-- **Bézout.**  If `φ` is killed by an irreducible `f` and `g(φ)` kills a nonzero vector,
then `f ∣ g`. -/
theorem dvd_of_aeval_apply_eq_zero {M : Type*} [AddCommGroup M] [Module ℝ M]
    (φ : M →ₗ[ℝ] M) {f : ℝ[X]} (hirr : Irreducible f) (hkill : aeval φ f = 0)
    {w : M} (hw : w ≠ 0) {g : ℝ[X]} (hg : (aeval φ g) w = 0) : f ∣ g := by
  by_contra hnd
  obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hnd
  have h1 : (aeval φ (a * f)) w = 0 := by
    rw [map_mul, hkill, mul_zero, LinearMap.zero_apply]
  have h2 : (aeval φ (b * g)) w = 0 := by
    rw [map_mul, Module.End.mul_apply, hg, map_zero]
  refine hw ?_
  calc w = (aeval φ (1 : ℝ[X])) w := by rw [map_one, Module.End.one_apply]
    _ = (aeval φ (a * f + b * g)) w := by rw [hab]
    _ = (aeval φ (a * f)) w + (aeval φ (b * g)) w := by rw [map_add, LinearMap.add_apply]
    _ = 0 := by rw [h1, h2, add_zero]

/-- `K_A(v) c = g(A) v` for the polynomial `g = ∑_{j<n} cⱼ Xʲ`. -/
lemma krylov_mulVec_eq_aeval {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v c : Fin n → ℝ) :
    Matrix.mulVec (krylov A v) c
      = (aeval A (∑ j : Fin n, Polynomial.monomial (j : ℕ) (c j))).mulVec v := by
  have hae : aeval A (∑ j : Fin n, Polynomial.monomial (j : ℕ) (c j))
      = ∑ j : Fin n, c j • A ^ (j : ℕ) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Polynomial.aeval_monomial, ← Algebra.smul_def]
  rw [hae, Matrix.sum_mulVec]
  funext i
  simp only [Matrix.mulVec, dotProduct, krylov_apply, Finset.sum_apply, Matrix.smul_mulVec,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

variable {n N : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ff : Fin N → ℝ[X])

/-- `g(A)` acts componentwise on the primary decomposition. -/
lemma aeval_mulVec_internalEquiv
    (h : DirectSum.IsInternal fun i : Fin N =>
      LinearMap.ker (Matrix.mulVecLin (aeval A (ff i))))
    (g : ℝ[X]) (w : ∀ i, LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))) :
    (aeval A g).mulVec (internalEquiv _ h w)
      = internalEquiv _ h (fun i => (aeval (restrictKer A (ff i)) g) (w i)) := by
  rw [internalEquiv_apply, internalEquiv_apply]
  show (Matrix.mulVecLin (aeval A g)) (∑ i, ((w i : Fin n → ℝ))) = _
  rw [map_sum]
  exact (Finset.sum_congr rfl fun i _ => coe_aeval_restrictKer A (ff i) g (w i)).symm

/-- **A cyclic vector.**  A vector whose primary components are all nonzero is cyclic. -/
theorem det_krylov_internalEquiv_ne_zero (hn : 0 < n) (hN : 0 < N)
    (hirr : ∀ i, Irreducible (ff i)) (hmon : ∀ i, (ff i).Monic)
    (hpw : Pairwise fun i j => IsCoprime (ff i) (ff j)) (hprod : ∏ i, ff i = A.charpoly)
    (w : ∀ i, LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))) (hw : ∀ i, w i ≠ 0) :
    (krylov A (internalEquiv _ (isInternal_ker A ff hN hpw hprod) w)).det ≠ 0 := by
  classical
  set h := isInternal_ker A ff hN hpw hprod with hh
  set v := internalEquiv
    (fun i : Fin N => LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))) h w with hv
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set g : ℝ[X] := ∑ j : Fin n, Polynomial.monomial (j : ℕ) (c j) with hgdef
  -- the coefficients of `g` are the entries of `c`
  have hcoeff : ∀ m : ℕ, g.coeff m = ∑ j : Fin n, if (j : ℕ) = m then c j else 0 := by
    intro m
    rw [hgdef, Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl fun j _ => Polynomial.coeff_monomial
  have hcj : ∀ j : Fin n, g.coeff (j : ℕ) = c j := by
    intro j
    rw [hcoeff, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp only [ite_eq_right_iff]
      intro hkj
      exact absurd (Fin.val_injective hkj) hk
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hdeg : g.degree < (n : ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [hcoeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hjn : (j : ℕ) < n := j.isLt
    have : (j : ℕ) ≠ m := by omega
    simp [this]
  -- `K_A(v) c = g(A) v`
  have hkey : Matrix.mulVec (krylov A v) c = (aeval A g).mulVec v := by
    rw [hgdef]; exact krylov_mulVec_eq_aeval A v c
  have hgv : (aeval A g).mulVec v = 0 := by rw [← hkey, hc]
  -- the components vanish separately
  have hcomp := aeval_mulVec_internalEquiv A ff h g w
  rw [hgv] at hcomp
  have hzero : ∀ i, (aeval (restrictKer A (ff i)) g) (w i) = 0 := by
    have h0 : (internalEquiv _ h) (fun i => (aeval (restrictKer A (ff i)) g) (w i))
        = (internalEquiv _ h) 0 := by rw [map_zero, ← hcomp]
    intro i
    exact congrFun ((internalEquiv _ h).injective h0) i
  -- Bézout, then pairwise coprimality, then degrees
  have hdvd : ∀ i, ff i ∣ g := fun i =>
    dvd_of_aeval_apply_eq_zero (restrictKer A (ff i)) (hirr i)
      (aeval_restrictKer_self A (ff i)) (hw i) (hzero i)
  have hpd : A.charpoly ∣ g := by
    rw [← hprod]
    exact Fintype.prod_dvd_of_coprime hpw hdvd
  have hg0 : g = 0 := by
    by_contra hne
    have h1 : A.charpoly.degree ≤ g.degree := Polynomial.degree_le_of_dvd hpd hne
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at h1
    exact absurd (lt_of_le_of_lt h1 hdeg) (lt_irrefl _)
  refine hc0 (funext fun j => ?_)
  rw [← hcj j, hg0]
  simp

end Cyclic

/-! ### The shape of one block

A block is `1×1` or `2×2`.  A `1×1` block contributes its coordinate — a *line* block.  A
`2×2` block contributes `det[u | Bu]`, a binary form whose discriminant is `tr² − 4 det`,
negative because the block's characteristic polynomial is irreducible over `ℝ`; completing
the square turns it into `‖·‖²` — a *plane* block. -/

section BlockShape

/-- A block factor vanishes only at the origin. -/
lemma BlockKind.eq_zero_of_factor_eq_zero (k : BlockKind) {u : Fin k.dim → ℝ}
    (h : k.factor u = 0) : u = 0 := by
  cases k with
  | line =>
      have h0 : u 0 = 0 := h
      funext i
      induction i using Fin.cases with
      | zero => rw [Pi.zero_apply]; exact h0
      | succ j => exact j.elim0
  | plane =>
      have h' : u 0 ^ 2 + u 1 ^ 2 = 0 := h
      have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      funext i
      fin_cases i
      · simpa using h0
      · simpa using h1

/-- Left multiplication by an invertible matrix, as a linear equivalence. -/
noncomputable def mulVecEquiv {m : ℕ} {P : Matrix (Fin m) (Fin m) ℝ} (hP : IsUnit P.det) :
    (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) where
  __ := Matrix.mulVecLin P
  invFun w := Matrix.mulVec P⁻¹ w
  left_inv z := by
    show Matrix.mulVec P⁻¹ (Matrix.mulVec P z) = z
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec]
  right_inv w := by
    show Matrix.mulVec P (Matrix.mulVec P⁻¹ w) = w
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]

@[simp] lemma mulVecEquiv_apply {m : ℕ} {P : Matrix (Fin m) (Fin m) ℝ} (hP : IsUnit P.det)
    (z : Fin m → ℝ) : mulVecEquiv hP z = Matrix.mulVec P z := rfl

/-- **A real quadratic with an irreducible characteristic polynomial has negative
discriminant.** -/
lemma disc_neg_of_irreducible_charpoly (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hirr : Irreducible B.charpoly) : (B 0 0 + B 1 1) ^ 2 - 4 * B.det < 0 := by
  by_contra hle
  rw [not_lt] at hle
  set T : ℝ := B 0 0 + B 1 1 with hT
  set D : ℝ := B.det with hD
  set r : ℝ := (T + Real.sqrt (T ^ 2 - 4 * D)) / 2 with hr
  have hsq : Real.sqrt (T ^ 2 - 4 * D) ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt (by linarith)
  have hroot : B.charpoly.IsRoot r := by
    rw [Polynomial.IsRoot, Matrix.charpoly_fin_two, Matrix.trace_fin_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [← hT, ← hD, hr]
    nlinarith [hsq]
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  rcases hirr.isUnit_or_isUnit hq with h | h
  · rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_X_sub_C] at h
    exact absurd h one_ne_zero
  · have hq0 : q ≠ 0 := fun hz => by
      rw [hz, mul_zero] at hq; exact B.charpoly_monic.ne_zero hq
    have hnd : (Polynomial.X - Polynomial.C r).natDegree + q.natDegree = 2 := by
      have h1 := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq0
      rw [← hq, Matrix.charpoly_natDegree_eq_dim] at h1
      simpa using h1.symm
    rw [Polynomial.natDegree_X_sub_C] at hnd
    rw [Polynomial.isUnit_iff_degree_eq_zero] at h
    have hq1 : q.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h)
    omega

/-- A `1×1` block is a line block. -/
theorem block_shape_one (B : Matrix (Fin 1) (Fin 1) ℝ) :
    ∃ (S : (Fin 1 → ℝ) ≃ₗ[ℝ] (Fin (BlockKind.line).dim → ℝ)) (c : ℝ), c ≠ 0 ∧
      ∀ u, (krylov B u).det = c * BlockKind.line.factor (S u) :=
  ⟨LinearEquiv.refl ℝ _, 1, one_ne_zero, fun u => by rw [det_krylov_one]; simp⟩

/-- An irreducible `2×2` block is a plane block. -/
theorem block_shape_two (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hdisc : (B 0 0 + B 1 1) ^ 2 - 4 * B.det < 0) :
    ∃ (S : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin (BlockKind.plane).dim → ℝ)) (c : ℝ), c ≠ 0 ∧
      ∀ u, (krylov B u).det = c * BlockKind.plane.factor (S u) := by
  obtain ⟨L, hL, hα, hid⟩ := definite_binary_form
    (α := B 1 0) (β := B 1 1 - B 0 0) (γ := -(B 0 1)) (by rw [disc_eq]; exact hdisc)
  refine ⟨mulVecEquiv hL, B 1 0, hα, fun u => ?_⟩
  have hu' : (![u 0, u 1] : Fin 2 → ℝ) = u := by funext i; fin_cases i <;> simp
  have h2 := hid (u 0) (u 1)
  rw [hu'] at h2
  rw [det_krylov_two]
  show _ = B 1 0 * ((Matrix.mulVec L u) 0 ^ 2 + (Matrix.mulVec L u) 1 ^ 2)
  linarith [h2]

/-- **Obligations 4–5.**  A block of size `1` or `2` whose characteristic polynomial is
irreducible has one of the two shapes, up to an invertible change of coordinates and a
nonzero constant. -/
theorem exists_block_shape {d : ℕ} (hd : 0 < d) (hd2 : d ≤ 2) (B : Matrix (Fin d) (Fin d) ℝ)
    (hirr : Irreducible B.charpoly) :
    ∃ (k : BlockKind) (S : (Fin d → ℝ) ≃ₗ[ℝ] (Fin k.dim → ℝ)) (c : ℝ), c ≠ 0 ∧
      ∀ u, (krylov B u).det = c * k.factor (S u) := by
  interval_cases d
  · obtain ⟨S, c, hc, hid⟩ := block_shape_one B
    exact ⟨BlockKind.line, S, c, hc, hid⟩
  · obtain ⟨S, c, hc, hid⟩ := block_shape_two B (disc_neg_of_irreducible_charpoly B hirr)
    exact ⟨BlockKind.plane, S, c, hc, hid⟩

/-- The characteristic polynomial of an endomorphism killed by a monic irreducible of the
right degree *is* that polynomial. -/
theorem charpoly_eq_of_irreducible {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] [Nontrivial M] (φ : M →ₗ[ℝ] M) {f : ℝ[X]}
    (hirr : Irreducible f) (hmon : f.Monic) (hkill : aeval φ f = 0)
    (hdim : Module.finrank ℝ M = f.natDegree) :
    φ.charpoly = f := by
  have hmin : minpoly ℝ φ = f := minpoly_eq_of_irreducible φ hirr hmon hkill
  have hdvd : f ∣ φ.charpoly := hmin ▸ φ.minpoly_dvd_charpoly
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q ≠ 0 := fun hz => by
    rw [hz, mul_zero] at hq; exact φ.charpoly_monic.ne_zero hq
  have hnd : f.natDegree + q.natDegree = f.natDegree := by
    have h1 := Polynomial.natDegree_mul hmon.ne_zero hq0
    rw [← hq, φ.charpoly_natDegree, hdim] at h1
    exact h1.symm
  have hq1 : q.natDegree = 0 := by omega
  have hqu : IsUnit q := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hq0, hq1]
    rfl
  exact (Polynomial.eq_of_monic_of_associated hmon φ.charpoly_monic
    ⟨hqu.unit, by rw [IsUnit.unit_spec]; exact hq.symm⟩).symm

end BlockShape

/-! ### The assembly

Everything now composes.  With a cyclic vector `v` every `z` is `g(A) v`, so

    Δ(z) = det K_A(z) = det g(A) · det K_A(v),

and `det g(A) = ∏ᵢ det g(φᵢ)` because `g(A)` respects the primary decomposition.  On the
`i`-th block, in an adapted basis, `det g(φᵢ) · κᵢ = det K_{Bᵢ}(uᵢ)` with
`uᵢ` the block coordinates of `z` and `κᵢ = det K_{Bᵢ}(coords wᵢ) ≠ 0`, by the same
`krylov_mulVec_of_commute`.  Finally each `det K_{Bᵢ}(uᵢ)` is a constant times a line or
plane factor. -/

section Assemble

/-- **The real block factorization, given a factorization of `charpoly`.** -/
theorem nonempty_realBlockFactorization_aux {n N : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (ff : Fin N → ℝ[X]) (hN : 0 < N)
    (hirr : ∀ i, Irreducible (ff i)) (hmon : ∀ i, (ff i).Monic)
    (hdeg2 : ∀ i, (ff i).natDegree ≤ 2)
    (hpw : Pairwise fun i j => IsCoprime (ff i) (ff j)) (hprod : ∏ i, ff i = A.charpoly) :
    Nonempty (RealBlockFactorization A) := by
  classical
  set h := isInternal_ker A ff hN hpw hprod with hh
  have hfr : ∀ i, Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (aeval A (ff i))))
      = (ff i).natDegree := finrank_ker_eq_natDegree A ff hN hirr hmon hpw hprod
  have hdpos : ∀ i, 0 < (ff i).natDegree := fun i => natDegree_pos_of_irreducible (hirr i)
  haveI hnt : ∀ i, Nontrivial (LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))) := by
    intro i
    refine Submodule.nontrivial_iff_ne_bot.mpr
      (ker_aeval_ne_bot A (Polynomial.degree_pos_of_irreducible (hirr i)) ?_)
    rw [← hprod]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  -- an adapted basis on each primary component
  obtain ⟨b, -⟩ : ∃ _b : ∀ i, Module.Basis (Fin (ff i).natDegree) ℝ
      (LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))), True :=
    ⟨fun i => Module.finBasisOfFinrankEq ℝ _ (hfr i), trivial⟩
  have hAE : ∀ (i : Fin N) (ψ : (LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))) →ₗ[ℝ]
      (LinearMap.ker (Matrix.mulVecLin (aeval A (ff i))))),
      LinearMap.toMatrixAlgEquiv (b i) ψ = LinearMap.toMatrix (b i) (b i) ψ := fun _ _ => rfl
  -- each block's characteristic polynomial is the corresponding factor
  have hcharB : ∀ i, (LinearMap.toMatrixAlgEquiv (b i) (restrictKer A (ff i))).charpoly
      = ff i := by
    intro i
    rw [hAE i, LinearMap.charpoly_toMatrix]
    exact charpoly_eq_of_irreducible _ (hirr i) (hmon i) (aeval_restrictKer_self A (ff i))
      (hfr i)
  -- the block shapes
  choose kind Sh cst hcst hshape using fun i => exists_block_shape (hdpos i) (hdeg2 i)
    (LinearMap.toMatrixAlgEquiv (b i) (restrictKer A (ff i)))
    (by rw [hcharB i]; exact hirr i)
  -- the cyclic vector
  set w : ∀ i, LinearMap.ker (Matrix.mulVecLin (aeval A (ff i))) :=
    fun i => b i ⟨0, hdpos i⟩ with hwdef
  have hw0 : ∀ i, w i ≠ 0 := fun i => (b i).ne_zero _
  set v := internalEquiv
    (fun i : Fin N => LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))) h w with hv
  have hγ0 : (krylov A v).det ≠ 0 :=
    det_krylov_internalEquiv_ne_zero A ff hn hN hirr hmon hpw hprod w hw0
  -- the block constants
  obtain ⟨κ, hκdef⟩ : ∃ κ : Fin N → ℝ, ∀ i, κ i =
      (krylov (LinearMap.toMatrixAlgEquiv (b i) (restrictKer A (ff i)))
        ((b i).equivFun (w i))).det := ⟨_, fun _ => rfl⟩
  have hκ : ∀ i, κ i ≠ 0 := by
    intro i hzero
    rw [hκdef i, hshape i] at hzero
    rcases mul_eq_zero.mp hzero with hc | hf
    · exact hcst i hc
    · refine hw0 i ((b i).equivFun.injective ((Sh i).injective ?_))
      rw [(kind i).eq_zero_of_factor_eq_zero hf]
      simp
  -- the coordinate change
  obtain ⟨Tm, hTm⟩ : ∃ Tm : (Fin n → ℝ) ≃ₗ[ℝ] (∀ i : Fin N, Fin (kind i).dim → ℝ),
      ∀ z i, Tm z i = Sh i ((b i).equivFun ((internalEquiv
        (fun i : Fin N => LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))) h).symm z i)) :=
    ⟨(internalEquiv _ h).symm.trans
      (LinearEquiv.piCongrRight fun i => (b i).equivFun.trans (Sh i)), fun _ _ => rfl⟩
  refine ⟨{ N := N
            kind := kind
            T := Tm
            γ := (krylov A v).det * (∏ i, (cst i / κ i))
            hγ := mul_ne_zero hγ0 (Finset.prod_ne_zero_iff.mpr fun i _ =>
              div_ne_zero (hcst i) (hκ i))
            key := ?_ }⟩
  intro z
  -- write `z = g(A) v`
  set cc : Fin n → ℝ := Matrix.mulVec (krylov A v)⁻¹ z with hcc
  set g : ℝ[X] := ∑ j : Fin n, Polynomial.monomial (j : ℕ) (cc j) with hgdef
  have hzg : (aeval A g).mulVec v = z := by
    rw [hgdef, ← krylov_mulVec_eq_aeval, hcc, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hγ0), Matrix.one_mulVec]
  -- `g(A)` respects the decomposition, and restricts to `g(φᵢ)`
  have hstab : ∀ i, ∀ x ∈ LinearMap.ker (Matrix.mulVecLin (aeval A (ff i))),
      (Matrix.mulVecLin (aeval A g)) x
        ∈ LinearMap.ker (Matrix.mulVecLin (aeval A (ff i))) := by
    intro i x hx
    rw [mem_ker_aeval] at hx ⊢
    show (aeval A (ff i)).mulVec ((aeval A g).mulVec x) = 0
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm, map_mul, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_zero]
  have hrestrict : ∀ i, (Matrix.mulVecLin (aeval A g)).restrict (hstab i)
      = aeval (restrictKer A (ff i)) g := by
    intro i
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [LinearMap.coe_restrict_apply, coe_aeval_restrictKer]
    rfl
  -- the block coordinates of `z`
  have hcoord : ∀ i, (internalEquiv
      (fun i : Fin N => LinearMap.ker (Matrix.mulVecLin (aeval A (ff i)))) h).symm z i
      = (aeval (restrictKer A (ff i)) g) (w i) := by
    intro i
    have h1 := aeval_mulVec_internalEquiv A ff h g w
    rw [hzg] at h1
    rw [h1, LinearEquiv.symm_apply_apply]
  -- the per-block determinant identity
  have hblock : ∀ i, (krylov (LinearMap.toMatrixAlgEquiv (b i) (restrictKer A (ff i)))
        ((b i).equivFun ((aeval (restrictKer A (ff i)) g) (w i)))).det
      = LinearMap.det (aeval (restrictKer A (ff i)) g) * κ i := by
    intro i
    have hae : aeval (LinearMap.toMatrixAlgEquiv (b i) (restrictKer A (ff i))) g
        = LinearMap.toMatrix (b i) (b i) (aeval (restrictKer A (ff i)) g) := by
      rw [Polynomial.aeval_algHom_apply (LinearMap.toMatrixAlgEquiv (b i)), hAE i]
    have hrepr : (b i).equivFun ((aeval (restrictKer A (ff i)) g) (w i))
        = Matrix.mulVec (aeval (LinearMap.toMatrixAlgEquiv (b i) (restrictKer A (ff i))) g)
            ((b i).equivFun (w i)) := by
      rw [hae, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
      exact (LinearMap.toMatrix_mulVec_repr (b i) (b i) _ (w i)).symm
    rw [hrepr, krylov_mulVec_of_commute (commute_aeval _ g), Matrix.det_mul, hκdef i, hae,
      LinearMap.det_toMatrix]
  -- and hence the factor identity
  have hfac : ∀ i, cst i / κ i * (kind i).factor (Tm z i)
      = LinearMap.det (aeval (restrictKer A (ff i)) g) := by
    intro i
    have hx := (hshape i ((b i).equivFun ((aeval (restrictKer A (ff i)) g) (w i)))).symm
    rw [hblock i] at hx
    rw [hTm z i, hcoord i, div_mul_eq_mul_div, div_eq_iff (hκ i)]
    linear_combination hx
  calc (krylov A z).det
      = (aeval A g).det * (krylov A v).det := by rw [← hzg, det_krylov_aeval_mulVec']
    _ = (krylov A v).det * ∏ i, LinearMap.det (aeval (restrictKer A (ff i)) g) := by
        rw [mul_comm]
        congr 1
        rw [← LinearMap.det_toLin' (aeval A g),
          show Matrix.toLin' (aeval A g) = Matrix.mulVecLin (aeval A g) from rfl,
          det_eq_prod_det_restrict _ h _ hstab]
        exact Finset.prod_congr rfl fun i _ => by rw [hrestrict i]
    _ = (krylov A v).det * ∏ i, (cst i / κ i * (kind i).factor (Tm z i)) := by
        congr 1
        exact (Finset.prod_congr rfl fun i _ => hfac i).symm
    _ = (krylov A v).det * (∏ i, (cst i / κ i)) * ∏ i, (kind i).factor (Tm z i) := by
        rw [Finset.prod_mul_distrib, ← mul_assoc]

/-- **Obligation 3, complete.**  A real matrix with squarefree characteristic polynomial has a
real block factorization of its degeneracy polynomial `Δ(z) = det K_A(z)`.

This is the last structural input to `hΨ`; no assumption on the spectrum is made — real
eigenvalues give line blocks, conjugate pairs give plane blocks, and the two are produced
uniformly by the primary decomposition. -/
theorem nonempty_realBlockFactorization_of_squarefree {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsq : Squarefree A.charpoly) : Nonempty (RealBlockFactorization A) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨{ N := 0
             kind := fun i => i.elim0
             T := { toFun := fun _ i => i.elim0
                    map_add' := fun _ _ => funext fun i => i.elim0
                    map_smul' := fun _ _ => funext fun i => i.elim0
                    invFun := fun _ => 0
                    left_inv := fun _ => funext fun i => i.elim0
                    right_inv := fun _ => funext fun i => i.elim0 }
             γ := 1
             hγ := one_ne_zero
             key := fun z => by simp }⟩
  obtain ⟨S, hSmem, hSprod, hScop⟩ := exists_factorization A.charpoly_monic hsq
  have hN : 0 < S.card := by
    rw [Finset.card_pos]
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exfalso
      rw [Finset.prod_empty] at hSprod
      have h2 := A.charpoly_natDegree_eq_dim
      rw [← hSprod] at h2
      simp only [Polynomial.natDegree_one, Fintype.card_fin] at h2
      omega
    · exact hne
  have hmemi : ∀ i : Fin S.card, ((S.equivFin.symm i : ℝ[X])) ∈ S := fun i => (S.equivFin.symm i).2
  refine nonempty_realBlockFactorization_aux A hn
    (fun i : Fin S.card => ((S.equivFin.symm i : ℝ[X]))) hN
    (fun i => (hSmem _ (hmemi i)).1) (fun i => (hSmem _ (hmemi i)).2.1)
    (fun i => (hSmem _ (hmemi i)).2.2) ?_ ?_
  · intro i j hij
    refine hScop (hmemi i) (hmemi j) fun heq => hij ?_
    exact S.equivFin.symm.injective (Subtype.ext heq)
  · calc ∏ i : Fin S.card, ((S.equivFin.symm i : ℝ[X]))
        = ∏ x : S, ((x : ℝ[X])) := Fintype.prod_equiv S.equivFin.symm _ _ fun _ => rfl
      _ = ∏ f ∈ S, f := Finset.prod_coe_sort S id
      _ = A.charpoly := hSprod

end Assemble

end MPE
