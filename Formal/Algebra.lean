import Mathlib

/-!
# The algebraic core: Cayley–Hamilton and the adjugate

Both `CycleData.hN` (the paper's Lemma 4.1(iii)) and the factorisation `G = Δ·N⁽²⁾`
(Lemma 4.3) rest on two identities:

* **Cayley–Hamilton**, in the form `K(x)c⁰ = -(A-I)Aⁿx`, which is what makes the leading
  term of `Ñ` vanish;
* **`U · adj U = D · I`**, which is the self-consistency relation `∑_j c̃_j u_j = 0` that
  the proof of Lemma 4.3 extracts the degree-(n+2) part of.

These are proved here from mathlib, with no hypotheses.
-/

namespace MPE

open Matrix Polynomial Finset

variable {n : ℕ}

/-- **Cayley–Hamilton, in the paper's form.**  The characteristic-polynomial coefficients
express `Aⁿ` as a combination of the lower powers:
`∑_{j<n} c⁰_j Aʲ = -Aⁿ`, where `c⁰_j` are the coefficients of `p_A`. -/
theorem charpoly_sum_eq_neg_pow (A : Matrix (Fin n) (Fin n) ℝ) :
    ∑ j ∈ range n, A.charpoly.coeff j • A ^ j = -(A ^ n) := by
  have hCH : (aeval A) A.charpoly = 0 := A.aeval_self_charpoly
  have hdeg : A.charpoly.natDegree = n := by
    simp
  have hlead : A.charpoly.coeff n = 1 := by
    have h := A.charpoly_monic.coeff_natDegree
    rwa [hdeg] at h
  rw [aeval_eq_sum_range, hdeg, Finset.sum_range_succ, hlead, one_smul] at hCH
  exact eq_neg_of_add_eq_zero_left hCH

/-- The Krylov identity at the level of matrices. -/
theorem krylov_matrix_combination (A : Matrix (Fin n) (Fin n) ℝ) :
    ∑ j ∈ range n, A.charpoly.coeff j • ((A - 1) * A ^ j) = -((A - 1) * A ^ n) := by
  calc ∑ j ∈ range n, A.charpoly.coeff j • ((A - 1) * A ^ j)
      = (A - 1) * ∑ j ∈ range n, A.charpoly.coeff j • A ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
    _ = (A - 1) * (-(A ^ n)) := by rw [charpoly_sum_eq_neg_pow]
    _ = -((A - 1) * A ^ n) := by rw [mul_neg]

/-- **The Krylov identity `K(x)c⁰ = -(A-I)Aⁿx`.**

The columns of `K(x)` are `(A-I)Aʲx`; combining them with the characteristic-polynomial
coefficients annihilates everything except `-(A-I)Aⁿx`.  This is the cancellation that
makes the degree-`(n+1)` part of `Ñ` vanish, and hence the source of the extra order in
Lemma 4.1(iii). -/
theorem krylov_charpoly_combination (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ∑ j ∈ range n, A.charpoly.coeff j • (((A - 1) * A ^ j).mulVec x)
      = -(((A - 1) * A ^ n).mulVec x) := by
  have hmat := krylov_matrix_combination A
  calc ∑ j ∈ range n, A.charpoly.coeff j • (((A - 1) * A ^ j).mulVec x)
      = (∑ j ∈ range n, A.charpoly.coeff j • ((A - 1) * A ^ j)).mulVec x := by
        rw [Matrix.sum_mulVec]
        exact Finset.sum_congr rfl fun j _ => (Matrix.smul_mulVec _ _ _).symm
    _ = (-((A - 1) * A ^ n)).mulVec x := by rw [hmat]
    _ = -(((A - 1) * A ^ n).mulVec x) := by simp [Matrix.neg_mulVec]

/-- **The self-consistency relation `∑_{j≤n} c̃_j u_j = 0`.**

With `c̃ = adj(U)(-u_n)` and `c̃_n := D = det U`, the combination of the differences with
the computed coefficients vanishes identically.  This is the identity whose degree-(n+2)
part gives the factorisation `G = Δ·N⁽²⁾`; it is exactly `U · adj U = D · I`. -/
theorem selfConsistency {R : Type*} [CommRing R]
    (U : Matrix (Fin n) (Fin n) R) (un : Fin n → R) :
    U.mulVec (U.adjugate.mulVec (-un)) + U.det • un = 0 := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  simp

end MPE
