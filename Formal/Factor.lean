import Formal.Algebra

/-!
# Lemma 4.3: the numerator is divisible by the degeneracy

The paper extracts the degree-`(n+2)` part of the self-consistency relation
`∑_{j≤n} c̃_j u_j = 0` and of `Ñ = ∑_{j≤n} c̃_j f^j`, and concludes

    G = Δ · N⁽²⁾,     N⁽²⁾ = -(A-I)⁻¹ ∑_j c⁰_j q(Aʲv).

Here that extraction is carried out.  The graded pieces are the inputs:

* `E j` is the degree-`(n+1)` part of `c̃_j` (its degree-`n` part being `Δ·c⁰_j`);
* `g j` is the quadratic part of `f^j`, satisfying the recursion `g_{j+1} = A g_j + q∘Aʲ`;
* `hcons` is the degree-`(n+2)` part of `∑_j c̃_j u_j = 0`, whose source identity
  `U · adj U = D · I` is `MPE.selfConsistency`.

The conclusion is stated **without** `(A-I)⁻¹`, as

    (A - I) · G = -Δ · ∑_j c⁰_j q(Aʲv),

which is equivalent since `A - I` is invertible, and is what yields `‖G‖ ≤ C_N|Δ|`.
-/

namespace MPE

open Matrix Finset

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The paper's `Ψ = (A-I)Φ + ∑_j c⁰_j q(Aʲv)`, from the recursion for the quadratic parts
of the iterates.  This is the step that makes the inverse of `A - I` disappear.

Stated over an arbitrary commutative ring, so that it applies both to the real setting and
to `MvPolynomial`, where the graded pieces live. -/
lemma sum_diff_eq (A : Matrix (Fin n) (Fin n) R) (N : ℕ) (c : ℕ → R)
    (g q : ℕ → (Fin n → R)) (hrec : ∀ j, g (j + 1) = A.mulVec (g j) + q j) :
    ∑ j ∈ range N, c j • (g (j + 1) - g j)
      = (A - 1).mulVec (∑ j ∈ range N, c j • g j) + ∑ j ∈ range N, c j • q j := by
  have hstep : ∀ j, g (j + 1) - g j = (A - 1).mulVec (g j) + q j := by
    intro j
    rw [hrec j, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  calc ∑ j ∈ range N, c j • (g (j + 1) - g j)
      = ∑ j ∈ range N, (c j • (A - 1).mulVec (g j) + c j • q j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hstep j, smul_add]
    _ = (∑ j ∈ range N, c j • (A - 1).mulVec (g j)) + ∑ j ∈ range N, c j • q j :=
        Finset.sum_add_distrib
    _ = (A - 1).mulVec (∑ j ∈ range N, c j • g j) + ∑ j ∈ range N, c j • q j := by
        congr 1
        rw [Matrix.mulVec_sum]
        exact Finset.sum_congr rfl fun j _ => (Matrix.mulVec_smul _ _ _).symm

/-- **Lemma 4.3, the extraction.**

If `hcons` is the degree-`(n+2)` part of the self-consistency relation, and `G` is the
degree-`(n+2)` part of `Ñ`, then `(A-I)G = -Δ ∑_j c⁰_j q(Aʲv)`.

Since `A - I` is invertible this says exactly `G = Δ·N⁽²⁾`: the degeneracy `Δ` divides the
numerator.  It is what gives the extra power of the radius in the sharp one-cycle bound,
and hence the improved exponent of Theorem 4.9. -/
theorem factorization
    (A : Matrix (Fin n) (Fin n) R) (Δ : R) (N : ℕ)
    (c : ℕ → R) (T Φ : Fin n → R) (g q : ℕ → (Fin n → R))
    (hrec : ∀ j, g (j + 1) = A.mulVec (g j) + q j)
    (hΦ : Φ = ∑ j ∈ range N, c j • g j)
    (hcons : (A - 1).mulVec T + Δ • (∑ j ∈ range N, c j • (g (j + 1) - g j)) = 0) :
    (A - 1).mulVec (T + Δ • Φ) = -(Δ • ∑ j ∈ range N, c j • q j) := by
  have hΨ : ∑ j ∈ range N, c j • (g (j + 1) - g j)
      = (A - 1).mulVec Φ + ∑ j ∈ range N, c j • q j := by
    rw [hΦ]; exact sum_diff_eq A N c g q hrec
  rw [hΨ] at hcons
  have hexp : (A - 1).mulVec (T + Δ • Φ)
      = (A - 1).mulVec T + Δ • (A - 1).mulVec Φ := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [hexp]
  have : (A - 1).mulVec T
      = -(Δ • ((A - 1).mulVec Φ + ∑ j ∈ range N, c j • q j)) :=
    eq_neg_of_add_eq_zero_left hcons
  rw [this, smul_add]
  abel

/-- **The bound the sharp analysis consumes.**

From the factorisation, `‖G‖ ≤ ‖(A-I)⁻¹‖ · ‖∑_j c⁰_j q(Aʲv)‖ · |Δ|`.  This is the
inequality `‖G(v)‖ ≤ C_N|Δ(v)|` used in Lemma 4.4(iii) — the *only* consequence of Lemma 4.3
that the sharp theorem actually needs. -/
theorem norm_G_le_of_factorization
    {A : Matrix (Fin n) (Fin n) ℝ} {Δ : ℝ} {G W : Fin n → ℝ} {B : ℝ}
    (hfac : (A - 1).mulVec G = -(Δ • W))
    (hinv : ∀ z : Fin n → ℝ, ‖z‖ ≤ B * ‖(A - 1).mulVec z‖) :
    ‖G‖ ≤ (B * ‖W‖) * |Δ| := by
  calc ‖G‖ ≤ B * ‖(A - 1).mulVec G‖ := hinv G
    _ = B * ‖(-(Δ • W))‖ := by rw [hfac]
    _ = B * (|Δ| * ‖W‖) := by rw [norm_neg, norm_smul, Real.norm_eq_abs]
    _ = (B * ‖W‖) * |Δ| := by ring

end MPE
