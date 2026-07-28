import Mathlib
import Formal.Blocks

/-!
# The Krylov determinant in an eigenbasis

Appendix §7, Step 1.  If the columns of `P` are eigenvectors of `A` with eigenvalues `lam`,
then the Krylov matrix at `z = P w` factors as

    K(P w)  =  P · diag(w) · vandermonde(lam),

so that

    det K(P w)  =  det P · (∏ w) · ∏_{i<j} (lam j - lam i).

Everything here is over an arbitrary commutative ring and is inverse-free: the eigenbasis
enters only through `A * P = P * diagonal lam`.
-/

namespace MPE

open Matrix Finset

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The Krylov matrix of `A` at `z`: its `j`-th column is `Aʲ z`. -/
noncomputable def krylov (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (A ^ (j : ℕ) *ᵥ z) i

@[simp] lemma krylov_apply (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) (i j : Fin n) :
    krylov A z i j = (A ^ (j : ℕ) *ᵥ z) i := rfl

/-- `A * P = P * D` iterates to `Aʲ * P = P * Dʲ`. -/
lemma pow_mul_of_comm {A P D : Matrix (Fin n) (Fin n) R} (h : A * P = P * D) (j : ℕ) :
    A ^ j * P = P * D ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc A ^ (j+1) * P = A ^ j * (A * P) := by rw [pow_succ, Matrix.mul_assoc]
        _ = A ^ j * (P * D) := by rw [h]
        _ = (A ^ j * P) * D := by rw [Matrix.mul_assoc]
        _ = (P * D ^ j) * D := by rw [ih]
        _ = P * D ^ (j+1) := by rw [Matrix.mul_assoc, ← pow_succ]

/-- **The Krylov factorization.**  With `A P = P diag(lam)`, `K(P w) = P · diag w ·
vandermonde lam`. -/
theorem krylov_of_eigen {A P : Matrix (Fin n) (Fin n) R} {lam : Fin n → R}
    (hA : A * P = P * Matrix.diagonal lam) (w : Fin n → R) :
    krylov A (P *ᵥ w) = P * Matrix.diagonal w * Matrix.vandermonde lam := by
  ext i j
  have hpow : A ^ (j : ℕ) * P = P * Matrix.diagonal lam ^ (j : ℕ) := pow_mul_of_comm hA _
  have hd : Matrix.diagonal lam ^ (j : ℕ) = Matrix.diagonal (fun k => lam k ^ (j : ℕ)) :=
    Matrix.diagonal_pow _ _
  calc krylov A (P *ᵥ w) i j
      = (A ^ (j : ℕ) *ᵥ (P *ᵥ w)) i := rfl
    _ = ((A ^ (j : ℕ) * P) *ᵥ w) i := by rw [Matrix.mulVec_mulVec]
    _ = ((P * Matrix.diagonal (fun k => lam k ^ (j : ℕ))) *ᵥ w) i := by rw [hpow, hd]
    _ = ∑ k, P i k * (lam k ^ (j : ℕ) * w k) := by
        simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = (P * Matrix.diagonal w * Matrix.vandermonde lam) i j := by
        rw [Matrix.mul_assoc]
        have hdv : Matrix.diagonal w * Matrix.vandermonde lam
            = Matrix.of (fun k j : Fin n => w k * lam k ^ (j : ℕ)) := by
          ext k j
          rw [Matrix.diagonal_mul]
          simp [Matrix.vandermonde_apply]
        rw [hdv]
        simp only [Matrix.mul_apply, Matrix.of_apply]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- **The determinant form.**  `det K(P w) = det P · (∏ w) · ∏_{i<j}(lam j - lam i)`. -/
theorem det_krylov_of_eigen {A P : Matrix (Fin n) (Fin n) R} {lam : Fin n → R}
    (hA : A * P = P * Matrix.diagonal lam) (w : Fin n → R) :
    (krylov A (P *ᵥ w)).det
      = (P.det * ∏ i : Fin n, ∏ j ∈ Ioi i, (lam j - lam i)) * ∏ k, w k := by
  rw [krylov_of_eigen hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_vandermonde]
  ring

/-! ### Similarity transport

Changing basis by `P` transports the Krylov matrix by `P` on the left, so the determinant
picks up exactly `det P`.  This is what lets the block factorization be proved in whatever
basis is convenient — in particular in the basis adapted to the primary decomposition.
Checked numerically in `verify_crt.py`. -/

/-- Conjugation is a ring hom, so it commutes with powers. -/
lemma conj_pow {A P : Matrix (Fin n) (Fin n) R} (hP : IsUnit P.det) (j : ℕ) :
    (P⁻¹ * A * P) ^ j = P⁻¹ * A ^ j * P := by
  induction j with
  | zero => simp [Matrix.nonsing_inv_mul P hP]
  | succ j ih =>
      rw [pow_succ, ih, pow_succ]
      have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
      calc P⁻¹ * A ^ j * P * (P⁻¹ * A * P)
          = P⁻¹ * A ^ j * (P * P⁻¹) * A * P := by
            simp only [Matrix.mul_assoc]
        _ = P⁻¹ * (A ^ j * A) * P := by
            rw [hPP]; simp only [Matrix.mul_assoc, Matrix.mul_one]

/-- **Similarity transport.**  `K_A(Pw) = P · K_{P⁻¹AP}(w)`. -/
theorem krylov_similar {A P : Matrix (Fin n) (Fin n) R} (hP : IsUnit P.det)
    (w : Fin n → R) :
    krylov A (P.mulVec w) = P * krylov (P⁻¹ * A * P) w := by
  ext i j
  have hpow : A ^ (j : ℕ) * P = P * (P⁻¹ * A * P) ^ (j : ℕ) := by
    rw [conj_pow hP]
    have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
    calc A ^ (j : ℕ) * P = (P * P⁻¹) * A ^ (j : ℕ) * P := by rw [hPP, Matrix.one_mul]
      _ = P * (P⁻¹ * A ^ (j : ℕ) * P) := by simp only [Matrix.mul_assoc]
  calc krylov A (P.mulVec w) i j
      = ((A ^ (j : ℕ) * P).mulVec w) i := by
        rw [krylov_apply, Matrix.mulVec_mulVec]
    _ = ((P * (P⁻¹ * A * P) ^ (j : ℕ)).mulVec w) i := by rw [hpow]
    _ = (P * krylov (P⁻¹ * A * P) w) i j := by
        rw [← Matrix.mulVec_mulVec]
        simp only [Matrix.mul_apply, krylov_apply]
        rfl

/-- The determinant form of similarity transport. -/
theorem det_krylov_similar {A P : Matrix (Fin n) (Fin n) R} (hP : IsUnit P.det)
    (w : Fin n → R) :
    (krylov A (P.mulVec w)).det = P.det * (krylov (P⁻¹ * A * P) w).det := by
  rw [krylov_similar hP, Matrix.det_mul]

/-! ### Cyclic vectors

`A` is cyclic exactly when some `v` has `v, Av, …, A^{n-1}v` a basis, i.e. when `K_A(v)` is
invertible.  This is the hinge of the encoding chosen in the appendix (Remark 5): with a
cyclic vector, `det_krylov_similar` transports everything to the *companion matrix*, where
the Krylov matrix is literally a multiplication matrix and the block structure enters only
through the Chinese-remainder ring isomorphism. -/

/-- If the Krylov vectors span, the Krylov matrix is invertible. -/
theorem isUnit_det_krylov_of_span {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (hspan : Submodule.span ℝ (Set.range fun j : Fin N => (A ^ (j : ℕ)).mulVec v) = ⊤) :
    IsUnit (krylov A v).det := by
  classical
  -- the columns of `K_A(v)` are exactly those vectors, so `mulVecLin` is onto
  have hrange : LinearMap.range (krylov A v).mulVecLin = ⊤ := by
    rw [Matrix.range_mulVecLin]
    have htr : (krylov A v).col = fun j : Fin N => (A ^ (j : ℕ)).mulVec v := by
      funext j; rfl
    rw [htr]
    exact hspan
  have hsurj : Function.Surjective (krylov A v).mulVecLin :=
    LinearMap.range_eq_top.mp hrange
  have hinj : Function.Injective (krylov A v).mulVecLin :=
    (LinearMap.injective_iff_surjective).mpr hsurj
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine hw0 (hinj ?_)
  simpa using hw

/-! ### Blocks

A block is a line (carrying a linear factor) or a plane (carrying a positive definite
quadratic factor).  These are the two shapes produced by the real form of a matrix with
distinct eigenvalues: a real eigenvalue gives a line, a conjugate pair gives a plane. -/

/-- The two kinds of block in the factorization of the degeneracy polynomial. -/
inductive BlockKind
  | line
  | plane
  deriving DecidableEq

/-- The dimension of a block, *minus one*.

Writing `dim` as `dm + 1` rather than matching on the literals `1` and `2` is what lets
`MeasurableEquiv.piFinSuccAbove` peel one coordinate off a block with **no dependent-type
cast**: `Fin (kind i).dim` is then *syntactically* `Fin ((kind i).dm + 1)`, which is the shape
that lemma requires.  Without this the chart cover of `Formal/Annulus.lean` would need a
`finCongr` transport inside a `MeasurableEquiv`. -/
abbrev BlockKind.dm : BlockKind → ℕ
  | .line => 0
  | .plane => 1

/-- The dimension of a block.  `abbrev` so that `Fin b.dim` reduces during instance
search, which is what makes the numerals `0`, `1` elaborate below. -/
abbrev BlockKind.dim (b : BlockKind) : ℕ := b.dm + 1

/-- The factor a block contributes: `u` for a line, `‖u‖²` for a plane. -/
abbrev BlockKind.factor : (b : BlockKind) → (Fin b.dim → ℝ) → ℝ
  | .line, u => u 0
  | .plane, u => (u 0) ^ 2 + (u 1) ^ 2

lemma BlockKind.dim_pos (b : BlockKind) : 0 < b.dim := Nat.succ_pos _

lemma BlockKind.dim_le_two (b : BlockKind) : b.dim ≤ 2 := by
  cases b <;> simp [BlockKind.dim, BlockKind.dm]

/-- **A block is anticoncentrated**, uniformly in its kind.  This is the input to the
product estimate of `Formal/Blocks.lean`. -/
lemma BlockKind.anticonc (b : BlockKind) :
    ∀ v : ℝ, 0 ≤ v → (blockMeasure b.dim) {u | |b.factor u| ≤ v} ≤ ENNReal.ofReal v := by
  cases b with
  | line =>
      intro v hv
      exact anticonc_line v hv
  | plane =>
      intro v hv
      have hset : {u : Fin 2 → ℝ | |BlockKind.factor .plane u| ≤ v}
          = {u : Fin 2 → ℝ | (u 0) ^ 2 + (u 1) ^ 2 ≤ v} := by
        ext u
        simp only [Set.mem_setOf_eq, BlockKind.factor]
        rw [abs_of_nonneg (by positivity)]
      rw [hset]
      exact anticonc_plane v hv

/-- **A real block factorization of the degeneracy polynomial.**

`T` is a real linear change of coordinates carrying `ℝⁿ` onto a product of blocks, in which
`det K(z)` becomes a nonzero constant times a product of one factor per block, *each
depending on its own block only*.  This is exactly what the anticoncentration argument
consumes: the product structure feeds `Formal/Blocks.lean`, and the individual factors have
the derivative lower bounds the fibering argument needs. -/
structure RealBlockFactorization (A : Matrix (Fin n) (Fin n) ℝ) where
  /-- the number of blocks -/
  N : ℕ
  /-- the kind of each block -/
  kind : Fin N → BlockKind
  /-- the real change of coordinates -/
  T : (Fin n → ℝ) ≃ₗ[ℝ] (∀ i : Fin N, Fin (kind i).dim → ℝ)
  /-- the constant -/
  γ : ℝ
  hγ : γ ≠ 0
  /-- the factorization -/
  key : ∀ z, (krylov A z).det = γ * ∏ i, (kind i).factor (T z i)

/-! ### The real-spectrum case

When every eigenvalue is real the eigenbasis can be taken real, every block is a line, and
the change of coordinates is just `z ↦ P⁻¹ z`.  No conjugate pairing is needed. -/

/-- Coordinates on a product of one-dimensional blocks. -/
noncomputable def lineBlocksEquiv (m : ℕ) :
    (Fin m → ℝ) ≃ₗ[ℝ] (∀ i : Fin m, Fin (BlockKind.line).dim → ℝ) where
  toFun w := fun i _ => w i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := fun i => u i 0
  left_inv _ := rfl
  right_inv u := by
    funext i k
    induction k using Fin.cases with
    | zero => rfl
    | succ j => exact j.elim0

/-- `z ↦ P⁻¹ z` as a linear equivalence, for an invertible real matrix `P`. -/
noncomputable def invMulVecEquiv {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsUnit P.det) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  __ := Matrix.mulVecLin P⁻¹
  invFun w := P *ᵥ w
  left_inv z := by
    show P *ᵥ (P⁻¹ *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
  right_inv w := by
    show P⁻¹ *ᵥ (P *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec]

/-- **The real-spectrum block factorization.**  If `A` has a real eigenbasis with distinct
eigenvalues, then `det K(z) = γ ∏ (P⁻¹ z)ᵢ` with `γ ≠ 0`: every block is a line. -/
theorem nonempty_realBlockFactorization_of_realSpectrum
    {A P : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (hP : IsUnit P.det) (hlam : Function.Injective lam)
    (hA : A * P = P * Matrix.diagonal lam) :
    Nonempty (RealBlockFactorization A) := by
  refine ⟨{
    N := n
    kind := fun _ => BlockKind.line
    T := (invMulVecEquiv hP).trans (lineBlocksEquiv n)
    γ := P.det * ∏ i : Fin n, ∏ j ∈ Ioi i, (lam j - lam i)
    hγ := ?_
    key := ?_ }⟩
  · -- `det P ≠ 0` and the Vandermonde product is nonzero because `lam` is injective
    refine mul_ne_zero (isUnit_iff_ne_zero.mp hP) ?_
    · refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
      refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
      exact sub_ne_zero_of_ne (fun hc => hij (hlam hc.symm))
  · intro z
    have hz : P *ᵥ (P⁻¹ *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
    calc (krylov A z).det = (krylov A (P *ᵥ (P⁻¹ *ᵥ z))).det := by rw [hz]
      _ = (P.det * ∏ i : Fin n, ∏ j ∈ Ioi i, (lam j - lam i)) * ∏ k, (P⁻¹ *ᵥ z) k :=
          det_krylov_of_eigen hA _
      _ = _ := rfl

end MPE
