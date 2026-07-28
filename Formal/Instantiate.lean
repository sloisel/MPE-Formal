import Formal.Construction
import Formal.Algebra
import Formal.Cycle
import Formal.Leading
import Formal.Factor
import Formal.Main

/-!
# Discharging `hN`

The MPE construction for a polynomial map `f = Ax + q`, assembled, with the degree bound
`‖Ñ(y)‖ ≤ M‖y‖^(n+2)` **proved** rather than assumed.  The result is a `CycleData` term
whose `hN` field is a theorem.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace MPE
namespace Poly

open MvPolynomial Finset

variable {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
  (q : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℝ)

local notation "n" => m + 1

/-- The polynomial map `f(x) = Ax + q(x)`. -/
noncomputable def fmap : Fin n → MvPolynomial (Fin n) ℝ := fun i => lin A i + q i

/-- Its iterates `f^j`. -/
noncomputable def F (j : ℕ) : Fin n → MvPolynomial (Fin n) ℝ := iter (fmap A q) j

/-- The differences `u_j = f^{j+1} - f^j`. -/
noncomputable def u (j : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ := F A q (j + 1) i - F A q j i

/-- The matrix `U` whose `j`-th column is `u_j`. -/
noncomputable def Umat : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℝ) :=
  fun i j => u A q (j : ℕ) i

/-- `-u_n`, named so that `Pi` negation has a single syntactic form. -/
noncomputable def unegN : Fin n → MvPolynomial (Fin n) ℝ := -(fun i => u A q n i)

/-- `c̃ = adj(U)(-u_n)`, extended by `c̃_n := det U`. -/
noncomputable def cc (j : ℕ) : MvPolynomial (Fin n) ℝ :=
  if h : j < n then (Umat A q).adjugate.mulVec (unegN A q) ⟨j, h⟩
  else (Umat A q).det

/-- The cleared numerator `Ñ = ∑_{j≤n} c̃_j f^j`. -/
noncomputable def Nt (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ range (n + 1), cc A q j * F A q j i

/-- `g_j = f^j - A^j x`, the part of the iterate above the linear term. -/
noncomputable def gpart (j : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  F A q j i - lin (A ^ j) i

/-- The linear-part contribution `T = ∑_j c̃_j A^j x` to `Ñ`. -/
noncomputable def Tlin (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ range (n + 1), cc A q j * lin (A ^ j) i

variable {A q}

/-! ### Degree bounds for the pieces -/

lemma lowDeg_q_one (hq : ∀ i, LowDeg 2 (q i)) (i : Fin n) : LowDeg 1 (q i) :=
  (hq i).mono (by norm_num)

lemma lowDeg_fmap (hq : ∀ i, LowDeg 2 (q i)) (i : Fin n) : LowDeg 1 (fmap A q i) :=
  (lowDeg_lin A i).add (lowDeg_q_one hq i)

lemma lowDeg_F (hq : ∀ i, LowDeg 2 (q i)) (j : ℕ) (i : Fin n) : LowDeg 1 (F A q j i) :=
  lowDeg_iter (lowDeg_fmap hq) j i

lemma lowDeg_u (hq : ∀ i, LowDeg 2 (q i)) (j : ℕ) (i : Fin n) : LowDeg 1 (u A q j i) :=
  (lowDeg_F hq (j + 1) i).sub (lowDeg_F hq j i)

lemma lowDeg_Umat (hq : ∀ i, LowDeg 2 (q i)) (i j : Fin n) : LowDeg 1 (Umat A q i j) :=
  lowDeg_u hq _ _

/-- `c̃_j` has degree `≥ n`, for every `j ≤ n`: the adjugate contributes `n-1` and `u_n`
one more, while the determinant contributes `n` directly. -/
lemma lowDeg_cc (hq : ∀ i, LowDeg 2 (q i)) (j : ℕ) : LowDeg n (cc A q j) := by
  rw [cc]
  split
  · next h =>
      have hadj : ∀ a b, LowDeg m ((Umat A q).adjugate a b) :=
        fun a b => LowDeg.adjugate (lowDeg_Umat hq) a b
      have hun : ∀ i, LowDeg 1 (unegN A q i) := fun i => (lowDeg_u hq n i).neg
      have := LowDeg.mulVec (a := m) (b := 1) hadj hun ⟨j, h⟩
      simpa using this
  · exact LowDeg.det (lowDeg_Umat hq)

/-! ### The graded pieces feeding `LowDeg.Ntilde` -/

lemma lowDeg_gpart (hq : ∀ i, LowDeg 2 (q i)) (j : ℕ) (i : Fin n) : LowDeg 2 (gpart A q j i) :=
  lowDeg_iter_sub_lin hq (fun _ => rfl) j i

lemma Nt_eq (i : Fin n) :
    Nt A q i = Tlin A q i + ∑ j ∈ range (n + 1), cc A q j * gpart A q j i := by
  rw [Nt, Tlin, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gpart, mul_sub]
  ring

/-! ### The self-consistency relation, and the degree bound for `Ñ` -/

lemma lin_sub (M N : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    lin M i - lin N i = lin (M - N) i := by
  simp only [lin, ← Finset.sum_sub_distrib, Matrix.sub_apply, map_sub, sub_mul]

lemma lin_mul (M N : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ∑ k, C (M i k) * lin N k = lin (M * N) i := by
  simp only [lin, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    rw [← mul_assoc, ← map_mul]

/-- `c̃` restricted to `Fin n` is the adjugate applied to `-u_n`. -/
lemma cc_coe (k : Fin n) :
    cc A q (k : ℕ) = (Umat A q).adjugate.mulVec (unegN A q) k := by
  rw [cc, dif_pos k.isLt]

/-- **`∑_{j≤n} c̃_j u_j = 0`** for the actual construction: the polynomial form of
`U · adj U = D · I`. -/
theorem sum_cc_u (i : Fin n) : ∑ j ∈ range (n + 1), cc A q j * u A q j i = 0 := by
  have hsc := MPE.selfConsistency (Umat A q) (fun i => u A q n i)
  rw [show -(fun i => u A q n i) = unegN A q from rfl] at hsc
  have hcomp := congrFun hsc i
  rw [Finset.sum_range_succ]
  have h1 : ∑ j ∈ range n, cc A q j * u A q j i
      = (Umat A q).mulVec ((Umat A q).adjugate.mulVec (unegN A q)) i := by
    have hmv : (Umat A q).mulVec ((Umat A q).adjugate.mulVec (unegN A q)) i
        = ∑ k, Umat A q i k * (Umat A q).adjugate.mulVec (unegN A q) k := rfl
    rw [hmv, ← Fin.sum_univ_eq_sum_range (fun j => cc A q j * u A q j i) n]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Umat, cc_coe]; ring
  have h2 : cc A q n * u A q n i = (Umat A q).det * u A q n i := by
    rw [cc, dif_neg (lt_irrefl n)]
  rw [h1, h2]
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hcomp

/-- The self-consistency relation in the form `LowDeg.Ntilde` consumes. -/
theorem hcons_poly (i : Fin n) :
    ((A - 1).map (MvPolynomial.C (σ := Fin n))).mulVec (Tlin A q) i
      = -(∑ j ∈ range (n + 1), cc A q j * (gpart A q (j + 1) i - gpart A q j i)) := by
  have hu : ∀ j, u A q j i = lin ((A - 1) * A ^ j) i
      + (gpart A q (j + 1) i - gpart A q j i) := by
    intro j
    rw [u, gpart, gpart, pow_succ']
    have : lin (A * A ^ j) i - lin (A ^ j) i = lin ((A - 1) * A ^ j) i := by
      rw [lin_sub]; congr 1; rw [sub_mul, one_mul]
    rw [← this]; ring
  have hsum := sum_cc_u (A := A) (q := q) i
  simp only [hu, mul_add, Finset.sum_add_distrib] at hsum
  have hT : ((A - 1).map (MvPolynomial.C (σ := Fin n))).mulVec (Tlin A q) i
      = ∑ j ∈ range (n + 1), cc A q j * lin ((A - 1) * A ^ j) i := by
    have hmv : ((A - 1).map (MvPolynomial.C (σ := Fin n))).mulVec (Tlin A q) i
        = ∑ k, ((A - 1).map (MvPolynomial.C (σ := Fin n))) i k * Tlin A q k := rfl
    rw [hmv]
    simp only [Matrix.map_apply, Tlin, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hpull : (∑ x, C ((A - 1) i x) * (cc A q j * lin (A ^ j) x))
        = cc A q j * ∑ x, C ((A - 1) i x) * lin (A ^ j) x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hpull, lin_mul]
  rw [hT]
  exact eq_neg_of_add_eq_zero_left hsum

/-- **`hN`, proved.**  `Ñ` has no monomials below degree `n + 2`. -/
theorem lowDeg_Nt (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) (i : Fin n) :
    LowDeg (n + 2) (Nt A q i) :=
  LowDeg.Ntilde (k := n) (N := n + 1) hA (fun j => lowDeg_cc hq j)
    (fun j i => lowDeg_gpart hq j i) (fun i => hcons_poly i) (fun i => Nt_eq i) i

/-! ### The `CycleData` term

Everything is now in place to build a `CycleData` whose `hN` field is a **theorem**.
-/

variable (A q)

/-- The cleared denominator `σ̃ = ∑_{j≤n} c̃_j`. -/
noncomputable def sigtPoly : MvPolynomial (Fin n) ℝ := ∑ j ∈ range (n + 1), cc A q j

/-- The `ℓ¹` norm of the coefficients — the explicit constant in the degree bound. -/
noncomputable def coeffSum (P : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∑ d ∈ P.support, |MvPolynomial.coeff d P|

/-- A constant dominating every component's coefficient sum, and at least `1`. -/
noncomputable def NtBound : ℝ := 1 + ∑ i, coeffSum (Nt A q i)

variable {A q}

lemma coeffSum_nonneg (P : MvPolynomial (Fin n) ℝ) : 0 ≤ coeffSum P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma one_le_NtBound : (1 : ℝ) ≤ NtBound A q := by
  have : (0 : ℝ) ≤ ∑ i, coeffSum (Nt A q i) :=
    Finset.sum_nonneg fun i _ => coeffSum_nonneg _
  rw [NtBound]; linarith

lemma coeffSum_le_NtBound (i : Fin n) : coeffSum (Nt A q i) ≤ NtBound A q := by
  have h := Finset.single_le_sum (f := fun i => coeffSum (Nt A q i))
    (fun i _ => coeffSum_nonneg _) (Finset.mem_univ i)
  rw [NtBound]; linarith

/-- **The `CycleData` term for a polynomial map.**

`d`, `Ñ`, `σ̃`, `M` and `ρ₁` are the actual objects of the construction, and the field
`hN` — the paper's Lemma 4.1(iii) — is discharged by `lowDeg_Nt` together with the
degree-to-norm bridge.  It is a theorem here, not a hypothesis. -/
noncomputable def cycleData (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) :
    CycleData (Fin n → ℝ) where
  d := n
  Ntil := fun y i => MvPolynomial.eval y (Nt A q i)
  sigt := fun y => MvPolynomial.eval y (sigtPoly A q)
  M := NtBound A q
  ρ₁ := 1
  hd := Nat.succ_pos m
  hM := one_le_NtBound
  hρ₁ := one_pos
  hN := by
    intro y hy
    exact LowDeg.norm_eval_le (le_trans zero_le_one one_le_NtBound)
      (fun i => lowDeg_Nt hq hA i) (fun i => coeffSum_le_NtBound i) y hy

/-- The `hN` field really is the paper's bound, with an explicit constant. -/
theorem cycleData_hN (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1))
    (y : Fin n → ℝ) (hy : ‖y‖ ≤ 1) :
    ‖(cycleData hq hA).Ntil y‖ ≤ NtBound A q * ‖y‖ ^ (n + 2) :=
  (cycleData hq hA).hN y hy

/-! ### Leading parts of the construction

`U`'s leading part is the Krylov matrix `K`, and `c̃`'s leading part is `Δ·c⁰` — the last
structural fact the sharp bound needs.
-/

variable (A q)

/-- The Krylov matrix `K(x)`, the leading part of `U`. -/
noncomputable def Kmat : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) ℝ) :=
  fun i j => lin ((A - 1) * A ^ (j : ℕ)) i

/-- `Δ = det K`, the leading part of `D = det U`. -/
noncomputable def Delta : MvPolynomial (Fin n) ℝ := (Kmat A).det

variable {A q}

lemma isHomogeneous_lin (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (lin M i).IsHomogeneous 1 :=
  MvPolynomial.IsHomogeneous.sum _ _ _ fun _k _ => MvPolynomial.isHomogeneous_C_mul_X _ _

lemma homogeneousComponent_one_lin (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    homogeneousComponent 1 (lin M i) = lin M i :=
  MvPolynomial.homogeneousComponent_eq_self (isHomogeneous_lin M i)

/-- **`U`'s leading part is `K`.**  `u_j = lin((A-I)Aʲ) + (degree ≥ 2)`. -/
theorem homogeneousComponent_one_u (hq : ∀ i, LowDeg 2 (q i)) (j : ℕ) (i : Fin n) :
    homogeneousComponent 1 (u A q j i) = lin ((A - 1) * A ^ j) i := by
  have hsplit : u A q j i = lin ((A - 1) * A ^ j) i
      + (gpart A q (j + 1) i - gpart A q j i) := by
    rw [u, gpart, gpart, pow_succ']
    have hl : lin (A * A ^ j) i - lin (A ^ j) i = lin ((A - 1) * A ^ j) i := by
      rw [lin_sub]; congr 1; rw [sub_mul, one_mul]
    rw [← hl]; ring
  rw [hsplit, map_add, homogeneousComponent_one_lin]
  have hrem : LowDeg 2 (gpart A q (j + 1) i - gpart A q j i) :=
    (lowDeg_gpart hq (j + 1) i).sub (lowDeg_gpart hq j i)
  rw [homogeneousComponent_eq_zero_of_lowDeg hrem (by norm_num), add_zero]

lemma lin_neg (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : lin (-M) i = -lin M i := by
  simp only [lin, ← Finset.sum_neg_distrib, Matrix.neg_apply, map_neg, neg_mul]

lemma lin_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (Ms : ι → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    lin (∑ j ∈ s, c j • Ms j) i = ∑ j ∈ s, C (c j) * lin (Ms j) i := by
  simp only [lin, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The Krylov identity in polynomial form.** -/
theorem krylov_poly (i : Fin n) :
    ∑ j ∈ range n, C (A.charpoly.coeff j) * lin ((A - 1) * A ^ j) i
      = -lin ((A - 1) * A ^ n) i := by
  rw [← lin_sum_smul, ← lin_neg]
  congr 1
  exact MPE.krylov_matrix_combination A

/-- `K ·ᵥ c⁰ = -u_n`'s leading part. -/
theorem Kmat_mulVec_charpoly (i : Fin n) :
    (Kmat A).mulVec (fun j => C (A.charpoly.coeff (j : ℕ))) i = -lin ((A - 1) * A ^ n) i := by
  have hmv : (Kmat A).mulVec (fun j => C (A.charpoly.coeff (j : ℕ))) i
      = ∑ j : Fin n, Kmat A i j * C (A.charpoly.coeff (j : ℕ)) := rfl
  rw [hmv, ← krylov_poly (A := A) i,
    ← Fin.sum_univ_eq_sum_range (fun j => C (A.charpoly.coeff j) * lin ((A - 1) * A ^ j) i) n]
  exact Finset.sum_congr rfl fun j _ => by rw [Kmat]; ring

/-- **`c̃`'s leading part is `Δ·c⁰`.**

The degree-`n` component of `c̃_j` is `Δ` times the `j`-th characteristic-polynomial
coefficient.  This holds uniformly for `j ≤ n`, the case `j = n` reading `Δ·1 = Δ` since
the characteristic polynomial is monic.  It is the last structural input to the sharp
one-cycle bound. -/
theorem homogeneousComponent_cc (hq : ∀ i, LowDeg 2 (q i)) (j : ℕ) (hj : j ≤ n) :
    homogeneousComponent n (cc A q j) = Delta A * C (A.charpoly.coeff j) := by
  classical
  have hK : ∀ a b, homogeneousComponent 1 (Umat A q a b) = Kmat A a b := by
    intro a b
    rw [Umat, Kmat]
    exact homogeneousComponent_one_u hq _ _
  rcases lt_or_eq_of_le hj with hlt | rfl
  · -- j < n : the adjugate branch
    rw [cc, dif_pos hlt]
    have hmv : (Umat A q).adjugate.mulVec (unegN A q) ⟨j, hlt⟩
        = ∑ b, (Umat A q).adjugate ⟨j, hlt⟩ b * unegN A q b := rfl
    rw [hmv, map_sum]
    have hterm : ∀ b : Fin n,
        homogeneousComponent n ((Umat A q).adjugate ⟨j, hlt⟩ b * unegN A q b)
          = (Kmat A).adjugate ⟨j, hlt⟩ b * (-lin ((A - 1) * A ^ n) b) := by
      intro b
      have hadj : LowDeg m ((Umat A q).adjugate ⟨j, hlt⟩ b) :=
        LowDeg.adjugate (fun a c => lowDeg_Umat hq a c) _ _
      have huneg : LowDeg 1 (unegN A q b) := (lowDeg_u hq n b).neg
      have := homogeneousComponent_mul_of_lowDeg (a := m) (b := 1) hadj huneg
      rw [this]
      congr 1
      · have hKeq : (Matrix.of fun a b => homogeneousComponent 1 (Umat A q a b)) = Kmat A :=
          Matrix.ext fun a b' => hK a b'
        rw [homogeneousComponent_adjugate (fun a c => lowDeg_Umat hq a c), hKeq]
      · show homogeneousComponent 1 (-(u A q n b)) = _
        rw [map_neg, homogeneousComponent_one_u hq]
    simp only [hterm]
    have : ∑ b, (Kmat A).adjugate ⟨j, hlt⟩ b * (-lin ((A - 1) * A ^ n) b)
        = ((Kmat A).adjugate.mulVec (fun b => -lin ((A - 1) * A ^ n) b)) ⟨j, hlt⟩ := rfl
    rw [this]
    have hneg : (fun b => -lin ((A - 1) * A ^ n) b)
        = (Kmat A).mulVec (fun b => C (A.charpoly.coeff (b : ℕ))) := by
      funext b; rw [Kmat_mulVec_charpoly]
    rw [hneg, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec, Delta]
    simp [smul_eq_mul]
  · -- j = n : the determinant branch, and `c⁰_n = 1`
    rw [cc, dif_neg (lt_irrefl n)]
    have hdet := homogeneousComponent_det_of_lowDeg (M := Umat A q)
      (fun a b => lowDeg_Umat hq a b)
    rw [hdet]
    have hKeq : (Matrix.of fun a b => homogeneousComponent 1 (Umat A q a b)) = Kmat A :=
      Matrix.ext fun a b => hK a b
    rw [hKeq]
    have hmonic : A.charpoly.coeff n = 1 := by
      have h := A.charpoly_monic.coeff_natDegree
      have hdeg : A.charpoly.natDegree = n := by simp
      rwa [hdeg] at h
    rw [hmonic, Delta]
    simp

/-! ### Assembling the degree-`(n+2)` part of `Ñ` -/

variable (A q)

/-- `E_j`, the degree-`(n+1)` part of `c̃_j`. -/
noncomputable def Epart (j : ℕ) : MvPolynomial (Fin n) ℝ :=
  homogeneousComponent (n + 1) (cc A q j)

/-- `g_j⁽²⁾`, the quadratic part of `f^j`. -/
noncomputable def g2 (j : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  homogeneousComponent 2 (F A q j i)

/-- `T`, the linear-part contribution to the degree-`(n+2)` component. -/
noncomputable def Tsharp (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ range (n + 1), Epart A q j * lin (A ^ j) i

/-- `Φ = ∑_j c⁰_j g_j⁽²⁾`. -/
noncomputable def Phi (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ range (n + 1), C (A.charpoly.coeff j) * g2 A q j i

variable {A q}

lemma homogeneousComponent_one_F (hq : ∀ i, LowDeg 2 (q i)) (j : ℕ) (i : Fin n) :
    homogeneousComponent 1 (F A q j i) = lin (A ^ j) i := by
  have hsplit : F A q j i = lin (A ^ j) i + gpart A q j i := by
    rw [gpart]; ring
  rw [hsplit, map_add, homogeneousComponent_one_lin,
    homogeneousComponent_eq_zero_of_lowDeg (lowDeg_gpart hq j i) (by norm_num), add_zero]

/-- **`Ñ`'s degree-`(n+2)` component is `T + Δ·Φ`.**

Each term `c̃_j f^j` contributes at that order through the two splittings `n + 2` and
`(n+1) + 1`, giving `Δ·c⁰_j·g_j⁽²⁾` and `E_j·Aʲx` respectively. -/
theorem homogeneousComponent_Nt (hq : ∀ i, LowDeg 2 (q i)) (i : Fin n) :
    homogeneousComponent (n + 2) (Nt A q i)
      = Tsharp A q i + Delta A * Phi A q i := by
  classical
  rw [Nt, map_sum, Tsharp, Phi, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsucc := homogeneousComponent_mul_succ (a := n) (b := 1)
    (p := cc A q j) (q := F A q j i) (lowDeg_cc hq j) (lowDeg_F hq j i)
  rw [hsucc, homogeneousComponent_cc hq j hjle, homogeneousComponent_one_F hq j i,
    Epart, g2]
  ring

lemma homogeneousComponent_C_mul (k : ℕ) (a : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    homogeneousComponent k (C a * P) = C a * homogeneousComponent k P := by
  rw [← MvPolynomial.smul_eq_C_mul, ← MvPolynomial.smul_eq_C_mul, map_smul]

variable (A q)

/-- `q(Aʲx)`, the quadratic part contributed at step `j`. -/
noncomputable def qq (j : ℕ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  homogeneousComponent 2 (MvPolynomial.bind₁ (F A q j) (q i))

variable {A q}

/-- The recursion `g_{j+1}⁽²⁾ = A g_j⁽²⁾ + q(Aʲx)` at the level of quadratic parts. -/
theorem g2_rec (i : Fin n) (j : ℕ) :
    g2 A q (j + 1) i = ((A.map (MvPolynomial.C (σ := Fin n))).mulVec (g2 A q j)) i
      + qq A q j i := by
  have hF : F A q (j + 1) i
      = (∑ k, C (A i k) * F A q j k) + MvPolynomial.bind₁ (F A q j) (q i) := by
    show MvPolynomial.bind₁ (F A q j) (fmap A q i) = _
    rw [fmap, map_add, bind₁_lin]
  have hmv : ((A.map (MvPolynomial.C (σ := Fin n))).mulVec (g2 A q j)) i
      = ∑ k, C (A i k) * g2 A q j k := rfl
  rw [g2, hF, map_add, hmv, qq, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => homogeneousComponent_C_mul 2 (A i k) (F A q j k)

/-- The degree-`(n+2)` part of `∑_j c̃_j u_j = 0`. -/
theorem hcons_sharp (hq : ∀ i, LowDeg 2 (q i)) (i : Fin n) :
    (((A - 1).map (MvPolynomial.C (σ := Fin n))).mulVec (Tsharp A q)) i
      + Delta A * (∑ j ∈ range (n + 1),
          C (A.charpoly.coeff j) * (g2 A q (j + 1) i - g2 A q j i)) = 0 := by
  classical
  have hzero : homogeneousComponent (n + 2) (∑ j ∈ range (n + 1), cc A q j * u A q j i) = 0 := by
    rw [sum_cc_u]; simp
  rw [map_sum] at hzero
  have hterm : ∀ j ∈ range (n + 1),
      homogeneousComponent (n + 2) (cc A q j * u A q j i)
        = Epart A q j * lin ((A - 1) * A ^ j) i
          + Delta A * (C (A.charpoly.coeff j) * (g2 A q (j + 1) i - g2 A q j i)) := by
    intro j hj
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsucc := homogeneousComponent_mul_succ (a := n) (b := 1)
      (p := cc A q j) (q := u A q j i) (lowDeg_cc hq j) (lowDeg_u hq j i)
    have hu2 : homogeneousComponent 2 (u A q j i) = g2 A q (j + 1) i - g2 A q j i := by
      rw [u, map_sub, g2, g2]
    rw [hsucc, homogeneousComponent_cc hq j hjle, hu2,
      homogeneousComponent_one_u hq j i, Epart]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum] at hzero
  have hT : (((A - 1).map (MvPolynomial.C (σ := Fin n))).mulVec (Tsharp A q)) i
      = ∑ j ∈ range (n + 1), Epart A q j * lin ((A - 1) * A ^ j) i := by
    have hmv : (((A - 1).map (MvPolynomial.C (σ := Fin n))).mulVec (Tsharp A q)) i
        = ∑ k, ((A - 1).map (MvPolynomial.C (σ := Fin n))) i k * Tsharp A q k := rfl
    rw [hmv]
    simp only [Matrix.map_apply, Tsharp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hpull : (∑ x, C ((A - 1) i x) * (Epart A q j * lin (A ^ j) x))
        = Epart A q j * ∑ x, C ((A - 1) i x) * lin (A ^ j) x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hpull, lin_mul]
  rw [hT]
  exact hzero

/-- **Lemma 4.3 for the actual construction.**

`(A-I)·G = -Δ·W` where `G` is the degree-`(n+2)` component of `Ñ` and
`W = ∑_j c⁰_j q(Aʲx)`.  Since `A - I` is invertible this says `Δ ∣ G`, which is the
extra order the sharp one-cycle bound rests on. -/
theorem factorization_construction (hq : ∀ i, LowDeg 2 (q i)) :
    ((A - 1).map (MvPolynomial.C (σ := Fin n))).mulVec
        (fun i => homogeneousComponent (n + 2) (Nt A q i))
      = -(Delta A • ∑ j ∈ range (n + 1),
          (C (A.charpoly.coeff j) : MvPolynomial (Fin n) ℝ) • qq A q j) := by
  have hNt : (fun i => homogeneousComponent (n + 2) (Nt A q i))
      = Tsharp A q + Delta A • Phi A q := by
    funext i
    rw [homogeneousComponent_Nt hq i]
    simp [Phi, smul_eq_mul]
  rw [hNt]
  have hmap : (A.map (MvPolynomial.C (σ := Fin n)) - 1)
      = (A - 1).map (MvPolynomial.C (σ := Fin n)) := by
    rw [Matrix.map_sub]
    · congr 1
      ext a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    · exact map_sub _
  rw [← hmap]
  refine MPE.factorization (A.map (MvPolynomial.C (σ := Fin n))) (Delta A) (n + 1)
    (fun j => C (A.charpoly.coeff j)) (Tsharp A q) (Phi A q) (g2 A q) (qq A q)
    (fun j => funext fun i => g2_rec i j) ?_ ?_
  · funext i
    simp [Phi, smul_eq_mul]
  · funext i
    rw [hmap]
    have := hcons_sharp (A := A) (q := q) hq i
    simpa [smul_eq_mul, Pi.add_apply, Pi.smul_apply] using this

/-! ### `σ̃`'s leading part, and the remainders -/

/-- The characteristic-polynomial coefficients sum to `p_A(1)`. -/
lemma sum_charpoly_coeff : ∑ j ∈ range (n + 1), A.charpoly.coeff j = A.charpoly.eval 1 := by
  have hdeg : A.charpoly.natDegree = n := by simp
  rw [Polynomial.eval_eq_sum_range, hdeg]
  exact Finset.sum_congr rfl fun j _ => by simp

/-- **`σ̃`'s leading part is `p_A(1)·Δ`.**  Summing `c̃`'s leading parts over `j ≤ n`
collects the characteristic-polynomial coefficients, whose sum is `p_A(1)`. -/
theorem homogeneousComponent_sigt (hq : ∀ i, LowDeg 2 (q i)) :
    homogeneousComponent n (sigtPoly A q) = C (A.charpoly.eval 1) * Delta A := by
  rw [sigtPoly, map_sum]
  have hterm : ∀ j ∈ range (n + 1),
      homogeneousComponent n (cc A q j) = C (A.charpoly.coeff j) * Delta A := by
    intro j hj
    rw [homogeneousComponent_cc hq j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum, sum_charpoly_coeff]

/-- `σ̃` has degree `≥ n`. -/
lemma lowDeg_sigt (hq : ∀ i, LowDeg 2 (q i)) : LowDeg n (sigtPoly A q) :=
  LowDeg.sum fun j _ => lowDeg_cc hq j

/-- The remainder of `σ̃` above its leading part has degree `≥ n+1`. -/
theorem lowDeg_sigt_remainder (hq : ∀ i, LowDeg 2 (q i)) :
    LowDeg (n + 1) (sigtPoly A q - C (A.charpoly.eval 1) * Delta A) := by
  have h := lowDeg_sub_homogeneousComponent (lowDeg_sigt (A := A) (q := q) hq)
  rwa [homogeneousComponent_sigt hq] at h

/-- The remainder of `Ñ` above its leading part has degree `≥ n+3`. -/
theorem lowDeg_Nt_remainder (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) (i : Fin n) :
    LowDeg (n + 3) (Nt A q i - homogeneousComponent (n + 2) (Nt A q i)) := by
  have h := lowDeg_sub_homogeneousComponent (lowDeg_Nt (A := A) (q := q) hq hA i)
  simpa using h

/-! ### From polynomials to numbers -/

/-- A crude but explicit bound for a constant matrix acting on vectors. -/
lemma norm_mulVec_le (M : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    ‖M.mulVec w‖ ≤ (∑ i, ∑ j, |M i j|) * ‖w‖ := by
  have hw : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hsum : (0 : ℝ) ≤ ∑ i, ∑ j, |M i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  have hmv : M.mulVec w i = ∑ j, M i j * w j := rfl
  rw [Real.norm_eq_abs, hmv]
  calc |∑ j, M i j * w j| ≤ ∑ j, |M i j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * ‖w‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w j)
          (abs_nonneg _)
    _ = (∑ j, |M i j|) * ‖w‖ := by rw [← Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, |M i j|) * ‖w‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hw
        exact Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)

/-- Since `A - I` is invertible, it is bounded below: this is the constant `B` of the
sharp one-cycle bound. -/
theorem exists_inv_bound (hA : IsUnit (A - 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : Fin n → ℝ, ‖z‖ ≤ B * ‖(A - 1).mulVec z‖ := by
  classical
  obtain ⟨N', hN'⟩ := hA.exists_right_inv
  have hNM : N' * (A - 1) = 1 := mul_eq_one_comm.mp hN'
  refine ⟨∑ i, ∑ j, |N' i j|,
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _, fun z => ?_⟩
  have hz : z = N'.mulVec ((A - 1).mulVec z) := by
    rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
  calc ‖z‖ = ‖N'.mulVec ((A - 1).mulVec z)‖ := by rw [← hz]
    _ ≤ (∑ i, ∑ j, |N' i j|) * ‖(A - 1).mulVec z‖ := norm_mulVec_le N' _

/-- `p_A(1) ≠ 0`, from the standing assumption that `A - I` is invertible. -/
theorem charpoly_eval_one_ne_zero (hA : IsUnit (A - 1)) : A.charpoly.eval 1 ≠ 0 := by
  rw [Matrix.eval_charpoly]
  have hscal : (Matrix.scalar (Fin n)) (1 : ℝ) - A = -(A - 1) := by
    have h1 : (Matrix.scalar (Fin n)) (1 : ℝ) = 1 := by simp
    rw [h1, neg_sub]
  rw [hscal, Matrix.det_neg]
  have hdet : (A - 1).det ≠ 0 := by
    intro h
    exact (Matrix.isUnit_iff_isUnit_det _ |>.mp hA).ne_zero h
  simpa using hdet

/-- Evaluation commutes with the action of a constant matrix. -/
lemma eval_map_mulVec (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → MvPolynomial (Fin n) ℝ) (y : Fin n → ℝ) (i : Fin n) :
    MvPolynomial.eval y ((M.map (MvPolynomial.C (σ := Fin n))).mulVec v i)
      = (M.mulVec (fun j => MvPolynomial.eval y (v j))) i := by
  have h1 : (M.map (MvPolynomial.C (σ := Fin n))).mulVec v i
      = ∑ j, C (M i j) * v j := rfl
  have h2 : (M.mulVec (fun j => MvPolynomial.eval y (v j))) i
      = ∑ j, M i j * MvPolynomial.eval y (v j) := rfl
  rw [h1, h2, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, MvPolynomial.eval_C]

/-! ### The sharp estimate -/

variable (A q)

/-- `W = ∑_j c⁰_j q(Aʲx)`, the quotient in the factorisation. -/
noncomputable def Wpoly (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ range (n + 1), C (A.charpoly.coeff j) * qq A q j i

variable {A q}

lemma lowDeg_Wpoly (i : Fin n) : LowDeg 2 (Wpoly A q i) :=
  LowDeg.sum fun j _ => by
    have := (lowDeg_zero (C (A.charpoly.coeff j))).mul
      (lowDeg_homogeneousComponent 2 (MvPolynomial.bind₁ (F A q j) (q i)))
    simpa [qq] using this

/-- **The sharp one-cycle estimate for the construction.**

`‖Ñ(y)‖ ≤ C₁|σ̃(y)|‖y‖² + C₂‖y‖^{n+3}`.  Dividing by `|σ̃(y)|` this is exactly
`‖S(y)‖ ≤ C₁‖y‖² + C₂‖y‖³/τ(y)`, the sharp bound of Lemma 4.4(iii): the first term is the
quadratic accuracy of a safe cycle, the second the weakened pole. -/
theorem sharp_estimate (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ y : Fin n → ℝ, ‖y‖ ≤ 1 →
        ‖fun i => MvPolynomial.eval y (Nt A q i)‖
          ≤ C₁ * |MvPolynomial.eval y (sigtPoly A q)| * ‖y‖ ^ 2
            + C₂ * ‖y‖ ^ (n + 3) := by
  classical
  obtain ⟨B, hB0, hB⟩ := exists_inv_bound (A := A) hA
  set pA1 := A.charpoly.eval 1 with hpA1
  have hpA1ne : pA1 ≠ 0 := charpoly_eval_one_ne_zero (A := A) hA
  -- constants for the three degree bounds
  set CW := 1 + ∑ i, coeffSum (Wpoly A q i) with hCW
  set CR := 1 + ∑ i, coeffSum (Nt A q i - homogeneousComponent (n + 2) (Nt A q i)) with hCR
  set CS := 1 + coeffSum (sigtPoly A q - C pA1 * Delta A) with hCS
  have hCW0 : (0:ℝ) < CW := by
    have : (0:ℝ) ≤ ∑ i, coeffSum (Wpoly A q i) :=
      Finset.sum_nonneg fun i _ => coeffSum_nonneg _
    rw [hCW]; linarith
  have hCR0 : (0:ℝ) < CR := by
    have : (0:ℝ) ≤ ∑ i, coeffSum (Nt A q i - homogeneousComponent (n + 2) (Nt A q i)) :=
      Finset.sum_nonneg fun i _ => coeffSum_nonneg _
    rw [hCR]; linarith
  have hCS0 : (0:ℝ) < CS := by
    have := coeffSum_nonneg (sigtPoly A q - C pA1 * Delta A)
    rw [hCS]; linarith
  refine ⟨B * CW / |pA1| + 1, B * CW * CS / |pA1| + CR, by positivity, by positivity, ?_⟩
  intro y hy
  have hy0 : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
  have hpabs : (0:ℝ) < |pA1| := abs_pos.mpr hpA1ne
  -- the leading part and the remainder of Ñ
  set G : Fin n → ℝ := fun i => MvPolynomial.eval y (homogeneousComponent (n + 2) (Nt A q i))
    with hG
  set Rm : Fin n → ℝ := fun i =>
    MvPolynomial.eval y (Nt A q i - homogeneousComponent (n + 2) (Nt A q i)) with hRm
  set W : Fin n → ℝ := fun i => MvPolynomial.eval y (Wpoly A q i) with hW
  set Dy : ℝ := MvPolynomial.eval y (Delta A) with hDy
  -- the factorisation, evaluated
  have hfac : (A - 1).mulVec G = -(Dy • W) := by
    funext i
    have h := congrFun (factorization_construction (A := A) (q := q) hq) i
    rw [← eval_map_mulVec (A - 1) (fun i => homogeneousComponent (n + 2) (Nt A q i)) y i]
    rw [h]
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, map_neg, map_mul, map_sum, 
      hW, hDy, Wpoly, Pi.smul_apply, smul_eq_mul]
    simp [Finset.sum_apply, map_sum, map_mul]
  -- bound each piece
  have hWc : ∀ i : Fin n, coeffSum (Wpoly A q i) ≤ CW := by
    intro i
    have hle := Finset.single_le_sum (f := fun i => coeffSum (Wpoly A q i))
      (fun i _ => coeffSum_nonneg _) (Finset.mem_univ i)
    rw [hCW]
    linarith
  have hRc : ∀ i : Fin n,
      coeffSum (Nt A q i - homogeneousComponent (n + 2) (Nt A q i)) ≤ CR := by
    intro i
    have hle := Finset.single_le_sum
      (f := fun i => coeffSum (Nt A q i - homogeneousComponent (n + 2) (Nt A q i)))
      (fun i _ => coeffSum_nonneg _) (Finset.mem_univ i)
    rw [hCR]
    linarith
  have hWb : ‖W‖ ≤ CW * ‖y‖ ^ 2 :=
    LowDeg.norm_eval_le (le_of_lt hCW0) (fun i => lowDeg_Wpoly i) hWc y hy
  have hRb : ‖Rm‖ ≤ CR * ‖y‖ ^ (n + 3) :=
    LowDeg.norm_eval_le (le_of_lt hCR0) (fun i => lowDeg_Nt_remainder hq hA i) hRc y hy
  have hGb : ‖G‖ ≤ (B * ‖W‖) * |Dy| := norm_G_le_of_factorization hfac hB
  -- σ̃'s leading part controls Δ
  have hSb : |MvPolynomial.eval y (sigtPoly A q - C pA1 * Delta A)| ≤ CS * ‖y‖ ^ (n + 1) := by
    have hbase := (lowDeg_sigt_remainder (A := A) (q := q) hq).abs_eval_le y hy
    refine hbase.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    show coeffSum (sigtPoly A q - C pA1 * Delta A) ≤ CS
    have := coeffSum_nonneg (sigtPoly A q - C pA1 * Delta A)
    rw [hCS]
    linarith
  have hDb : |Dy| * |pA1| ≤ |MvPolynomial.eval y (sigtPoly A q)| + CS * ‖y‖ ^ (n + 1) := by
    have hexp : MvPolynomial.eval y (sigtPoly A q)
        = pA1 * Dy + MvPolynomial.eval y (sigtPoly A q - C pA1 * Delta A) := by
      simp [hDy, map_sub, map_mul, MvPolynomial.eval_C]
    have habs : |pA1 * Dy| ≤ |MvPolynomial.eval y (sigtPoly A q)|
        + |MvPolynomial.eval y (sigtPoly A q - C pA1 * Delta A)| := by
      calc |pA1 * Dy|
          = |MvPolynomial.eval y (sigtPoly A q)
              - MvPolynomial.eval y (sigtPoly A q - C pA1 * Delta A)| := by
            rw [hexp]; ring_nf
        _ ≤ _ := abs_sub _ _
    rw [abs_mul, mul_comm] at habs
    linarith
  -- assemble
  have hsplit : (fun i => MvPolynomial.eval y (Nt A q i)) = G + Rm := by
    funext i; simp [hG, hRm, map_sub]
  rw [hsplit]
  have htri : ‖G + Rm‖ ≤ ‖G‖ + ‖Rm‖ := norm_add_le _ _
  have hWnn : (0:ℝ) ≤ ‖W‖ := norm_nonneg W
  have hDnn : (0:ℝ) ≤ |Dy| := abs_nonneg _
  have hkey : ‖G‖ ≤ (B * CW / |pA1|) * |MvPolynomial.eval y (sigtPoly A q)| * ‖y‖ ^ 2
      + (B * CW * CS / |pA1|) * ‖y‖ ^ (n + 3) := by
    have h1 : ‖G‖ ≤ (B * (CW * ‖y‖ ^ 2)) * |Dy| := by
      refine hGb.trans (mul_le_mul_of_nonneg_right ?_ hDnn)
      exact mul_le_mul_of_nonneg_left hWb hB0
    have h2 : |Dy| ≤ (|MvPolynomial.eval y (sigtPoly A q)| + CS * ‖y‖ ^ (n + 1)) / |pA1| := by
      rw [le_div_iff₀ hpabs]; exact hDb
    have h3 : (B * (CW * ‖y‖ ^ 2)) * |Dy|
        ≤ (B * (CW * ‖y‖ ^ 2)) *
            ((|MvPolynomial.eval y (sigtPoly A q)| + CS * ‖y‖ ^ (n + 1)) / |pA1|) := by
      refine mul_le_mul_of_nonneg_left h2 (by positivity)
    have hpow : ‖y‖ ^ 2 * ‖y‖ ^ (n + 1) = ‖y‖ ^ (n + 3) := by
      rw [← pow_add]
      congr 1
      omega
    have heq : (B * (CW * ‖y‖ ^ 2)) *
        ((|MvPolynomial.eval y (sigtPoly A q)| + CS * ‖y‖ ^ (n + 1)) / |pA1|)
        = (B * CW / |pA1|) * |MvPolynomial.eval y (sigtPoly A q)| * ‖y‖ ^ 2
          + (B * CW * CS / |pA1|) * ‖y‖ ^ (n + 3) := by
      rw [← hpow]
      field_simp
    exact h1.trans (h3.trans (le_of_eq heq))
  nlinarith [htri, hkey, hRb, pow_nonneg hy0 (n + 3),
    abs_nonneg (MvPolynomial.eval y (sigtPoly A q)), sq_nonneg ‖y‖]

/-- **The `SharpBound` term.**

The field `bound` — the paper's Lemma 4.4(iii) — is discharged by `sharp_estimate`, divided
through by `|σ̃(y)|`.  Like `hN`, it is a theorem here, not a hypothesis. -/
theorem nonempty_sharpBound (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) :
    Nonempty (SharpBound (cycleData hq hA)) := by
  classical
  obtain ⟨C₁, C₂, hC₁, hC₂, hbd⟩ := sharp_estimate hq hA
  refine ⟨{ C₁ := C₁, C₂ := C₂, hC₁ := hC₁, hC₂ := hC₂, bound := ?_ }⟩
  intro y hy0 hy1 hσ
  have hyn : (0:ℝ) < ‖y‖ ^ (n : ℕ) := pow_pos hy0 _
  have hσabs : (0:ℝ) < |(cycleData hq hA).sigt y| := abs_pos.mpr hσ
  -- the estimate, and the shapes of `S` and `τ`
  have hest := hbd y hy1
  have hNt : ‖(cycleData hq hA).Ntil y‖ = ‖fun i => MvPolynomial.eval y (Nt A q i)‖ := rfl
  have hsig : (cycleData hq hA).sigt y = MvPolynomial.eval y (sigtPoly A q) := rfl
  have hS : ‖(cycleData hq hA).S y‖
      = ‖(cycleData hq hA).Ntil y‖ / |(cycleData hq hA).sigt y| := by
    rw [CycleData.S, norm_smul, norm_inv, Real.norm_eq_abs]; ring
  have hτ : (cycleData hq hA).τ y = |(cycleData hq hA).sigt y| / ‖y‖ ^ (n : ℕ) := rfl
  have hτpos : 0 < (cycleData hq hA).τ y := by rw [hτ]; positivity
  rw [hS, hτ]
  rw [div_le_iff₀ hσabs]
  -- C₂‖y‖³ / (|σ|/‖y‖ⁿ) = C₂‖y‖^{n+3} / |σ|
  have hpow : ‖y‖ ^ (2:ℕ) * ‖y‖ ^ (n : ℕ) * ‖y‖ = ‖y‖ ^ (n + 3) := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hrhs : (C₁ * ‖y‖ ^ 2
        + C₂ * ‖y‖ ^ 3 / (|(cycleData hq hA).sigt y| / ‖y‖ ^ (n : ℕ)))
        * |(cycleData hq hA).sigt y|
      = C₁ * |(cycleData hq hA).sigt y| * ‖y‖ ^ 2 + C₂ * ‖y‖ ^ (n + 3) := by
    field_simp
    rw [← hpow]
    ring
  rw [hrhs, hNt, hsig]
  exact hest

/-- **Everything but `hΨ`.**

For a polynomial map `f = Ax + q` with `q` of degree `≥ 2` and `A - I` invertible — the
paper's standing assumptions — *both* structural hypotheses of Theorem 4.9 are theorems:

* the `CycleData` exists, with `hN` (Lemma 4.1(iii)) proved;
* it carries a `SharpBound`, with `bound` (Lemma 4.4(iii)) proved.

The only remaining input to `MPE.dither_sharp` is the per-cycle margin probability `hΨ`,
which needs Brudnyi–Ganzburg or the anticoncentration lemma. -/
theorem structural_hypotheses_discharged
    (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) :
    ∃ C : CycleData (Fin n → ℝ), Nonempty (SharpBound C) :=
  ⟨cycleData hq hA, nonempty_sharpBound hq hA⟩

end Poly
end MPE
