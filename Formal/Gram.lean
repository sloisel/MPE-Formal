import Mathlib
import Formal.CThree
import Formal.VanGen
import Formal.GramSub

/-!
# The construction at the general window

`Formal/CThree.lean` builds the MPE construction for the *full* window `k = n`, where `U` is
square and `D = det U`.  The paper's primary construction is the Gram one, valid at the
standing window `k = deg m_A ≤ n`:

    U(x) ∈ ℝ^{n×k},  Γ(x) = U(x)ᵀU(x),  D = det Γ,  c̃ = adj(Γ)(-Uᵀu_k),

with `σ̃ = Σ_{j≤k} c̃_j` (setting `c̃_k := D`) and `Ñ = Σ_{j≤k} c̃_j f^j`.  This file builds
that, and proves the two facts the cycle analysis needs:

* `sigtG_split`  — `|σ̃ - m_A(1)Δ| = O(r^{2k+1})`, where `Δ = det(KᵀK)` is the degeneracy
  form of `Formal/GramSub.lean`;
* `van_NtilG`    — `‖Ñ(y)‖ = O(r^{2k+2})`, which is Lemma 4.1(iii) and gives a `CycleData`
  of order `d = 2k`.

Two things make this a port of `CThree.lean` rather than a redesign.  First, Cramer's rule
replaces the adjugate: `c̃_j = det(Γ with column j replaced by -Uᵀu_k)`, a single `k × k`
determinant, exactly as in the square case.  Second, the paper's proof of Lemma 4.1(iii)
never uses the square identity `U·adj U = D·I`; it needs only that the leading part of `c̃_j`
is `c⁰_j Δ`, together with the Cayley–Hamilton cancellation `Σ_j c⁰_j A^j = m_A(A) = 0`.

The annihilating polynomial is carried as data: coefficients `cz` with `cz k = 1` and
`Σ_{j≤k} cz j • A^j = 0`.  Any monic annihilating polynomial of degree `k` will do; at
`k = deg m_A` it is the minimal polynomial, which is the paper's standing window.
-/

namespace MPE

open Metric Set Matrix

section GramCon

variable {m kk : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)}

/-- The MPE matrix of the general window: `n × k`, with columns `u_0, …, u_{k-1}`. -/
noncomputable def UevalG (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (y : Fin (m + 1) → ℝ) : Matrix (Fin (m + 1)) (Fin (kk + 1)) ℝ :=
  Matrix.of fun i j => uu f (j : ℕ) y i

/-- Its linear model, `K(y)`.  This is the `gkry` of `Formal/GramSub.lean`. -/
noncomputable def KevalG (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (y : Fin (m + 1) → ℝ) : Matrix (Fin (m + 1)) (Fin (kk + 1)) ℝ :=
  Matrix.of fun i j => uuLin f (j : ℕ) y i

lemma KevalG_eq_gkry (y : Fin (m + 1) → ℝ) :
    KevalG (kk := kk) f y = gkry (k := kk + 1) (Amat f) y := rfl

/-- The Gram matrix `Γ = UᵀU`. -/
noncomputable def GamG (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (y : Fin (m + 1) → ℝ) : Matrix (Fin (kk + 1)) (Fin (kk + 1)) ℝ :=
  (UevalG (kk := kk) f y)ᵀ * (UevalG (kk := kk) f y)

/-- Its linear model, `KᵀK`, whose determinant is the degeneracy form `Δ`. -/
noncomputable def KGamG (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (y : Fin (m + 1) → ℝ) : Matrix (Fin (kk + 1)) (Fin (kk + 1)) ℝ :=
  (KevalG (kk := kk) f y)ᵀ * (KevalG (kk := kk) f y)

lemma det_KGamG (y : Fin (m + 1) → ℝ) :
    (KGamG (kk := kk) f y).det = gramDelta (k := kk + 1) (Amat f) y := rfl

/-- The right-hand side `-Uᵀ u_k` of the normal equations. -/
noncomputable def bG (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (y : Fin (m + 1) → ℝ) : Fin (kk + 1) → ℝ :=
  fun j => -((UevalG (kk := kk) f y)ᵀ.mulVec (uu f (kk + 1) y) j)

/-- Its linear model. -/
noncomputable def bKG (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (y : Fin (m + 1) → ℝ) : Fin (kk + 1) → ℝ :=
  fun j => -((KevalG (kk := kk) f y)ᵀ.mulVec (uuLin f (kk + 1) y) j)

/-- **The cleared coefficients**, by Cramer's rule; `c̃_k = det Γ`. -/
noncomputable def cctG (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (j : ℕ)
    (y : Fin (m + 1) → ℝ) : ℝ :=
  if h : j < kk + 1 then (GamG (kk := kk) f y).cramer (bG (kk := kk) f y) ⟨j, h⟩
  else (GamG (kk := kk) f y).det

/-- The cleared denominator `σ̃ = Σ_{j≤k} c̃_j`. -/
noncomputable def sigtG (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (y : Fin (m + 1) → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (kk + 2), cctG (kk := kk) f j y

/-- The cleared numerator `Ñ = Σ_{j≤k} c̃_j f^j`. -/
noncomputable def NtilG (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ))
    (y : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  ∑ j ∈ Finset.range (kk + 2), cctG (kk := kk) f j y • f^[j] y

/-! ### The Cayley–Hamilton cancellation

`Σ_{j<k} c⁰_j (A-I)A^j y = (A-I)(m_A(A) - A^k) y = -(A-I)A^k y`, so the linear model of the
right-hand side is `Γ_K c⁰`, and Cramer then gives `det(Γ_K col j ← Γ_K c⁰) = Δ·c⁰_j`. -/

variable (cz : ℕ → ℝ)

/-- The annihilating relation, as used below: `Σ_{j<k} c⁰_j A^j = -A^k`. -/
lemma sum_pow_eq_neg (hann : ∑ j ∈ Finset.range (kk + 2), cz j • ((Amat f) ^ j) = 0)
    (htop : cz (kk + 1) = 1) :
    ∑ j ∈ Finset.range (kk + 1), cz j • ((Amat f) ^ j) = -((Amat f) ^ (kk + 1)) := by
  rw [Finset.sum_range_succ, htop, one_smul] at hann
  linear_combination (norm := module) hann

lemma KevalG_mulVec_cz (hann : ∑ j ∈ Finset.range (kk + 2), cz j • ((Amat f) ^ j) = 0)
    (htop : cz (kk + 1) = 1) (y : Fin (m + 1) → ℝ) :
    (KevalG (kk := kk) f y).mulVec (fun j : Fin (kk + 1) => cz (j : ℕ))
      = fun i => -(uuLin f (kk + 1) y i) := by
  funext i
  have hlhs : (KevalG (kk := kk) f y).mulVec (fun j : Fin (kk + 1) => cz (j : ℕ)) i
      = ∑ j : Fin (kk + 1), cz (j : ℕ) * uuLin f (j : ℕ) y i := by
    simp only [Matrix.mulVec, dotProduct, KevalG, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hlhs]
  have hrange : ∑ j : Fin (kk + 1), cz (j : ℕ) * uuLin f (j : ℕ) y i
      = ∑ j ∈ Finset.range (kk + 1), cz j * uuLin f j y i := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => cz j * uuLin f j y i) (kk + 1)]
  rw [hrange]
  have hentry : ∀ j : ℕ, cz j * uuLin f j y i
      = ((cz j • ((Amat f - 1) * (Amat f) ^ j)).mulVec y) i := by
    intro j
    rw [uuLin, Matrix.smul_mulVec]
    rfl
  simp only [hentry]
  rw [← Finset.sum_apply, ← Matrix.sum_mulVec]
  have hM : ∑ j ∈ Finset.range (kk + 1), cz j • ((Amat f - 1) * (Amat f) ^ j)
      = (Amat f - 1) * (∑ j ∈ Finset.range (kk + 1), cz j • ((Amat f) ^ j)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_smul]
  rw [hM, sum_pow_eq_neg cz hann htop, uuLin, Matrix.mul_neg, Matrix.neg_mulVec]
  rfl

/-- **The linear determinant, in closed form.**  `det(Γ_K with column j replaced by its
right-hand side) = c⁰_j · Δ`. -/
theorem cramer_KGamG (hann : ∑ j ∈ Finset.range (kk + 2), cz j • ((Amat f) ^ j) = 0)
    (htop : cz (kk + 1) = 1) (y : Fin (m + 1) → ℝ) (j : Fin (kk + 1)) :
    (KGamG (kk := kk) f y).cramer (bKG (kk := kk) f y) j
      = cz (j : ℕ) * gramDelta (k := kk + 1) (Amat f) y := by
  have hb : bKG (kk := kk) f y
      = (KGamG (kk := kk) f y).mulVec (fun l : Fin (kk + 1) => cz (l : ℕ)) := by
    funext l
    have hrw : (KGamG (kk := kk) f y).mulVec (fun l : Fin (kk + 1) => cz (l : ℕ))
        = (KevalG (kk := kk) f y)ᵀ.mulVec
            ((KevalG (kk := kk) f y).mulVec (fun l : Fin (kk + 1) => cz (l : ℕ))) := by
      rw [KGamG, Matrix.mulVec_mulVec]
    rw [hrw, KevalG_mulVec_cz cz hann htop]
    simp only [bKG, Matrix.mulVec, dotProduct, Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hb, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, ← det_KGamG]
  simp [smul_eq_mul, mul_comm]

/-! ### The `Van` estimates

Entries of `Γ` are products of two entries of `U`, hence `O(r²)`; entries of `Γ - KᵀK`
carry one factor `U - K = O(r²)` against one `O(r)`, hence `O(r³)`.  Feeding `p = 1` and
`d = 2` to `Van.det_gen` and `Van.det_sub_gen` gives `O(r^{2k})` and `O(r^{2k+1})`. -/

end GramCon

namespace SmoothData

section GramEst

variable {m kk : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)} (D : SmoothData f)

/-- Entries of `U`, as functions, vanish to order `1`. -/
theorem van_UevalG_entry {N : ℕ} (hj : kk + 2 ≤ N) (i : Fin (m + 1)) (j : Fin (kk + 1)) :
    Van (D.rad N) 0 (D.CB N) (fun y => UevalG (kk := kk) f y i j) := by
  have hjN : (j : ℕ) + 1 ≤ N := by have := j.isLt; omega
  have hpos : (0:ℝ) ≤ D.L ^ N + D.L ^ N := by
    have := pow_nonneg D.L_pos.le N; linarith
  have h := (Van.pi_apply hpos (D.van_uu hjN) i).mono_const
    (le_max_left (D.L ^ N + D.L ^ N) (CKb f))
  exact h

/-- The same for `K`. -/
theorem van_KevalG_entry {N : ℕ} (hkn : kk + 1 ≤ m + 1) (i : Fin (m + 1)) (j : Fin (kk + 1)) :
    Van (D.rad N) 0 (D.CB N) (fun y => KevalG (kk := kk) f y i j) := by
  have hjle : (j : ℕ) ≤ m + 1 := by have := j.isLt; omega
  exact (van_uuLin' (ρ := D.rad N) hjle i).mono_const (le_max_right _ _)

/-- `U - K` vanishes to order `2`, entrywise. -/
theorem van_UevalG_sub {N : ℕ} (hj : kk + 2 ≤ N) (i : Fin (m + 1)) (j : Fin (kk + 1)) :
    Van (D.rad N) 1 (D.CD N)
      (fun y => UevalG (kk := kk) f y i j - KevalG (kk := kk) f y i j) := by
  have hjN : (j : ℕ) + 1 ≤ N := by have := j.isLt; omega
  exact Van.pi_apply (D.CD_nonneg N) (D.van_uu_sub_lin hjN) i

/-! #### The Gram matrix -/

lemma GamG_apply (y : Fin (m + 1) → ℝ) (i j : Fin (kk + 1)) :
    GamG (kk := kk) f y i j
      = ∑ l : Fin (m + 1), UevalG (kk := kk) f y l i * UevalG (kk := kk) f y l j := by
  rw [GamG, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => rfl

lemma KGamG_apply (y : Fin (m + 1) → ℝ) (i j : Fin (kk + 1)) :
    KGamG (kk := kk) f y i j
      = ∑ l : Fin (m + 1), KevalG (kk := kk) f y l i * KevalG (kk := kk) f y l j := by
  rw [KGamG, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => rfl

/-- Entries of `Γ` vanish to order `2`. -/
theorem van_GamG_entry {N : ℕ} (hj : kk + 2 ≤ N) (i j : Fin (kk + 1)) :
    Van (D.rad N) 1 ((m + 1 : ℕ) * (2 * (D.CB N * D.CB N)))
      (fun y => GamG (kk := kk) f y i j) := by
  have hfun : (fun y => GamG (kk := kk) f y i j)
      = fun y => ∑ l : Fin (m + 1),
          UevalG (kk := kk) f y l i * UevalG (kk := kk) f y l j := by
    funext y; exact GamG_apply y i j
  rw [hfun]
  have hterm : ∀ l : Fin (m + 1), l ∈ Finset.univ →
      Van (D.rad N) 1 (2 * (D.CB N * D.CB N))
        (fun y => UevalG (kk := kk) f y l i * UevalG (kk := kk) f y l j) :=
    fun l _ => Van.mul (D.CB_nonneg N) (D.CB_nonneg N)
      (D.van_UevalG_entry hj l i) (D.van_UevalG_entry hj l j)
  have h := Van.sum (ρ := D.rad N) (k := 1) Finset.univ
    (by have := D.CB_nonneg N; positivity) hterm
  refine h.mono_const (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fin]

/-- The same for `KᵀK`. -/
theorem van_KGamG_entry {N : ℕ} (hkn : kk + 1 ≤ m + 1) (i j : Fin (kk + 1)) :
    Van (D.rad N) 1 ((m + 1 : ℕ) * (2 * (D.CB N * D.CB N)))
      (fun y => KGamG (kk := kk) f y i j) := by
  have hfun : (fun y => KGamG (kk := kk) f y i j)
      = fun y => ∑ l : Fin (m + 1),
          KevalG (kk := kk) f y l i * KevalG (kk := kk) f y l j := by
    funext y; exact KGamG_apply y i j
  rw [hfun]
  have hterm : ∀ l : Fin (m + 1), l ∈ Finset.univ →
      Van (D.rad N) 1 (2 * (D.CB N * D.CB N))
        (fun y => KevalG (kk := kk) f y l i * KevalG (kk := kk) f y l j) :=
    fun l _ => Van.mul (D.CB_nonneg N) (D.CB_nonneg N)
      (D.van_KevalG_entry hkn l i) (D.van_KevalG_entry hkn l j)
  have h := Van.sum (ρ := D.rad N) (k := 1) Finset.univ
    (by have := D.CB_nonneg N; positivity) hterm
  refine h.mono_const (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fin]

/-- `Γ - KᵀK` vanishes to order `3`: each term carries one factor `U - K = O(r²)` against
one factor of size `O(r)`. -/
theorem van_GamG_sub {N : ℕ} (hj : kk + 2 ≤ N) (hkn : kk + 1 ≤ m + 1) (i j : Fin (kk + 1)) :
    Van (D.rad N) 2 ((m + 1 : ℕ) * (2 * (D.CD N * D.CB N) + 2 * (D.CB N * D.CD N)))
      (fun y => GamG (kk := kk) f y i j - KGamG (kk := kk) f y i j) := by
  have hfun : (fun y => GamG (kk := kk) f y i j - KGamG (kk := kk) f y i j)
      = fun y => ∑ l : Fin (m + 1),
          ((UevalG (kk := kk) f y l i - KevalG (kk := kk) f y l i)
              * UevalG (kk := kk) f y l j
            + KevalG (kk := kk) f y l i
              * (UevalG (kk := kk) f y l j - KevalG (kk := kk) f y l j)) := by
    funext y
    rw [GamG_apply, KGamG_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hfun]
  have hterm : ∀ l : Fin (m + 1), l ∈ Finset.univ →
      Van (D.rad N) 2 (2 * (D.CD N * D.CB N) + 2 * (D.CB N * D.CD N))
        (fun y => ((UevalG (kk := kk) f y l i - KevalG (kk := kk) f y l i)
              * UevalG (kk := kk) f y l j
            + KevalG (kk := kk) f y l i
              * (UevalG (kk := kk) f y l j - KevalG (kk := kk) f y l j))) := by
    intro l _
    have h1 := Van.mul (D.CD_nonneg N) (D.CB_nonneg N)
      (D.van_UevalG_sub hj l i) (D.van_UevalG_entry hj l j)
    have h2 := Van.mul (D.CB_nonneg N) (D.CD_nonneg N)
      (D.van_KevalG_entry hkn l i) (D.van_UevalG_sub hj l j)
    exact h1.add h2
  have h := Van.sum (ρ := D.rad N) (k := 2) Finset.univ
    (by have := D.CB_nonneg N; have := D.CD_nonneg N; positivity) hterm
  refine h.mono_const (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fin]

/-! #### The right-hand side -/

lemma bG_apply (y : Fin (m + 1) → ℝ) (j : Fin (kk + 1)) :
    bG (kk := kk) f y j
      = -∑ l : Fin (m + 1), UevalG (kk := kk) f y l j * uu f (kk + 1) y l := rfl

lemma bKG_apply (y : Fin (m + 1) → ℝ) (j : Fin (kk + 1)) :
    bKG (kk := kk) f y j
      = -∑ l : Fin (m + 1), KevalG (kk := kk) f y l j * uuLin f (kk + 1) y l := rfl

theorem van_bG_entry {N : ℕ} (hj : kk + 2 ≤ N) (j : Fin (kk + 1)) :
    Van (D.rad N) 1 ((m + 1 : ℕ) * (2 * (D.CB N * D.CB N)))
      (fun y => bG (kk := kk) f y j) := by
  have hfun : (fun y => bG (kk := kk) f y j)
      = fun y => -∑ l : Fin (m + 1),
          UevalG (kk := kk) f y l j * uu f (kk + 1) y l := by
    funext y; exact bG_apply y j
  rw [hfun]
  have huk : ∀ l : Fin (m + 1), Van (D.rad N) 0 (D.CB N) (fun y => uu f (kk + 1) y l) := by
    intro l
    have hpos : (0:ℝ) ≤ D.L ^ N + D.L ^ N := by
      have := pow_nonneg D.L_pos.le N; linarith
    exact (Van.pi_apply hpos (D.van_uu (by omega : kk + 1 + 1 ≤ N)) l).mono_const
      (le_max_left _ _)
  have hterm : ∀ l : Fin (m + 1), l ∈ Finset.univ →
      Van (D.rad N) 1 (2 * (D.CB N * D.CB N))
        (fun y => UevalG (kk := kk) f y l j * uu f (kk + 1) y l) :=
    fun l _ => Van.mul (D.CB_nonneg N) (D.CB_nonneg N)
      (D.van_UevalG_entry hj l j) (huk l)
  have h := Van.sum (ρ := D.rad N) (k := 1) Finset.univ
    (by have := D.CB_nonneg N; positivity) hterm
  have h2 := h.neg
  refine h2.mono_const (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fin]

theorem van_bKG_entry {N : ℕ} (hkn : kk + 1 ≤ m + 1) (j : Fin (kk + 1)) :
    Van (D.rad N) 1 ((m + 1 : ℕ) * (2 * (D.CB N * D.CB N)))
      (fun y => bKG (kk := kk) f y j) := by
  have hfun : (fun y => bKG (kk := kk) f y j)
      = fun y => -∑ l : Fin (m + 1),
          KevalG (kk := kk) f y l j * uuLin f (kk + 1) y l := by
    funext y; exact bKG_apply y j
  rw [hfun]
  have huk : ∀ l : Fin (m + 1),
      Van (D.rad N) 0 (D.CB N) (fun y => uuLin f (kk + 1) y l) := fun l =>
    (van_uuLin' (ρ := D.rad N) (by omega : kk + 1 ≤ m + 1) l).mono_const (le_max_right _ _)
  have hterm : ∀ l : Fin (m + 1), l ∈ Finset.univ →
      Van (D.rad N) 1 (2 * (D.CB N * D.CB N))
        (fun y => KevalG (kk := kk) f y l j * uuLin f (kk + 1) y l) :=
    fun l _ => Van.mul (D.CB_nonneg N) (D.CB_nonneg N)
      (D.van_KevalG_entry hkn l j) (huk l)
  have h := Van.sum (ρ := D.rad N) (k := 1) Finset.univ
    (by have := D.CB_nonneg N; positivity) hterm
  have h2 := h.neg
  refine h2.mono_const (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fin]

theorem van_bG_sub {N : ℕ} (hj : kk + 2 ≤ N) (hkn : kk + 1 ≤ m + 1) (j : Fin (kk + 1)) :
    Van (D.rad N) 2 ((m + 1 : ℕ) * (2 * (D.CD N * D.CB N) + 2 * (D.CB N * D.CD N)))
      (fun y => bG (kk := kk) f y j - bKG (kk := kk) f y j) := by
  have huk : ∀ l : Fin (m + 1), Van (D.rad N) 0 (D.CB N) (fun y => uu f (kk + 1) y l) := by
    intro l
    have hpos : (0:ℝ) ≤ D.L ^ N + D.L ^ N := by
      have := pow_nonneg D.L_pos.le N; linarith
    exact (Van.pi_apply hpos (D.van_uu (by omega : kk + 1 + 1 ≤ N)) l).mono_const
      (le_max_left _ _)
  have huksub : ∀ l : Fin (m + 1), Van (D.rad N) 1 (D.CD N)
      (fun y => uu f (kk + 1) y l - uuLin f (kk + 1) y l) := fun l =>
    Van.pi_apply (D.CD_nonneg N) (D.van_uu_sub_lin (by omega : kk + 1 + 1 ≤ N)) l
  have hfun : (fun y => bG (kk := kk) f y j - bKG (kk := kk) f y j)
      = fun y => -∑ l : Fin (m + 1),
          ((UevalG (kk := kk) f y l j - KevalG (kk := kk) f y l j)
              * uu f (kk + 1) y l
            + KevalG (kk := kk) f y l j
              * (uu f (kk + 1) y l - uuLin f (kk + 1) y l)) := by
    funext y
    rw [bG_apply, bKG_apply, neg_sub_neg, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hfun]
  have hterm : ∀ l : Fin (m + 1), l ∈ Finset.univ →
      Van (D.rad N) 2 (2 * (D.CD N * D.CB N) + 2 * (D.CB N * D.CD N))
        (fun y => ((UevalG (kk := kk) f y l j - KevalG (kk := kk) f y l j)
              * uu f (kk + 1) y l
            + KevalG (kk := kk) f y l j
              * (uu f (kk + 1) y l - uuLin f (kk + 1) y l))) := by
    intro l _
    have h1 := Van.mul (D.CD_nonneg N) (D.CB_nonneg N) (D.van_UevalG_sub hj l j) (huk l)
    have h2 := Van.mul (D.CB_nonneg N) (D.CD_nonneg N)
      (D.van_KevalG_entry hkn l j) (huksub l)
    exact h1.add h2
  have h := Van.sum (ρ := D.rad N) (k := 2) Finset.univ
    (by have := D.CB_nonneg N; have := D.CD_nonneg N; positivity) hterm
  have h2 := h.neg
  refine h2.mono_const (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_fin]

/-! #### The column-replaced matrices, and the determinant estimates -/

/-- `Γ` with column `j` replaced by the right-hand side, as a matrix of functions. -/
noncomputable def GcolF (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin (kk + 1)) :
    Matrix (Fin (kk + 1)) (Fin (kk + 1)) ((Fin (m + 1) → ℝ) → ℝ) :=
  fun i l => if l = j then (fun y => bG (kk := kk) f y i)
             else (fun y => GamG (kk := kk) f y i l)

/-- The same for the linear model. -/
noncomputable def KGcolF (f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin (kk + 1)) :
    Matrix (Fin (kk + 1)) (Fin (kk + 1)) ((Fin (m + 1) → ℝ) → ℝ) :=
  fun i l => if l = j then (fun y => bKG (kk := kk) f y i)
             else (fun y => KGamG (kk := kk) f y i l)

lemma GcolF_det (j : Fin (kk + 1)) (y : Fin (m + 1) → ℝ) :
    Matrix.det (fun i l => GcolF (kk := kk) f j i l y)
      = (GamG (kk := kk) f y).cramer (bG (kk := kk) f y) j := by
  rw [Matrix.cramer_apply]
  congr 1
  funext i l
  rw [Matrix.updateCol_apply, GcolF]
  by_cases h : l = j <;> simp [h]

lemma KGcolF_det (j : Fin (kk + 1)) (y : Fin (m + 1) → ℝ) :
    Matrix.det (fun i l => KGcolF (kk := kk) f j i l y)
      = (KGamG (kk := kk) f y).cramer (bKG (kk := kk) f y) j := by
  rw [Matrix.cramer_apply]
  congr 1
  funext i l
  rw [Matrix.updateCol_apply, KGcolF]
  by_cases h : l = j <;> simp [h]

section Est2

variable {m kk : ℕ} {f : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)} (D : SmoothData f)

/-- **`c̃_j` has leading part `c⁰_j Δ`**, to order `2k+1`.  This is the general-window
analogue of `cct_sub_leading`, and the only place `Van.det_sub_gen` is used. -/
theorem cctG_sub_leading {N : ℕ} (hj : kk + 2 ≤ N) (hkn : kk + 1 ≤ m + 1)
    (cz : ℕ → ℝ) (hann : ∑ i ∈ Finset.range (kk + 2), cz i • ((Amat f) ^ i) = 0)
    (htop : cz (kk + 1) = 1) (j : ℕ) (hjk : j ≤ kk + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ Van (D.rad N) (kk * 2 + 2) C
      (fun y => cctG (kk := kk) f j y
        - cz j * gramDelta (k := kk + 1) (Amat f) y) := by
  classical
  rcases lt_or_eq_of_le hjk with hlt | rfl
  · -- `j < k`: Cramer, with the column-replaced matrices
    set jf : Fin (kk + 1) := ⟨j, hlt⟩ with hjf
    have hM : ∀ i l, Van (D.rad N) 1 ((m + 1 : ℕ) * (2 * (D.CB N * D.CB N)))
        (GcolF (kk := kk) f jf i l) := by
      intro i l
      rw [GcolF]
      by_cases h : l = jf
      · simp only [h, if_pos]; exact D.van_bG_entry hj i
      · simp only [if_neg h]; exact D.van_GamG_entry hj i l
    have hN' : ∀ i l, Van (D.rad N) 1 ((m + 1 : ℕ) * (2 * (D.CB N * D.CB N)))
        (KGcolF (kk := kk) f jf i l) := by
      intro i l
      rw [KGcolF]
      by_cases h : l = jf
      · simp only [h, if_pos]; exact D.van_bKG_entry hkn i
      · simp only [if_neg h]; exact D.van_KGamG_entry hkn i l
    have hMN : ∀ i l, Van (D.rad N) 2
        ((m + 1 : ℕ) * (2 * (D.CD N * D.CB N) + 2 * (D.CB N * D.CD N)))
        (fun y => GcolF (kk := kk) f jf i l y - KGcolF (kk := kk) f jf i l y) := by
      intro i l
      rw [GcolF, KGcolF]
      by_cases h : l = jf
      · simp only [h, if_pos]; exact D.van_bG_sub hj hkn i
      · simp only [if_neg h]; exact D.van_GamG_sub hj hkn i l
    obtain ⟨K, hK0, hKv⟩ := Van.det_sub_gen (p := 1) (d := 2)
      (by have := D.CB_nonneg N; positivity)
      (by have := D.CB_nonneg N; have := D.CD_nonneg N; positivity) hM hN' hMN
    refine ⟨K, hK0, ?_⟩
    have hfun : (fun y => cctG (kk := kk) f j y - cz j * gramDelta (k := kk + 1) (Amat f) y)
        = fun y => Matrix.det (fun i l => GcolF (kk := kk) f jf i l y)
            - Matrix.det (fun i l => KGcolF (kk := kk) f jf i l y) := by
      funext y
      rw [GcolF_det, KGcolF_det, cramer_KGamG cz hann htop, cctG, dif_pos hlt]
    rw [hfun]
    exact hKv
  · -- `j = k`: the determinant of `Γ` itself
    obtain ⟨K, hK0, hKv⟩ := Van.det_sub_gen (p := 1) (d := 2)
      (C := (m + 1 : ℕ) * (2 * (D.CB N * D.CB N)))
      (D := (m + 1 : ℕ) * (2 * (D.CD N * D.CB N) + 2 * (D.CB N * D.CD N)))
      (M := fun i l => fun y => GamG (kk := kk) f y i l)
      (N := fun i l => fun y => KGamG (kk := kk) f y i l)
      (by have := D.CB_nonneg N; positivity)
      (by have := D.CB_nonneg N; have := D.CD_nonneg N; positivity)
      (fun i l => D.van_GamG_entry hj i l) (fun i l => D.van_KGamG_entry hkn i l)
      (fun i l => D.van_GamG_sub hj hkn i l)
    refine ⟨K, hK0, ?_⟩
    have hfun : (fun y => cctG (kk := kk) f (kk + 1) y
          - cz (kk + 1) * gramDelta (k := kk + 1) (Amat f) y)
        = fun y => Matrix.det (fun i l => GamG (kk := kk) f y i l)
            - Matrix.det (fun i l => KGamG (kk := kk) f y i l) := by
      funext y
      rw [cctG, dif_neg (lt_irrefl _), htop, one_mul, ← det_KGamG]
    rw [hfun]
    exact hKv

/-- Scaling a `Van` map by a constant. -/
lemma van_const_smul {ρ C : ℝ} {kv : ℕ}
    {g : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)} (c : ℝ) (hC : 0 ≤ C) (hg : Van ρ kv C g) :
    Van ρ kv (|c| * C) (fun y => c • g y) := by
  have h := Van.clm_comp (c • ContinuousLinearMap.id ℝ (Fin (m + 1) → ℝ)) hC hg
  have hnorm : ‖(c • ContinuousLinearMap.id ℝ (Fin (m + 1) → ℝ))‖ ≤ |c| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  exact h.mono_const (mul_le_mul_of_nonneg_right hnorm hC)

/-- **The Cayley–Hamilton cancellation, at the level of the iterates.**  `Σ_j c⁰_j f^j`
vanishes to order `2`, because its linear part is `Σ_j c⁰_j A^j = m_A(A) = 0`. -/
theorem van_sum_cz_iter {N : ℕ} (hkn : kk + 2 ≤ N)
    (cz : ℕ → ℝ) (hann : ∑ i ∈ Finset.range (kk + 2), cz i • ((Amat f) ^ i) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ Van (D.rad N) 1 C
      (fun y => ∑ j ∈ Finset.range (kk + 2), cz j • f^[j] y) := by
  classical
  have hzero : ∀ y : Fin (m + 1) → ℝ,
      ∑ j ∈ Finset.range (kk + 2), cz j • (((linPart f) ^ j) y) = 0 := by
    intro y
    have hstep : ∀ j : ℕ, cz j • (((linPart f) ^ j) y)
        = ((cz j • ((Amat f) ^ j)).mulVec y) := by
      intro j
      rw [Matrix.smul_mulVec, Amat_pow_mulVec]
    simp only [hstep]
    rw [← Matrix.sum_mulVec, hann, Matrix.zero_mulVec]
  have hfun : (fun y => ∑ j ∈ Finset.range (kk + 2), cz j • f^[j] y)
      = fun y => ∑ j ∈ Finset.range (kk + 2),
          cz j • (f^[j] y - ((linPart f) ^ j) y) := by
    funext y
    rw [← sub_zero (∑ j ∈ Finset.range (kk + 2), cz j • f^[j] y), ← hzero y,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [← smul_sub]
  rw [hfun]
  set Cs : ℝ := D.CD N with hCs
  have hCs0 : 0 ≤ Cs := D.CD_nonneg N
  have hterm : ∀ j ∈ Finset.range (kk + 2),
      Van (D.rad N) 1 ((Finset.range (kk + 2)).sup' ⟨0, by simp⟩ (fun i => |cz i|) * Cs)
        (fun y => cz j • (f^[j] y - ((linPart f) ^ j) y)) := by
    intro j hjm
    have hjN : j ≤ N := by rw [Finset.mem_range] at hjm; omega
    have hv := D.van_iter_sub_pow N j hjN
    have hbase0 : (0:ℝ) ≤ (D.K * (D.L ^ N) ^ 2)
        * ∑ i ∈ Finset.range (N + 1), (max ‖linPart f‖ 1) ^ i := by
      refine mul_nonneg (mul_nonneg D.hK (by positivity)) (Finset.sum_nonneg fun i _ => ?_)
      exact pow_nonneg (le_trans zero_le_one (le_max_right _ _)) i
    have h := van_const_smul (cz j) hbase0 hv
    refine h.mono_const (mul_le_mul (Finset.le_sup' (fun i => |cz i|) hjm) ?_ hbase0 ?_)
    · rw [hCs, SmoothData.CD]; linarith
    · exact le_trans (abs_nonneg (cz 0)) (Finset.le_sup' (fun i => |cz i|) (by simp))
  have hsup0 : 0 ≤ (Finset.range (kk + 2)).sup' ⟨0, by simp⟩ (fun i => |cz i|) :=
    le_trans (abs_nonneg (cz 0)) (Finset.le_sup' (fun i => |cz i|) (by simp))
  have h := Van.sum (ρ := D.rad N) (k := 1) (Finset.range (kk + 2))
    (mul_nonneg hsup0 hCs0) hterm
  exact ⟨_, by positivity, h⟩

/-- **The `σ̃` splitting at the general window.**  `σ̃ = m_A(1)·Δ + O(r^{2k+1})`. -/
theorem sigtG_split {N : ℕ} (hj : kk + 2 ≤ N) (hkn : kk + 1 ≤ m + 1)
    (cz : ℕ → ℝ) (hann : ∑ i ∈ Finset.range (kk + 2), cz i • ((Amat f) ^ i) = 0)
    (htop : cz (kk + 1) = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ Van (D.rad N) (kk * 2 + 2) C
      (fun y => sigtG (kk := kk) f y
        - (∑ i ∈ Finset.range (kk + 2), cz i) * gramDelta (k := kk + 1) (Amat f) y) := by
  classical
  choose C hC0 hCv using fun j : Fin (kk + 2) =>
    D.cctG_sub_leading hj hkn cz hann htop (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)
  set Ctot : ℝ := ∑ j : Fin (kk + 2), C j with hCtot
  have hCtot0 : 0 ≤ Ctot := Finset.sum_nonneg fun j _ => hC0 j
  refine ⟨((kk + 2 : ℕ) : ℝ) * Ctot, by positivity, ?_⟩
  have hfun : (fun y => sigtG (kk := kk) f y
        - (∑ i ∈ Finset.range (kk + 2), cz i) * gramDelta (k := kk + 1) (Amat f) y)
      = fun y => ∑ j ∈ Finset.range (kk + 2),
          (cctG (kk := kk) f j y - cz j * gramDelta (k := kk + 1) (Amat f) y) := by
    funext y
    rw [sigtG, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hfun]
  have hterm : ∀ j ∈ Finset.range (kk + 2),
      Van (D.rad N) (kk * 2 + 2) Ctot
        (fun y => cctG (kk := kk) f j y - cz j * gramDelta (k := kk + 1) (Amat f) y) := by
    intro j hjm
    have hjlt : j < kk + 2 := Finset.mem_range.mp hjm
    set jf : Fin (kk + 2) := ⟨j, hjlt⟩ with hjf
    have h := hCv jf
    refine h.mono_const ?_
    exact Finset.single_le_sum (f := C) (fun l _ => hC0 l) (Finset.mem_univ jf)
  have h := Van.sum (ρ := D.rad N) (k := kk * 2 + 2) (Finset.range (kk + 2)) hCtot0 hterm
  refine h.mono_const (le_of_eq ?_)
  rw [Finset.card_range]

/-- **Lemma 4.1(iii) at the general window.**  `‖Ñ(y)‖ = O(r^{2k+2})`.

`Ñ = Σ_j c̃_j f^j = Δ·(Σ_j c⁰_j f^j) + Σ_j (c̃_j - c⁰_j Δ) f^j`.  The first term is
`O(r^{2k})·O(r²)` by the Cayley–Hamilton cancellation, the second `O(r^{2k+1})·O(r)`. -/
theorem van_NtilG {N : ℕ} (hj : kk + 2 ≤ N) (hkn : kk + 1 ≤ m + 1)
    (cz : ℕ → ℝ) (hann : ∑ i ∈ Finset.range (kk + 2), cz i • ((Amat f) ^ i) = 0)
    (htop : cz (kk + 1) = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ Van (D.rad N) (kk * 2 + 3) C (NtilG (kk := kk) f) := by
  classical
  -- `Δ` vanishes to order `2k`
  have hDelta : Van (D.rad N) (kk * 2 + 1)
      ((kk + 1).factorial * (1 * (2 ^ kk * ((m + 1 : ℕ) * (2 * (D.CB N * D.CB N))) ^ (kk + 1))))
      (fun y => gramDelta (k := kk + 1) (Amat f) y) := by
    have h := Van.det_gen (ρ := D.rad N) (p := 1)
      (M := fun i l => fun y => KGamG (kk := kk) f y i l)
      (by have := D.CB_nonneg N; positivity)
      (fun i l => D.van_KGamG_entry hkn i l)
    exact h
  have hD0 : (0:ℝ) ≤ (kk + 1).factorial
      * (1 * (2 ^ kk * ((m + 1 : ℕ) * (2 * (D.CB N * D.CB N))) ^ (kk + 1))) := by
    have := D.CB_nonneg N; positivity
  -- the Cayley–Hamilton factor
  obtain ⟨Cs, hCs0, hCsv⟩ := D.van_sum_cz_iter hj cz hann
  -- the corrections
  choose CE hCE0 hCEv using fun j : Fin (kk + 2) =>
    D.cctG_sub_leading hj hkn cz hann htop (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)
  set CEtot : ℝ := ∑ j : Fin (kk + 2), CE j with hCEtot
  have hCEtot0 : 0 ≤ CEtot := Finset.sum_nonneg fun j _ => hCE0 j
  -- the decomposition
  have hfun : NtilG (kk := kk) f
      = fun y => (gramDelta (k := kk + 1) (Amat f) y)
            • (∑ j ∈ Finset.range (kk + 2), cz j • f^[j] y)
          + ∑ j ∈ Finset.range (kk + 2),
              (cctG (kk := kk) f j y - cz j * gramDelta (k := kk + 1) (Amat f) y) • f^[j] y := by
    funext y
    rw [NtilG, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [sub_smul, smul_smul]
      module
  rw [hfun]
  -- the first term
  have h1 := Van.smul hD0 hCs0 hDelta hCsv
  rw [show kk * 2 + 1 + 1 + 1 = kk * 2 + 3 from by ring] at h1
  -- the second term
  have hiter : ∀ j ∈ Finset.range (kk + 2),
      Van (D.rad N) 0 (D.L ^ N) (fun y => f^[j] y) := by
    intro j hjm
    have hjN : j ≤ N := by rw [Finset.mem_range] at hjm; omega
    exact D.van_iter hjN
  have hterm2 : ∀ j ∈ Finset.range (kk + 2),
      Van (D.rad N) (kk * 2 + 3) (2 * (CEtot * D.L ^ N))
        (fun y => (cctG (kk := kk) f j y
          - cz j * gramDelta (k := kk + 1) (Amat f) y) • f^[j] y) := by
    intro j hjm
    have hjlt : j < kk + 2 := Finset.mem_range.mp hjm
    set jf : Fin (kk + 2) := ⟨j, hjlt⟩ with hjf
    have hE := (hCEv jf).mono_const
      (Finset.single_le_sum (f := CE) (fun l _ => hCE0 l) (Finset.mem_univ jf))
    have h := Van.smul hCEtot0 (pow_nonneg D.L_pos.le N) hE (hiter j hjm)
    rwa [show kk * 2 + 2 + 0 + 1 = kk * 2 + 3 from by ring] at h
  have h2 := Van.sum (ρ := D.rad N) (k := kk * 2 + 3) (Finset.range (kk + 2))
    (by have := pow_nonneg D.L_pos.le N; positivity) hterm2
  exact ⟨_, by
    have := pow_nonneg D.L_pos.le N
    have h1c : (0:ℝ) ≤ 2 * (((kk + 1).factorial
      * (1 * (2 ^ kk * ((m + 1 : ℕ) * (2 * (D.CB N * D.CB N))) ^ (kk + 1)))) * Cs) := by
      have := D.CB_nonneg N; positivity
    positivity, h1.add h2⟩

end Est2

end GramEst

end SmoothData

end MPE
