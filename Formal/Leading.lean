import Formal.Degree

/-!
# Leading parts

`LowDeg` bounds degrees from below.  The sharp one-cycle bound needs more: the *leading*
homogeneous component, with two-sided control of the remainder.  This file provides that.

* `lowDeg_sub_homogeneousComponent` splits `P` of degree `≥ k` into its degree-`k`
  component plus a remainder of degree `≥ k+1`;
* `homogeneousComponent_mul_of_lowDeg` says leading parts multiply — the key step, since
  `Ñ`'s leading part is built from those of `c̃` and `f^j`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace MPE

open MvPolynomial Finset

variable {σ : Type*} [DecidableEq σ]

/-- **The leading part splits off.**  If every monomial of `P` has degree `≥ k`, then
`P` minus its degree-`k` component has every monomial of degree `≥ k+1`. -/
theorem lowDeg_sub_homogeneousComponent {k : ℕ} {P : MvPolynomial σ ℝ} (hP : LowDeg k P) :
    LowDeg (k + 1) (P - homogeneousComponent k P) := by
  intro d hd
  have hc : coeff d (P - homogeneousComponent k P)
      = coeff d P - (if Finsupp.degree d = k then coeff d P else 0) := by
    rw [coeff_sub, coeff_homogeneousComponent]
  have hne : coeff d (P - homogeneousComponent k P) ≠ 0 := by
    simpa [MvPolynomial.mem_support_iff] using hd
  by_cases hdk : Finsupp.degree d = k
  · rw [hc, if_pos hdk, sub_self] at hne; exact absurd rfl hne
  · have hdP : d ∈ P.support := by
      rw [MvPolynomial.mem_support_iff]
      intro h0
      rw [hc, if_neg hdk, h0, sub_zero] at hne
      exact hne rfl
    exact Nat.succ_le_of_lt (lt_of_le_of_ne (hP d hdP) (Ne.symm hdk))

/-- If `d` splits as `d₁ + d₂` with the two degrees adding to the total, and the parts are
constrained below by `a` and `b` with `a + b` the total, then the degrees are exactly `a`
and `b`. -/
private lemma degree_eq_of_add {a b : ℕ} {d₁ d₂ : σ →₀ ℕ}
    (h : Finsupp.degree d₁ + Finsupp.degree d₂ = a + b)
    (h₁ : a ≤ Finsupp.degree d₁) (h₂ : b ≤ Finsupp.degree d₂) :
    Finsupp.degree d₁ = a ∧ Finsupp.degree d₂ = b :=
  ⟨by omega, by omega⟩

/-- **Leading parts multiply.**  For `p` of degree `≥ a` and `q` of degree `≥ b`, the
degree-`(a+b)` component of `pq` is the product of the degree-`a` component of `p` and the
degree-`b` component of `q`. -/
theorem homogeneousComponent_mul_of_lowDeg {a b : ℕ} {p q : MvPolynomial σ ℝ}
    (hp : LowDeg a p) (hq : LowDeg b q) :
    homogeneousComponent (a + b) (p * q)
      = homogeneousComponent a p * homogeneousComponent b q := by
  classical
  ext d
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hdeg : Finsupp.degree d = a + b
  · rw [if_pos hdeg]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hsum : Finsupp.degree x.1 + Finsupp.degree x.2 = a + b := by
      rw [← map_add Finsupp.degree, hx', hdeg]
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases h1 : coeff x.1 p = 0
    · simp [h1]
    by_cases h2 : coeff x.2 q = 0
    · simp [h2]
    have hd1 : a ≤ Finsupp.degree x.1 := hp _ (MvPolynomial.mem_support_iff.mpr h1)
    have hd2 : b ≤ Finsupp.degree x.2 := hq _ (MvPolynomial.mem_support_iff.mpr h2)
    obtain ⟨e1, e2⟩ := degree_eq_of_add hsum hd1 hd2
    rw [if_pos e1, if_pos e2]
  · rw [if_neg hdeg]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    have hx' : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases e1 : Finsupp.degree x.1 = a
    · by_cases e2 : Finsupp.degree x.2 = b
      · exfalso
        apply hdeg
        rw [← hx', map_add Finsupp.degree, e1, e2]
      · simp [e2]
    · simp [e1]

/-- A sum of leading parts, for the `∑_j c̃_j f^j` shape. -/
theorem homogeneousComponent_sum_mul {a b : ℕ} {ι : Type*} {s : Finset ι}
    {c F : ι → MvPolynomial σ ℝ}
    (hc : ∀ j, LowDeg a (c j)) (hF : ∀ j, LowDeg b (F j)) :
    homogeneousComponent (a + b) (∑ j ∈ s, c j * F j)
      = ∑ j ∈ s, homogeneousComponent a (c j) * homogeneousComponent b (F j) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => homogeneousComponent_mul_of_lowDeg (hc j) (hF j)

/-- Leading parts of a product over a finset. -/
theorem homogeneousComponent_prod_of_lowDeg {ι : Type*} {s : Finset ι}
    {f : ι → MvPolynomial σ ℝ} {k : ι → ℕ} (h : ∀ i ∈ s, LowDeg (k i) (f i)) :
    homogeneousComponent (∑ i ∈ s, k i) (∏ i ∈ s, f i)
      = ∏ i ∈ s, homogeneousComponent (k i) (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
        homogeneousComponent_mul_of_lowDeg (h a (Finset.mem_insert_self a s))
          (LowDeg.prod fun i hi => h i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

lemma homogeneousComponent_units_smul {k : ℕ} (u : ℤˣ) (p : MvPolynomial σ ℝ) :
    homogeneousComponent k (u • p) = u • homogeneousComponent k p := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [one_smul, one_smul]
  · have h1 : ((-1 : ℤˣ) • p) = -p := by
      rw [Units.smul_def]; simp
    have h2 : ((-1 : ℤˣ) • homogeneousComponent k p) = -homogeneousComponent k p := by
      rw [Units.smul_def]; simp
    rw [h1, h2, map_neg]

/-- **The determinant's leading part.**  If every entry of an `N × N` matrix has degree
`≥ 1`, the degree-`N` component of its determinant is the determinant of the degree-`1`
components.

This is what identifies `Δ = det K` as the leading part of `D = det U`, and — applied to
the adjugate's minors — gives `c̃`'s leading part as `Δ·c⁰`. -/
theorem homogeneousComponent_det_of_lowDeg {N : ℕ}
    {M : Matrix (Fin N) (Fin N) (MvPolynomial σ ℝ)} (hM : ∀ i j, LowDeg 1 (M i j)) :
    homogeneousComponent N M.det
      = (Matrix.of fun i j => homogeneousComponent 1 (M i j)).det := by
  classical
  rw [Matrix.det_apply, map_sum, Matrix.det_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [homogeneousComponent_units_smul]
  congr 1
  have hprod : homogeneousComponent (∑ _i : Fin N, 1) (∏ i : Fin N, M (τ i) i)
      = ∏ i : Fin N, homogeneousComponent 1 (M (τ i) i) :=
    homogeneousComponent_prod_of_lowDeg (k := fun _ => 1) fun i _ => hM (τ i) i
  simpa using hprod

/-- Row-wise version: with per-row degree bounds, the leading component of the determinant
is the determinant of the per-row leading components. -/
theorem homogeneousComponent_det_of_rows {N : ℕ}
    {M : Matrix (Fin N) (Fin N) (MvPolynomial σ ℝ)} {k : Fin N → ℕ}
    (hM : ∀ i j, LowDeg (k i) (M i j)) :
    homogeneousComponent (∑ i, k i) M.det
      = (Matrix.of fun i j => homogeneousComponent (k i) (M i j)).det := by
  classical
  rw [Matrix.det_apply, map_sum, Matrix.det_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [homogeneousComponent_units_smul]
  congr 1
  have hprod : homogeneousComponent (∑ i : Fin N, k (τ i)) (∏ i : Fin N, M (τ i) i)
      = ∏ i : Fin N, homogeneousComponent (k (τ i)) (M (τ i) i) :=
    homogeneousComponent_prod_of_lowDeg (k := fun i => k (τ i)) fun i _ => hM (τ i) i
  rwa [Equiv.sum_comp τ k] at hprod

lemma homogeneousComponent_zero_of_constant (a : ℝ) :
    homogeneousComponent 0 (C a : MvPolynomial σ ℝ) = C a := by
  rw [MvPolynomial.homogeneousComponent_zero, MvPolynomial.coeff_C]
  simp

/-- **The adjugate's leading part.**  Every entry of `adj M` has degree `≥ m`, and its
degree-`m` component is the corresponding entry of the adjugate of the leading parts.

Together with the Krylov identity this is what gives `c̃`'s leading part as `Δ·c⁰`. -/
theorem homogeneousComponent_adjugate {m : ℕ}
    {M : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial σ ℝ)}
    (hM : ∀ i j, LowDeg 1 (M i j)) (i j : Fin (m + 1)) :
    homogeneousComponent m (M.adjugate i j)
      = (Matrix.of fun a b => homogeneousComponent 1 (M a b)).adjugate i j := by
  classical
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  have hrow : ∀ a b : Fin (m + 1),
      LowDeg (if a = j then 0 else 1) ((M.updateRow j (Pi.single i 1)) a b) := by
    intro a b
    by_cases hab : a = j
    · simp [hab]
    · simpa [Matrix.updateRow_ne hab, hab] using hM a b
  have hsum : (∑ a : Fin (m + 1), if a = j then 0 else 1) = m := by
    simp [Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem]
  have hdet := homogeneousComponent_det_of_rows
    (k := fun a => if a = j then 0 else 1) hrow
  rw [hsum] at hdet
  rw [hdet]
  congr 1
  ext a b
  by_cases hab : a = j
  · subst hab
    simp only [Matrix.of_apply, if_pos rfl, Matrix.updateRow_self]
    by_cases hbi : b = i
    · subst hbi
      simpa using homogeneousComponent_zero_of_constant (σ := σ) 1
    · simp [Pi.single_apply, hbi]
  · simp [Matrix.of_apply, if_neg hab, Matrix.updateRow_ne hab]

/-- Components below the guaranteed degree vanish. -/
theorem homogeneousComponent_eq_zero_of_lowDeg {j k : ℕ} {P : MvPolynomial σ ℝ}
    (hP : LowDeg k P) (hjk : j < k) : homogeneousComponent j P = 0 := by
  classical
  ext d
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_zero]
  by_cases hd : Finsupp.degree d = j
  · rw [if_pos hd]
    by_contra hne
    have := hP d (MvPolynomial.mem_support_iff.mpr hne)
    omega
  · rw [if_neg hd]

/-- **The next order.**  For `p` of degree `≥ a` and `q` of degree `≥ b`, the
degree-`(a+b+1)` component of `pq` has exactly two contributions.  This is what produces
`Ñ`'s degree-`(n+2)` part as `∑_j (E_j·Aʲx + Δ·c⁰_j·g_j⁽²⁾)`. -/
theorem homogeneousComponent_mul_succ {a b : ℕ} {p q : MvPolynomial σ ℝ}
    (hp : LowDeg a p) (hq : LowDeg b q) :
    homogeneousComponent (a + b + 1) (p * q)
      = homogeneousComponent a p * homogeneousComponent (b + 1) q
        + homogeneousComponent (a + 1) p * homogeneousComponent b q := by
  classical
  ext d
  rw [coeff_homogeneousComponent, MvPolynomial.coeff_add, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, ← Finset.sum_add_distrib]
  by_cases hdeg : Finsupp.degree d = a + b + 1
  · rw [if_pos hdeg]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hsum : Finsupp.degree x.1 + Finsupp.degree x.2 = a + b + 1 := by
      rw [← map_add Finsupp.degree, hx', hdeg]
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent,
      coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases h1 : coeff x.1 p = 0
    · simp [h1]
    by_cases h2 : coeff x.2 q = 0
    · simp [h2]
    have hd1 : a ≤ Finsupp.degree x.1 := hp _ (MvPolynomial.mem_support_iff.mpr h1)
    have hd2 : b ≤ Finsupp.degree x.2 := hq _ (MvPolynomial.mem_support_iff.mpr h2)
    -- the degrees are (a, b+1) or (a+1, b)
    by_cases e1 : Finsupp.degree x.1 = a
    · have e2 : Finsupp.degree x.2 = b + 1 := by omega
      rw [if_pos e1, if_pos e2, if_neg (by omega : Finsupp.degree x.1 ≠ a + 1),
        if_neg (by omega : Finsupp.degree x.2 ≠ b)]
      ring
    · have e1' : Finsupp.degree x.1 = a + 1 := by omega
      have e2 : Finsupp.degree x.2 = b := by omega
      rw [if_neg e1, if_neg (by omega : Finsupp.degree x.2 ≠ b + 1), if_pos e1', if_pos e2]
      ring
  · rw [if_neg hdeg]
    refine (Finset.sum_eq_zero fun x hx => ?_).symm
    have hx' : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent,
      coeff_homogeneousComponent, coeff_homogeneousComponent]
    have hdd : Finsupp.degree x.1 + Finsupp.degree x.2 = Finsupp.degree d := by
      rw [← map_add Finsupp.degree, hx']
    by_cases e1 : Finsupp.degree x.1 = a
    · by_cases e2 : Finsupp.degree x.2 = b + 1
      · exact absurd (by omega : Finsupp.degree d = a + b + 1) hdeg
      · by_cases e1' : Finsupp.degree x.1 = a + 1
        · omega
        · simp [e1', e2]
    · by_cases e1' : Finsupp.degree x.1 = a + 1
      · by_cases e2 : Finsupp.degree x.2 = b
        · exact absurd (by omega : Finsupp.degree d = a + b + 1) hdeg
        · simp [e1, e2]
      · simp [e1, e1']

/-- A homogeneous component has the degree it names. -/
theorem lowDeg_homogeneousComponent (k : ℕ) (P : MvPolynomial σ ℝ) :
    LowDeg k (homogeneousComponent k P) := by
  classical
  intro d hd
  by_cases hdk : Finsupp.degree d = k
  · exact le_of_eq hdk.symm
  · exfalso
    rw [MvPolynomial.mem_support_iff, coeff_homogeneousComponent, if_neg hdk] at hd
    exact hd rfl

end MPE
