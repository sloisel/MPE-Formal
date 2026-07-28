import Mathlib
import Formal.Smooth

/-!
# `Van` products and determinants at a general vanishing order

`Van.prod_fin`, `Van.prod_sub`, `Van.det` and `Van.det_sub` in `Formal/Smooth.lean` assume
each factor vanishes to order exactly `1` (`Van ρ 0 C`), which is the right shape for the
square window: there the matrix entries are the components of `u_j`, of size `O(r)`.

The general window needs the same lemmas one order up.  Its degeneracy form is
`Δ = det(UᵀU)`, and the entries of the Gram matrix are `O(r²)`, i.e. `Van ρ 1 C`.  Feeding
those to `Van.det_sub` as merely `Van ρ 0 C` would give `O(r^{k+2})` where the truth is
`O(r^{2k+1})` — far too weak for the margin analysis.

So this file carries the vanishing order `p` of each factor as a parameter.  A product of
`m+1` factors each `Van ρ p` is `Van ρ (m(p+1)+p)`, and if corresponding factors agree to
order `d+1` the products agree to order `m(p+1)+d+1`.  At `p = 0` these are the original
lemmas; at `p = 1` and `d = 2`, with `m+1 = k`, they give exactly the `O(r^{2k})` and
`O(r^{2k+1})` the Gram construction needs.
-/

namespace MPE

open Metric Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {ρ C C' : ℝ} {k k' : ℕ}

namespace Van

/-- **A product of `m+1` factors, each vanishing to order `p+1`.**  The product vanishes to
order `(m+1)(p+1)`, written `m(p+1)+p+1` to avoid a truncated subtraction. -/
lemma prod_fin_gen (hC : 0 ≤ C) (p : ℕ) : ∀ (m : ℕ) (a : Fin (m + 1) → E → ℝ),
    (∀ i, Van ρ p C (a i)) →
      Van ρ (m * (p + 1) + p) (2 ^ m * C ^ (m + 1)) (fun y => ∏ i, a i y) := by
  intro m
  induction m with
  | zero =>
      intro a ha
      have hfun : (fun y => ∏ i : Fin 1, a i y) = a 0 := by funext y; simp
      rw [hfun]
      simpa using ha 0
  | succ m ih =>
      intro a ha
      have htail := ih (fun i => a i.succ) (fun i => ha i.succ)
      have hstep := (ha 0).mul hC (by positivity) htail
      have hfun : (fun y => ∏ i : Fin (m + 1 + 1), a i y)
          = fun y => a 0 y * ∏ i : Fin (m + 1), a i.succ y := by
        funext y; rw [Fin.prod_univ_succ]
      rw [hfun]
      rw [show p + (m * (p + 1) + p) + 1 = (m + 1) * (p + 1) + p from by ring] at hstep
      refine hstep.mono_const (le_of_eq ?_)
      rw [pow_succ, pow_succ]
      ring

/-- **Comparison of products at order `p`.**  Two products of `m+1` factors, each vanishing
to order `p+1`, whose corresponding factors agree to order `d+1`, agree to order
`m(p+1)+d+1`. -/
lemma prod_sub_gen {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (p d : ℕ) :
    ∀ (m : ℕ) (a b : Fin (m + 1) → E → ℝ),
      (∀ i, Van ρ p C (a i)) → (∀ i, Van ρ p C (b i)) →
      (∀ i, Van ρ d D (fun y => a i y - b i y)) →
      ∃ K : ℝ, 0 ≤ K ∧ Van ρ (m * (p + 1) + d) K (fun y => (∏ i, a i y) - ∏ i, b i y) := by
  intro m
  induction m with
  | zero =>
      intro a b _ _ hab
      refine ⟨D, hD, ?_⟩
      have hfun : (fun y => (∏ i : Fin 1, a i y) - ∏ i : Fin 1, b i y)
          = fun y => a 0 y - b 0 y := by funext y; simp
      rw [hfun, Nat.zero_mul, Nat.zero_add]
      exact hab 0
  | succ m ih =>
      intro a b ha hb hab
      obtain ⟨K, hK, hAB⟩ := ih (fun i => a i.succ) (fun i => b i.succ)
        (fun i => ha i.succ) (fun i => hb i.succ) (fun i => hab i.succ)
      have hpc : (0:ℝ) ≤ 2 ^ m * C ^ (m + 1) := mul_nonneg (by positivity) (pow_nonneg hC _)
      have hprodA := Van.prod_fin_gen hC p m (fun i => a i.succ) (fun i => ha i.succ)
      have h1 := Van.mul hD hpc (hab 0) hprodA
      have h2 := Van.mul hC hK (hb 0) hAB
      rw [show d + (m * (p + 1) + p) + 1 = (m + 1) * (p + 1) + d from by ring] at h1
      rw [show p + (m * (p + 1) + d) + 1 = (m + 1) * (p + 1) + d from by ring] at h2
      refine ⟨2 * (D * (2 ^ m * C ^ (m + 1))) + 2 * (C * K), ?_, ?_⟩
      · have := mul_nonneg hD hpc
        have := mul_nonneg hC hK
        linarith
      · have hsum := h1.add h2
        have hfun : (fun y => (∏ i : Fin (m + 1 + 1), a i y) - ∏ i : Fin (m + 1 + 1), b i y)
            = fun y => (a 0 y - b 0 y) * (∏ i : Fin (m + 1), a i.succ y)
                + b 0 y * ((∏ i : Fin (m + 1), a i.succ y) - ∏ i : Fin (m + 1), b i.succ y) := by
          funext y
          rw [Fin.prod_univ_succ (fun i => a i y), Fin.prod_univ_succ (fun i => b i y)]
          ring
        rw [hfun]
        exact hsum

end Van

/-- **The determinant of a matrix whose entries vanish to order `p+1`.** -/
theorem Van.det_gen {ρ C : ℝ} {m p : ℕ} {M : Matrix (Fin (m + 1)) (Fin (m + 1)) (E → ℝ)}
    (hC : 0 ≤ C) (hM : ∀ i j, Van ρ p C (M i j)) :
    Van ρ (m * (p + 1) + p) ((m + 1).factorial * (1 * (2 ^ m * C ^ (m + 1))))
      (fun y => Matrix.det (fun i j => M i j y)) := by
  classical
  have hfun : (fun y => Matrix.det (fun i j => M i j y))
      = fun y => ∑ σ : Equiv.Perm (Fin (m + 1)),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i y := by
    funext y
    rw [Matrix.det_apply']
  rw [hfun]
  have hterm : ∀ σ : Equiv.Perm (Fin (m + 1)), σ ∈ Finset.univ →
      Van ρ (m * (p + 1) + p) (1 * (2 ^ m * C ^ (m + 1)))
        (fun y => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i y) := by
    intro σ _
    have hp := Van.prod_fin_gen hC p m (fun i => M (σ i) i) (fun i => hM (σ i) i)
    have habs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
    have := Van.const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ)) hp
    rwa [habs] at this
  have hsum := Van.sum (ρ := ρ) (k := m * (p + 1) + p) Finset.univ
    (mul_nonneg zero_le_one (mul_nonneg (by positivity) (pow_nonneg hC _))) hterm
  refine hsum.mono_const (le_of_eq ?_)
  congr 1
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- **Comparison of determinants at order `p`.**  Entries vanishing to order `p+1`, agreeing
to order `d+1`, give determinants agreeing to order `m(p+1)+d+1`.  With `p = 1`, `d = 2`
and `m + 1 = k` this is the `O(r^{2k+1})` that the general window needs. -/
theorem Van.det_sub_gen {ρ C D : ℝ} {m p d : ℕ}
    {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) (E → ℝ)}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : ∀ i j, Van ρ p C (M i j)) (hN : ∀ i j, Van ρ p C (N i j))
    (hMN : ∀ i j, Van ρ d D (fun y => M i j y - N i j y)) :
    ∃ K : ℝ, 0 ≤ K ∧ Van ρ (m * (p + 1) + d) K
      (fun y => Matrix.det (fun i j => M i j y) - Matrix.det (fun i j => N i j y)) := by
  classical
  choose K hK0 hKv using fun σ : Equiv.Perm (Fin (m + 1)) =>
    Van.prod_sub_gen (ρ := ρ) hC hD p d m (fun i => M (σ i) i) (fun i => N (σ i) i)
      (fun i => hM (σ i) i) (fun i => hN (σ i) i) (fun i => hMN (σ i) i)
  set Ktot : ℝ := ∑ σ : Equiv.Perm (Fin (m + 1)), K σ with hKtot
  have hKtot0 : 0 ≤ Ktot := Finset.sum_nonneg fun σ _ => hK0 σ
  have hle : ∀ σ : Equiv.Perm (Fin (m + 1)), K σ ≤ Ktot := fun σ =>
    Finset.single_le_sum (f := K) (fun τ _ => hK0 τ) (Finset.mem_univ σ)
  refine ⟨(Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ) * Ktot, by positivity, ?_⟩
  have hfun : (fun y => Matrix.det (fun i j => M i j y) - Matrix.det (fun i j => N i j y))
      = fun y => ∑ σ : Equiv.Perm (Fin (m + 1)),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((∏ i, M (σ i) i y) - ∏ i, N (σ i) i y) := by
    funext y
    rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [hfun]
  have hterm : ∀ σ : Equiv.Perm (Fin (m + 1)), σ ∈ Finset.univ →
      Van ρ (m * (p + 1) + d) Ktot
        (fun y => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((∏ i, M (σ i) i y) - ∏ i, N (σ i) i y)) := by
    intro σ _
    have habs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
    have h := Van.const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ)) (hKv σ)
    rw [habs, one_mul] at h
    exact h.mono_const (hle σ)
  have hsum := Van.sum (ρ := ρ) (k := m * (p + 1) + d) Finset.univ hKtot0 hterm
  refine hsum.mono_const (le_of_eq ?_)
  rw [Finset.card_univ]

end MPE
