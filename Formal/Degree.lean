import Mathlib

/-!
# Degree counting for the MPE construction

The remaining input to `CycleData.hN` and `SharpBound.bound` is the observation that, for
polynomial `f` with `f(0) = 0`, the cleared numerator `Ñ` has no monomials of degree below
`n + 2`:

* every entry of `U` vanishes at `0`, so has degree `≥ 1`;
* hence `D = det U` has degree `≥ n`, and each entry of `adj U` degree `≥ n - 1`;
* hence `c̃ = adj(U)(-uₙ)` has degree `≥ n`, and `Ñ = ∑_j c̃_j f^j` degree `≥ n + 1`;
* the degree-`(n+1)` part then vanishes by Cayley–Hamilton (`MPE.krylov_charpoly_combination`).

This file proves the degree bookkeeping — the first three bullets — as reusable lemmas
about `MvPolynomial`.  `LowDeg k p` says every monomial of `p` has total degree at least
`k`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace MPE

open MvPolynomial Finset

variable {σ : Type*} [DecidableEq σ]

/-- Every monomial of `p` has total degree at least `k`.  (`Finsupp.degree` of an exponent
vector is the total degree of the corresponding monomial.) -/
def LowDeg (k : ℕ) (p : MvPolynomial σ ℝ) : Prop :=
  ∀ d ∈ p.support, k ≤ d.degree

lemma LowDeg.mono {j k : ℕ} {p : MvPolynomial σ ℝ} (h : LowDeg k p) (hjk : j ≤ k) :
    LowDeg j p := fun d hd => le_trans hjk (h d hd)

@[simp] lemma lowDeg_zero (p : MvPolynomial σ ℝ) : LowDeg 0 p := fun _ _ => Nat.zero_le _

lemma lowDeg_of_zero (k : ℕ) : LowDeg k (0 : MvPolynomial σ ℝ) := by
  intro d hd; simp at hd

/-- A sum of polynomials each of low degree `≥ k` has low degree `≥ k`. -/
lemma LowDeg.add {k : ℕ} {p q : MvPolynomial σ ℝ} (hp : LowDeg k p) (hq : LowDeg k q) :
    LowDeg k (p + q) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hp d h
  · exact hq d h

lemma LowDeg.neg {k : ℕ} {p : MvPolynomial σ ℝ} (hp : LowDeg k p) : LowDeg k (-p) := by
  intro d hd
  exact hp d (by simpa using hd)

lemma LowDeg.sub {k : ℕ} {p q : MvPolynomial σ ℝ} (hp : LowDeg k p) (hq : LowDeg k q) :
    LowDeg k (p - q) := by
  rw [sub_eq_add_neg]; exact hp.add hq.neg

lemma LowDeg.sum {k : ℕ} {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ ℝ}
    (h : ∀ i ∈ s, LowDeg k (f i)) : LowDeg k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using lowDeg_of_zero k
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Degrees add under multiplication. -/
lemma LowDeg.mul {a b : ℕ} {p q : MvPolynomial σ ℝ} (hp : LowDeg a p) (hq : LowDeg b q) :
    LowDeg (a + b) (p * q) := by
  intro d hd
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  calc a + b ≤ d₁.degree + d₂.degree := Nat.add_le_add (hp d₁ hd₁) (hq d₂ hd₂)
    _ = (d₁ + d₂).degree := (map_add Finsupp.degree d₁ d₂).symm

/-- A product over a finset: degrees add. -/
lemma LowDeg.prod {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ ℝ} {k : ι → ℕ}
    (h : ∀ i ∈ s, LowDeg (k i) (f i)) :
    LowDeg (∑ i ∈ s, k i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma LowDeg.units_smul {k : ℕ} {p : MvPolynomial σ ℝ} (u : ℤˣ) (hp : LowDeg k p) :
    LowDeg k (u • p) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using hp
  · have : ((-1 : ℤˣ) : ℤ) • p = -p := by simp
    simpa [this] using hp.neg

/-- **The determinant bound.**  If every entry of an `n × n` matrix vanishes at the origin
(degree `≥ 1`), then its determinant has degree `≥ n`.

This is the step that gives `D = det U` degree `≥ n`, hence `Δ` its leading part. -/
theorem LowDeg.det {n : ℕ} {M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)}
    (hM : ∀ i j, LowDeg 1 (M i j)) : LowDeg n M.det := by
  classical
  rw [Matrix.det_apply]
  refine LowDeg.sum fun τ _ => LowDeg.units_smul _ ?_
  have hprod : LowDeg (∑ _i : Fin n, 1) (∏ i : Fin n, M (τ i) i) :=
    LowDeg.prod (k := fun _ => 1) fun i _ => hM (τ i) i
  simpa using hprod

/-- **Determinant bound, row-wise.**  If every entry of row `i` has degree at least `k i`,
then `det` has degree at least `∑ i, k i`.  (The permutation reindexes the sum.) -/
theorem LowDeg.det_of_rows {n : ℕ} {M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ)}
    {k : Fin n → ℕ} (hM : ∀ i j, LowDeg (k i) (M i j)) : LowDeg (∑ i, k i) M.det := by
  classical
  rw [Matrix.det_apply]
  refine LowDeg.sum fun τ _ => LowDeg.units_smul _ ?_
  have hprod : LowDeg (∑ i : Fin n, k (τ i)) (∏ i : Fin n, M (τ i) i) :=
    LowDeg.prod (k := fun i => k (τ i)) fun i _ => hM (τ i) i
  rwa [Equiv.sum_comp τ k] at hprod

/-- **The adjugate bound.**  If every entry of an `(m+1) × (m+1)` matrix has degree `≥ 1`,
every entry of its adjugate has degree `≥ m`: one row is replaced by a constant vector, the
remaining `m` rows still contribute. -/
theorem LowDeg.adjugate {m : ℕ} {M : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial σ ℝ)}
    (hM : ∀ i j, LowDeg 1 (M i j)) (i j : Fin (m + 1)) :
    LowDeg m (M.adjugate i j) := by
  classical
  rw [Matrix.adjugate_apply]
  have hrow : ∀ a b : Fin (m + 1),
      LowDeg (if a = j then 0 else 1) ((M.updateRow j (Pi.single i 1)) a b) := by
    intro a b
    by_cases hab : a = j
    · simp [hab]
    · simpa [Matrix.updateRow_ne hab, hab] using hM a b
  have := LowDeg.det_of_rows (k := fun a => if a = j then 0 else 1) hrow
  have hsum : (∑ a : Fin (m + 1), if a = j then 0 else 1) = m := by
    simp [Finset.sum_ite, Finset.filter_ne', Finset.card_erase_of_mem]
  rwa [hsum] at this

/-! ### From degrees to norms -/

/-- **The analytic consequence.**  A polynomial all of whose monomials have degree at least
`k` is `O(‖y‖^k)` on the unit ball, with the explicit constant `∑|coeff|`.

This is the bridge from the degree bookkeeping to the bound `‖Ñ(y)‖ ≤ M‖y‖^(d+2)` that
`CycleData.hN` asserts. -/
theorem LowDeg.abs_eval_le {n k : ℕ} {P : MvPolynomial (Fin n) ℝ} (hP : LowDeg k P)
    (y : Fin n → ℝ) (hy : ‖y‖ ≤ 1) :
    |MvPolynomial.eval y P| ≤ (∑ d ∈ P.support, |MvPolynomial.coeff d P|) * ‖y‖ ^ k := by
  classical
  have hy0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  rw [MvPolynomial.eval_eq]
  calc |∑ d ∈ P.support, MvPolynomial.coeff d P * ∏ i ∈ d.support, y i ^ d i|
      ≤ ∑ d ∈ P.support, |MvPolynomial.coeff d P * ∏ i ∈ d.support, y i ^ d i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.support, |MvPolynomial.coeff d P| * ‖y‖ ^ k := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        -- the monomial is at most ‖y‖ ^ (degree d) ≤ ‖y‖ ^ k
        have hmono : |∏ i ∈ d.support, y i ^ d i| ≤ ‖y‖ ^ d.degree := by
          rw [Finset.abs_prod]
          calc ∏ i ∈ d.support, |y i ^ d i|
              = ∏ i ∈ d.support, |y i| ^ d i := by
                exact Finset.prod_congr rfl fun i _ => abs_pow _ _
            _ ≤ ∏ i ∈ d.support, ‖y‖ ^ d i := by
                refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
                exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm y i) _
            _ = ‖y‖ ^ (∑ i ∈ d.support, d i) := Finset.prod_pow_eq_pow_sum _ _ _
            _ = ‖y‖ ^ d.degree := by rw [Finsupp.degree_apply]
        exact hmono.trans (pow_le_pow_of_le_one hy0 hy (hP d hd))
    _ = (∑ d ∈ P.support, |MvPolynomial.coeff d P|) * ‖y‖ ^ k := by
        rw [Finset.sum_mul]

/-- **The matrix-vector step.**  `c̃ = adj(U) *ᵥ (-uₙ)`: degrees add.  With `adj U` of
degree `≥ m` and `uₙ` of degree `≥ 1`, this gives `c̃` degree `≥ m + 1 = n`. -/
theorem LowDeg.mulVec {N : ℕ} {A : Matrix (Fin N) (Fin N) (MvPolynomial σ ℝ)}
    {v : Fin N → MvPolynomial σ ℝ} {a b : ℕ}
    (hA : ∀ i j, LowDeg a (A i j)) (hv : ∀ j, LowDeg b (v j)) (i : Fin N) :
    LowDeg (a + b) (A.mulVec v i) := by
  classical
  show LowDeg (a + b) (∑ j, A i j * v j)
  exact LowDeg.sum fun j _ => (hA i j).mul (hv j)

/-- **The final degree count.**  `Ñ = ∑_j c̃_j · f^j` with `c̃_j` of degree `≥ n` and `f^j`
of degree `≥ 1` has degree `≥ n + 1`.  (The remaining order, to `n + 2`, comes from the
Cayley–Hamilton cancellation, `MPE.krylov_charpoly_combination`.) -/
theorem LowDeg.weighted_sum {N a b : ℕ} {c : Fin N → MvPolynomial σ ℝ}
    {F : Fin N → MvPolynomial σ ℝ}
    (hc : ∀ j, LowDeg a (c j)) (hF : ∀ j, LowDeg b (F j)) :
    LowDeg (a + b) (∑ j, c j * F j) :=
  LowDeg.sum fun j _ => (hc j).mul (hF j)

/-- **The vector-valued bound**, as `CycleData.hN` needs it: a vector of polynomials all of
whose monomials have degree at least `k` satisfies `‖P(y)‖ ≤ C‖y‖^k` on the unit ball. -/
theorem LowDeg.norm_eval_le {n k : ℕ} {P : Fin n → MvPolynomial (Fin n) ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hP : ∀ l, LowDeg k (P l))
    (hC : ∀ l, (∑ d ∈ (P l).support, |MvPolynomial.coeff d (P l)|) ≤ C)
    (y : Fin n → ℝ) (hy : ‖y‖ ≤ 1) :
    ‖fun l => MvPolynomial.eval y (P l)‖ ≤ C * ‖y‖ ^ k := by
  have hy0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun l => ?_
  rw [Real.norm_eq_abs]
  calc |MvPolynomial.eval y (P l)|
      ≤ (∑ d ∈ (P l).support, |MvPolynomial.coeff d (P l)|) * ‖y‖ ^ k :=
        (hP l).abs_eval_le y hy
    _ ≤ C * ‖y‖ ^ k := by
        exact mul_le_mul_of_nonneg_right (hC l) (by positivity)

/-! ### Constant matrices, and the final order

An invertible matrix of *scalars* neither creates nor destroys low-degree monomials.  This
is what lets the last order of `Ñ` be recovered from the exact self-consistency relation,
without any leading-part analysis of the adjugate.
-/

/-- Multiplying by a constant matrix preserves low degree. -/
lemma LowDeg.const_mulVec {N k : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    {v : Fin N → MvPolynomial σ ℝ} (hv : ∀ i, LowDeg k (v i)) (i : Fin N) :
    LowDeg k ((M.map (MvPolynomial.C (σ := σ))).mulVec v i) := by
  have h := LowDeg.mulVec (A := M.map (MvPolynomial.C (σ := σ))) (v := v) (a := 0) (b := k)
    (fun _ _ => lowDeg_zero _) hv i
  simpa using h

/-- **Cancelling an invertible constant matrix.**  If `M` is invertible over `ℝ` and
`M · T` has degree `≥ k`, then so does `T`.

This is what recovers the last order of `Ñ` from the exact self-consistency relation,
with no leading-part analysis of the adjugate: `(A-I)T` has degree `≥ n+2` because
`c̃_j` has degree `≥ n` and the quadratic parts have degree `≥ 2`, and `A - I` is
invertible by the standing assumption `1 ∉ spec A`. -/
theorem LowDeg.of_mulVec_of_isUnit {N k : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    (hM : IsUnit M) {T : Fin N → MvPolynomial σ ℝ}
    (h : ∀ i, LowDeg k ((M.map (MvPolynomial.C (σ := σ))).mulVec T i)) (i : Fin N) :
    LowDeg k (T i) := by
  classical
  obtain ⟨N', hN'⟩ := hM.exists_right_inv
  have hNM : N' * M = 1 := mul_eq_one_comm.mp hN'
  have hinv : (N'.map (MvPolynomial.C (σ := σ))) * (M.map (MvPolynomial.C (σ := σ)))
      = 1 := by
    rw [← Matrix.map_mul, hNM]
    ext a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  have hT : T = (N'.map (MvPolynomial.C (σ := σ))).mulVec
      ((M.map (MvPolynomial.C (σ := σ))).mulVec T) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [hT]
  exact LowDeg.const_mulVec N' h i

/-- **Lemma 4.1(iii), the degree count — the capstone.**

Write `f^j = A^j x + g_j` with `g_j` of degree `≥ 2`, and let `T = ∑_j c̃_j A^j x` be the
linear-part contribution to `Ñ`, so that `Ñ = T + ∑_j c̃_j g_j`.  The exact
self-consistency relation `∑_j c̃_j u_j = 0` reads

    (A - I) · T = -∑_j c̃_j (g_{j+1} - g_j).

Its right-hand side has degree `≥ k + 2` because `c̃_j` has degree `≥ k` and the `g_j`
degree `≥ 2`; since `A - I` is invertible, `T` has degree `≥ k + 2` too, and hence so does
`Ñ`.

With `k = n` (from `LowDeg.det` and `LowDeg.adjugate`) this is exactly
`‖Ñ(y)‖ = O(‖y‖^{n+2})`, the content of `CycleData.hN` — and it needs no leading-part
analysis of the adjugate. -/
theorem LowDeg.Ntilde {n k N : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit (A - 1))
    {ct : ℕ → MvPolynomial (Fin n) ℝ} {g : ℕ → Fin n → MvPolynomial (Fin n) ℝ}
    {T Ntil : Fin n → MvPolynomial (Fin n) ℝ}
    (hct : ∀ j, LowDeg k (ct j))
    (hg : ∀ j i, LowDeg 2 (g j i))
    (hcons : ∀ i, ((A - 1).map (MvPolynomial.C (σ := Fin n))).mulVec T i
        = -(∑ j ∈ Finset.range N, ct j * (g (j + 1) i - g j i)))
    (hNtil : ∀ i, Ntil i = T i + ∑ j ∈ Finset.range N, ct j * g j i) :
    ∀ i, LowDeg (k + 2) (Ntil i) := by
  -- the right-hand side of the self-consistency relation has degree ≥ k+2
  have hrhs : ∀ i, LowDeg (k + 2)
      (∑ j ∈ Finset.range N, ct j * (g (j + 1) i - g j i)) := by
    intro i
    refine LowDeg.sum (k := k + 2)
      (f := fun j => ct j * (g (j + 1) i - g j i)) ?_
    intro j _
    exact (hct j).mul ((hg (j + 1) i).sub (hg j i))
  -- hence so does (A-I)·T, hence so does T
  have hT : ∀ i, LowDeg (k + 2) (T i) := by
    refine LowDeg.of_mulVec_of_isUnit hA (fun i => ?_)
    rw [hcons i]
    exact (hrhs i).neg
  -- and the remaining sum too
  intro i
  rw [hNtil i]
  refine (hT i).add ?_
  refine LowDeg.sum (k := k + 2) (f := fun j => ct j * g j i) ?_
  intro j _
  exact (hct j).mul (hg j i)

end MPE
