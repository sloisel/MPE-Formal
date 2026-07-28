import Mathlib

/-!
# Sublevel sets of polynomials

The estimate Theorem 4.7 needs: on a convex body, the set where a polynomial of degree `≤ k`
is smaller than `ε` times its supremum has relative measure `O(ε^(1/k))`.

This is usually cited to Brudnyi–Ganzburg, whose route runs through a Chebyshev extremal
theorem.  The sharp constant is not needed here, and without it the estimate is elementary:

* `exists_sep` — a set of measure `μ` contains `N+1` points with pairwise gaps `≥ μ/(N+1)`,
  by the cumulative measure `t ↦ |E ∩ (-∞,t]|`, which is `1`-Lipschitz;
* `sublevel_one` — in one variable, the polynomial *is* its Lagrange interpolant at those
  points, all of which lie in the sublevel set, so the interpolation formula bounds the
  supremum by `ε M (2L/h)^k / k!` and forces `h` small;
* the several-variable case then follows by fibring over rays from a maximising point.

See `../../appendix2.tex` §9.
-/

namespace MPE

open MeasureTheory Set

/-! ### The cumulative measure -/

section Cum

/-- The measure of `E` to the left of `t`. -/
noncomputable def cum (E : Set ℝ) (t : ℝ) : ℝ := (volume (E ∩ Iic t)).toReal

variable {E : Set ℝ} {a b : ℝ}

lemma cum_ne_top (hsub : E ⊆ Icc a b) (t : ℝ) : volume (E ∩ Iic t) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (inter_subset_left.trans hsub))
  exact measure_Icc_lt_top.ne

/-- The increment of `cum` is exactly the measure of the slab. -/
lemma cum_sub_eq (hE : MeasurableSet E) (hsub : E ⊆ Icc a b) {s t : ℝ} (hst : s ≤ t) :
    cum E t - cum E s = (volume (E ∩ Ioc s t)).toReal := by
  have hdec : E ∩ Iic t = (E ∩ Iic s) ∪ (E ∩ Ioc s t) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_union, mem_Ioc]
    constructor
    · rintro ⟨hx, hxt⟩
      rcases le_or_gt x s with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h, hxt⟩
    · rintro (⟨hx, h⟩ | ⟨hx, _, h⟩)
      · exact ⟨hx, le_trans h hst⟩
      · exact ⟨hx, h⟩
  have hdisj : Disjoint (E ∩ Iic s) (E ∩ Ioc s t) := by
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    exact absurd hx'.2.1 (not_lt.mpr hx.2)
  have hm : volume (E ∩ Iic t) = volume (E ∩ Iic s) + volume (E ∩ Ioc s t) := by
    rw [hdec, measure_union hdisj ((hE.inter measurableSet_Ioc))]
  have hfin1 : volume (E ∩ Iic s) ≠ ⊤ := cum_ne_top hsub s
  have hfin2 : volume (E ∩ Ioc s t) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono inter_subset_right)
  have hsplit : cum E t = cum E s + (volume (E ∩ Ioc s t)).toReal := by
    rw [cum, cum, hm, ENNReal.toReal_add hfin1 hfin2]
  rw [hsplit]; ring

/-- Hence the increment is at most the width: `cum` is `1`-Lipschitz. -/
lemma cum_sub_le (hE : MeasurableSet E) (hsub : E ⊆ Icc a b) {s t : ℝ} (hst : s ≤ t) :
    cum E t - cum E s ≤ t - s := by
  rw [cum_sub_eq hE hsub hst]
  have hle : (volume (E ∩ Ioc s t)).toReal ≤ (volume (Ioc s t)).toReal :=
    ENNReal.toReal_mono measure_Ioc_lt_top.ne (measure_mono inter_subset_right)
  rwa [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ t - s)] at hle

lemma cum_mono (hE : MeasurableSet E) (hsub : E ⊆ Icc a b) : Monotone (cum E) := by
  intro s t hst
  have := cum_sub_le hE hsub hst
  have hm : volume (E ∩ Iic s) ≤ volume (E ∩ Iic t) :=
    measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.mpr hst))
  exact ENNReal.toReal_mono (cum_ne_top hsub t) hm

lemma continuous_cum (hE : MeasurableSet E) (hsub : E ⊆ Icc a b) : Continuous (cum E) := by
  refine Metric.continuous_iff.mpr fun x ε hε => ⟨ε, hε, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  rw [abs_lt] at hy
  rcases le_total y x with h | h
  · have h1 := cum_sub_le hE hsub h
    have h2 := cum_mono hE hsub h
    rw [abs_lt]
    exact ⟨by linarith [hy.1], by linarith⟩
  · have h1 := cum_sub_le hE hsub h
    have h2 := cum_mono hE hsub h
    rw [abs_lt]
    exact ⟨by linarith, by linarith [hy.2]⟩

lemma cum_le_bot (hsub : E ⊆ Icc a b) {t : ℝ} (ht : t < a) : cum E t = 0 := by
  have : E ∩ Iic t = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_and]
    intro hx hxt
    exact absurd hxt (not_le.mpr (lt_of_lt_of_le ht (hsub hx).1))
  rw [cum, this, measure_empty, ENNReal.toReal_zero]

lemma cum_top (hsub : E ⊆ Icc a b) {t : ℝ} (ht : b ≤ t) :
    cum E t = (volume E).toReal := by
  have : E ∩ Iic t = E := by
    refine inter_eq_left.mpr fun x hx => ?_
    exact le_trans (hsub hx).2 ht
  rw [cum, this]

end Cum

/-! ### Separated points in a set of positive measure -/

/-- **Appendix 2, Lemma 1.**  A closed set of measure `μ` inside a bounded interval contains
`N+1` points whose pairwise gaps are at least `(j-i)·μ/(N+1)`.

The points are the level crossings `sInf {t | c ≤ cum E t}` of the cumulative measure, which
is `1`-Lipschitz; that Lipschitz bound is exactly what converts a gap in measure into a gap
in position. -/
theorem exists_sep {E : Set ℝ} (hEcl : IsClosed E) {a b : ℝ} (hsub : E ⊆ Icc a b)
    {μ : ℝ} (hμ : μ ≤ (volume E).toReal) (hμ0 : 0 < μ) (N : ℕ) :
    ∃ t : ℕ → ℝ, (∀ j, t j ∈ E) ∧
      ∀ i j : ℕ, i ≤ j → j ≤ N → ((j : ℝ) - i) * (μ / (N + 1)) ≤ t j - t i := by
  classical
  have hE : MeasurableSet E := hEcl.measurableSet
  have hN1 : (0:ℝ) < N + 1 := by positivity
  set c : ℕ → ℝ := fun j => ((j : ℝ) + 1/2) * (μ / (N + 1)) with hcdef
  have hc0 : ∀ j, 0 < c j := fun j => by
    show (0:ℝ) < ((j : ℝ) + 1/2) * (μ / (N + 1))
    have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    positivity
  have hcN : ∀ j ≤ N, c j < μ := by
    intro j hj
    have hjN : (j : ℝ) ≤ N := Nat.cast_le.mpr hj
    show ((j:ℝ) + 1/2) * (μ / (N+1)) < μ
    rw [show ((j:ℝ) + 1/2) * (μ / (N+1)) = μ * (((j:ℝ)+1/2)/(N+1)) by ring]
    have hfrac : ((j:ℝ) + 1/2)/(N+1) < 1 := by rw [div_lt_one hN1]; linarith
    nlinarith [hμ0, hfrac]
  -- the level crossings of the cumulative measure
  set S : ℕ → Set ℝ := fun j => {x | c j ≤ cum E x} with hSdef
  have hSclosed : ∀ j, IsClosed (S j) :=
    fun j => isClosed_le continuous_const (continuous_cum hE hsub)
  have hSne : ∀ j ≤ N, (S j).Nonempty := by
    intro j hj
    refine ⟨b, ?_⟩
    show c j ≤ cum E b
    rw [cum_top hsub (le_refl b)]
    linarith [hcN j hj, hμ]
  have hSbdd : ∀ j, BddBelow (S j) := by
    intro j
    refine ⟨a, fun x hx => ?_⟩
    by_contra hlt
    push Not at hlt
    have : cum E x = 0 := cum_le_bot hsub hlt
    have hx' : c j ≤ cum E x := hx
    rw [this] at hx'
    linarith [hc0 j]
  set t : ℕ → ℝ := fun j => if j ≤ N then sInf (S j) else b with htdef
  -- `t j` lies in `S j`, and `cum E (t j) ≤ c j` by approaching from the left
  have hmem : ∀ j ≤ N, t j ∈ S j := by
    intro j hj
    show (if j ≤ N then sInf (S j) else b) ∈ S j
    rw [if_pos hj]
    exact (hSclosed j).csInf_mem (hSne j hj) (hSbdd j)
  have hlow : ∀ j ≤ N, ∀ x < t j, cum E x < c j := by
    intro j hj x hx
    by_contra hge
    push Not at hge
    have : sInf (S j) ≤ x := csInf_le (hSbdd j) hge
    rw [htdef] at hx
    simp only [if_pos hj] at hx
    linarith
  have hupp : ∀ j ≤ N, cum E (t j) ≤ c j := by
    intro j hj
    have hlim : Filter.Tendsto (cum E) (nhdsWithin (t j) (Iio (t j))) (nhds (cum E (t j))) :=
      ((continuous_cum hE hsub).continuousAt).continuousWithinAt
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hlow j hj x hx).le
  -- points of `E` accumulate at `t j` from the left, and `E` is closed
  have hmemE : ∀ j ≤ N, t j ∈ E := by
    intro j hj
    rw [← hEcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have hle : t j - ε/2 ≤ t j := by linarith
    have hpos : 0 < (volume (E ∩ Ioc (t j - ε/2) (t j))).toReal := by
      rw [← cum_sub_eq hE hsub hle]
      have h1 := hlow j hj (t j - ε/2) (by linarith)
      have h2 : c j ≤ cum E (t j) := hmem j hj
      linarith
    have hne : (E ∩ Ioc (t j - ε/2) (t j)).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, measure_empty, ENNReal.toReal_zero] at hpos
      exact lt_irrefl 0 hpos
    obtain ⟨y, hyE, hy1, hy2⟩ := hne
    exact ⟨y, hyE, by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith⟩
  have hcmono : ∀ i j : ℕ, i ≤ j → c i ≤ c j := by
    intro i j hij
    show ((i:ℝ) + 1/2) * (μ / (N + 1)) ≤ ((j:ℝ) + 1/2) * (μ / (N + 1))
    have : (i:ℝ) ≤ j := Nat.cast_le.mpr hij
    have hq : 0 ≤ μ / (N+1) := by positivity
    nlinarith
  refine ⟨fun j => t (min j N), fun j => hmemE _ (min_le_right _ _), ?_⟩
  intro i j hij hjN
  have hiN : i ≤ N := le_trans hij hjN
  show ((j:ℝ) - i) * (μ / (N + 1)) ≤ t (min j N) - t (min i N)
  rw [min_eq_left hiN, min_eq_left hjN]
  have hSsub : S j ⊆ S i := fun x hx => le_trans (hcmono i j hij) hx
  have htij : t i ≤ t j := by
    show (if i ≤ N then sInf (S i) else b) ≤ (if j ≤ N then sInf (S j) else b)
    rw [if_pos hiN, if_pos hjN]
    exact csInf_le_csInf (hSbdd i) (hSne j hjN) hSsub
  have h1 := cum_sub_le hE hsub htij
  have h2 : c j ≤ cum E (t j) := hmem j hjN
  have h3 : cum E (t i) ≤ c i := hupp i hiN
  have hcdiff : c j - c i = ((j:ℝ) - i) * (μ / (N + 1)) := by
    show ((j:ℝ) + 1/2) * (μ / (N + 1)) - ((i:ℝ) + 1/2) * (μ / (N + 1)) = _
    ring
  linarith

/-! ### The one-variable sublevel bound -/

/-- **Appendix 2, Lemma 2.**  If a polynomial of degree `≤ k` is at most `ε M` on a set `S`
inside `[a,b]`, while reaching `M` somewhere in `[a,b]`, then `|S|` is small:
`|S|^k ≤ ε (k+1)^(k+1) (b-a)^k`, i.e. `|S| = O(ε^(1/k))`.

The polynomial *is* its Lagrange interpolant at `k+1` points of `S`, which `exists_sep`
supplies with pairwise gaps `≥ |S|/(k+1)`; the interpolation formula at the maximising point
then bounds `M` by `ε M` times a product controlled by those gaps.

The constant is cruder than the `2(k+1)/(k!)^{1/k}` of `appendix2.tex` — each factor of the
denominator is bounded below by one gap rather than by `|i-j|` gaps — which costs a factor
growing in `k` and saves the factorial bookkeeping.  In the application `k` is the fixed
degree of `Q̃`, so only the exponent `1/k` matters. -/
theorem sublevel_one {k : ℕ} (hk : 0 < k) (φ : Polynomial ℝ) (hdeg : φ.natDegree ≤ k)
    {a b M ε : ℝ} (hab : a ≤ b) (hM0 : 0 < M) (hε0 : 0 < ε)
    (xM : ℝ) (hxmem : xM ∈ Icc a b) (hxMax : M ≤ |φ.eval xM|) :
    ((volume {x | x ∈ Icc a b ∧ |φ.eval x| ≤ ε * M}).toReal) ^ k
      ≤ ε * ((k : ℝ) + 1) ^ (k + 1) * (b - a) ^ k := by
  classical
  set S : Set ℝ := {x | x ∈ Icc a b ∧ |φ.eval x| ≤ ε * M} with hSdef
  set μ : ℝ := (volume S).toReal with hμdef
  have hμnn : 0 ≤ μ := ENNReal.toReal_nonneg
  have hL : 0 ≤ b - a := by linarith
  rcases eq_or_lt_of_le hμnn with hμ0 | hμ0
  · rw [← hμ0, zero_pow hk.ne']
    positivity
  -- the sublevel set is closed and lives in `[a,b]`
  have hScl : IsClosed S := by
    have h1 : Continuous fun x : ℝ => |φ.eval x| := φ.continuous_aeval.abs
    exact (isClosed_Icc.inter (isClosed_le h1 continuous_const))
  have hSsub : S ⊆ Icc a b := fun x hx => hx.1
  obtain ⟨t, htS, htgap⟩ := exists_sep hScl hSsub (le_refl μ) hμ0 k
  set h : ℝ := μ / ((k : ℝ) + 1) with hhdef
  have hk1 : (0:ℝ) < (k : ℝ) + 1 := by positivity
  have hh0 : 0 < h := by rw [hhdef]; positivity
  -- the nodes are separated, hence distinct
  have hsep : ∀ i j : ℕ, i < j → j ≤ k → h ≤ t j - t i := by
    intro i j hij hjk
    have := htgap i j hij.le hjk
    have hji : (1:ℝ) ≤ (j : ℝ) - i := by
      have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
      linarith
    rw [hhdef]
    nlinarith [this, hji, hh0]
  set s : Finset ℕ := Finset.range (k + 1) with hsdef
  have hinj : Set.InjOn t s := by
    intro i hi j hj hij
    rw [hsdef, Finset.coe_range, mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hsep i j hlt (by omega); rw [hij] at this; linarith
    · have := hsep j i hlt (by omega); rw [hij] at this; linarith
  -- `φ` is its own interpolant at these `k+1` nodes
  have hcard : (s.card : ℕ) = k + 1 := by rw [hsdef, Finset.card_range]
  have hdeglt : φ.degree < s.card := by
    rw [hcard]
    exact lt_of_le_of_lt (Polynomial.degree_le_natDegree.trans
      (by exact_mod_cast Nat.cast_le.mpr hdeg)) (by exact_mod_cast Nat.lt_succ_self k)
  have hinterp := Lagrange.eq_interpolate (v := t) (s := s) hinj hdeglt
  -- bound each Lagrange basis polynomial at the maximising point
  have hbasis : ∀ i ∈ s, |(Lagrange.basis s t i).eval xM| ≤ (b - a) ^ k / h ^ k := by
    intro i hi
    have hcard' : (s.erase i).card = k := by
      rw [Finset.card_erase_of_mem hi, hcard]
      omega
    have heval : (Lagrange.basis s t i).eval xM
        = ∏ j ∈ s.erase i, (t i - t j)⁻¹ * (xM - t j) := by
      rw [Lagrange.basis, Polynomial.eval_prod]
      exact Finset.prod_congr rfl fun j _ => by
        rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [heval, Finset.abs_prod]
    have hterm : ∀ j ∈ s.erase i, |(t i - t j)⁻¹ * (xM - t j)| ≤ (b - a) / h := by
      intro j hj
      have hjne : j ≠ i := Finset.ne_of_mem_erase hj
      have hjs : j ∈ s := Finset.mem_of_mem_erase hj
      rw [hsdef, Finset.mem_range] at hi hjs
      have hgap : h ≤ |t i - t j| := by
        rcases lt_or_gt_of_ne hjne with hlt | hlt
        · have := hsep j i hlt (by omega)
          rw [abs_of_nonneg (by linarith)]; linarith
        · have := hsep i j hlt (by omega)
          rw [abs_of_nonpos (by linarith), neg_sub]; linarith
      have hnum : |xM - t j| ≤ b - a := by
        have h1 := htS j
        have h2 : t j ∈ Icc a b := hSsub h1
        rw [abs_le]
        constructor <;> [linarith [hxmem.1, h2.2]; linarith [hxmem.2, h2.1]]
      rw [abs_mul, abs_inv]
      rw [div_eq_mul_inv, mul_comm]
      refine mul_le_mul hnum ?_ (by positivity) hL
      exact inv_anti₀ hh0 hgap
    calc ∏ j ∈ s.erase i, |(t i - t j)⁻¹ * (xM - t j)|
        ≤ ∏ _j ∈ s.erase i, ((b - a) / h) :=
          Finset.prod_le_prod (fun j _ => abs_nonneg _) hterm
      _ = ((b - a) / h) ^ k := by rw [Finset.prod_const, hcard']
      _ = (b - a) ^ k / h ^ k := by rw [div_pow]
  -- the interpolation bound at `xM`
  have hMbd : M ≤ ε * M * (((k : ℝ) + 1) * ((b - a) ^ k / h ^ k)) := by
    have hev : φ.eval xM = ∑ i ∈ s, φ.eval (t i) * (Lagrange.basis s t i).eval xM := by
      conv_lhs => rw [hinterp]
      rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_mul, Polynomial.eval_C]
    have habs : |φ.eval xM| ≤ ∑ i ∈ s, (ε * M) * ((b - a) ^ k / h ^ k) := by
      rw [hev]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i hi => ?_)
      rw [abs_mul]
      exact mul_le_mul (htS i).2 (hbasis i hi) (abs_nonneg _) (by positivity)
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at habs
    have : ((k : ℕ) + 1 : ℝ) = (k : ℝ) + 1 := by ring
    calc M ≤ |φ.eval xM| := hxMax
      _ ≤ ((k + 1 : ℕ) : ℝ) * ((ε * M) * ((b - a) ^ k / h ^ k)) := habs
      _ = ε * M * (((k : ℝ) + 1) * ((b - a) ^ k / h ^ k)) := by push_cast; ring
  -- unwind
  have hhk : 0 < h ^ k := pow_pos hh0 k
  have hkey : h ^ k ≤ ε * ((k : ℝ) + 1) * (b - a) ^ k := by
    refine le_of_mul_le_mul_left ?_ hM0
    calc M * h ^ k
        ≤ (ε * M * (((k : ℝ) + 1) * ((b - a) ^ k / h ^ k))) * h ^ k :=
          mul_le_mul_of_nonneg_right hMbd hhk.le
      _ = M * (ε * ((k : ℝ) + 1) * (b - a) ^ k) := by field_simp
  have hμh : μ = ((k : ℝ) + 1) * h := by rw [hhdef]; field_simp
  rw [hμh, mul_pow]
  calc ((k : ℝ) + 1) ^ k * h ^ k
      ≤ ((k : ℝ) + 1) ^ k * (ε * ((k : ℝ) + 1) * (b - a) ^ k) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ε * ((k : ℝ) + 1) ^ (k + 1) * (b - a) ^ k := by rw [pow_succ]; ring

/-! ### The sublevel bound from the leading coefficient

For the application the polynomial is `Q̃`, which is *homogeneous*: along every line in a
fixed direction `v` the restriction has leading coefficient `Q̃(v)`, the same for all lines.
That makes a bound in terms of the leading coefficient — rather than the supremum — the
useful one, and it has a shorter proof: factor over `ℂ` and cover the sublevel set by `d`
intervals around the real parts of the roots. -/

/-- If every entry of a multiset of reals is at least `ρ ≥ 0`, the product is at least
`ρ ^ card`.  (`Multiset.prod_map_le_prod_map` does not apply: `ℝ` is not `MulLeftMono`.) -/
lemma pow_card_le_prod' {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ m : Multiset ℝ, (∀ y ∈ m, ρ ≤ y) → ρ ^ (Multiset.card m) ≤ m.prod := by
  intro m
  refine Multiset.induction_on m (by simp) ?_
  intro a t ih h
  have ha : ρ ≤ a := h a (Multiset.mem_cons_self a t)
  have ht : ∀ y ∈ t, ρ ≤ y := fun y hy => h y (Multiset.mem_cons_of_mem hy)
  have hprod : ρ ^ (Multiset.card t) ≤ t.prod := ih ht
  have h1 : (0:ℝ) ≤ ρ ^ (Multiset.card t) := by positivity
  rw [Multiset.card_cons, Multiset.prod_cons, pow_succ]
  nlinarith [ha, hprod, h1, hρ]

/-- `‖·‖` is multiplicative on `ℂ`, hence passes through a multiset product. -/
lemma norm_multiset_prod_complex (m : Multiset ℂ) :
    ‖m.prod‖ = (m.map fun z => ‖z‖).prod := by
  refine Multiset.induction_on m (by simp) ?_
  intro a s ih
  simp [ih]

open Polynomial in
/-- **The sublevel set of a polynomial, from its leading coefficient.**  If `p` has degree
`d ≥ 1` and leading coefficient `a`, then `{|p| ≤ s}` is covered by `d` intervals of radius
`2(s/|a|)^(1/d)` about the real parts of the complex roots, so has measure `≤ 4d(s/|a|)^(1/d)`.

Unlike `sublevel_one` this needs no maximising point, only the leading coefficient — which
is what makes it usable along a *fixed* direction for a homogeneous polynomial, where the
leading coefficient is the same on every line. -/
theorem sublevel_root {p : Polynomial ℝ} {d : ℕ} (hd : 0 < d) (hdeg : p.natDegree = d)
    {s : ℝ} (hs : 0 ≤ s) :
    volume {x : ℝ | |p.eval x| ≤ s}
      ≤ ENNReal.ofReal (4 * d * (s / |p.leadingCoeff|) ^ ((d : ℝ)⁻¹)) := by
  classical
  have hp0 : p ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
  have ha : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have haabs : 0 < |p.leadingCoeff| := abs_pos.mpr ha
  set ρ : ℝ := (s / |p.leadingCoeff|) ^ ((d : ℝ)⁻¹) with hρdef
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by positivity) _
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · -- `s = 0`: the sublevel set is the (finite) real root set
    have hsub : {x : ℝ | |p.eval x| ≤ s} ⊆ (p.roots.toFinset : Set ℝ) := by
      intro x hx
      have hz : p.eval x = 0 := by
        have h0 : |p.eval x| ≤ 0 := by rw [hs0]; exact hx
        exact abs_nonpos_iff.mp h0
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots').mpr ⟨hp0, hz⟩
    have hfin : {x : ℝ | |p.eval x| ≤ s}.Finite :=
      Set.Finite.subset (p.roots.toFinset).finite_toSet hsub
    rw [hfin.measure_zero]
    exact bot_le
  -- `s > 0`, so `ρ > 0`
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos (by positivity) _
  set q : Polynomial ℂ := p.map (algebraMap ℝ ℂ) with hqdef
  have hq0 : q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hp0
  have hqdeg : q.natDegree = d := by
    rw [hqdef, natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective, hdeg]
  have hcard : Multiset.card q.roots = q.natDegree :=
    (Polynomial.splits_iff_card_roots).mp (IsAlgClosed.splits q)
  have hcard' : Multiset.card q.roots = d := by rw [hcard, hqdeg]
  have hρd : ρ ^ d = s / |p.leadingCoeff| := by
    rw [hρdef, ← Real.rpow_natCast ((s / |p.leadingCoeff|) ^ ((d : ℝ)⁻¹)) d,
      ← Real.rpow_mul (by positivity), inv_mul_cancel₀ (by exact_mod_cast hd.ne'),
      Real.rpow_one]
  -- the sublevel set is covered by `d` intervals of radius `2ρ`
  have hcover : {x : ℝ | |p.eval x| ≤ s}
      ⊆ ⋃ z ∈ q.roots.toFinset, Icc (z.re - 2 * ρ) (z.re + 2 * ρ) := by
    intro x hx
    by_contra hnot
    simp only [mem_iUnion, mem_Icc, not_exists, not_and] at hnot
    have hfar : ∀ z ∈ q.roots, 2 * ρ ≤ ‖(x : ℂ) - z‖ := by
      intro z hz
      have hzt : z ∈ q.roots.toFinset := Multiset.mem_toFinset.mpr hz
      have hne := hnot z hzt
      have hre : 2 * ρ < |x - z.re| := by
        by_contra hle
        push Not at hle
        rw [abs_le] at hle
        exact hne (by linarith [hle.1]) (by linarith [hle.2])
      calc 2 * ρ ≤ |x - z.re| := hre.le
        _ = |((x : ℂ) - z).re| := by rw [Complex.sub_re, Complex.ofReal_re]
        _ ≤ ‖(x : ℂ) - z‖ := by simpa using RCLike.abs_re_le_norm ((x : ℂ) - z)
    -- the factorisation and the product bound
    have hmapeq : (Multiset.map (eval (x : ℂ) ∘ fun a => X - C a) q.roots)
        = (Multiset.map (fun z => (x : ℂ) - z) q.roots) :=
      Multiset.map_congr rfl fun z _ => by simp
    have hfact : q.eval (x : ℂ)
        = q.leadingCoeff * (q.roots.map fun z => (x : ℂ) - z).prod := by
      conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
      rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, hmapeq]
    have hpx : ((p.eval x : ℝ) : ℂ) = q.eval (x : ℂ) := by
      rw [hqdef, eval_map]
      exact (eval₂_at_apply (algebraMap ℝ ℂ) x).symm
    have hlead : ‖q.leadingCoeff‖ = |p.leadingCoeff| := by
      rw [hqdef, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
      · simp
      · simp [ha]
    have hnorm : |p.eval x| = |p.leadingCoeff| * ‖(q.roots.map fun z => (x : ℂ) - z).prod‖ := by
      have h1 : |p.eval x| = ‖((p.eval x : ℝ) : ℂ)‖ := by simp
      rw [h1, hpx, hfact, norm_mul, hlead]
    have hprod : (2 * ρ) ^ d ≤ ‖(q.roots.map fun z => (x : ℂ) - z).prod‖ := by
      rw [norm_multiset_prod_complex, Multiset.map_map]
      have hall : ∀ y ∈ (q.roots.map ((fun z => ‖z‖) ∘ fun z => (x : ℂ) - z)),
          2 * ρ ≤ y := by
        intro y hy
        simp only [Multiset.mem_map, Function.comp_apply] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact hfar z hz
      have hpc := pow_card_le_prod' (by positivity : (0:ℝ) ≤ 2 * ρ) _ hall
      rwa [Multiset.card_map, hcard'] at hpc
    -- `(2ρ)^d = 2^d s/|a| ≥ 2 s/|a| > s/|a|`
    have h2d : (2 : ℝ) ≤ 2 ^ d := by
      calc (2:ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
    have hcontra : s < |p.eval x| := by
      rw [hnorm]
      have hstep : s < |p.leadingCoeff| * (2 * ρ) ^ d := by
        rw [mul_pow, hρd]
        have : |p.leadingCoeff| * (2 ^ d * (s / |p.leadingCoeff|)) = 2 ^ d * s := by
          field_simp
        rw [this]
        nlinarith [h2d, hs0]
      exact lt_of_lt_of_le hstep (mul_le_mul_of_nonneg_left hprod haabs.le)
    exact absurd hx (not_le.mpr hcontra)
  -- and the cover has measure at most `d · 4ρ`
  refine le_trans (measure_mono hcover) (le_trans (measure_biUnion_finset_le _ _) ?_)
  have hterm : ∀ z ∈ q.roots.toFinset,
      volume (Icc (z.re - 2 * ρ) (z.re + 2 * ρ)) ≤ ENNReal.ofReal (4 * ρ) := by
    intro z _
    rw [Real.volume_Icc]
    exact le_of_eq (by congr 1; ring)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcardle : (q.roots.toFinset.card : ℝ) ≤ d := by
    have h1 : q.roots.toFinset.card ≤ Multiset.card q.roots := Multiset.toFinset_card_le _
    rw [hcard'] at h1
    exact_mod_cast h1
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (q.roots.toFinset.card : ℝ) * (4 * ρ) ≤ (d : ℝ) * (4 * ρ) :=
        mul_le_mul_of_nonneg_right hcardle (by positivity)
    _ = 4 * d * ρ := by ring

/-! ### Restricting a multivariate polynomial to a line

The remaining step towards Lemma 4.6 is to view `y ↦ Q(y)` along a line `a + t v` as a
one-variable polynomial in `t`, so that `sublevel_root` applies.  For *homogeneous* `Q` of
degree `d` the leading coefficient is `Q(v)` — independent of the base point `a` — which is
exactly what makes a fixed direction work. -/

open Polynomial MvPolynomial in
/-- The restriction of `Q` to the line `a + t v`, as a polynomial in `t`. -/
noncomputable def lineRestrict {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) (a v : Fin n → ℝ) :
    Polynomial ℝ :=
  MvPolynomial.aeval (fun i => Polynomial.C (a i) + Polynomial.C (v i) * Polynomial.X) Q

open Polynomial MvPolynomial in
/-- `lineRestrict` does restrict: evaluating at `t` gives `Q (a + t v)`. -/
@[simp] lemma lineRestrict_eval {n : ℕ} (Q : MvPolynomial (Fin n) ℝ) (a v : Fin n → ℝ)
    (t : ℝ) :
    (lineRestrict Q a v).eval t = MvPolynomial.eval (fun i => a i + t * v i) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lineRestrict]
  | add f g hf hg => simp [lineRestrict] at hf hg ⊢; rw [hf, hg]
  | mul_X f i hf =>
      rw [lineRestrict, map_mul, map_mul, Polynomial.eval_mul]
      rw [lineRestrict] at hf
      rw [hf]
      simp [mul_comm t (v i)]

/-! ### The determinant of a matrix pencil

For the application the polynomial is `Δ = det K_A`, and `K_A` is *linear* in `y`, so
`K(a + t v) = K(a) + t K(v)`.  The line restriction is therefore the determinant of a
pencil, whose leading coefficient is `det K(v) = Δ(v)` by multilinearity — no
`MvPolynomial` machinery is needed. -/

section Pencil

open Polynomial

variable {n : ℕ}

/-- `det (B₀ + t B₁)` as a polynomial in `t`. -/
noncomputable def detPencil (B₀ B₁ : Matrix (Fin n) (Fin n) ℝ) : Polynomial ℝ :=
  Matrix.det (fun i j => Polynomial.C (B₀ i j) + Polynomial.C (B₁ i j) * Polynomial.X)

lemma detPencil_eval (B₀ B₁ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    (detPencil B₀ B₁).eval t = Matrix.det (B₀ + t • B₁) := by
  rw [detPencil, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_evalRingHom,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Each entry of the pencil is affine, so the determinant has degree at most `n`. -/
lemma detPencil_natDegree_le (B₀ B₁ : Matrix (Fin n) (Fin n) ℝ) :
    (detPencil B₀ B₁).natDegree ≤ n := by
  classical
  rw [detPencil, Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc ∑ i : Fin n, (Polynomial.C (B₀ (σ i) i)
        + Polynomial.C (B₁ (σ i) i) * Polynomial.X).natDegree
      ≤ ∑ _i : Fin n, 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine le_trans (Polynomial.natDegree_add_le _ _) ?_
        simp only [Polynomial.natDegree_C, max_le_iff]
        exact ⟨Nat.zero_le _, le_trans (Polynomial.natDegree_C_mul_le _ _)
          (by simp)⟩
    _ = n := by simp

/-- **The leading coefficient of the pencil is `det B₁`.**  This is multilinearity of the
determinant, obtained from `coeff_prod_of_natDegree_le` at degree bound `1`: each of the
`n` factors of a permutation term is affine, and the top coefficient of the product is the
product of the top coefficients. -/
lemma detPencil_coeff (B₀ B₁ : Matrix (Fin n) (Fin n) ℝ) :
    (detPencil B₀ B₁).coeff n = B₁.det := by
  classical
  rw [detPencil, Matrix.det_apply, Polynomial.finsetSum_coeff, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Polynomial.coeff_smul]
  congr 1
  have hdeg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (Polynomial.C (B₀ (σ i) i) + Polynomial.C (B₁ (σ i) i) * Polynomial.X).natDegree ≤ 1 := by
    intro i _
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp only [Polynomial.natDegree_C, max_le_iff]
    exact ⟨Nat.zero_le _, le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)⟩
  have hc := Polynomial.coeff_prod_of_natDegree_le (Finset.univ : Finset (Fin n))
    (fun i : Fin n => Polynomial.C (B₀ (σ i) i) + Polynomial.C (B₁ (σ i) i) * Polynomial.X)
    1 hdeg
  rw [Finset.card_univ, Fintype.card_fin, mul_one] at hc
  rw [hc]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Polynomial.coeff_add, Polynomial.coeff_C]

/-! ### Determinants of matrices of polynomials

`detPencil` above is the case `p = 1` of the following: if every entry of a `k × k` matrix
of polynomials has degree at most `p`, the determinant has degree at most `kp` and its
coefficient in degree `kp` is the determinant of the matrix of top coefficients.  The
general window needs `p = 2`, because there the degeneracy form is `det(KᵀK)` and the
entries of the Gram matrix are quadratic along a line. -/

section PolyDet

variable {k p : ℕ}

lemma natDegree_det_le (M : Matrix (Fin k) (Fin k) (Polynomial ℝ))
    (h : ∀ i j, (M i j).natDegree ≤ p) : (Matrix.det M).natDegree ≤ k * p := by
  classical
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc ∑ i : Fin k, (M (σ i) i).natDegree ≤ ∑ _i : Fin k, p :=
        Finset.sum_le_sum fun i _ => h (σ i) i
    _ = k * p := by simp []

lemma coeff_det_top (M : Matrix (Fin k) (Fin k) (Polynomial ℝ))
    (h : ∀ i j, (M i j).natDegree ≤ p) :
    (Matrix.det M).coeff (k * p) = Matrix.det (fun i j => (M i j).coeff p) := by
  classical
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Polynomial.coeff_smul]
  congr 1
  have hc := Polynomial.coeff_prod_of_natDegree_le (Finset.univ : Finset (Fin k))
    (fun i : Fin k => M (σ i) i) p (fun i _ => h (σ i) i)
  rwa [Finset.card_univ, Fintype.card_fin] at hc

end PolyDet

/-! ### The Gram pencil

For a rectangular pencil `B₀ + t B₁` the degeneracy form of the general window is
`det((B₀+tB₁)ᵀ(B₀+tB₁))`.  Each Gram entry is a sum of products of two affine polynomials,
hence quadratic, with `t²`-coefficient the corresponding entry of `B₁ᵀB₁`; so the
determinant has degree `2k` and top coefficient `det(B₁ᵀB₁)`. -/

section GramPencil

open Matrix

variable {n k : ℕ}

/-- The Gram matrix of the pencil `B₀ + t B₁`, entrywise as polynomials in `t`. -/
noncomputable def gramPencil (B₀ B₁ : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin k) (Fin k) (Polynomial ℝ) :=
  fun i j => ∑ l : Fin n,
    (Polynomial.C (B₀ l i) + Polynomial.C (B₁ l i) * Polynomial.X) *
    (Polynomial.C (B₀ l j) + Polynomial.C (B₁ l j) * Polynomial.X)

lemma gramPencil_eval (B₀ B₁ : Matrix (Fin n) (Fin k) ℝ) (t : ℝ) (i j : Fin k) :
    (gramPencil B₀ B₁ i j).eval t = ((B₀ + t • B₁)ᵀ * (B₀ + t • B₁)) i j := by
  rw [gramPencil, Matrix.mul_apply]
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

lemma gramPencil_natDegree_le (B₀ B₁ : Matrix (Fin n) (Fin k) ℝ) (i j : Fin k) :
    (gramPencil B₀ B₁ i j).natDegree ≤ 2 := by
  rw [gramPencil]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun l _ => ?_
  have haff : ∀ a b : ℝ,
      (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
    intro a b
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp only [Polynomial.natDegree_C, max_le_iff]
    exact ⟨Nat.zero_le _, le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)⟩
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  have := haff (B₀ l i) (B₁ l i)
  have := haff (B₀ l j) (B₁ l j)
  omega

lemma gramPencil_coeff (B₀ B₁ : Matrix (Fin n) (Fin k) ℝ) (i j : Fin k) :
    (gramPencil B₀ B₁ i j).coeff 2 = (B₁ᵀ * B₁) i j := by
  rw [gramPencil, Polynomial.finsetSum_coeff, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hexp : (Polynomial.C (B₀ l i) + Polynomial.C (B₁ l i) * Polynomial.X) *
      (Polynomial.C (B₀ l j) + Polynomial.C (B₁ l j) * Polynomial.X)
      = Polynomial.C (B₀ l i * B₀ l j)
        + Polynomial.C (B₀ l i * B₁ l j + B₁ l i * B₀ l j) * Polynomial.X
        + Polynomial.C (B₁ l i * B₁ l j) * Polynomial.X ^ 2 := by
    push_cast [Polynomial.C_mul, Polynomial.C_add]
    ring
  rw [hexp, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Matrix.transpose_apply]
  norm_num

/-- **The Gram pencil determinant.**  Degree at most `2k`, with `t^{2k}`-coefficient
`det(B₁ᵀB₁)`. -/
noncomputable def detGramPencil (B₀ B₁ : Matrix (Fin n) (Fin k) ℝ) : Polynomial ℝ :=
  Matrix.det (gramPencil B₀ B₁)

lemma detGramPencil_eval (B₀ B₁ : Matrix (Fin n) (Fin k) ℝ) (t : ℝ) :
    (detGramPencil B₀ B₁).eval t
      = Matrix.det ((B₀ + t • B₁)ᵀ * (B₀ + t • B₁)) := by
  rw [detGramPencil, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_evalRingHom]
  exact gramPencil_eval B₀ B₁ t i j

lemma detGramPencil_natDegree_le (B₀ B₁ : Matrix (Fin n) (Fin k) ℝ) :
    (detGramPencil B₀ B₁).natDegree ≤ 2 * k := by
  rw [detGramPencil, mul_comm]
  exact natDegree_det_le _ (fun i j => gramPencil_natDegree_le B₀ B₁ i j)

lemma detGramPencil_coeff (B₀ B₁ : Matrix (Fin n) (Fin k) ℝ) :
    (detGramPencil B₀ B₁).coeff (2 * k) = Matrix.det (B₁ᵀ * B₁) := by
  rw [detGramPencil, mul_comm]
  rw [coeff_det_top _ (fun i j => gramPencil_natDegree_le B₀ B₁ i j)]
  congr 1
  ext i j
  exact gramPencil_coeff B₀ B₁ i j

end GramPencil

end Pencil

/-! ### Fibring: from one variable to `n`

The hypotheses of `sublevel_slice` say that slicing `F` along the first coordinate always
produces a polynomial of degree at most `d` whose coefficient in degree `d` is the *same*
nonzero `c`, whatever the base point `u`.  That uniformity is exactly what homogeneity of
the leading form buys — and what `detPencil_coeff` supplies for `Δ`.  Each slice is then
controlled by `sublevel_root`, and Tonelli multiplies by the measure `(2K)^n` of the base. -/

section Slice

open MeasureTheory Polynomial

/-- **The several-variable sublevel bound**, by fibring in the first coordinate. -/
theorem sublevel_slice {n d : ℕ} (hd : 0 < d) {c : ℝ} (hc : c ≠ 0)
    {F : (Fin (n + 1) → ℝ) → ℝ} (hFmeas : Measurable F)
    (P : (Fin n → ℝ) → Polynomial ℝ)
    (hdeg : ∀ u, (P u).natDegree ≤ d)
    (hcoeff : ∀ u, (P u).coeff d = c)
    (hval : ∀ u t, F (Fin.cons t u) = (P u).eval t)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    volume {y : Fin (n + 1) → ℝ | |F y| ≤ ε ∧ ∀ i, |y i| ≤ K}
      ≤ ENNReal.ofReal ((2 * K) ^ n) *
        ENNReal.ofReal (4 * d * (ε / |c|) ^ ((d : ℝ)⁻¹)) := by
  classical
  -- every slice polynomial has degree exactly `d`, with leading coefficient `c`
  have hdeg' : ∀ u, (P u).natDegree = d := fun u =>
    le_antisymm (hdeg u) (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff u]; exact hc))
  have hlead : ∀ u, (P u).leadingCoeff = c := fun u => by
    rw [Polynomial.leadingCoeff, hdeg' u, hcoeff u]
  set B : ℝ := 4 * d * (ε / |c|) ^ ((d : ℝ)⁻¹) with hB
  have hB0 : 0 ≤ B := by
    have : (0:ℝ) ≤ (ε / |c|) ^ ((d : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
    rw [hB]; positivity
  set base : Set (Fin n → ℝ) := {u | ∀ i, |u i| ≤ K} with hbase
  have hbasem : MeasurableSet base := by
    rw [hbase, Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le ((measurable_pi_apply i).abs) measurable_const
  set S : Set (Fin (n + 1) → ℝ) := {y | |F y| ≤ ε ∧ ∀ i, |y i| ≤ K} with hSdef
  have hSm : MeasurableSet S := by
    have h1 : MeasurableSet {y : Fin (n + 1) → ℝ | |F y| ≤ ε} :=
      measurableSet_le hFmeas.abs measurable_const
    have h2 : MeasurableSet {y : Fin (n + 1) → ℝ | ∀ i, |y i| ≤ K} := by
      rw [Set.setOf_forall]
      exact MeasurableSet.iInter fun i =>
        measurableSet_le ((measurable_pi_apply i).abs) measurable_const
    exact h1.inter h2
  -- transport to the product `ℝ × (Fin n → ℝ)`
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with hedef
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))
  have hesymm : ∀ (t : ℝ) (u : Fin n → ℝ), e.symm (t, u) = Fin.cons t u := by
    intro t u
    exact Fin.insertNth_zero' t u
  have hT : MeasurableSet (e.symm ⁻¹' S) := e.symm.measurable hSm
  have hpre : e ⁻¹' (e.symm ⁻¹' S) = S := by ext y; simp
  have hvolS : volume S = (volume : Measure (ℝ × (Fin n → ℝ))) (e.symm ⁻¹' S) := by
    conv_lhs => rw [← hpre]
    exact hmp.measure_preimage hT.nullMeasurableSet
  -- the fibre over `u`
  have hfib : ∀ u : Fin n → ℝ,
      (fun t => (t, u)) ⁻¹' (e.symm ⁻¹' S) = {t : ℝ | Fin.cons t u ∈ S} := by
    intro u; ext t; simp [hesymm t u]
  have hslice : ∀ u : Fin n → ℝ,
      volume ((fun t => (t, u)) ⁻¹' (e.symm ⁻¹' S))
        ≤ base.indicator (fun _ => ENNReal.ofReal B) u := by
    intro u
    rw [hfib u]
    by_cases hu : u ∈ base
    · rw [Set.indicator_of_mem hu]
      have hsub : {t : ℝ | Fin.cons t u ∈ S} ⊆ {t : ℝ | |(P u).eval t| ≤ ε} := by
        intro t ht
        have h1 := ht.1
        rwa [hval u t] at h1
      refine le_trans (measure_mono hsub) ?_
      have hsr := sublevel_root hd (hdeg' u) hε
      rwa [hlead u] at hsr
    · have hempty : {t : ℝ | Fin.cons t u ∈ S} = ∅ := by
        have hu' : ∃ j, K < |u j| := by
          by_contra hcon
          push Not at hcon
          exact hu (fun i => hcon i)
        obtain ⟨j, hj⟩ := hu'
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, h2⟩
        have := h2 j.succ
        rw [Fin.cons_succ] at this
        linarith
      rw [hempty]
      simp
  -- Tonelli
  rw [hvolS, Measure.volume_eq_prod, Measure.prod_apply_symm hT]
  calc ∫⁻ u, volume ((fun t => (t, u)) ⁻¹' (e.symm ⁻¹' S))
      ≤ ∫⁻ u, base.indicator (fun _ => ENNReal.ofReal B) u :=
        lintegral_mono hslice
    _ = ENNReal.ofReal B * volume base := lintegral_indicator_const hbasem _
    _ = ENNReal.ofReal ((2 * K) ^ n) * ENNReal.ofReal B := by
        rw [mul_comm]
        congr 1
        have hb : base = Set.univ.pi fun _ : Fin n => Set.Icc (-K) K := by
          ext u
          simp only [hbase, Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
          exact forall_congr' fun i => abs_le
        rw [hb, volume_pi_pi]
        simp only [Real.volume_Icc]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← ENNReal.ofReal_pow (by linarith)]
        congr 1
        ring

/-! ### An arbitrary direction, by a unipotent shear

To slice along a direction `v` other than `e₀` we shear `e₀` onto `v`.  Normalising
`v₀ = 1` — legitimate because the leading form is homogeneous, so `v` may be rescaled —
makes the shear *unipotent* lower-triangular, of determinant `1`, hence measure
preserving.  No Jacobian survives into the constant. -/

/-- The shear `w ↦ w + w₀ • v'`. -/
noncomputable def shearMat {n : ℕ} (v' : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => (if i = j then (1:ℝ) else 0) + (if j = 0 then v' i else 0)

lemma shearMat_mulVec {n : ℕ} (v' w : Fin (n + 1) → ℝ) :
    (shearMat v').mulVec w = w + w 0 • v' := by
  ext i
  simp only [shearMat, Matrix.mulVec, Matrix.of_apply, dotProduct, add_mul,
    Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · simp [ite_mul, Finset.sum_ite_eq]
  · simp [Finset.sum_ite_eq', mul_comm]

/-- Unipotent lower-triangular: determinant `1`. -/
lemma det_shearMat {n : ℕ} {v' : Fin (n + 1) → ℝ} (hv' : v' 0 = 0) :
    (shearMat v').det = 1 := by
  have htri : (shearMat v').BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
    have h1 : i ≠ j := ne_of_lt hlt
    have h2 : j ≠ 0 := by
      intro h; rw [h] at hlt; exact absurd hlt (by simp)
    simp [shearMat, h1, h2]
  rw [Matrix.det_of_lowerTriangular _ htri]
  refine Finset.prod_eq_one fun i _ => ?_
  by_cases hi : i = 0
  · subst hi; simp [shearMat, hv']
  · simp [shearMat, hi]

/-- **The sublevel bound along an arbitrary direction.**  Along every line in direction
`v` (normalised so `v 0 = 1`) the restriction of `F` is a polynomial of degree at most `d`
whose top coefficient is the same nonzero `c`.  Then the sublevel set of `F` inside the box
of half-width `K` is small. -/
theorem sublevel_dir {n d : ℕ} (hd : 0 < d) {c : ℝ} (hc : c ≠ 0)
    {F : (Fin (n + 1) → ℝ) → ℝ} (hFmeas : Measurable F)
    {v : Fin (n + 1) → ℝ} (hv0 : v 0 = 1)
    (P : (Fin (n + 1) → ℝ) → Polynomial ℝ)
    (hdeg : ∀ a, (P a).natDegree ≤ d)
    (hcoeff : ∀ a, (P a).coeff d = c)
    (hval : ∀ a t, F (a + t • v) = (P a).eval t)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    volume {y : Fin (n + 1) → ℝ | |F y| ≤ ε ∧ ∀ i, |y i| ≤ K}
      ≤ ENNReal.ofReal ((2 * (K * (1 + ‖v‖))) ^ n) *
        ENNReal.ofReal (4 * d * (ε / |c|) ^ ((d : ℝ)⁻¹)) := by
  classical
  set v' : Fin (n + 1) → ℝ := v - Pi.single 0 1 with hv'def
  have hv'0 : v' 0 = 0 := by simp [hv'def, hv0]
  have hv'le : ∀ i, |v' i| ≤ ‖v‖ := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [hv'0]; simp
    · have : v' i = v i := by simp [hv'def, hi]
      rw [this]
      simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
  set L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) := Matrix.toLin' (shearMat v') with hLdef
  have hLapply : ∀ w, L w = w + w 0 • v' := by
    intro w; rw [hLdef, Matrix.toLin'_apply, shearMat_mulVec]
  have hLdet : LinearMap.det L = 1 := by
    rw [hLdef, LinearMap.det_toLin', det_shearMat hv'0]
  have hLmeas : Measurable L := (L.continuous_of_finiteDimensional).measurable
  set K' : ℝ := K * (1 + ‖v‖) with hK'def
  have hK'0 : 0 ≤ K' := by rw [hK'def]; positivity
  set S : Set (Fin (n + 1) → ℝ) := {y | |F y| ≤ ε ∧ ∀ i, |y i| ≤ K} with hSdef
  -- the shear is measure preserving
  have hpre : volume S = volume (L ⁻¹' S) := by
    have hdet : LinearMap.det L ≠ 0 := by rw [hLdet]; norm_num
    have h := Measure.addHaar_preimage_linearMap
      (μ := (volume : Measure (Fin (n + 1) → ℝ))) hdet S
    rw [h, hLdet]
    simp
  -- and carries the box into a slightly larger box
  have hsub : L ⁻¹' S ⊆ {w : Fin (n + 1) → ℝ | |F (L w)| ≤ ε ∧ ∀ i, |w i| ≤ K'} := by
    intro w hw
    obtain ⟨h1, h2⟩ := hw
    refine ⟨h1, fun i => ?_⟩
    have h0 : (L w) 0 = w 0 := by rw [hLapply]; simp [hv'0]
    have hLi : (L w) i = w i + w 0 * v' i := by rw [hLapply]; simp
    have hwi : w i = (L w) i - (L w) 0 * v' i := by rw [hLi, h0]; ring
    rw [hwi]
    calc |(L w) i - (L w) 0 * v' i| ≤ |(L w) i| + |(L w) 0| * |v' i| := by
          refine le_trans (abs_sub _ _) ?_
          rw [abs_mul]
      _ ≤ K + K * ‖v‖ := by
          refine add_le_add (h2 i) ?_
          exact mul_le_mul (h2 0) (hv'le i) (abs_nonneg _) hK
      _ = K' := by rw [hK'def]; ring
  -- the sliced polynomial
  have hcons : ∀ (t : ℝ) (u : Fin n → ℝ),
      L (Fin.cons t u) = (Fin.cons (0:ℝ) u) + t • v := by
    intro t u
    have h0 : (Fin.cons t u : Fin (n + 1) → ℝ) 0 = t := by simp
    rw [hLapply, h0]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hv'0, hv0]
    · simp [hv'def]
  have hGval : ∀ (u : Fin n → ℝ) (t : ℝ),
      (F ∘ L) (Fin.cons t u) = (P (Fin.cons (0:ℝ) u)).eval t := by
    intro u t
    simp only [Function.comp_apply, hcons t u]
    exact hval _ t
  calc volume S = volume (L ⁻¹' S) := hpre
    _ ≤ volume {w : Fin (n + 1) → ℝ | |(F ∘ L) w| ≤ ε ∧ ∀ i, |w i| ≤ K'} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal ((2 * K') ^ n) *
          ENNReal.ofReal (4 * d * (ε / |c|) ^ ((d : ℝ)⁻¹)) :=
        sublevel_slice hd hc (hFmeas.comp hLmeas)
          (fun u => P (Fin.cons (0:ℝ) u)) (fun u => hdeg _) (fun u => hcoeff _) hGval hK'0 hε

end Slice

end MPE
