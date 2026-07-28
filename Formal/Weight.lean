import Mathlib

/-!
# The logarithmic weight `Λ`

`Λ t = 1 + log⁺(1/t)` is the weight carried through the anticoncentration estimate
(appendix §2).  Everything here is elementary; it is isolated because the *multiplicative*
absorption of constants (`Lam_mul_le_of_pos`) is what survives being raised to a power,
whereas the naive additive bound `Λ(Kt) ≤ Λ t + log(1/K)` does not.

Since `log (1/t) = - log t`, we take `Λ t = 1 + max 0 (- log t)` as the definition.
-/

namespace MPE

open Real

/-- The logarithmic weight `Λ t = 1 + log⁺(1/t)`. -/
noncomputable def Lam (t : ℝ) : ℝ := 1 + max 0 (-Real.log t)

lemma one_le_Lam (t : ℝ) : 1 ≤ Lam t := by
  have : (0 : ℝ) ≤ max 0 (-Real.log t) := le_max_left _ _
  simp [Lam]

lemma Lam_pos (t : ℝ) : 0 < Lam t := lt_of_lt_of_le one_pos (one_le_Lam t)

lemma Lam_nonneg (t : ℝ) : 0 ≤ Lam t := (Lam_pos t).le

/-- `Λ` is antitone on the positive reals. -/
lemma Lam_le_Lam {t t' : ℝ} (ht : 0 < t) (h : t ≤ t') : Lam t' ≤ Lam t := by
  have hlog : Real.log t ≤ Real.log t' := Real.log_le_log ht h
  have : max 0 (-Real.log t') ≤ max 0 (-Real.log t) :=
    max_le_max le_rfl (by linarith)
  simpa [Lam] using this

/-- `Λ t = 1` once `t ≥ 1`. -/
lemma Lam_eq_one {t : ℝ} (ht : 1 ≤ t) : Lam t = 1 := by
  have : Real.log t ≥ 0 := Real.log_nonneg ht
  simp [Lam, max_eq_left (by linarith : -Real.log t ≤ 0)]

/-- Absorbing a constant `≥ 1`: scaling up can only decrease `Λ`. -/
lemma Lam_mul_le_of_one_le {K t : ℝ} (hK : 1 ≤ K) (ht : 0 < t) :
    Lam (K * t) ≤ Lam t :=
  Lam_le_Lam ht (by nlinarith)

/-- **Multiplicative absorption.**  For any `K > 0` there is a constant, namely
`1 + log⁺(1/K)`, with `Λ (K t) ≤ (1 + log⁺(1/K)) * Λ t` for all `t > 0`.

This is the form to use: the additive bound `Λ (K t) ≤ Λ t + log (1/K)` is useless inside a
product of several such factors, while this one survives being raised to a power. -/
lemma Lam_mul_le_of_pos {K : ℝ} (hK : 0 < K) {t : ℝ} (ht : 0 < t) :
    Lam (K * t) ≤ Lam K * Lam t := by
  have hsplit : Real.log (K * t) = Real.log K + Real.log t :=
    Real.log_mul hK.ne' ht.ne'
  -- `max 0 (-log K - log t) ≤ max 0 (-log K) + max 0 (-log t)`
  have hmax : max 0 (-Real.log (K * t)) ≤ max 0 (-Real.log K) + max 0 (-Real.log t) := by
    rw [hsplit]
    rcases le_or_gt (-Real.log K - Real.log t) 0 with h | h
    · calc max 0 (-(Real.log K + Real.log t)) = 0 := by
            apply max_eq_left; linarith
        _ ≤ max 0 (-Real.log K) + max 0 (-Real.log t) :=
            add_nonneg (le_max_left _ _) (le_max_left _ _)
    · have h1 : -Real.log K ≤ max 0 (-Real.log K) := le_max_right _ _
      have h2 : -Real.log t ≤ max 0 (-Real.log t) := le_max_right _ _
      calc max 0 (-(Real.log K + Real.log t)) = -(Real.log K + Real.log t) := by
            apply max_eq_right; linarith
        _ ≤ max 0 (-Real.log K) + max 0 (-Real.log t) := by linarith
  -- now `Λ(Kt) ≤ 1 + a + b ≤ (1+a)(1+b) = Λ K * Λ t`
  have ha : (0 : ℝ) ≤ max 0 (-Real.log K) := le_max_left _ _
  have hb : (0 : ℝ) ≤ max 0 (-Real.log t) := le_max_left _ _
  have : Lam (K * t) ≤ 1 + max 0 (-Real.log K) + max 0 (-Real.log t) := by
    rw [Lam]; linarith
  calc Lam (K * t) ≤ 1 + max 0 (-Real.log K) + max 0 (-Real.log t) := this
    _ ≤ Lam K * Lam t := by simp only [Lam]; nlinarith

/-- The two-parameter weight dominates each factor: `Λ t ≤ Λ (t * η)` when `η ≤ 1`. -/
lemma Lam_le_Lam_mul_right {t η : ℝ} (ht : 0 < t) (hη : 0 < η) (hη1 : η ≤ 1) :
    Lam t ≤ Lam (t * η) :=
  Lam_le_Lam (by positivity) (by nlinarith)

/-- Symmetrically, `Λ η ≤ Λ (t * η)` when `t ≤ 1`. -/
lemma Lam_le_Lam_mul_left {t η : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hη : 0 < η) :
    Lam η ≤ Lam (t * η) :=
  Lam_le_Lam (by positivity) (by nlinarith)

/-- Powers of `Λ` are monotone in the exponent, since `Λ ≥ 1`. -/
lemma Lam_pow_le_pow {t : ℝ} {i j : ℕ} (hij : i ≤ j) : Lam t ^ i ≤ Lam t ^ j :=
  pow_le_pow_right₀ (one_le_Lam t) hij

lemma Lam_pow_pos (t : ℝ) (j : ℕ) : 0 < Lam t ^ j := pow_pos (Lam_pos t) j

lemma one_le_Lam_pow (t : ℝ) (j : ℕ) : 1 ≤ Lam t ^ j := one_le_pow₀ (one_le_Lam t)

/-- Monotonicity of `Λ ^ j` in `t`. -/
lemma Lam_pow_le_Lam_pow {t t' : ℝ} (ht : 0 < t) (h : t ≤ t') (j : ℕ) :
    Lam t' ^ j ≤ Lam t ^ j :=
  pow_le_pow_left₀ (Lam_nonneg t') (Lam_le_Lam ht h) j

/-- `Λ` is measurable (it is continuous on `(0, ∞)`, but measurability is all we need). -/
lemma measurable_Lam : Measurable Lam := by
  unfold Lam
  fun_prop

/-! ### Dyadic scaling

The annuli of `Formal/Anticonc.lean` shrink dyadically, and each carries its own weight
`Λ(s ηⱼ)` with `ηⱼ ≍ 2⁻ʲ δ`.  The bound `Λ(a·2⁻ʲ) ≤ Λ(a)·(1+j)` is what lets the geometric
weights `2⁻ⁿʲ` dominate the growing logarithms — the appendix's `Λ'ⱼ ≤ C(Λ+j)`, in the
multiplicative form that survives being raised to a power. -/

/-- `Λ((1/2)^j) ≤ 1 + j`. -/
lemma Lam_half_pow_le (j : ℕ) : Lam ((1/2 : ℝ) ^ j) ≤ 1 + j := by
  have hlog : Real.log ((1/2 : ℝ) ^ j) = -(j * Real.log 2) := by
    rw [Real.log_pow, one_div, Real.log_inv]
    ring
  have hlt : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hnn : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [Lam, hlog, neg_neg, max_eq_right (by positivity)]
  have : (j : ℝ) * Real.log 2 ≤ j := by
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  linarith

/-- **Dyadic scaling of the weight.**  `Λ(a·2⁻ʲ) ≤ Λ(a)·(1+j)`. -/
lemma Lam_mul_half_pow_le {a : ℝ} (ha : 0 < a) (j : ℕ) :
    Lam (a * (1/2 : ℝ) ^ j) ≤ Lam a * (1 + j) := by
  refine le_trans (Lam_mul_le_of_pos ha (by positivity)) ?_
  exact mul_le_mul_of_nonneg_left (Lam_half_pow_le j) (Lam_nonneg a)

/-- Raising to a power `≤ 2` at most doubles the weight. -/
lemma Lam_rpow_le_two_mul {x a : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ha2 : a ≤ 2) :
    Lam (x ^ a) ≤ 2 * Lam x := by
  have hlog : Real.log (x ^ a) = a * Real.log x := Real.log_rpow hx a
  have hnn : (0:ℝ) ≤ -Real.log x := by
    have := Real.log_nonpos hx.le hx1; linarith
  rcases le_or_gt (-(a * Real.log x)) 0 with h | h
  · rw [Lam, hlog, max_eq_left h, Lam]
    have : (0:ℝ) ≤ max 0 (-Real.log x) := le_max_left _ _
    linarith
  · rw [Lam, hlog, max_eq_right h.le, Lam, max_eq_right hnn]
    nlinarith

/-! ### The geometric-beats-polynomial constant

`∑ⱼ 2⁻ⁿʲ (1+j)^p` converges for `n ≥ 1`; its value is the constant absorbing the sum over
annuli.  Since every constant in the analysis is existentially quantified, defining it as
the sum itself costs nothing. -/

lemma summable_dyadic (n p : ℕ) (hn : 0 < n) :
    Summable fun j : ℕ => ((1:ℝ)/2) ^ (n * j) * (1 + j) ^ p := by
  set r : ℝ := ((1:ℝ)/2) ^ n with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by
    rw [hr]
    exact pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
  -- majorize by `2^p (j^p r^j + r^j)`
  have hmaj : Summable fun j : ℕ => (2:ℝ) ^ p * ((j:ℝ) ^ p * r ^ j + r ^ j) := by
    refine Summable.mul_left _ (Summable.add ?_ ?_)
    · exact summable_pow_mul_geometric_of_norm_lt_one p (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
    · exact summable_geometric_of_lt_one hr0.le hr1
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hmaj
  have hpow : ((1:ℝ)/2) ^ (n * j) = r ^ j := by rw [hr, ← pow_mul]
  rw [hpow]
  have hp2 : (1:ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have hjp : (0:ℝ) ≤ (j:ℝ) ^ p := by positivity
  have hbound : (1 + (j:ℝ)) ^ p ≤ 2 ^ p * ((j:ℝ) ^ p + 1) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have h0 : (1 + ((0:ℕ):ℝ)) ^ p = 1 := by norm_num
      rw [h0]
      nlinarith
    · have h1 : (1:ℝ) + j ≤ 2 * j := by
        have : (1:ℝ) ≤ j := by exact_mod_cast hj
        linarith
      calc (1 + (j:ℝ)) ^ p ≤ (2 * (j:ℝ)) ^ p :=
            pow_le_pow_left₀ (by positivity) h1 p
        _ = 2 ^ p * (j:ℝ) ^ p := by rw [mul_pow]
        _ ≤ 2 ^ p * ((j:ℝ) ^ p + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hrj : (0:ℝ) ≤ r ^ j := by positivity
  calc r ^ j * (1 + (j:ℝ)) ^ p = (1 + (j:ℝ)) ^ p * r ^ j := by ring
    _ ≤ (2 ^ p * ((j:ℝ) ^ p + 1)) * r ^ j := mul_le_mul_of_nonneg_right hbound hrj
    _ = 2 ^ p * ((j:ℝ) ^ p * r ^ j + r ^ j) := by ring

/-- The constant `∑ⱼ 2⁻ⁿʲ (1+j)^p`. -/
noncomputable def dyadicConst (n p : ℕ) : ℝ := ∑' j : ℕ, ((1:ℝ)/2) ^ (n * j) * (1 + j) ^ p

lemma dyadicConst_nonneg (n p : ℕ) : 0 ≤ dyadicConst n p :=
  tsum_nonneg fun j => by positivity

/-- The dyadic constant is at least its `j = 0` term, which is `1`. -/
lemma one_le_dyadicConst {n p : ℕ} (hn : 0 < n) : 1 ≤ dyadicConst n p := by
  have h0 : ((1:ℝ)/2) ^ (n * 0) * (1 + (0:ℕ)) ^ p = 1 := by norm_num
  calc (1:ℝ) = ((1:ℝ)/2) ^ (n * 0) * (1 + (0:ℕ)) ^ p := h0.symm
    _ ≤ dyadicConst n p := by
        refine (summable_dyadic n p hn).le_tsum 0 (fun j _ => by positivity)

lemma dyadicConst_pos {n p : ℕ} (hn : 0 < n) : 0 < dyadicConst n p :=
  lt_of_lt_of_le one_pos (one_le_dyadicConst hn)

/-- Every partial sum is bounded by the constant. -/
lemma sum_le_dyadicConst {n p : ℕ} (hn : 0 < n) (s : Finset ℕ) :
    ∑ j ∈ s, ((1:ℝ)/2) ^ (n * j) * (1 + j) ^ p ≤ dyadicConst n p :=
  (summable_dyadic n p hn).sum_le_tsum s (fun j _ => by positivity)

/-- The dyadic sum, as a `tsum`. -/
lemma tsum_dyadic {n p : ℕ} (_hn : 0 < n) :
    ∑' j : ℕ, ((1:ℝ)/2) ^ (n * j) * (1 + j) ^ p = dyadicConst n p := rfl

/-- The two dyadic series that occur in the shell sum, added. -/
lemma summable_dyadic_pair {n p : ℕ} (hn : 0 < n) (K₁ K₂ : ℝ) :
    Summable fun j : ℕ => K₁ * (((1:ℝ)/2) ^ (n * j) * (1 + j) ^ 0)
      + K₂ * (((1:ℝ)/2) ^ ((n + 1) * j) * (1 + j) ^ p) :=
  ((summable_dyadic n 0 hn).mul_left K₁).add
    ((summable_dyadic (n + 1) p (by omega)).mul_left K₂)

lemma tsum_dyadic_pair {n p : ℕ} (hn : 0 < n) (K₁ K₂ : ℝ) :
    ∑' j : ℕ, (K₁ * (((1:ℝ)/2) ^ (n * j) * (1 + j) ^ 0)
      + K₂ * (((1:ℝ)/2) ^ ((n + 1) * j) * (1 + j) ^ p))
      = K₁ * dyadicConst n 0 + K₂ * dyadicConst (n + 1) p := by
  rw [Summable.tsum_add ((summable_dyadic n 0 hn).mul_left K₁)
    ((summable_dyadic (n + 1) p (by omega)).mul_left K₂), tsum_mul_left, tsum_mul_left]
  rfl

/-! ### Absorbing the logarithm into a power

`dither_sharp` demands a per-cycle bound of the pure form `A δ^p`, whereas Lemma 4.8 produces
`s Λ(s)^{n-1}`.  The two are reconciled by the fact that a logarithm is dominated by any
positive power: for every `p < 1` there is a constant with `x Λ(x)^k ≤ C x^p` on `(0,1]`. -/

lemma log_le_rpow_div {y : ℝ} (hy : 0 < y) {ε : ℝ} (hε : 0 < ε) :
    Real.log y ≤ y ^ ε / ε := by
  have h1 : Real.log (y ^ ε) ≤ y ^ ε - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_rpow hy] at h1
  rw [le_div_iff₀ hε]
  nlinarith

/-- **The logarithm is absorbed by any positive power.**  For `0 < p < 1` there is `C > 0`
with `x · Λ(x)^k ≤ C · x^p` for all `x ∈ (0,1]`. -/
theorem exists_mul_Lam_pow_le_rpow (k : ℕ) {p : ℝ} (_hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 → x * Lam x ^ k ≤ C * x ^ p := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- no logarithm at all: `x = x^1 ≤ x^p` since `x ≤ 1` and `p < 1`
    refine ⟨1, one_pos, fun x hx hx1 => ?_⟩
    simp only [pow_zero, mul_one, one_mul]
    calc x = x ^ (1:ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge hx hx1 hp1.le
  set a : ℝ := 1 - p with ha
  have ha0 : 0 < a := by simp [ha]; linarith
  set ε : ℝ := a / k with hε
  have hε0 : 0 < ε := by
    have : (0:ℝ) < k := by exact_mod_cast hk
    positivity
  refine ⟨(1 + 1/ε) ^ k, by positivity, fun x hx hx1 => ?_⟩
  set y : ℝ := x⁻¹ with hy
  have hy1 : 1 ≤ y := by rw [hy]; rw [le_inv_comm₀ one_pos hx]; simpa using hx1
  have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
  have hlogy : Real.log y = -Real.log x := by rw [hy, Real.log_inv]
  -- `Λ x = 1 + log y`
  have hLamx : Lam x = 1 + Real.log y := by
    rw [Lam, hlogy]
    congr 1
    refine max_eq_right ?_
    rw [← hlogy]
    exact Real.log_nonneg hy1
  -- `1 + log y ≤ (1 + 1/ε) y^ε`
  have hstep : Lam x ≤ (1 + 1/ε) * y ^ ε := by
    have hyε : (1:ℝ) ≤ y ^ ε := Real.one_le_rpow hy1 hε0.le
    have hlog : Real.log y ≤ y ^ ε / ε := log_le_rpow_div hy0 hε0
    rw [hLamx]
    have : y ^ ε / ε = (1/ε) * y ^ ε := by field_simp
    rw [this] at hlog
    nlinarith
  -- raise to the power `k` and convert `y^(εk) = x^(-a)`
  have hyεk : (y ^ ε) ^ k = x ^ (-a) := by
    rw [← Real.rpow_natCast (y ^ ε) k, ← Real.rpow_mul hy0.le]
    have hk0 : (k:ℝ) ≠ 0 := by positivity
    rw [hε, div_mul_cancel₀ _ hk0, hy, ← Real.rpow_neg_one x, ← Real.rpow_mul hx.le]
    ring_nf
  have hpow : Lam x ^ k ≤ (1 + 1/ε) ^ k * x ^ (-a) := by
    calc Lam x ^ k ≤ ((1 + 1/ε) * y ^ ε) ^ k :=
          pow_le_pow_left₀ (Lam_nonneg x) hstep k
      _ = (1 + 1/ε) ^ k * (y ^ ε) ^ k := by rw [mul_pow]
      _ = (1 + 1/ε) ^ k * x ^ (-a) := by rw [hyεk]
  -- multiply by `x` and use `x · x^(-a) = x^p`
  have hxa : x * x ^ (-a) = x ^ p := by
    have h := Real.rpow_add hx 1 (-a)
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    simp [ha]
  calc x * Lam x ^ k ≤ x * ((1 + 1/ε) ^ k * x ^ (-a)) :=
        mul_le_mul_of_nonneg_left hpow hx.le
    _ = (1 + 1/ε) ^ k * (x * x ^ (-a)) := by ring
    _ = (1 + 1/ε) ^ k * x ^ p := by rw [hxa]

end MPE
