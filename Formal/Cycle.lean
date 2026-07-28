import Mathlib

/-!
# One MPE cycle in terms of the margin

Formalisation of the paper's Lemma "one cycle in terms of the margin", together with the
three contraction steps that Theorem 4.7, Theorem 4.9 and the Corollary run on.

The expansion data of the paper's Lemma "leading terms" is a **hypothesis**, not an axiom:
it is a field of `CycleData`, so it appears in the statement of everything that uses it.
Nothing load-bearing is off-screen.

`CycleData.S` is the *cleared form* `S = Ñ / σ̃`.
-/

namespace MPE

open Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The data of one restart cycle, with the paper's Lemma 4.1(iii) as a hypothesis.

* `d` is `deg Q̃`;
* `Ntil`, `sigt` are the cleared numerator `Ñ` and denominator `σ̃`;
* `hN` is Lemma 4.1(iii): `‖Ñ(y)‖ ≤ M‖y‖^(d+2)` on the ball of radius `ρ₁`. -/
structure CycleData (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  d : ℕ
  Ntil : E → E
  sigt : E → ℝ
  M : ℝ
  ρ₁ : ℝ
  hd : 0 < d
  hM : (1 : ℝ) ≤ M
  hρ₁ : (0 : ℝ) < ρ₁
  hN : ∀ y : E, ‖y‖ ≤ ρ₁ → ‖Ntil y‖ ≤ M * ‖y‖ ^ (d + 2)

namespace CycleData

variable (C : CycleData E)

/-- The margin `τ(y) = |σ̃(y)| / ‖y‖^d`. -/
noncomputable def τ (y : E) : ℝ := |C.sigt y| / ‖y‖ ^ C.d

/-- One cycle, in cleared form `S = Ñ / σ̃`. -/
noncomputable def S (y : E) : E := (C.sigt y)⁻¹ • C.Ntil y

lemma sigt_abs (y : E) (hy : 0 < ‖y‖) : |C.sigt y| = C.τ y * ‖y‖ ^ C.d := by
  have hne : (‖y‖ ^ C.d) ≠ 0 := (pow_pos hy _).ne'
  rw [τ, div_mul_cancel₀ _ hne]

lemma τ_pos (y : E) (hy : 0 < ‖y‖) (hσ : C.sigt y ≠ 0) : 0 < C.τ y :=
  div_pos (abs_pos.mpr hσ) (pow_pos hy _)

/-- `σ̃(0) = 0`, so the margin vanishes at the origin: any positive lower bound on `τ`
forces `y ≠ 0`.  This is the paper's remark that a lower bound on `τ` forces `y ≠ 0`. -/
lemma τ_zero_of_norm_zero {y : E} (hy : ‖y‖ = 0) : C.τ y = 0 := by
  rw [τ, hy, zero_pow C.hd.ne', div_zero]

/-- A positive margin forces both `y ≠ 0` and `σ̃(y) ≠ 0` — the two side conditions of
`norm_S_le`. -/
lemma pos_of_τ_pos {y : E} (h : 0 < C.τ y) : 0 < ‖y‖ ∧ C.sigt y ≠ 0 := by
  constructor
  · rcases (norm_nonneg y).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (C.τ_zero_of_norm_zero h'.symm) h.ne'
  · intro hcon
    rw [τ, hcon, abs_zero, zero_div] at h
    exact lt_irrefl 0 h

/-- **Lemma (one cycle in terms of the margin), part (i).**
Under `C²` smoothness alone, `‖S(y)‖ ≤ M‖y‖² / τ(y)`. -/
theorem norm_S_le {y : E} (hy : 0 < ‖y‖) (hy₁ : ‖y‖ ≤ C.ρ₁) (hσ : C.sigt y ≠ 0) :
    ‖C.S y‖ ≤ C.M * ‖y‖ ^ 2 / C.τ y := by
  have hτpos : 0 < C.τ y := C.τ_pos y hy hσ
  have hnorm : ‖C.S y‖ = ‖C.Ntil y‖ / |C.sigt y| := by
    rw [S, norm_smul, norm_inv, Real.norm_eq_abs]; ring
  rw [hnorm, C.sigt_abs y hy, div_le_div_iff₀ (by positivity) hτpos]
  calc ‖C.Ntil y‖ * C.τ y
      ≤ (C.M * ‖y‖ ^ (C.d + 2)) * C.τ y :=
        mul_le_mul_of_nonneg_right (C.hN y hy₁) hτpos.le
    _ = C.M * ‖y‖ ^ 2 * (C.τ y * ‖y‖ ^ C.d) := by rw [pow_add]; ring

end CycleData

/-! ### Powers of `δ` used by the schedule -/

private lemma rpow_split {δ a : ℝ} (hδ : 0 < δ) (n : ℕ) (h : a + ((n : ℝ) - a) = (n : ℝ)) :
    δ ^ a * δ ^ ((n : ℝ) - a) = δ ^ n := by
  rw [← rpow_add hδ, h, rpow_natCast]

/-! ### The three contraction steps

Each says: with the stated margin threshold, one cycle lands inside the next radius of the
schedule.  These are the arithmetic steps the convergence proofs turn on.
-/

/-- **Theorem 4.7, condition (a).**  With margin threshold `4Mδ^(2-θ)` and `‖y‖ ≤ 2δ`, the
general one-cycle bound returns exactly `δ^θ`.  No slack in the exponent is needed: the
constant is absorbed by the threshold, which is what improves the exponent of Theorem 4.7
from `(2-θ)/(2d)` to `(2-θ)/d`. -/
theorem contraction_general {M δ θ r τ : ℝ} (hM : 1 ≤ M) (hδ : 0 < δ) (hr : 0 < r)
    (hrle : r ≤ 2 * δ) (hτ : 4 * M * δ ^ (2 - θ) ≤ τ) :
    M * r ^ 2 / τ ≤ δ ^ θ := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hδθ : (0 : ℝ) < δ ^ θ := rpow_pos_of_pos hδ θ
  have hsplit : δ ^ θ * δ ^ (2 - θ) = δ ^ (2 : ℕ) :=
    rpow_split hδ 2 (by push_cast; ring)
  have hr2 : r ^ 2 ≤ (2 * δ) ^ 2 := pow_le_pow_left₀ hr.le hrle 2
  rw [div_le_iff₀ hτpos]
  calc M * r ^ 2 ≤ 4 * M * δ ^ (2 : ℕ) := by nlinarith [hr2, hM0.le]
    _ = δ ^ θ * (4 * M * δ ^ (2 - θ)) := by rw [← hsplit]; ring
    _ ≤ δ ^ θ * τ := by gcongr

/-- **Theorem 4.9, condition (a).**  With the sharp one-cycle bound `C₁r² + C₂r³/τ` and margin
`16C₂δ^(3-θ)`, one cycle again lands inside `δ^θ`, provided `8C₁δ^(2-θ) ≤ 1`.  The extra
power of `r` in the second term is what the factorisation `G = Δ·N⁽²⁾` buys. -/
theorem contraction_sharp {C₁ C₂ δ θ r : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hδ : 0 < δ)
    (hr : 0 < r) (hrle : r ≤ 2 * δ) (hslack : 8 * C₁ * δ ^ (2 - θ) ≤ 1) :
    C₁ * r ^ 2 + C₂ * r ^ 3 / (16 * C₂ * δ ^ (3 - θ)) ≤ δ ^ θ := by
  have hδθ : (0 : ℝ) < δ ^ θ := rpow_pos_of_pos hδ θ
  have hs2 : δ ^ θ * δ ^ (2 - θ) = δ ^ (2 : ℕ) := rpow_split hδ 2 (by push_cast; ring)
  have hs3 : δ ^ θ * δ ^ (3 - θ) = δ ^ (3 : ℕ) := rpow_split hδ 3 (by push_cast; ring)
  have hr2 : r ^ 2 ≤ (2 * δ) ^ 2 := pow_le_pow_left₀ hr.le hrle 2
  have hr3 : r ^ 3 ≤ (2 * δ) ^ 3 := pow_le_pow_left₀ hr.le hrle 3
  -- the pole term contributes at most half of δ^θ
  have hsecond : C₂ * r ^ 3 / (16 * C₂ * δ ^ (3 - θ)) ≤ δ ^ θ / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    have hexp : δ ^ θ * (16 * C₂ * δ ^ (3 - θ)) = 16 * C₂ * δ ^ (3 : ℕ) := by
      rw [← hs3]; ring
    nlinarith [hr3, hC₂.le, hexp]
  -- the quadratic term contributes at most the other half, by the slack hypothesis
  have hfirst : C₁ * r ^ 2 ≤ δ ^ θ / 2 := by
    have hkey : 8 * C₁ * δ ^ (2 : ℕ) ≤ δ ^ θ := by
      calc 8 * C₁ * δ ^ (2 : ℕ) = (8 * C₁ * δ ^ (2 - θ)) * δ ^ θ := by rw [← hs2]; ring
        _ ≤ 1 * δ ^ θ := mul_le_mul_of_nonneg_right hslack hδθ.le
        _ = δ ^ θ := one_mul _
    nlinarith [hr2, hC₁.le]
  linarith

/-- **Corollary (quadratic order), condition (a).**  With `δ_{m+1} = Kδ²` the margin is
`(16C₂/K)δ`, and one cycle lands inside `Kδ²` provided `4C₁ ≤ K/2`.  This is the endpoint
`θ = 2`, which the old analysis could not reach. -/
theorem contraction_quadratic {C₁ C₂ δ K r : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hδ : 0 < δ)
    (hK : 0 < K) (hr : 0 < r) (hrle : r ≤ 2 * δ) (hKC : 4 * C₁ ≤ K / 2) :
    C₁ * r ^ 2 + C₂ * r ^ 3 / (16 * C₂ / K * δ) ≤ K * δ ^ 2 := by
  have hr2 : r ^ 2 ≤ (2 * δ) ^ 2 := pow_le_pow_left₀ hr.le hrle 2
  have hr3 : r ^ 3 ≤ (2 * δ) ^ 3 := pow_le_pow_left₀ hr.le hrle 3
  have hsecond : C₂ * r ^ 3 / (16 * C₂ / K * δ) ≤ K / 2 * δ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hexp : K / 2 * δ ^ 2 * (16 * C₂ / K * δ) = 8 * C₂ * δ ^ 3 := by
      field_simp; ring
    nlinarith [hr3, hC₂.le, hexp]
  have hfirst : C₁ * r ^ 2 ≤ K / 2 * δ ^ 2 := by nlinarith [hr2, hC₁.le, sq_nonneg δ]
  linarith

end MPE
