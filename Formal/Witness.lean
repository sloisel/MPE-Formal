import Formal.Main

/-!
# Non-vacuity

The theorems of `Formal.Main` are stated under hypotheses.  If those hypotheses were
contradictory the theorems would be true and worthless — this is the `P ∨ True` failure
mode, and reading the statements does **not** rule it out.

This file rules it out, by exhibiting a concrete cycle satisfying all of them:

    Ñ(y) = y³,   σ̃(y) = y,   d = 1,   M = 1,   ρ₁ = 1

for which the margin is identically `1` and one cycle is `S(y) = y²` — genuine quadratic
contraction.  So `CycleData` and `SharpBound` are inhabited, and the good events of both
theorems are attainable rather than empty.
-/

namespace MPE

open Real

/-- A concrete cycle: `Ñ(y) = y³`, `σ̃(y) = y`, in dimension one. -/
noncomputable def witness : CycleData ℝ where
  d := 1
  Ntil := fun y => y ^ 3
  sigt := fun y => y
  M := 1
  ρ₁ := 1
  hd := one_pos
  hM := le_refl 1
  hρ₁ := one_pos
  hN := by
    intro y _
    simp [Real.norm_eq_abs]

/-- One cycle of the witness is `S(y) = y²`: quadratic contraction, as the analysis
expects.  In particular the cycle map is not degenerate. -/
@[simp] lemma witness_S (y : ℝ) : witness.S y = y ^ 2 := by
  have h : witness.S y = y⁻¹ * y ^ 3 := rfl
  rw [h]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · field_simp

/-- The margin of the witness is identically `1` away from the origin.  Hence the margin
thresholds of both theorems are clearable for small `δ`, so their good events are **not**
empty and the conclusions are not vacuous. -/
@[simp] lemma witness_τ {y : ℝ} (hy : y ≠ 0) : witness.τ y = 1 := by
  simp [CycleData.τ, witness, Real.norm_eq_abs, abs_ne_zero.mpr hy]

/-- The sharp bound is satisfiable too, with `C₁ = C₂ = 1`. -/
noncomputable def witnessSharp : SharpBound witness where
  C₁ := 1
  C₂ := 1
  hC₁ := one_pos
  hC₂ := one_pos
  bound := by
    intro y hy _ hσ
    have hy0 : y ≠ 0 := hσ
    rw [witness_S, witness_τ hy0]
    have hn : ‖y ^ 2‖ = ‖y‖ ^ 2 := by simp [Real.norm_eq_abs]
    rw [hn]
    have h3 : (0 : ℝ) ≤ ‖y‖ ^ 3 := by positivity
    simp only [one_mul, div_one]
    linarith

/-- **Non-vacuity, stated.**  There is a cycle satisfying every hypothesis of
`CycleData` and of `SharpBound`. -/
theorem hypotheses_are_satisfiable :
    ∃ (C : CycleData ℝ), Nonempty (SharpBound C) :=
  ⟨witness, ⟨witnessSharp⟩⟩

end MPE
