import Mathlib

/-!
# The schedule induction

Formalisation of the paper's Lemma "schedule induction": the deterministic induction on
the invariant `‖x_m‖ ≤ δ_m`, combined with the union bound over the per-cycle margin
failures.

This is the part of the argument that is indifferent to *where* the margin bound comes
from, and it is shared by Theorem 4.7 (Brudnyi–Ganzburg input) and Theorem 4.9
(anticoncentration input).
-/

namespace MPE

open MeasureTheory Set
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]

omit [MeasurableSpace Ω] in
/-- **First-failure decomposition.**  If some good event fails, then there is a *first* one
that fails.  This is what turns a bare union into the disjointified form the per-cycle
estimate applies to. -/
lemma compl_iInter_subset (H : ℕ → Set Ω) :
    (⋂ m, H m)ᶜ ⊆ ⋃ m, ((H m)ᶜ ∩ ⋂ j < m, H j) := by
  classical
  intro ω hω
  simp only [mem_compl_iff, mem_iInter, not_forall] at hω
  obtain ⟨m, hm⟩ := hω
  have hex : ∃ k, ω ∉ H k := ⟨m, hm⟩
  refine mem_iUnion.mpr ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  simp only [mem_iInter]
  intro j hj
  by_contra hcon
  exact absurd (Nat.find_le hcon) (not_le.mpr hj)

/-- **Union bound.**  The probability that any good event fails is at most the sum of the
per-cycle conditional bounds. -/
theorem measure_compl_iInter_le (μ : Measure Ω) (H : ℕ → Set Ω) (Ψ : ℕ → ℝ≥0∞)
    (hΨ : ∀ m, μ ((H m)ᶜ ∩ ⋂ j < m, H j) ≤ Ψ m) :
    μ ((⋂ m, H m)ᶜ) ≤ ∑' m, Ψ m :=
  calc μ ((⋂ m, H m)ᶜ)
      ≤ μ (⋃ m, ((H m)ᶜ ∩ ⋂ j < m, H j)) := measure_mono (compl_iInter_subset H)
    _ ≤ ∑' m, μ ((H m)ᶜ ∩ ⋂ j < m, H j) := measure_iUnion_le _
    _ ≤ ∑' m, Ψ m := ENNReal.tsum_le_tsum hΨ

/-- **Lemma (schedule induction).**

Given a schedule `δ`, iterates `x`, and good events `H` such that

* `h0`  : the run starts inside the schedule;
* `hstep` : on the good event, one cycle stays inside the schedule (condition (a));
* `hΨ`  : the per-cycle margin failure has probability at most `Ψ m` (condition (b));

the probability that the invariant `‖x_m‖ ≤ δ_m` ever fails is at most `∑ Ψ m`.

Both Theorem 4.7 and Theorem 4.9 are this lemma with different `Ψ`. -/
theorem schedule_induction (μ : Measure Ω) (x : ℕ → Ω → E) (δ : ℕ → ℝ) (H : ℕ → Set Ω)
    (Ψ : ℕ → ℝ≥0∞)
    (h0 : ∀ ω, ‖x 0 ω‖ ≤ δ 0)
    (hstep : ∀ (m : ℕ) (ω : Ω), ω ∈ H m → ‖x m ω‖ ≤ δ m → ‖x (m + 1) ω‖ ≤ δ (m + 1))
    (hΨ : ∀ m, μ ((H m)ᶜ ∩ ⋂ j < m, H j) ≤ Ψ m) :
    μ {ω | ∃ m, ¬ ‖x m ω‖ ≤ δ m} ≤ ∑' m, Ψ m := by
  -- on every good event the invariant propagates, by induction on the cycle count
  have hgood : ∀ ω ∈ ⋂ m, H m, ∀ m, ‖x m ω‖ ≤ δ m := by
    intro ω hω m
    induction m with
    | zero => exact h0 ω
    | succ k ih => exact hstep k ω (mem_iInter.mp hω k) ih
  have hsub : {ω | ∃ m, ¬ ‖x m ω‖ ≤ δ m} ⊆ (⋂ m, H m)ᶜ := by
    intro ω hω hmem
    obtain ⟨m, hm⟩ := hω
    exact hm (hgood ω hmem m)
  exact le_trans (measure_mono hsub) (measure_compl_iInter_le μ H Ψ hΨ)

end MPE
