import Formal.Main
import Formal.Schedule
import Formal.Witness

/-!
# The theorem, assembled

One statement, listing every assumption in one place.  This is the file to read.

The chain is:

  per-cycle margin bound  →  (union bound)  →  ∑ Ψ m  →  (Bernoulli + geometric)  →  2Aδ^p

`dither_sharp` supplies the middle; `Schedule.schedule_series_bound` supplies the right-hand
end; this file joins them and states the result with an explicit constant.
-/

namespace MPE

open Real MeasureTheory Set
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The doubly exponential schedule raised to a power: `δ_m^p = (δ^p)^(θ^m)`.
This is what turns the per-cycle bounds into a geometric series. -/
lemma sched_rpow {δ : ℝ} (hδ : 0 < δ) (θ p : ℝ) (m : ℕ) :
    (sched δ θ m) ^ p = (δ ^ p) ^ (θ ^ m) := by
  rw [sched, ← rpow_natCast, ← rpow_mul hδ.le, ← rpow_mul hδ.le, mul_comm]

/-- **Summing the per-cycle bounds.**  If the per-cycle margin failure is at most
`A·δ_m^p`, the total is at most `2A·δ^p`, provided the geometric ratio `(δ^p)^(θ-1)` is at
most `1/2`.  This is the paper's Step 3, with the corrected Bernoulli argument. -/
theorem tsum_sched_bound {δ θ p A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 1 ≤ θ) (hp : 0 < p)
    (hA : 0 ≤ A) (hratio : (δ ^ p) ^ (θ - 1) ≤ 1 / 2) :
    ∑' m : ℕ, ENNReal.ofReal (A * (sched δ θ m) ^ p) ≤ ENNReal.ofReal (2 * A * δ ^ p) := by
  set q : ℝ := δ ^ p with hq
  have hq0 : 0 < q := rpow_pos_of_pos hδ p
  have hq1 : q ≤ 1 := rpow_le_one hδ.le hδ1 hp.le
  -- rewrite the terms as A * q ^ (θ ^ m)
  have hterm : ∀ m : ℕ, A * (sched δ θ m) ^ p = A * q ^ (θ ^ m) := by
    intro m; rw [sched_rpow hδ]
  -- the real series is summable and bounded by 2Aq
  have hbound : ∑' m : ℕ, q ^ (θ ^ m) ≤ 2 * q :=
    Schedule.schedule_series_bound hq0 hq1 hθ hratio
  have hnn : ∀ m : ℕ, 0 ≤ q ^ (θ ^ m) := fun m => (rpow_pos_of_pos hq0 _).le
  have hr0 : 0 ≤ q ^ (θ - 1) := (rpow_pos_of_pos hq0 _).le
  have hr1 : q ^ (θ - 1) < 1 := lt_of_le_of_lt hratio (by norm_num)
  have hsummable : Summable fun m : ℕ => q ^ (θ ^ m) := by
    refine Summable.of_nonneg_of_le hnn (fun m => Schedule.geometric_term_bound hq0 hq1 hθ m)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left q)
  have hsummableA : Summable fun m : ℕ => A * q ^ (θ ^ m) := hsummable.mul_left A
  calc ∑' m : ℕ, ENNReal.ofReal (A * (sched δ θ m) ^ p)
      = ∑' m : ℕ, ENNReal.ofReal (A * q ^ (θ ^ m)) := by simp_rw [hterm]
    _ = ENNReal.ofReal (∑' m : ℕ, A * q ^ (θ ^ m)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg hA (hnn m)) hsummableA).symm
    _ ≤ ENNReal.ofReal (2 * A * δ ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        rw [tsum_mul_left]
        calc A * ∑' m : ℕ, q ^ (θ ^ m) ≤ A * (2 * q) := by
              exact mul_le_mul_of_nonneg_left hbound hA
          _ = 2 * A * q := by ring

/-- **The theorem, assembled.**

Dithered restarted MPE, in cleared form, with the doubly exponential schedule
`δ_m = δ^(θ^m)`.  If

* `C`  packages the expansion bound of the paper's Lemma 4.1(iii)  (hypothesis);
* `B`  packages the sharp one-cycle bound of Lemma 4.4(iii)        (hypothesis);
* `hΨ` bounds the per-cycle margin failure by `A·δ_m^p`          (hypothesis: this is
  where Brudnyi–Ganzburg, or the anticoncentration lemma, is supplied);

then the invariant `‖x_m‖ ≤ δ_m` fails with probability at most `2A·δ^p`.

Everything else — the one-cycle estimate, the contraction, the induction, the union bound,
the Bernoulli inequality and the geometric summation — is proved. -/
theorem mpe_converges
    (C : CycleData E) (B : SharpBound C) (μ : Measure Ω)
    {δ θ p A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 1 ≤ θ) (hp : 0 < p) (hA : 0 ≤ A)
    (hratio : (δ ^ p) ^ (θ - 1) ≤ 1 / 2)
    (x y : ℕ → Ω → E)
    (h0 : ∀ ω, ‖x 0 ω‖ ≤ δ)
    (hdither : ∀ m ω, ‖y m ω - x m ω‖ ≤ sched δ θ m)
    (hcycle : ∀ m ω, x (m + 1) ω = C.S (y m ω))
    (hsmall : ∀ m, 2 * sched δ θ m ≤ C.ρ₁)
    (hslack : ∀ m, 8 * B.C₁ * (sched δ θ m) ^ (2 - θ) ≤ 1)
    (hΨ : ∀ m, μ ((goodSharp C B δ θ y m)ᶜ ∩ ⋂ j < m, goodSharp C B δ θ y j)
        ≤ ENNReal.ofReal (A * (sched δ θ m) ^ p)) :
    μ {ω | ∃ m, ¬ ‖x m ω‖ ≤ sched δ θ m} ≤ ENNReal.ofReal (2 * A * δ ^ p) :=
  le_trans
    (dither_sharp C B μ hδ x y _ h0 hdither hcycle hsmall hslack hΨ)
    (tsum_sched_bound hδ hδ1 hθ hp hA hratio)

end MPE
