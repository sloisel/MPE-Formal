import Formal.Cycle
import Formal.Induction

/-!
# Convergence of dithered restarted MPE

The paper's Theorem 4.7 (general), Theorem 4.9 (sharp) and Corollary (quadratic order),
assembled from

* `MPE.CycleData.norm_S_le` — one cycle in terms of the margin (Lemma 4.4);
* `MPE.contraction_*`       — the arithmetic of condition (a);
* `MPE.schedule_induction`  — the induction and union bound (Lemma 4.5).

Everything the analysis assumes is a **hypothesis**, visible in the statements below:
the expansion bound (a field of `CycleData`), the sharp bound (a field of `SharpBound`),
and the per-cycle margin-failure probability `Ψ`, which is where Brudnyi–Ganzburg
(Theorem 4.7) or the anticoncentration lemma (Theorem 4.9) would be supplied.
-/

namespace MPE

open Real MeasureTheory Set
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The doubly exponential schedule -/

/-- The schedule `δ_m = δ ^ (θ ^ m)`. -/
noncomputable def sched (δ θ : ℝ) (m : ℕ) : ℝ := δ ^ (θ ^ m)

@[simp] lemma sched_zero (δ θ : ℝ) : sched δ θ 0 = δ := by
  simp [sched]

lemma sched_pos {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (m : ℕ) : 0 < sched δ θ m :=
  rpow_pos_of_pos hδ _

/-- The defining recursion of the schedule: `δ_{m+1} = δ_m ^ θ`. -/
lemma sched_succ {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) (m : ℕ) :
    sched δ θ (m + 1) = (sched δ θ m) ^ θ := by
  rw [sched, sched, pow_succ, rpow_mul hδ.le]

/-! ### Theorem 4.7: the general theorem -/

/-- The good event of Theorem 4.7 at cycle `m`: the margin at the dithered point clears the
threshold `4Mδ_m^(2-θ)`.  The constant sits in the *threshold*, not in a slack exponent —
this is what gives the exponent `(2-θ)/d` rather than `(2-θ)/(2d)`. -/
def goodGeneral (C : CycleData E) (δ θ : ℝ) (y : ℕ → Ω → E) (m : ℕ) : Set Ω :=
  {ω | 4 * C.M * (sched δ θ m) ^ (2 - θ) ≤ C.τ (y m ω)}

/-- **Theorem 4.7 (dithered restarts).**  If the run starts inside the schedule, each dither
moves the point by at most `δ_m`, and the per-cycle margin failure has probability at most
`Ψ m`, then the invariant `‖x_m‖ ≤ δ_m` fails with probability at most `∑ Ψ m`.

The hypotheses `hN` (inside `C`) and `hΨ` are the only inputs; `hΨ` is where
Brudnyi–Ganzburg is supplied. -/
theorem dither_general
    (C : CycleData E) (μ : Measure Ω) {δ θ : ℝ} (hδ : 0 < δ)
    (x y : ℕ → Ω → E) (Ψ : ℕ → ℝ≥0∞)
    (h0 : ∀ ω, ‖x 0 ω‖ ≤ δ)
    (hdither : ∀ m ω, ‖y m ω - x m ω‖ ≤ sched δ θ m)
    (hcycle : ∀ m ω, x (m + 1) ω = C.S (y m ω))
    (hsmall : ∀ m, 2 * sched δ θ m ≤ C.ρ₁)
    (hΨ : ∀ m, μ ((goodGeneral C δ θ y m)ᶜ ∩ ⋂ j < m, goodGeneral C δ θ y j) ≤ Ψ m) :
    μ {ω | ∃ m, ¬ ‖x m ω‖ ≤ sched δ θ m} ≤ ∑' m, Ψ m := by
  refine schedule_induction μ x (sched δ θ) (goodGeneral C δ θ y) Ψ ?_ ?_ hΨ
  · intro ω; simpa using h0 ω
  · -- condition (a): on the good event one cycle stays inside the schedule
    intro m ω hmem hx
    have hδm : 0 < sched δ θ m := sched_pos hδ θ m
    have hthr : 0 < 4 * C.M * (sched δ θ m) ^ (2 - θ) := by
      have : (0 : ℝ) < C.M := lt_of_lt_of_le one_pos C.hM
      positivity
    have hτ : 4 * C.M * (sched δ θ m) ^ (2 - θ) ≤ C.τ (y m ω) := hmem
    have hτpos : 0 < C.τ (y m ω) := lt_of_lt_of_le hthr hτ
    obtain ⟨hypos, hσ⟩ := C.pos_of_τ_pos hτpos
    -- the dithered point is within 2δ_m of the fixed point
    have hyle : ‖y m ω‖ ≤ 2 * sched δ θ m := by
      have hsplit : y m ω = x m ω + (y m ω - x m ω) := by abel
      calc ‖y m ω‖ = ‖x m ω + (y m ω - x m ω)‖ := by rw [← hsplit]
        _ ≤ ‖x m ω‖ + ‖y m ω - x m ω‖ := norm_add_le _ _
        _ ≤ sched δ θ m + sched δ θ m := add_le_add hx (hdither m ω)
        _ = 2 * sched δ θ m := by ring
    have hyρ : ‖y m ω‖ ≤ C.ρ₁ := le_trans hyle (hsmall m)
    rw [hcycle m ω, sched_succ hδ θ m]
    calc ‖C.S (y m ω)‖
        ≤ C.M * ‖y m ω‖ ^ 2 / C.τ (y m ω) := C.norm_S_le hypos hyρ hσ
      _ ≤ (sched δ θ m) ^ θ :=
          contraction_general C.hM hδm hypos hyle hτ

/-! ### Theorem 4.9: the sharp theorem -/

/-- The sharp one-cycle bound of Lemma 4.4(iii), available at the full window under `C³` via
the factorisation `G = Δ·N⁽²⁾`.  Taken as a hypothesis. -/
structure SharpBound (C : CycleData E) where
  C₁ : ℝ
  C₂ : ℝ
  hC₁ : 0 < C₁
  hC₂ : 0 < C₂
  bound : ∀ y : E, 0 < ‖y‖ → ‖y‖ ≤ C.ρ₁ → C.sigt y ≠ 0 →
    ‖C.S y‖ ≤ C₁ * ‖y‖ ^ 2 + C₂ * ‖y‖ ^ 3 / C.τ y

/-- The good event of Theorem 4.9: the margin clears `16C₂δ_m^(3-θ)`.  Note this threshold is
*smaller* than `δ_m` (since `3-θ > 1`), which is exactly why Theorem 4.9 obtains no lower
bound on `D` and is a statement about the cleared form only. -/
def goodSharp (C : CycleData E) (B : SharpBound C) (δ θ : ℝ) (y : ℕ → Ω → E) (m : ℕ) :
    Set Ω :=
  {ω | 16 * B.C₂ * (sched δ θ m) ^ (3 - θ) ≤ C.τ (y m ω)}

/-- **Condition (a) for Theorem 4.9**, extracted so that the schedule invariant
`‖x_m‖ ≤ δ_m` can be re-derived wherever it is needed — in particular when *proving* `hΨ`,
which must know that the centre of the dither ball is inside the schedule. -/
theorem sharp_step
    (C : CycleData E) (B : SharpBound C) {δ θ : ℝ} (hδ : 0 < δ)
    (x y : ℕ → Ω → E)
    (hdither : ∀ m ω, ‖y m ω - x m ω‖ ≤ sched δ θ m)
    (hcycle : ∀ m ω, x (m + 1) ω = C.S (y m ω))
    (hsmall : ∀ m, 2 * sched δ θ m ≤ C.ρ₁)
    (hslack : ∀ m, 8 * B.C₁ * (sched δ θ m) ^ (2 - θ) ≤ 1) :
    ∀ (m : ℕ) (ω : Ω), ω ∈ goodSharp C B δ θ y m → ‖x m ω‖ ≤ sched δ θ m →
      ‖x (m + 1) ω‖ ≤ sched δ θ (m + 1) := by
  intro m ω hmem hx
  have hδm : 0 < sched δ θ m := sched_pos hδ θ m
  have hthr : 0 < 16 * B.C₂ * (sched δ θ m) ^ (3 - θ) := by
    have := B.hC₂; positivity
  have hτ : 16 * B.C₂ * (sched δ θ m) ^ (3 - θ) ≤ C.τ (y m ω) := hmem
  have hτpos : 0 < C.τ (y m ω) := lt_of_lt_of_le hthr hτ
  obtain ⟨hypos, hσ⟩ := C.pos_of_τ_pos hτpos
  have hyle : ‖y m ω‖ ≤ 2 * sched δ θ m := by
    have hsplit : y m ω = x m ω + (y m ω - x m ω) := by abel
    calc ‖y m ω‖ = ‖x m ω + (y m ω - x m ω)‖ := by rw [← hsplit]
      _ ≤ ‖x m ω‖ + ‖y m ω - x m ω‖ := norm_add_le _ _
      _ ≤ sched δ θ m + sched δ θ m := add_le_add hx (hdither m ω)
      _ = 2 * sched δ θ m := by ring
  have hyρ : ‖y m ω‖ ≤ C.ρ₁ := le_trans hyle (hsmall m)
  rw [hcycle m ω, sched_succ hδ θ m]
  have hC2 := B.hC₂
  have hdiv : B.C₂ * ‖y m ω‖ ^ 3 / C.τ (y m ω)
      ≤ B.C₂ * ‖y m ω‖ ^ 3 / (16 * B.C₂ * (sched δ θ m) ^ (3 - θ)) :=
    div_le_div_of_nonneg_left (by positivity) hthr hτ
  calc ‖C.S (y m ω)‖
      ≤ B.C₁ * ‖y m ω‖ ^ 2 + B.C₂ * ‖y m ω‖ ^ 3 / C.τ (y m ω) :=
        B.bound _ hypos hyρ hσ
    _ ≤ B.C₁ * ‖y m ω‖ ^ 2
          + B.C₂ * ‖y m ω‖ ^ 3 / (16 * B.C₂ * (sched δ θ m) ^ (3 - θ)) := by
        linarith
    _ ≤ (sched δ θ m) ^ θ :=
        contraction_sharp B.hC₁ B.hC₂ hδm hypos hyle (hslack m)

/-- **The schedule invariant.**  On the first `m` good events the run is still inside the
schedule.  This is what `hΨ` needs: it puts the centre of the `m`-th dither ball within
`δ_m` of the fixed point, which is the hypothesis of Lemma 4.8. -/
theorem norm_le_sched_of_good
    (C : CycleData E) (B : SharpBound C) {δ θ : ℝ} (hδ : 0 < δ)
    (x y : ℕ → Ω → E)
    (h0 : ∀ ω, ‖x 0 ω‖ ≤ δ)
    (hdither : ∀ m ω, ‖y m ω - x m ω‖ ≤ sched δ θ m)
    (hcycle : ∀ m ω, x (m + 1) ω = C.S (y m ω))
    (hsmall : ∀ m, 2 * sched δ θ m ≤ C.ρ₁)
    (hslack : ∀ m, 8 * B.C₁ * (sched δ θ m) ^ (2 - θ) ≤ 1) :
    ∀ (m : ℕ) (ω : Ω), (∀ j < m, ω ∈ goodSharp C B δ θ y j) →
      ‖x m ω‖ ≤ sched δ θ m := by
  intro m
  induction m with
  | zero => intro ω _; simpa using h0 ω
  | succ k ih =>
      intro ω hω
      exact sharp_step C B hδ x y hdither hcycle hsmall hslack k ω
        (hω k (Nat.lt_succ_self k)) (ih ω fun j hj => hω j (by omega))

/-- **Theorem 4.9 (sharp failure probability).**  Same conclusion as Theorem 4.7, from the
sharp one-cycle bound and the slack condition `8C₁δ_m^(2-θ) ≤ 1`.  Here `hΨ` is where the
anticoncentration lemma is supplied. -/
theorem dither_sharp
    (C : CycleData E) (B : SharpBound C) (μ : Measure Ω) {δ θ : ℝ} (hδ : 0 < δ)
    (x y : ℕ → Ω → E) (Ψ : ℕ → ℝ≥0∞)
    (h0 : ∀ ω, ‖x 0 ω‖ ≤ δ)
    (hdither : ∀ m ω, ‖y m ω - x m ω‖ ≤ sched δ θ m)
    (hcycle : ∀ m ω, x (m + 1) ω = C.S (y m ω))
    (hsmall : ∀ m, 2 * sched δ θ m ≤ C.ρ₁)
    (hslack : ∀ m, 8 * B.C₁ * (sched δ θ m) ^ (2 - θ) ≤ 1)
    (hΨ : ∀ m, μ ((goodSharp C B δ θ y m)ᶜ ∩ ⋂ j < m, goodSharp C B δ θ y j) ≤ Ψ m) :
    μ {ω | ∃ m, ¬ ‖x m ω‖ ≤ sched δ θ m} ≤ ∑' m, Ψ m := by
  refine schedule_induction μ x (sched δ θ) (goodSharp C B δ θ y) Ψ ?_ ?_ hΨ
  · intro ω; simpa using h0 ω
  · exact sharp_step C B hδ x y hdither hcycle hsmall hslack

end MPE
