import Mathlib
import Formal.Psi
import Formal.SchedGen

/-!
# The dithered process for an arbitrary schedule

`Psi.lean` and `Main.lean` build the dithered process around the doubly-exponential
schedule `sched δ θ m = δ^(θᵐ)`.  Nothing in the measure-theoretic half depends on that
choice: the process, the schedule invariant and the Tonelli reduction use only that the
`m`-th dither radius is *some* positive number `d m ≤ δ`, and that the `m`-th margin
threshold is *some* `s m ∈ (0,1]`.

This file rebuilds that half with `d, s : ℕ → ℝ` abstract, so that the paper's
Theorem 4.9 (quadratic schedule) can be proved from the same anticoncentration input as
Theorem 4.9.  The contraction step — the one place the two schedules genuinely differ — is
a hypothesis here, discharged per schedule.

See `../../corollary.tex` §3 (Obligation 2).
-/

namespace MPE

open MeasureTheory Metric Set
open scoped ENNReal

section Process

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {M : ℕ}

variable (C : CycleData (Fin (M + 2) → ℝ)) (x₀ : Fin (M + 2) → ℝ) (d : ℕ → ℝ)

/-- The iterate `x_m` for the schedule `d`, as a function of the first `m` dithers. -/
noncomputable def xFinG : (m : ℕ) → (Fin m → (Fin (M + 2) → ℝ)) → (Fin (M + 2) → ℝ)
  | 0, _ => x₀
  | (m + 1), u =>
      C.S (xFinG m (fun j => u j.castSucc) + (d m) • clamp (u (Fin.last m)))

/-- The iterate, as a function on the dither space. -/
noncomputable def xProcG (m : ℕ) (ω : ℕ → (Fin (M + 2) → ℝ)) : Fin (M + 2) → ℝ :=
  xFinG C x₀ d m (finRestrict m ω)

/-- The dithered point. -/
noncomputable def yProcG (m : ℕ) (ω : ℕ → (Fin (M + 2) → ℝ)) : Fin (M + 2) → ℝ :=
  xProcG C x₀ d m ω + (d m) • clamp (ω m)

lemma xProcG_zero (ω) : xProcG C x₀ d 0 ω = x₀ := rfl

/-- **The cycle relation**, true by construction. -/
lemma xProcG_succ (m : ℕ) (ω) :
    xProcG C x₀ d (m + 1) ω = C.S (yProcG C x₀ d m ω) := by
  show xFinG C x₀ d (m + 1) (finRestrict (m + 1) ω) = _
  rw [xFinG, finRestrict_castSucc]
  rfl

/-- **The dither is small**, pointwise. -/
lemma norm_yProcG_sub (hd : ∀ m, 0 < d m) (m : ℕ) (ω) :
    ‖yProcG C x₀ d m ω - xProcG C x₀ d m ω‖ ≤ d m := by
  have hsub : yProcG C x₀ d m ω - xProcG C x₀ d m ω = (d m) • clamp (ω m) := by
    rw [yProcG]; abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (hd m)]
  calc d m * ‖clamp (ω m)‖ ≤ d m * 1 :=
        mul_le_mul_of_nonneg_left (norm_clamp_le _) (hd m).le
    _ = d m := mul_one _

lemma measurable_xFinG (hS : Measurable C.S) : ∀ m, Measurable (xFinG C x₀ d m)
  | 0 => measurable_const
  | (m + 1) => by
      refine hS.comp (Measurable.add ?_ ?_)
      · exact (measurable_xFinG hS m).comp
          (measurable_pi_lambda _ fun j => measurable_pi_apply _)
      · have hproj : Measurable
            (fun u : Fin (m + 1) → (Fin (M + 2) → ℝ) => u (Fin.last m)) :=
          measurable_pi_apply _
        exact ((measurable_clamp (M := M)).comp hproj).const_smul (d m)

end Process

/-! ### The good event and the schedule invariant -/

section Invariant

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The good event for an abstract margin threshold: the margin at the dithered point
clears `s m`. -/
def goodGen (C : CycleData E) (s : ℕ → ℝ) (y : ℕ → Ω → E) (m : ℕ) : Set Ω :=
  {ω | s m ≤ C.τ (y m ω)}

omit [MeasurableSpace Ω] in
/-- **The schedule invariant, abstractly.**  The contraction step is a hypothesis: it is
the one place the two schedules of the paper differ. -/
theorem norm_le_of_good_gen (C : CycleData E) {d s : ℕ → ℝ} (x y : ℕ → Ω → E)
    (h0 : ∀ ω, ‖x 0 ω‖ ≤ d 0)
    (hcycle : ∀ m ω, x (m + 1) ω = C.S (y m ω))
    (hdither : ∀ m ω, ‖y m ω - x m ω‖ ≤ d m)
    (hstep : ∀ (m : ℕ) (z : E), 0 < ‖z‖ → ‖z‖ ≤ 2 * d m → s m ≤ C.τ z →
      ‖C.S z‖ ≤ d (m + 1))
    (hs0 : ∀ m, 0 < s m) :
    ∀ (m : ℕ) (ω : Ω), (∀ j < m, ω ∈ goodGen C s y j) → ‖x m ω‖ ≤ d m := by
  intro m
  induction m with
  | zero => intro ω _; exact h0 ω
  | succ k ih =>
      intro ω hω
      have hxk : ‖x k ω‖ ≤ d k := ih ω fun j hj => hω j (by omega)
      have hgood : s k ≤ C.τ (y k ω) := hω k (Nat.lt_succ_self k)
      have hτpos : 0 < C.τ (y k ω) := lt_of_lt_of_le (hs0 k) hgood
      obtain ⟨hypos, -⟩ := C.pos_of_τ_pos hτpos
      have hyle : ‖y k ω‖ ≤ 2 * d k := by
        have hsplit : y k ω = x k ω + (y k ω - x k ω) := by abel
        calc ‖y k ω‖ = ‖x k ω + (y k ω - x k ω)‖ := by rw [← hsplit]
          _ ≤ ‖x k ω‖ + ‖y k ω - x k ω‖ := norm_add_le _ _
          _ ≤ d k + d k := add_le_add hxk (hdither k ω)
          _ = 2 * d k := by ring
      rw [hcycle k ω]
      exact hstep k (y k ω) hypos hyle hgood

/-- **The union bound, abstractly.**  This is `dither_sharp` with the schedule abstract. -/
theorem dither_gen (C : CycleData E) (μ : Measure Ω) {d s : ℕ → ℝ}
    (x y : ℕ → Ω → E) (Ψ : ℕ → ℝ≥0∞)
    (h0 : ∀ ω, ‖x 0 ω‖ ≤ d 0)
    (hcycle : ∀ m ω, x (m + 1) ω = C.S (y m ω))
    (hdither : ∀ m ω, ‖y m ω - x m ω‖ ≤ d m)
    (hstep : ∀ (m : ℕ) (z : E), 0 < ‖z‖ → ‖z‖ ≤ 2 * d m → s m ≤ C.τ z →
      ‖C.S z‖ ≤ d (m + 1))
    (hs0 : ∀ m, 0 < s m)
    (hΨ : ∀ m, μ ((goodGen C s y m)ᶜ ∩ ⋂ j < m, goodGen C s y j) ≤ Ψ m) :
    μ {ω | ∃ m, ¬ ‖x m ω‖ ≤ d m} ≤ ∑' m, Ψ m := by
  refine schedule_induction μ x d (goodGen C s y) Ψ h0 ?_ hΨ
  intro m ω hmem hx
  have hτpos : 0 < C.τ (y m ω) := lt_of_lt_of_le (hs0 m) hmem
  obtain ⟨hypos, -⟩ := C.pos_of_τ_pos hτpos
  have hyle : ‖y m ω‖ ≤ 2 * d m := by
    have hsplit : y m ω = x m ω + (y m ω - x m ω) := by abel
    calc ‖y m ω‖ = ‖x m ω + (y m ω - x m ω)‖ := by rw [← hsplit]
      _ ≤ ‖x m ω‖ + ‖y m ω - x m ω‖ := norm_add_le _ _
      _ ≤ d m + d m := add_le_add hx (hdither m ω)
      _ = 2 * d m := by ring
  rw [hcycle m ω]
  exact hstep m (y m ω) hypos hyle hmem

omit [MeasurableSpace Ω] in
/-- **The enlarged margin dominates `M₀‖y‖`.**  This is the bridge to Lemma 4.4(ii): with
the threshold `s m ≥ 2 M₀ * d m` of the paper's Theorem 4.9, every good cycle satisfies the
hypothesis `τ(y) ≥ M₀‖y‖` of that lemma, and hence has `D ≠ 0`.  Under the deleted
doubly-exponential schedule this was impossible, since there `s m ≍ (d m)^(3-θ) ≪ d m`. -/
theorem margin_dominates_of_good (C : CycleData E) {d s : ℕ → ℝ} {M₀ : ℝ}
    (x y : ℕ → Ω → E)
    (h0 : ∀ ω, ‖x 0 ω‖ ≤ d 0)
    (hcycle : ∀ m ω, x (m + 1) ω = C.S (y m ω))
    (hdither : ∀ m ω, ‖y m ω - x m ω‖ ≤ d m)
    (hstep : ∀ (m : ℕ) (z : E), 0 < ‖z‖ → ‖z‖ ≤ 2 * d m → s m ≤ C.τ z →
      ‖C.S z‖ ≤ d (m + 1))
    (hs0 : ∀ m, 0 < s m)
    (hM₀ : 0 ≤ M₀) (hsM : ∀ m, 2 * M₀ * d m ≤ s m) :
    ∀ (m : ℕ) (ω : Ω), (∀ j ≤ m, ω ∈ goodGen C s y j) → M₀ * ‖y m ω‖ ≤ C.τ (y m ω) := by
  intro m ω hω
  have hxm : ‖x m ω‖ ≤ d m :=
    norm_le_of_good_gen C x y h0 hcycle hdither hstep hs0 m ω fun j hj => hω j (le_of_lt hj)
  have hyle : ‖y m ω‖ ≤ 2 * d m := by
    have hsplit : y m ω = x m ω + (y m ω - x m ω) := by abel
    calc ‖y m ω‖ = ‖x m ω + (y m ω - x m ω)‖ := by rw [← hsplit]
      _ ≤ ‖x m ω‖ + ‖y m ω - x m ω‖ := norm_add_le _ _
      _ ≤ d m + d m := add_le_add hxm (hdither m ω)
      _ = 2 * d m := by ring
  have hgood : s m ≤ C.τ (y m ω) := hω m (le_refl m)
  calc M₀ * ‖y m ω‖ ≤ M₀ * (2 * d m) := mul_le_mul_of_nonneg_left hyle hM₀
    _ = 2 * M₀ * d m := by ring
    _ ≤ s m := hsM m
    _ ≤ C.τ (y m ω) := hgood

/-- **The union bound covering both clauses of Theorem 4.9.**  The failure event now
includes a cycle at which some property `P` of the dithered point fails — for Theorem 4.9,
`P y` is `det U(y) ≠ 0`.  Both clauses hold on the same good event, so the same bound
covers both. -/
theorem dither_gen_full (C : CycleData E) (μ : Measure Ω) {d s : ℕ → ℝ}
    (x y : ℕ → Ω → E) (Ψ : ℕ → ℝ≥0∞) (P : E → Prop)
    (h0 : ∀ ω, ‖x 0 ω‖ ≤ d 0)
    (hcycle : ∀ m ω, x (m + 1) ω = C.S (y m ω))
    (hdither : ∀ m ω, ‖y m ω - x m ω‖ ≤ d m)
    (hstep : ∀ (m : ℕ) (z : E), 0 < ‖z‖ → ‖z‖ ≤ 2 * d m → s m ≤ C.τ z →
      ‖C.S z‖ ≤ d (m + 1))
    (hs0 : ∀ m, 0 < s m)
    (hP : ∀ (m : ℕ) (ω : Ω), (∀ j ≤ m, ω ∈ goodGen C s y j) → P (y m ω))
    (hΨ : ∀ m, μ ((goodGen C s y m)ᶜ ∩ ⋂ j < m, goodGen C s y j) ≤ Ψ m) :
    μ {ω | ∃ m, ¬ ‖x m ω‖ ≤ d m ∨ ¬ P (y m ω)} ≤ ∑' m, Ψ m := by
  have hinv := norm_le_of_good_gen C x y h0 hcycle hdither hstep hs0
  have hsub : {ω | ∃ m, ¬ ‖x m ω‖ ≤ d m ∨ ¬ P (y m ω)}
      ⊆ (⋂ m, goodGen C s y m)ᶜ := by
    intro ω hω hmem
    have hall : ∀ j, ω ∈ goodGen C s y j := fun j => Set.mem_iInter.mp hmem j
    obtain ⟨m, hm⟩ := hω
    rcases hm with hbad | hbad
    · exact hbad (hinv m ω fun j _ => hall j)
    · exact hbad (hP m ω fun j _ => hall j)
  exact le_trans (measure_mono hsub) (measure_compl_iInter_le μ (goodGen C s y) Ψ hΨ)

end Invariant

/-! ### `hΨ` for an arbitrary schedule

The Tonelli reduction of `Psi.hPsi`, with the dither radius `d m` and the margin threshold
`s m` abstract.  The anticoncentration input `hCA` is untouched: it already quantifies over
an arbitrary radius and threshold, which is what makes this possible. -/

section HPsiGen

variable {M : ℕ}

open Poly

/-- **`hΨ`, for an arbitrary schedule.**  Identical to `Psi.hPsi` with
`sched δ θ m ↦ d m` and `16 C₂ (sched δ θ m)^(3-θ) ↦ s m`. -/
theorem hPsiGen_of {ρ : ℝ} (C : CycleData (Fin (M + 2) → ℝ)) (x₀ : Fin (M + 2) → ℝ)
    {d s : ℕ → ℝ} (Ψb : ℝ → ℝ → ℝ≥0∞)
    (hd0 : ∀ m, 0 < d m) (hs0 : ∀ m, 0 < s m) (hs1 : ∀ m, s m ≤ 1)
    (hx₀ : ‖x₀‖ ≤ d 0)
    (hstep : ∀ (m : ℕ) (z : Fin (M + 2) → ℝ), 0 < ‖z‖ → ‖z‖ ≤ 2 * d m → s m ≤ C.τ z →
      ‖C.S z‖ ≤ d (m + 1))
    (hSmeas : Measurable C.S) (hτmeas : Measurable C.τ)
    (hρ : ∀ m : ℕ, 2 * d m ≤ ρ)
    (hCA : ∀ δ' s' : ℝ, 0 < δ' → 2 * δ' ≤ ρ → 0 < s' → s' ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | C.τ (x + δ' • clamp b) < s'} ≤ Ψb δ' s') :
    ∀ m : ℕ,
      (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
          ((goodGen C s (yProcG C x₀ d) m)ᶜ
            ∩ ⋂ j < m, goodGen C s (yProcG C x₀ d) j)
        ≤ Ψb (d m) (s m) := by
  classical
  have hdither : ∀ m ω, ‖yProcG C x₀ d m ω - xProcG C x₀ d m ω‖ ≤ d m :=
    fun m ω => norm_yProcG_sub C x₀ d hd0 m ω
  have hcycle : ∀ m ω, xProcG C x₀ d (m + 1) ω = C.S (yProcG C x₀ d m ω) :=
    fun m ω => xProcG_succ C x₀ d m ω
  have h0 : ∀ ω, ‖xProcG C x₀ d 0 ω‖ ≤ d 0 := fun _ => hx₀
  have hinv := norm_le_of_good_gen C (xProcG C x₀ d) (yProcG C x₀ d) h0 hcycle hdither
    hstep hs0
  intro m
  refine le_trans (measure_mono (?_ :
      ((goodGen C s (yProcG C x₀ d) m)ᶜ
        ∩ ⋂ j < m, goodGen C s (yProcG C x₀ d) j)
      ⊆ {ω : ℕ → (Fin (M + 2) → ℝ) |
          (xFinG C x₀ d m (finRestrict m ω), ω m) ∈
            {p : (Fin (M + 2) → ℝ) × (Fin (M + 2) → ℝ) |
              ‖p.1‖ ≤ d m ∧ C.τ (p.1 + (d m) • clamp p.2) < s m}})) ?_
  · rintro ω ⟨hbad, hpast⟩
    refine ⟨hinv m ω (fun j hj => (Set.mem_iInter₂.mp hpast) j hj), ?_⟩
    exact not_le.mp hbad
  refine measure_past_slice_le _ m (xFinG C x₀ d m)
    (measurable_xFinG C x₀ d hSmeas m) _ ?_ ?_
  · refine MeasurableSet.inter (measurableSet_le measurable_fst.norm measurable_const) ?_
    refine measurableSet_lt (f := fun p : (Fin (M + 2) → ℝ) × (Fin (M + 2) → ℝ) =>
      C.τ (p.1 + (d m) • clamp p.2)) ?_ measurable_const
    refine hτmeas.comp (measurable_fst.add ?_)
    exact ((measurable_clamp (M := M)).comp measurable_snd).const_smul (d m)
  intro x
  by_cases hx : ‖x‖ ≤ d m
  · have hset : {b | (x, b) ∈ {p : (Fin (M + 2) → ℝ) × (Fin (M + 2) → ℝ) |
        ‖p.1‖ ≤ d m ∧ C.τ (p.1 + (d m) • clamp p.2) < s m}}
        = {b | C.τ (x + (d m) • clamp b) < s m} := by
      ext b
      simp only [Set.mem_setOf_eq, and_iff_right hx]
    rw [hset]
    exact hCA _ _ (hd0 m) (hρ m) (hs0 m) (hs1 m) x hx
  · have hempty : {b | (x, b) ∈ {p : (Fin (M + 2) → ℝ) × (Fin (M + 2) → ℝ) |
        ‖p.1‖ ≤ d m ∧ C.τ (p.1 + (d m) • clamp p.2) < s m}} = ∅ := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hx h.1
    rw [hempty]
    simp

/-- **The simple-spectrum specialization**, in the shape Theorem 4.9 consumes.  Theorem 4.7
uses `hPsiGen_of` with a different `Ψb`. -/
theorem hPsiGen {ρ : ℝ} (C : CycleData (Fin (M + 2) → ℝ)) (x₀ : Fin (M + 2) → ℝ)
    {d s : ℕ → ℝ}
    (hd0 : ∀ m, 0 < d m) (hs0 : ∀ m, 0 < s m) (hs1 : ∀ m, s m ≤ 1)
    (hx₀ : ‖x₀‖ ≤ d 0)
    (hstep : ∀ (m : ℕ) (z : Fin (M + 2) → ℝ), 0 < ‖z‖ → ‖z‖ ≤ 2 * d m → s m ≤ C.τ z →
      ‖C.S z‖ ≤ d (m + 1))
    (hSmeas : Measurable C.S) (hτmeas : Measurable C.τ)
    (hρ : ∀ m : ℕ, 2 * d m ≤ ρ)
    {CA : ℝ}
    (hCA : ∀ δ' s' : ℝ, 0 < δ' → 2 * δ' ≤ ρ → 0 < s' → s' ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | C.τ (x + δ' • clamp b) < s'}
          ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
              (s' * Lam s' ^ (M + 1) + δ' * Lam δ' ^ M))) :
    ∀ m : ℕ,
      (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
          ((goodGen C s (yProcG C x₀ d) m)ᶜ
            ∩ ⋂ j < m, goodGen C s (yProcG C x₀ d) j)
        ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
            (s m * Lam (s m) ^ (M + 1) + d m * Lam (d m) ^ M)) :=
  hPsiGen_of C x₀
    (fun δ' s' => ENNReal.ofReal (CA * 2 ^ (M + 3) *
      (s' * Lam s' ^ (M + 1) + δ' * Lam δ' ^ M)))
    hd0 hs0 hs1 hx₀ hstep hSmeas hτmeas hρ hCA

end HPsiGen

end MPE
