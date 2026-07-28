import Mathlib
import Formal.Gen
import Formal.Sublevel

/-!
# Theorem 4.7

The paper's general result: `C²` smoothness, no spectral hypothesis beyond
`1 ∉ spec A`, failure probability `C δ^((2-θ)/d)`.

The cycle analysis and the schedule induction are already abstract (`Gen.dither_gen`,
`Cycle.contraction_general`), and the `hΨ` reduction now takes the per-cycle bound as a
parameter (`Gen.hPsiGen_of`).  What is specific to Theorem 4.7 is only the *shape* of that
per-cycle bound: `A (s + δ)^(1/d)` rather than the simple-spectrum
`C_A 2^(n+1) (s Λ(s)^(n-1) + δ Λ(δ)^(n-2))`.

`theorem47_of_anticonc` below is Theorem 4.7 with that bound as a named hypothesis — the
same shape in which `hΨ` was carried for Theorem 4.9 before it was discharged.  Supplying it
is `../../appendix2.tex` Ob.\ref{ob:nd} together with Ob.\ref{ob:off}, and rests on
`Sublevel.sublevel_root`.

See `../../appendix2.tex` §3.
-/

namespace MPE

open MeasureTheory Set
open scoped ENNReal

variable {M : ℕ}

/-- The margin threshold of Theorem 4.7: `h_m = 4 M δ_m^(2-θ)`. -/
noncomputable def hSched (Mc δ θ : ℝ) (m : ℕ) : ℝ := 4 * Mc * (sched δ θ m) ^ (2 - θ)

lemma hSched_pos {Mc δ θ : ℝ} (hMc : 1 ≤ Mc) (hδ : 0 < δ) (m : ℕ) : 0 < hSched Mc δ θ m := by
  have : (0:ℝ) < sched δ θ m := sched_pos hδ θ m
  have hMc0 : (0:ℝ) < Mc := lt_of_lt_of_le one_pos hMc
  rw [hSched]
  positivity

/-- **Condition (a) of Theorem 4.7**, in the shape `dither_gen` and `hPsiGen_of` consume:
on the good event one cycle stays inside the schedule.  This is
`Cycle.contraction_general` plus `CycleData.norm_S_le`. -/
theorem sevenStep (C : CycleData (Fin (M + 2) → ℝ)) {δ θ : ℝ} (hδ : 0 < δ)
    (hρ : ∀ m, 2 * sched δ θ m ≤ C.ρ₁) :
    ∀ (m : ℕ) (z : Fin (M + 2) → ℝ), 0 < ‖z‖ → ‖z‖ ≤ 2 * sched δ θ m →
      hSched C.M δ θ m ≤ C.τ z → ‖C.S z‖ ≤ sched δ θ (m + 1) := by
  intro m z hz0 hzle hτ
  have hδm : 0 < sched δ θ m := sched_pos hδ θ m
  have hτ0 : 0 < C.τ z := lt_of_lt_of_le (hSched_pos C.hM hδ m) hτ
  obtain ⟨-, hσ⟩ := C.pos_of_τ_pos hτ0
  have hzρ : ‖z‖ ≤ C.ρ₁ := le_trans hzle (hρ m)
  have hb := C.norm_S_le hz0 hzρ hσ
  rw [sched_succ hδ θ m]
  exact le_trans hb (contraction_general C.hM hδm hz0 hzle hτ)

/-- **Theorem 4.7, from the anticoncentration bound.**

The hypothesis `hCA` is the paper's Lemma 4.6 in probability form, in the shape the
Tonelli reduction consumes: on the dither ball of radius `δ'` about any admissible centre,
the margin drops below `s'` with probability at most `A (s' + δ')^(1/dQ)`.  Everything else
is the machinery already built for Theorem 4.9. -/
theorem theorem47_of_anticonc (C : CycleData (Fin (M + 2) → ℝ)) {ρ : ℝ}
    (hSmeas : Measurable C.S) (hτmeas : Measurable C.τ)
    {dQ : ℕ} (_hdQ : 0 < dQ) {A : ℝ} (_hA0 : 0 ≤ A)
    (hCA : ∀ δ' s' : ℝ, 0 < δ' → 2 * δ' ≤ ρ → 0 < s' → s' ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | C.τ (x + δ' • clamp b) < s'}
          ≤ ENNReal.ofReal (A * (s' + δ') ^ ((dQ : ℝ)⁻¹)))
    {θ : ℝ} (hθ1 : 1 < θ) (_hθ2 : θ < 2) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ ρ → 2 * δ ≤ C.ρ₁ →
      (∀ m, hSched C.M δ θ m ≤ 1) →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
            {ω | ∃ m, ¬ ‖xProcG C x₀ (sched δ θ) m ω‖ ≤ sched δ θ m
                  ∨ C.sigt (yProcG C x₀ (sched δ θ) m ω) = 0}
          ≤ ∑' m : ℕ, ENNReal.ofReal
              (A * (hSched C.M δ θ m + sched δ θ m) ^ ((dQ : ℝ)⁻¹)) := by
  intro δ hδ hδ1 h2δρ h2δρ₁ hs1 x₀ hx₀
  have hθ0 : (1:ℝ) ≤ θ := hθ1.le
  have hd0 : ∀ m, 0 < sched δ θ m := fun m => sched_pos hδ θ m
  have hdle : ∀ m, sched δ θ m ≤ δ := fun m => sched_le hδ hδ1 hθ0 m
  have hs0 : ∀ m, 0 < hSched C.M δ θ m := fun m => hSched_pos C.hM hδ m
  have hρm : ∀ m, 2 * sched δ θ m ≤ ρ := fun m => by linarith [hdle m]
  have hρ₁m : ∀ m, 2 * sched δ θ m ≤ C.ρ₁ := fun m => by linarith [hdle m]
  have hstep := sevenStep C hδ hρ₁m
  have hx₀d : ‖x₀‖ ≤ sched δ θ 0 := by rwa [sched_zero]
  -- the per-cycle bound, through the Tonelli reduction
  have hpsi := hPsiGen_of C x₀
    (fun δ' s' => ENNReal.ofReal (A * (s' + δ') ^ ((dQ : ℝ)⁻¹)))
    hd0 hs0 hs1 hx₀d hstep hSmeas hτmeas hρm hCA
  -- and the union bound
  have hdither : ∀ m ω, ‖yProcG C x₀ (sched δ θ) m ω
      - xProcG C x₀ (sched δ θ) m ω‖ ≤ sched δ θ m :=
    fun m ω => norm_yProcG_sub C x₀ (sched δ θ) hd0 m ω
  have hcycle : ∀ m ω, xProcG C x₀ (sched δ θ) (m + 1) ω
      = C.S (yProcG C x₀ (sched δ θ) m ω) :=
    fun m ω => xProcG_succ C x₀ (sched δ θ) m ω
  have hP : ∀ (m : ℕ) (ω : ℕ → Fin (M + 2) → ℝ),
      (∀ j ≤ m, ω ∈ goodGen C (hSched C.M δ θ) (yProcG C x₀ (sched δ θ)) j) →
        C.sigt (yProcG C x₀ (sched δ θ) m ω) ≠ 0 := fun m ω h =>
    (C.pos_of_τ_pos (lt_of_lt_of_le (hs0 m) (h m (le_refl m)))).2
  have := dither_gen_full C (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
    (xProcG C x₀ (sched δ θ)) (yProcG C x₀ (sched δ θ)) _
    (fun z => C.sigt z ≠ 0)
    (fun _ => hx₀d) hcycle hdither hstep hs0 hP hpsi
  refine le_trans (le_of_eq ?_) this
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, not_not]

/-! ### Summing the series

Theorem 4.7's induction runs at `(p₁,q₁) = ((2-θ)/d, 0)`: the exponent `q₁ = 0` means *no
logarithms*, so the plain `Schedule.schedule_series_bound` suffices and neither
`SchedLog.lean` nor `SchedGen.lean` is needed. -/

open Real in
/-- **Theorem 4.7**, with the series summed: failure probability `C δ^((2-θ)/d)`. -/
theorem theorem47 (C : CycleData (Fin (M + 2) → ℝ)) {ρ : ℝ}
    (hSmeas : Measurable C.S) (hτmeas : Measurable C.τ)
    {dQ : ℕ} (hdQ : 0 < dQ) {A : ℝ} (hA0 : 0 ≤ A)
    (hCA : ∀ δ' s' : ℝ, 0 < δ' → 2 * δ' ≤ ρ → 0 < s' → s' ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | C.τ (x + δ' • clamp b) < s'}
          ≤ ENNReal.ofReal (A * (s' + δ') ^ ((dQ : ℝ)⁻¹)))
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ Cst : ℝ, 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ ρ → 2 * δ ≤ C.ρ₁ →
        (∀ m, hSched C.M δ θ m ≤ 1) →
        ((δ ^ ((2 - θ) / dQ)) ^ (θ - 1) ≤ 1 / 2) →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
            {ω | ∃ m, ¬ ‖xProcG C x₀ (sched δ θ) m ω‖ ≤ sched δ θ m
                  ∨ C.sigt (yProcG C x₀ (sched δ θ) m ω) = 0}
          ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / dQ)) := by
  have hM1 := C.hM
  have hM0 : (0:ℝ) < C.M := lt_of_lt_of_le one_pos hM1
  set A' : ℝ := 2 * (A * (4 * C.M + 1) ^ ((dQ : ℝ)⁻¹)) + 1 with hA'def
  have hA'0 : 0 < A' := by
    have : (0:ℝ) ≤ A * (4 * C.M + 1) ^ ((dQ : ℝ)⁻¹) :=
      mul_nonneg hA0 (Real.rpow_nonneg (by positivity) _)
    rw [hA'def]; linarith
  refine ⟨A', hA'0, ?_⟩
  intro δ hδ hδ1 h2δρ h2δρ₁ hs1 hratio x₀ hx₀
  have hθ0 : (1:ℝ) ≤ θ := hθ1.le
  have hd0 : ∀ m, 0 < sched δ θ m := fun m => sched_pos hδ θ m
  have hdle : ∀ m, sched δ θ m ≤ δ := fun m => sched_le hδ hδ1 hθ0 m
  have hd1 : ∀ m, sched δ θ m ≤ 1 := fun m => le_trans (hdle m) hδ1
  refine le_trans (theorem47_of_anticonc C hSmeas hτmeas hdQ hA0 hCA hθ1 hθ2
    δ hδ hδ1 h2δρ h2δρ₁ hs1 x₀ hx₀) ?_
  set p : ℝ := (2 - θ) / dQ with hpdef
  have hp0 : 0 < p := by
    rw [hpdef]
    have : (0:ℝ) < (dQ : ℝ) := by exact_mod_cast hdQ
    have : (0:ℝ) < 2 - θ := by linarith
    positivity
  set q : ℝ := δ ^ p with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hδ p
  have hq1 : q ≤ 1 := Real.rpow_le_one hδ.le hδ1 hp0.le
  -- each term is at most `A'' · q^(θ^m)`
  have hterm : ∀ m : ℕ,
      A * (hSched C.M δ θ m + sched δ θ m) ^ ((dQ : ℝ)⁻¹)
        ≤ (A * (4 * C.M + 1) ^ ((dQ : ℝ)⁻¹)) * q ^ (θ ^ m) := by
    intro m
    have hdm := hd0 m
    have hdm1 := hd1 m
    have hpow : sched δ θ m ≤ (sched δ θ m) ^ (2 - θ) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hdm hdm1 (by linarith : (2:ℝ) - θ ≤ 1)
      rwa [Real.rpow_one] at h
    have hsum : hSched C.M δ θ m + sched δ θ m
        ≤ (4 * C.M + 1) * (sched δ θ m) ^ (2 - θ) := by
      rw [hSched]; nlinarith [hpow, hM0]
    have h1 : (hSched C.M δ θ m + sched δ θ m) ^ ((dQ : ℝ)⁻¹)
        ≤ ((4 * C.M + 1) * (sched δ θ m) ^ (2 - θ)) ^ ((dQ : ℝ)⁻¹) :=
      Real.rpow_le_rpow (add_nonneg (hSched_pos C.hM hδ m).le (hd0 m).le)
        hsum (by positivity : (0:ℝ) ≤ (dQ : ℝ)⁻¹)
    have h2 : ((4 * C.M + 1) * (sched δ θ m) ^ (2 - θ)) ^ ((dQ : ℝ)⁻¹)
        = (4 * C.M + 1) ^ ((dQ : ℝ)⁻¹) * q ^ (θ ^ m) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      rw [hqdef, sched, ← Real.rpow_mul hδ.le, ← Real.rpow_mul hδ.le, ← Real.rpow_mul hδ.le,
        hpdef]
      congr 1
      field_simp
    calc A * (hSched C.M δ θ m + sched δ θ m) ^ ((dQ : ℝ)⁻¹)
        ≤ A * ((4 * C.M + 1) * (sched δ θ m) ^ (2 - θ)) ^ ((dQ : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 hA0
      _ = (A * (4 * C.M + 1) ^ ((dQ : ℝ)⁻¹)) * q ^ (θ ^ m) := by rw [h2]; ring
  -- sum the geometric-type series
  have hsummable : Summable fun m : ℕ => q ^ (θ ^ m) := by
    have hr0 : (0:ℝ) ≤ q ^ (θ - 1) := (Real.rpow_pos_of_pos hq0 _).le
    have hr1 : q ^ (θ - 1) < 1 := lt_of_le_of_lt hratio (by norm_num)
    refine Summable.of_nonneg_of_le (fun m => (Real.rpow_pos_of_pos hq0 _).le)
      (fun m => Schedule.geometric_term_bound hq0 hq1 hθ0 m)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left q)
  have hser : ∑' m : ℕ, q ^ (θ ^ m) ≤ 2 * q := Schedule.schedule_series_bound hq0 hq1 hθ0 hratio
  calc ∑' m : ℕ, ENNReal.ofReal (A * (hSched C.M δ θ m + sched δ θ m) ^ ((dQ : ℝ)⁻¹))
      ≤ ∑' m : ℕ, ENNReal.ofReal ((A * (4 * C.M + 1) ^ ((dQ : ℝ)⁻¹)) * q ^ (θ ^ m)) :=
        ENNReal.tsum_le_tsum fun m => ENNReal.ofReal_le_ofReal (hterm m)
    _ = ENNReal.ofReal ((A * (4 * C.M + 1) ^ ((dQ : ℝ)⁻¹)) * ∑' m : ℕ, q ^ (θ ^ m)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun m => by positivity) (hsummable.mul_left _), tsum_mul_left]
    _ ≤ ENNReal.ofReal (A' * q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hcc : (0:ℝ) ≤ A * (4 * C.M + 1) ^ ((dQ : ℝ)⁻¹) :=
          mul_nonneg hA0 (Real.rpow_nonneg (by positivity) _)
        calc (A * (4 * C.M + 1) ^ ((dQ : ℝ)⁻¹)) * ∑' m : ℕ, q ^ (θ ^ m)
            ≤ (A * (4 * C.M + 1) ^ ((dQ : ℝ)⁻¹)) * (2 * q) :=
              mul_le_mul_of_nonneg_left hser hcc
          _ ≤ A' * q := by rw [hA'def]; nlinarith [hq0.le, hcc]

end MPE
