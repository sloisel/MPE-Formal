import Mathlib
import Formal.Main
import Formal.Anticonc
import Formal.SchedLog

/-!
# The dither space: finite marginals of an infinite product

Appendix Obligation 10, first half.  The dither sequence lives on `Ω = ∏_{m} B` with the
product probability measure (`Measure.infinitePi`).  Everything the Tonelli reduction needs
is the *finite marginal*: the law of the first `k` coordinates is the finite product
measure, on which `measurePreserving_piFinSuccAbove` then splits off the last coordinate.

`Measure.infinitePi_map_restrict` gives this for the index set `Finset.range k`, whose
coercion is `↥(range k)`; this file transports it to `Fin k`, which is the shape the rest
of the development uses.
-/

namespace MPE

open MeasureTheory Measure

variable {B : Type*} [MeasurableSpace B]

/-- `Fin k ≃ ↥(Finset.range k)`. -/
def rangeEquivFin (k : ℕ) : Fin k ≃ ↥(Finset.range k) where
  toFun i := ⟨i.1, Finset.mem_range.mpr i.2⟩
  invFun j := ⟨j.1, Finset.mem_range.mp j.2⟩
  left_inv i := by ext; rfl
  right_inv j := by ext; rfl

/-- Restriction of a sequence to its first `k` terms. -/
def finRestrict (k : ℕ) (ω : ℕ → B) : Fin k → B := fun i => ω (i : ℕ)

lemma measurable_finRestrict (k : ℕ) : Measurable (finRestrict (B := B) k) :=
  measurable_pi_lambda _ fun _i => measurable_pi_apply _

omit [MeasurableSpace B] in
lemma finRestrict_castSucc (k : ℕ) (ω : ℕ → B) :
    (fun j : Fin k => finRestrict (k + 1) ω j.castSucc) = finRestrict k ω := by
  funext j; rfl

/-- **The finite marginal.**  The law of the first `k` coordinates of the infinite product
is the finite product measure. -/
theorem map_finRestrict (ν : Measure B) [IsProbabilityMeasure ν] (k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (finRestrict k)
      = Measure.pi (fun _ : Fin k => ν) := by
  classical
  set I : Finset ℕ := Finset.range k with hI
  set e : Fin k ≃ ↥I := rangeEquivFin k with he
  -- the restriction to `I` has the finite product law
  have h1 : (Measure.infinitePi (fun _ : ℕ => ν)).map I.restrict
      = Measure.pi (fun _ : ↥I => ν) := Measure.infinitePi_map_restrict _
  -- reindexing `↥I` by `Fin k` is measure preserving
  have h2 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ↥I => B) e).symm
      (Measure.pi (fun _ : ↥I => ν)) (Measure.pi (fun _ : Fin k => ν)) :=
    (measurePreserving_piCongrLeft (fun _ : ↥I => ν) e).symm _
  -- and the composite is `finRestrict`
  have hcomp : finRestrict (B := B) k
      = (MeasurableEquiv.piCongrLeft (fun _ : ↥I => B) e).symm ∘ I.restrict := by
    funext ω i
    rfl
  rw [hcomp, ← Measure.map_map
      (MeasurableEquiv.measurable (MeasurableEquiv.piCongrLeft (fun _ : ↥I => B) e).symm)
      (Finset.measurable_restrict I), h1, h2.map_eq]

/-! ### The Tonelli reduction

An event of the form "the past determines `x`, and the fresh coordinate `ω m` makes
something happen" has probability at most the uniform bound on the fresh coordinate's
slice.  This is the whole content of the appendix's Obligation 10: no conditional
distributions, no filtration — the coordinate `m` is split off the finite marginal by
`measurePreserving_piFinSuccAbove`, exactly as in `Formal/Blocks.lean`.
-/

open scoped ENNReal

theorem measure_past_slice_le {E : Type*} [MeasurableSpace E]
    (ν : Measure B) [IsProbabilityMeasure ν] (m : ℕ)
    (f : (Fin m → B) → E) (hf : Measurable f)
    (Z : Set (E × B)) (hZ : MeasurableSet Z) {K : ℝ≥0∞}
    (hK : ∀ x : E, ν {b | (x, b) ∈ Z} ≤ K) :
    (Measure.infinitePi (fun _ : ℕ => ν))
        {ω : ℕ → B | (f (finRestrict m ω), ω m) ∈ Z} ≤ K := by
  classical
  -- the event is a cylinder on the first `m+1` coordinates
  set S : Set (Fin (m + 1) → B) :=
    {u | (f (fun j : Fin m => u j.castSucc), u (Fin.last m)) ∈ Z} with hS
  have hSmeas : MeasurableSet S := by
    refine hZ.preimage ?_
    exact ((hf.comp (measurable_pi_lambda _ fun j => measurable_pi_apply _)).prodMk
      (measurable_pi_apply _))
  have hcyl : {ω : ℕ → B | (f (finRestrict m ω), ω m) ∈ Z}
      = finRestrict (m + 1) ⁻¹' S := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS, finRestrict]
    rfl
  rw [hcyl, ← Measure.map_apply (measurable_finRestrict _) hSmeas, map_finRestrict ν (m + 1)]
  -- split off the last coordinate
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => B) (Fin.last m) with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) (Fin.last m)
  set T : Set (B × ((j : Fin m) → B)) := {p | (f p.2, p.1) ∈ Z} with hT
  have hTmeas : MeasurableSet T := by
    refine hZ.preimage ?_
    exact ((hf.comp measurable_snd).prodMk measurable_fst)
  have hpre : e ⁻¹' T = S := by
    ext u
    have h1 : (e u).1 = u (Fin.last m) := rfl
    have h2 : (e u).2 = fun j : Fin m => u j.castSucc := by
      funext j
      show u ((Fin.last m).succAbove j) = u j.castSucc
      rw [Fin.succAbove_last]
    simp only [Set.mem_preimage, hT, hS, Set.mem_setOf_eq, h1, h2]
  rw [← hpre, hmp.measure_preimage hTmeas.nullMeasurableSet]
  -- Tonelli, then the uniform slice bound
  rw [Measure.prod_apply_symm hTmeas]
  calc ∫⁻ y, ν ((fun b => (b, y)) ⁻¹' T) ∂(Measure.pi fun _ : Fin m => ν)
      ≤ ∫⁻ _, K ∂(Measure.pi fun _ : Fin m => ν) := by
        refine lintegral_mono fun y => ?_
        have : (fun b => (b, y)) ⁻¹' T = {b | (f y, b) ∈ Z} := by
          ext b; simp [hT]
        rw [this]
        exact hK (f y)
    _ = K := by rw [lintegral_const, measure_univ, mul_one]

/-! ### The dithered process

The process is *defined* through `finRestrict m`, so "the past depends only on the past" is
true by construction rather than something to prove.  The dither is clamped into the cube so
that `‖ξ_m‖ ≤ δ_m` holds **pointwise**, as `dither_sharp` requires; since the dither measure
is supported on the cube, clamping changes nothing almost everywhere.
-/

section Dither

variable {M : ℕ}

/-- Clamp a vector into the closed unit cube. -/
def clamp (v : Fin (M + 2) → ℝ) : Fin (M + 2) → ℝ := fun i => max (-1) (min 1 (v i))

lemma norm_clamp_le (v : Fin (M + 2) → ℝ) : ‖clamp v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clamp_eq_self {v : Fin (M + 2) → ℝ} (hv : ‖v‖ ≤ 1) : clamp v = v := by
  funext i
  have : |v i| ≤ 1 := by
    have := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at this
    linarith [this, hv]
  rw [abs_le] at this
  rw [clamp, min_eq_right this.2, max_eq_right this.1]

lemma measurable_clamp : Measurable (clamp (M := M)) := by
  unfold clamp
  fun_prop

variable (C : CycleData (Fin (M + 2) → ℝ)) (x₀ : Fin (M + 2) → ℝ) (δ θ : ℝ)

/-- The iterate `x_m`, as a function of the first `m` dithers. -/
noncomputable def xFin : (m : ℕ) → (Fin m → (Fin (M + 2) → ℝ)) → (Fin (M + 2) → ℝ)
  | 0, _ => x₀
  | (m + 1), u =>
      C.S (xFin m (fun j => u j.castSucc) + (sched δ θ m) • clamp (u (Fin.last m)))

/-- The iterate, as a function on the dither space. -/
noncomputable def xProc (m : ℕ) (ω : ℕ → (Fin (M + 2) → ℝ)) : Fin (M + 2) → ℝ :=
  xFin C x₀ δ θ m (finRestrict m ω)

/-- The dithered point. -/
noncomputable def yProc (m : ℕ) (ω : ℕ → (Fin (M + 2) → ℝ)) : Fin (M + 2) → ℝ :=
  xProc C x₀ δ θ m ω + (sched δ θ m) • clamp (ω m)

lemma xProc_zero (ω) : xProc C x₀ δ θ 0 ω = x₀ := rfl

/-- **The cycle relation**, true by construction. -/
lemma xProc_succ (m : ℕ) (ω) :
    xProc C x₀ δ θ (m + 1) ω = C.S (yProc C x₀ δ θ m ω) := by
  show xFin C x₀ δ θ (m + 1) (finRestrict (m + 1) ω) = _
  rw [xFin, finRestrict_castSucc]
  rfl

/-- **The dither is small**, pointwise. -/
lemma norm_yProc_sub (hδ : 0 < δ) (m : ℕ) (ω) :
    ‖yProc C x₀ δ θ m ω - xProc C x₀ δ θ m ω‖ ≤ sched δ θ m := by
  have hsub : yProc C x₀ δ θ m ω - xProc C x₀ δ θ m ω
      = (sched δ θ m) • clamp (ω m) := by
    rw [yProc]; abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (sched_pos hδ θ m)]
  calc sched δ θ m * ‖clamp (ω m)‖ ≤ sched δ θ m * 1 :=
        mul_le_mul_of_nonneg_left (norm_clamp_le _) (sched_pos hδ θ m).le
    _ = sched δ θ m := mul_one _

lemma measurable_xFin (hS : Measurable C.S) :
    ∀ m, Measurable (xFin C x₀ δ θ m)
  | 0 => measurable_const
  | (m + 1) => by
      refine hS.comp (Measurable.add ?_ ?_)
      · exact (measurable_xFin hS m).comp
          (measurable_pi_lambda _ fun j => measurable_pi_apply _)
      · have hproj : Measurable
            (fun u : Fin (m + 1) → (Fin (M + 2) → ℝ) => u (Fin.last m)) :=
          measurable_pi_apply _
        exact ((measurable_clamp (M := M)).comp hproj).const_smul (sched δ θ m)

end Dither

/-! ### `hΨ`

The three ingredients meet here: the schedule invariant puts the centre of the `m`-th
dither ball inside `δ_m`; the Tonelli reduction turns the event into a uniform bound on the
fresh coordinate's slice; and Lemma 4.8 supplies that bound. -/

section HPsi

open Poly

variable {M : ℕ} {A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
  {q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ}

lemma sched_le {δ θ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 1 ≤ θ) (m : ℕ) :
    sched δ θ m ≤ δ := by
  rw [sched]
  calc δ ^ (θ ^ m) ≤ δ ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (one_le_pow₀ hθ)
    _ = δ := Real.rpow_one δ

/-! ### Normalizing the eigenbasis

`hcontr` (`‖P⁻¹z‖ ≤ ‖z‖`) is a normalization, not a restriction: replacing `P` by `κP`
for large `κ` leaves the eigenvector relation intact and shrinks `P⁻¹` as much as wanted.
-/

lemma exists_scaled_eigenbasis {P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
    {lam : Fin (M + 2) → ℝ} (hP : IsUnit P.det)
    (hAP : A * P = P * Matrix.diagonal lam) :
    ∃ P' : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ, IsUnit P'.det ∧
      A * P' = P' * Matrix.diagonal lam ∧
      ∀ z : Fin (M + 2) → ℝ, ‖(P'⁻¹).mulVec z‖ ≤ ‖z‖ := by
  classical
  set K : ℝ := (∑ i, ∑ j, |(P⁻¹) i j|) + 1 with hK
  have hK1 : (1:ℝ) ≤ K := by
    have : (0:ℝ) ≤ ∑ i, ∑ j, |(P⁻¹) i j| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    rw [hK]; linarith
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
  refine ⟨K • P, ?_, ?_, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin]
    exact (isUnit_iff_ne_zero.mpr (by positivity)).mul hP
  · rw [Matrix.mul_smul, Matrix.smul_mul, hAP]
  · intro z
    have hinv : (K • P)⁻¹ = K⁻¹ • P⁻¹ := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_nonsing_inv P hP, smul_smul,
        mul_inv_cancel₀ hK0.ne', one_smul]
    rw [hinv, Matrix.smul_mulVec, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < K⁻¹)]
    have hb := norm_mulVec_le (P⁻¹) z
    rw [inv_mul_le_iff₀ hK0]
    calc ‖P⁻¹.mulVec z‖ ≤ (∑ i, ∑ j, |(P⁻¹) i j|) * ‖z‖ := hb
      _ ≤ K * ‖z‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg z)
          rw [hK]; linarith

/-! ### Measurability of the concrete cycle data -/

lemma measurable_cycleData_sigt (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) :
    Measurable (cycleData hq hA).sigt :=
  (MvPolynomial.continuous_eval _).measurable

lemma measurable_cycleData_Ntil (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) :
    Measurable (cycleData hq hA).Ntil :=
  measurable_pi_lambda _ fun _i => (MvPolynomial.continuous_eval _).measurable

lemma measurable_cycleData_S (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) :
    Measurable (cycleData hq hA).S := by
  show Measurable fun y => ((cycleData hq hA).sigt y)⁻¹ • (cycleData hq hA).Ntil y
  exact ((measurable_cycleData_sigt hq hA).inv).smul (measurable_cycleData_Ntil hq hA)

lemma measurable_cycleData_tau (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) :
    Measurable (cycleData hq hA).τ := by
  show Measurable fun y => |(cycleData hq hA).sigt y| / ‖y‖ ^ (cycleData hq hA).d
  exact ((measurable_cycleData_sigt hq hA).abs).div (measurable_norm.pow_const _)

/-- `σ̃` vanishes at the origin (it has no constant term). -/
lemma eval_sigtPoly_zero (hq : ∀ i, LowDeg 2 (q i)) :
    MvPolynomial.eval (0 : Fin (M + 2) → ℝ) (sigtPoly A q) = 0 := by
  have h := (lowDeg_sigt (A := A) hq).abs_eval_le (0 : Fin (M + 2) → ℝ) (by simp)
  have hz : ‖(0 : Fin (M + 2) → ℝ)‖ ^ (M + 2) = 0 := by simp
  rw [hz, mul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- The margin event implies the polynomial inequality Lemma 4.8 bounds. -/
lemma tau_lt_imp {Sig : (Fin (M + 2) → ℝ) → ℝ} (C : CycleData (Fin (M + 2) → ℝ))
    (hd : C.d = M + 2) (hsig : ∀ y, C.sigt y = Sig y) (hz : Sig 0 = 0)
    {s : ℝ} {y : Fin (M + 2) → ℝ} (h : C.τ y < s) :
    |Sig y| ≤ s * ‖y‖ ^ (M + 2) := by
  rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
  · -- `y = 0`
    have hy : y = 0 := norm_eq_zero.mp h0.symm
    rw [hy, hz]
    simp
  · have habs := C.sigt_abs y h0
    rw [hd] at habs
    have hyn : (0:ℝ) < ‖y‖ ^ (M + 2) := pow_pos h0 _
    rw [← hsig y, habs]
    nlinarith

/-- **The slice bound.**  For a dither uniform on the unit cube, clamped and scaled, the
margin fails with probability at most Lemma 4.8's bound. -/
theorem slice_bound {Sig : (Fin (M + 2) → ℝ) → ℝ} {ρ : ℝ}
    (C : CycleData (Fin (M + 2) → ℝ))
    (hd : C.d = M + 2) (hsig : ∀ y, C.sigt y = Sig y) (hz : Sig 0 = 0)
    (h7 : ∃ CA : ℝ, 0 < CA ∧ ∀ δ s : ℝ, 0 < δ → 2 * δ ≤ ρ → 0 < s → s ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ →
        blockMeasure (M + 2)
            {b | |Sig (x + δ • b)|
                ≤ s * ‖x + δ • b‖ ^ (M + 2)}
          ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
              (s * Lam s ^ (M + 1) + δ * Lam δ ^ M))) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ δ s : ℝ, 0 < δ → 2 * δ ≤ ρ → 0 < s → s ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ →
        blockMeasure (M + 2) {b | C.τ (x + δ • clamp b) < s}
          ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
              (s * Lam s ^ (M + 1) + δ * Lam δ ^ M)) := by
  obtain ⟨CA, hCA0, hCA⟩ := h7
  refine ⟨CA, hCA0, ?_⟩
  intro δ s hδ h2δ hs hs1 x hx
  set S : Set (Fin (M + 2) → ℝ) := {b | C.τ (x + δ • clamp b) < s} with hS
  set T : Set (Fin (M + 2) → ℝ) :=
    {b | |Sig (x + δ • b)| ≤ s * ‖x + δ • b‖ ^ (M + 2)} with hT
  -- off the cube the dither measure is null; on it, clamping is the identity
  have hsub : S ∩ cube (M + 2) ⊆ T := by
    rintro b ⟨hb, hbc⟩
    have hbn : ‖b‖ ≤ 1 := by rwa [← closedBall_eq_cube] at hbc
    have : clamp b = b := clamp_eq_self hbn
    rw [hS, Set.mem_setOf_eq, this] at hb
    exact tau_lt_imp C hd hsig hz hb
  calc blockMeasure (M + 2) S
      ≤ blockMeasure (M + 2) (S ∩ cube (M + 2))
        + blockMeasure (M + 2) (cube (M + 2))ᶜ := by
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro b hb
        by_cases hbc : b ∈ cube (M + 2)
        · exact Or.inl ⟨hb, hbc⟩
        · exact Or.inr hbc
    _ = blockMeasure (M + 2) (S ∩ cube (M + 2)) := by
        rw [blockMeasure_compl_cube, add_zero]
    _ ≤ blockMeasure (M + 2) T := measure_mono hsub
    _ ≤ _ := hCA δ s hδ h2δ hs hs1 x hx

/-- **`hΨ`.**  The per-cycle margin-failure probability of the dithered process, bounded by
Lemma 4.8 uniformly in the past.  This is the hypothesis `MPE.dither_sharp` takes. -/
theorem hPsi {ρ : ℝ} (C : CycleData (Fin (M + 2) → ℝ)) (B : SharpBound C)
    (x₀ : Fin (M + 2) → ℝ) {δ θ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (_h2δ : 2 * δ ≤ 1) (hθ : 1 ≤ θ)
    (hx₀ : ‖x₀‖ ≤ δ)
    (hslack : ∀ m, 8 * B.C₁ * (sched δ θ m) ^ (2 - θ) ≤ 1)
    (hs1 : ∀ m, 16 * B.C₂ * (sched δ θ m) ^ (3 - θ) ≤ 1)
    (hSmeas : Measurable C.S)
    (hτmeas : Measurable C.τ)
    (hρ : ∀ m : ℕ, 2 * sched δ θ m ≤ C.ρ₁)
    {CA : ℝ}
    (h2δρ : 2 * δ ≤ ρ)
    (hCA : ∀ δ' s : ℝ, 0 < δ' → 2 * δ' ≤ ρ → 0 < s → s ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ' →
        blockMeasure (M + 2) {b | C.τ (x + δ' • clamp b) < s}
          ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
              (s * Lam s ^ (M + 1) + δ' * Lam δ' ^ M))) :
    ∀ m : ℕ,
      (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
          ((goodSharp C B δ θ
              (yProc C x₀ δ θ) m)ᶜ
            ∩ ⋂ j < m, goodSharp C B δ θ
              (yProc C x₀ δ θ) j)
        ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
            ((16 * B.C₂ * (sched δ θ m) ^ (3 - θ))
                * Lam (16 * B.C₂ * (sched δ θ m) ^ (3 - θ)) ^ (M + 1)
              + sched δ θ m * Lam (sched δ θ m) ^ M)) := by
  classical
  -- the hypotheses of the schedule invariant
  have hdither : ∀ m ω, ‖yProc C x₀ δ θ m ω
      - xProc C x₀ δ θ m ω‖ ≤ sched δ θ m :=
    fun m ω => norm_yProc_sub _ x₀ δ θ hδ m ω
  have hcycle : ∀ m ω, xProc C x₀ δ θ (m + 1) ω
      = C.S (yProc C x₀ δ θ m ω) :=
    fun m ω => xProc_succ _ x₀ δ θ m ω
  have hschedle : ∀ m, sched δ θ m ≤ δ := fun m => sched_le hδ hδ1 hθ m
  have hsmall : ∀ m, 2 * sched δ θ m ≤ C.ρ₁ := hρ
  have h0 : ∀ ω, ‖xProc C x₀ δ θ 0 ω‖ ≤ δ := fun ω => hx₀
  have hinv := norm_le_sched_of_good C B hδ
    (xProc C x₀ δ θ) (yProc C x₀ δ θ)
    h0 hdither hcycle hsmall hslack
  intro m
  have hδm0 : 0 < sched δ θ m := sched_pos hδ θ m
  have hδm2 : 2 * sched δ θ m ≤ ρ := by linarith [hschedle m]
  have hsm0 : 0 < 16 * B.C₂ * (sched δ θ m) ^ (3 - θ) := by
    have := B.hC₂; positivity
  -- the event lies in the shape the Tonelli reduction consumes
  refine le_trans (measure_mono (?_ :
      ((goodSharp C B δ θ (yProc C x₀ δ θ) m)ᶜ
        ∩ ⋂ j < m, goodSharp C B δ θ (yProc C x₀ δ θ) j)
      ⊆ {ω : ℕ → (Fin (M + 2) → ℝ) |
          (xFin C x₀ δ θ m (finRestrict m ω), ω m) ∈
            {p : (Fin (M + 2) → ℝ) × (Fin (M + 2) → ℝ) |
              ‖p.1‖ ≤ sched δ θ m ∧
                C.τ (p.1 + (sched δ θ m) • clamp p.2)
                  < 16 * B.C₂ * (sched δ θ m) ^ (3 - θ)}})) ?_
  · rintro ω ⟨hbad, hpast⟩
    refine ⟨hinv m ω (fun j hj => (Set.mem_iInter₂.mp hpast) j hj), ?_⟩
    exact not_le.mp hbad
  refine measure_past_slice_le _ m (xFin C x₀ δ θ m)
    (measurable_xFin _ x₀ δ θ hSmeas m) _ ?_ ?_
  · refine MeasurableSet.inter (measurableSet_le measurable_fst.norm measurable_const) ?_
    refine measurableSet_lt (f := fun p : (Fin (M + 2) → ℝ) × (Fin (M + 2) → ℝ) =>
      C.τ (p.1 + (sched δ θ m) • clamp p.2)) ?_ measurable_const
    refine hτmeas.comp (measurable_fst.add ?_)
    exact ((measurable_clamp (M := M)).comp measurable_snd).const_smul (sched δ θ m)
  -- the uniform slice bound
  intro x
  by_cases hx : ‖x‖ ≤ sched δ θ m
  · have hset : {b | (x, b) ∈ {p : (Fin (M + 2) → ℝ) × (Fin (M + 2) → ℝ) |
        ‖p.1‖ ≤ sched δ θ m ∧
          C.τ (p.1 + (sched δ θ m) • clamp p.2)
            < 16 * B.C₂ * (sched δ θ m) ^ (3 - θ)}}
        = {b | C.τ (x + (sched δ θ m) • clamp b)
            < 16 * B.C₂ * (sched δ θ m) ^ (3 - θ)} := by
      ext b
      simp only [Set.mem_setOf_eq, and_iff_right hx]
    rw [hset]
    exact hCA _ _ hδm0 hδm2 hsm0 (hs1 m) x hx
  · have hempty : {b | (x, b) ∈ {p : (Fin (M + 2) → ℝ) × (Fin (M + 2) → ℝ) |
        ‖p.1‖ ≤ sched δ θ m ∧
          C.τ (p.1 + (sched δ θ m) • clamp p.2)
            < 16 * B.C₂ * (sched δ θ m) ^ (3 - θ)}} = ∅ := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hx h.1
    rw [hempty]
    simp

/-! ### Theorem 4.9

`hPsi` is fed to `dither_sharp`, and the resulting series is summed with
`schedule_series_bound_log` — keeping the logarithms, so the exponent of `δ` is exactly `1`
as in the paper, not a pure power. -/

/-- **The two terms of `hΨ` collapse into one.**  Since `3 − θ > 1` and `δₘ ≤ 1`, the
`s`-term is dominated by the `δ`-term: `sₘ = 16C₂δₘ^{3−θ} ≤ 16C₂δₘ`, and
`Λ(sₘ) ≤ Λ(16C₂)·2·Λ(δₘ)`. -/
lemma hPsi_term_le {C₂ : ℝ} (hC₂ : 0 < C₂)
    {δ θ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2) (m : ℕ) :
    (16 * C₂ * (sched δ θ m) ^ (3 - θ))
        * Lam (16 * C₂ * (sched δ θ m) ^ (3 - θ)) ^ (M + 1)
      + sched δ θ m * Lam (sched δ θ m) ^ M
    ≤ (16 * C₂ * (2 * Lam (16 * C₂)) ^ (M + 1) + 1)
        * (sched δ θ m * Lam (sched δ θ m) ^ (M + 1)) := by
  set δm := sched δ θ m with hδm
  have hδm0 : 0 < δm := sched_pos hδ θ m
  have hδm1 : δm ≤ 1 := le_trans (sched_le hδ hδ1 hθ1 m) hδ1
  have hK0 : (0:ℝ) < 16 * C₂ := by positivity
  have hLδm : (0:ℝ) < Lam δm ^ (M + 1) := Lam_pow_pos _ _
  -- `δm ^ (3-θ) ≤ δm`
  have hrp : δm ^ (3 - θ) ≤ δm := by
    calc δm ^ (3 - θ) ≤ δm ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hδm0 hδm1 (by linarith)
      _ = δm := Real.rpow_one δm
  have hrp0 : (0:ℝ) < δm ^ (3 - θ) := Real.rpow_pos_of_pos hδm0 _
  -- `Λ(16C₂ δm^{3-θ}) ≤ Λ(16C₂) · 2 · Λ(δm)`
  have hLam : Lam (16 * C₂ * δm ^ (3 - θ)) ≤ (2 * Lam (16 * C₂)) * Lam δm := by
    calc Lam (16 * C₂ * δm ^ (3 - θ)) ≤ Lam (16 * C₂) * Lam (δm ^ (3 - θ)) :=
          Lam_mul_le_of_pos hK0 hrp0
      _ ≤ Lam (16 * C₂) * (2 * Lam δm) :=
          mul_le_mul_of_nonneg_left (Lam_rpow_le_two_mul hδm0 hδm1 (by linarith))
            (Lam_nonneg _)
      _ = (2 * Lam (16 * C₂)) * Lam δm := by ring
  have hLampow : Lam (16 * C₂ * δm ^ (3 - θ)) ^ (M + 1)
      ≤ (2 * Lam (16 * C₂)) ^ (M + 1) * Lam δm ^ (M + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Lam_nonneg _) hLam (M + 1)
  -- the `s`-term
  have hfirst : (16 * C₂ * δm ^ (3 - θ)) * Lam (16 * C₂ * δm ^ (3 - θ)) ^ (M + 1)
      ≤ (16 * C₂ * (2 * Lam (16 * C₂)) ^ (M + 1)) * (δm * Lam δm ^ (M + 1)) := by
    have h1 : (16 * C₂ * δm ^ (3 - θ)) ≤ 16 * C₂ * δm :=
      mul_le_mul_of_nonneg_left hrp hK0.le
    calc (16 * C₂ * δm ^ (3 - θ)) * Lam (16 * C₂ * δm ^ (3 - θ)) ^ (M + 1)
        ≤ (16 * C₂ * δm) * ((2 * Lam (16 * C₂)) ^ (M + 1) * Lam δm ^ (M + 1)) := by
          refine mul_le_mul h1 hLampow (Lam_pow_pos _ _).le (by positivity)
      _ = (16 * C₂ * (2 * Lam (16 * C₂)) ^ (M + 1)) * (δm * Lam δm ^ (M + 1)) := by ring
  -- the `δ`-term
  have hsecond : δm * Lam δm ^ M ≤ 1 * (δm * Lam δm ^ (M + 1)) := by
    have : Lam δm ^ M ≤ Lam δm ^ (M + 1) := Lam_pow_le_pow (by omega)
    nlinarith [hδm0.le, (Lam_pow_pos δm M).le]
  linarith [hfirst, hsecond]

/-- **Theorem 4.9 for a real spectrum.**  Dithered restarted MPE, in cleared form, with the
schedule `δₘ = δ^(θᵐ)`: the invariant `‖xₘ‖ ≤ δₘ` fails with probability at most
`C · δ · (1 + log(1/δ))^{n-1}`.

This is the paper's Theorem 4.9 with the exponent of `δ` equal to `1`, uniformly in `θ` and in
the dimension — *not* a pure-power weakening: the logarithms are kept and summed with
`schedule_series_bound_log`.  The smallness conditions on `δ` are the paper's `δ ≤ δ_*`. -/
theorem theorem3_of_lemma7 {Sig : (Fin (M + 2) → ℝ) → ℝ} {ρ : ℝ}
    (C : CycleData (Fin (M + 2) → ℝ)) (hd : C.d = M + 2) (hsig : ∀ y, C.sigt y = Sig y)
    (hz : Sig 0 = 0) (hSmeas : Measurable C.S) (hτmeas : Measurable C.τ)
    (h7 : ∃ CA : ℝ, 0 < CA ∧ ∀ δ s : ℝ, 0 < δ → 2 * δ ≤ ρ → 0 < s → s ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ →
        blockMeasure (M + 2)
            {b | |Sig (x + δ • b)|
                ≤ s * ‖x + δ • b‖ ^ (M + 2)}
          ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
              (s * Lam s ^ (M + 1) + δ * Lam δ ^ M)))
    (B : SharpBound C) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ 1 → 2 * δ ≤ ρ → 2 * δ ≤ C.ρ₁ →
      (∀ m, 8 * B.C₁ * (sched δ θ m) ^ (2 - θ) ≤ 1) →
      (∀ m, 16 * B.C₂ * (sched δ θ m) ^ (3 - θ) ≤ 1) →
      ((δ ^ (1:ℝ)) ^ (θ - 1) * θ ^ (M + 1) ≤ 1 / 2) →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
            {ω | ∃ m, ¬ ‖xProc C x₀ δ θ m ω‖ ≤ sched δ θ m}
          ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) := by
  classical
  -- normalize the eigenbasis, then extract the (δ-independent) slice constant
  obtain ⟨CA, hCA0, hCA⟩ := slice_bound C hd hsig hz h7
  set D : ℝ := 16 * B.C₂ * (2 * Lam (16 * B.C₂)) ^ (M + 1) + 1 with hD
  have hD0 : 0 < D := by
    have := B.hC₂
    have h1 : (0:ℝ) < (2 * Lam (16 * B.C₂)) ^ (M + 1) := by
      have := Lam_pos (16 * B.C₂); positivity
    rw [hD]; positivity
  refine ⟨CA * 2 ^ (M + 3) * D * 2, by positivity, ?_⟩
  intro δ hδ hδ1 h2δ1 h2δ h2δρ hslack hs1 hratio x₀ hx₀
  have hθ0 : (1:ℝ) ≤ θ := hθ1.le
  -- `hΨ`
  have hsmall : ∀ m, 2 * sched δ θ m ≤ C.ρ₁ := by
    intro m
    have := sched_le hδ hδ1 hθ0 m
    linarith [h2δρ]
  have hpsi := hPsi C B x₀ hδ hδ1 h2δ1 hθ0 hx₀ hslack hs1 hSmeas hτmeas hsmall h2δ hCA
  -- feed it to `dither_sharp`
  have hdither : ∀ m ω, ‖yProc C x₀ δ θ m ω
      - xProc C x₀ δ θ m ω‖ ≤ sched δ θ m :=
    fun m ω => norm_yProc_sub _ x₀ δ θ hδ m ω
  have hcycle : ∀ m ω, xProc C x₀ δ θ (m + 1) ω
      = C.S (yProc C x₀ δ θ m ω) :=
    fun m ω => xProc_succ _ x₀ δ θ m ω
  have hmain := dither_sharp C B
    (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2))) hδ
    (xProc C x₀ δ θ) (yProc C x₀ δ θ) _
    (fun ω => hx₀) hdither hcycle hsmall hslack hpsi
  refine le_trans hmain ?_
  -- sum the series, collapsing the two terms first
  have hterm : ∀ m : ℕ,
      ENNReal.ofReal (CA * 2 ^ (M + 3) *
          ((16 * B.C₂ * (sched δ θ m) ^ (3 - θ))
              * Lam (16 * B.C₂ * (sched δ θ m) ^ (3 - θ)) ^ (M + 1)
            + sched δ θ m * Lam (sched δ θ m) ^ M))
      ≤ ENNReal.ofReal ((CA * 2 ^ (M + 3) * D) *
          ((δ ^ (θ ^ m)) ^ (1:ℝ) * Lam (δ ^ (θ ^ m)) ^ (M + 1))) := by
    intro m
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hPsi_term_le (M := M) B.hC₂ hδ hδ1 hθ0 hθ2.le m
    have hpow : (δ ^ (θ ^ m)) ^ (1:ℝ) = sched δ θ m := by
      rw [Real.rpow_one]; rfl
    rw [hpow]
    have hc : (0:ℝ) ≤ CA * 2 ^ (M + 3) := by positivity
    calc CA * 2 ^ (M + 3) * (_ + _) ≤ CA * 2 ^ (M + 3) * (D * (sched δ θ m
            * Lam (sched δ θ m) ^ (M + 1))) := by
          exact mul_le_mul_of_nonneg_left (by rw [hD]; exact h) hc
      _ = CA * 2 ^ (M + 3) * D * (sched δ θ m * Lam (sched δ θ m) ^ (M + 1)) := by ring
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  -- now a single log-weighted schedule sum
  have hsummable := summable_schedule_log (δ := δ) (θ := θ) (p := (1:ℝ)) (M + 1)
    hδ hδ1 hθ0 one_pos hratio
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun m => by
      have h1 : (0:ℝ) ≤ (δ ^ (θ ^ m)) ^ (1:ℝ) :=
        (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hδ _) _).le
      have h2 : (0:ℝ) ≤ Lam (δ ^ (θ ^ m)) ^ (M + 1) := (Lam_pow_pos _ _).le
      positivity)
    (hsummable.mul_left _)]
  rw [tsum_mul_left]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsum := schedule_series_bound_log (δ := δ) (θ := θ) (p := (1:ℝ)) (M + 1)
    hδ hδ1 hθ0 one_pos hratio
  have hc : (0:ℝ) ≤ CA * 2 ^ (M + 3) * D := by positivity
  calc CA * 2 ^ (M + 3) * D *
        ∑' m : ℕ, (δ ^ (θ ^ m)) ^ (1:ℝ) * Lam (δ ^ (θ ^ m)) ^ (M + 1)
      ≤ CA * 2 ^ (M + 3) * D * (2 * (δ ^ (1:ℝ) * Lam δ ^ (M + 1))) :=
        mul_le_mul_of_nonneg_left hsum hc
    _ = CA * 2 ^ (M + 3) * D * 2 * δ * Lam δ ^ (M + 1) := by
        rw [Real.rpow_one]; ring

/-- **Theorem 4.9 for a real spectrum**, as a corollary of `theorem3_of_lemma7`. -/
theorem theorem3_realSpectrum (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1))
    {P : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ} {lam : Fin (M + 2) → ℝ}
    (hP : IsUnit P.det) (hlam : Function.Injective lam)
    (hAP : A * P = P * Matrix.diagonal lam)
    (B : SharpBound (cycleData hq hA)) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ 1 →
      (∀ m, 8 * B.C₁ * (sched δ θ m) ^ (2 - θ) ≤ 1) →
      (∀ m, 16 * B.C₂ * (sched δ θ m) ^ (3 - θ) ≤ 1) →
      ((δ ^ (1:ℝ)) ^ (θ - 1) * θ ^ (M + 1) ≤ 1 / 2) →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
            {ω | ∃ m, ¬ ‖xProc (cycleData hq hA) x₀ δ θ m ω‖ ≤ sched δ θ m}
          ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) :=
  by
  obtain ⟨Cst, hCst, hmain⟩ := theorem3_of_lemma7 (cycleData hq hA) rfl (fun _ => rfl)
    (eval_sigtPoly_zero hq) (measurable_cycleData_S hq hA) (measurable_cycleData_tau hq hA)
    (ρ := 1)
    (by
      obtain ⟨P', hP', hAP', hcontr'⟩ := exists_scaled_eigenbasis hP hAP
      exact lemma7_prob (lemma7_volume hq hA hP' hlam hAP' hcontr'))
    B hθ1 hθ2
  exact ⟨Cst, hCst, fun δ hδ hδ1 h2δ hslack hs1 hratio x₀ hx₀ =>
    hmain δ hδ hδ1 h2δ h2δ h2δ hslack hs1 hratio x₀ hx₀⟩

end HPsi

end MPE
