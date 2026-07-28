import Mathlib
import Formal.Weight
import Formal.Dyadic

/-!
# Anticoncentration of a product of blocks

Appendix §§5–6.  A nonnegative random variable `X` is *anticoncentrated* if
`μ{X ≤ v} ≤ v` for every `v ≥ 0`; the two kinds of block occurring in the factorization of
the degeneracy polynomial both are (`Formal/Blocks.lean`, end of file).  The main result is
that a product of `N` independent anticoncentrated variables satisfies

    μ{∏ Xᵢ ≤ t} ≤ C_N · t · Λ(t)^(N-1).

Two design choices, both following the appendix:

* the hypothesis is imposed for `v ≥ 0` **including `v = 0`**, which makes `μ{X ≤ 0} = 0`
  immediate and removes the only analytic obstacle (otherwise one has to prove
  `v Λ(v)^j → 0`);
* independence is not used as a hypothesis about a σ-algebra: the variables live on a
  product space and every step is Tonelli, as recommended in the appendix's remark on the
  conditioning step.
-/

namespace MPE

open MeasureTheory Set Finset
open scoped ENNReal

/-- `X` is anticoncentrated for `μ`: `μ{X ≤ v} ≤ v` for all `v ≥ 0`. -/
def Anticonc {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  ∀ v : ℝ, 0 ≤ v → μ {ω | X ω ≤ v} ≤ ENNReal.ofReal v

/-- The tail shape propagated by the induction: `μ{Y ≤ v} ≤ C v Λ(v)^j`. -/
def TailBound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : Ω → ℝ) (C : ℝ) (j : ℕ) :
    Prop :=
  ∀ v : ℝ, 0 ≤ v → μ {ω | Y ω ≤ v} ≤ ENNReal.ofReal (C * v * Lam v ^ j)

lemma Anticonc.tailBound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (h : Anticonc μ X) : TailBound μ X 1 0 := by
  intro v hv
  simpa using h v hv

/-- A tail bound at `v = 0` says the variable is a.e. positive. -/
lemma TailBound.measure_nonpos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}
    {C : ℝ} {j : ℕ} (h : TailBound μ Y C j) : μ {ω | Y ω ≤ 0} = 0 := by
  have := h 0 le_rfl
  simpa using this

/-- **The two-factor step.**  On a product space, if `X` is anticoncentrated and `Y` has a
`(C, j)` tail bound, then `X · Y` has a `(4C + 1, j + 1)` tail bound.

This is Tonelli plus `lintegral_min_one_div_le`; it is the only place the dyadic lemma is
invoked in this file. -/
theorem tailBound_mul {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {X : Ω₁ → ℝ} {Y : Ω₂ → ℝ} (hXm : Measurable X) (hYm : Measurable Y)
    (_hXnn : ∀ ω, 0 ≤ X ω) (_hYnn : ∀ ω, 0 ≤ Y ω)
    (hX : Anticonc μ₁ X) {C : ℝ} (hC : 0 ≤ C) {j : ℕ} (hY : TailBound μ₂ Y C j) :
    TailBound (μ₁.prod μ₂) (fun p => X p.1 * Y p.2) (4 * C + 1) (j + 1) := by
  intro t ht
  have hSmeas : MeasurableSet {p : Ω₁ × Ω₂ | X p.1 * Y p.2 ≤ t} :=
    (((hXm.comp measurable_fst).mul (hYm.comp measurable_snd))) measurableSet_Iic
  -- the slice over a fixed second coordinate
  have hslice : ∀ ω₂ : Ω₂, 0 < Y ω₂ →
      μ₁ ((fun ω₁ => (ω₁, ω₂)) ⁻¹' {p : Ω₁ × Ω₂ | X p.1 * Y p.2 ≤ t})
        ≤ ENNReal.ofReal (min 1 (t / Y ω₂)) := by
    intro ω₂ hy
    have hset : (fun ω₁ => (ω₁, ω₂)) ⁻¹' {p : Ω₁ × Ω₂ | X p.1 * Y p.2 ≤ t}
        = {ω₁ | X ω₁ ≤ t / Y ω₂} := by
      ext ω₁
      simp only [Set.mem_preimage, Set.mem_setOf_eq, le_div_iff₀ hy]
    rw [hset]
    rcases le_total 1 (t / Y ω₂) with h1 | h1
    · rw [min_eq_left h1]
      simpa using prob_le_one
    · rw [min_eq_right h1]
      exact hX _ (by positivity)
  -- a.e. the second coordinate is positive
  have hae : ∀ᵐ ω₂ ∂μ₂, 0 < Y ω₂ := by
    rw [ae_iff]
    have hset : {ω | ¬ 0 < Y ω} = {ω | Y ω ≤ 0} := by ext ω; simp [not_lt]
    rw [hset]
    exact hY.measure_nonpos
  calc (μ₁.prod μ₂) {p : Ω₁ × Ω₂ | X p.1 * Y p.2 ≤ t}
      = ∫⁻ ω₂, μ₁ ((fun ω₁ => (ω₁, ω₂)) ⁻¹' {p : Ω₁ × Ω₂ | X p.1 * Y p.2 ≤ t}) ∂μ₂ :=
        Measure.prod_apply_symm hSmeas
    _ ≤ ∫⁻ ω₂, ENNReal.ofReal (min 1 (t / Y ω₂)) ∂μ₂ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with ω₂ hω₂ using hslice ω₂ hω₂
    _ ≤ ENNReal.ofReal ((4 * C + 1) * t * Lam t ^ (j + 1)) := by
        rcases eq_or_lt_of_le ht with rfl | htpos
        · -- `t = 0`: the left side is `0` because `Y > 0` a.e. and `X > 0` a.e.
          simp
        · exact lintegral_min_one_div_le hYm zero_le_one hC htpos j
            (by simp) (fun u hu => hY u hu.le)

/-- The exponent of the logarithm may be raised, since `Λ ≥ 1`. -/
lemma TailBound.mono_exp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}
    {C : ℝ} (hC : 0 ≤ C) {j k : ℕ} (h : TailBound μ Y C j) (hjk : j ≤ k) :
    TailBound μ Y C k := by
  intro v hv
  refine le_trans (h v hv) (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_Lam v) hjk) (by positivity)

/-- A tail bound only weakens when the constant grows. -/
lemma TailBound.mono_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : Ω → ℝ}
    {C C' : ℝ} {j : ℕ} (h : TailBound μ Y C j) (hCC : C ≤ C') :
    TailBound μ Y C' j := by
  intro v hv
  refine le_trans (h v hv) (ENNReal.ofReal_le_ofReal ?_)
  have : (0:ℝ) ≤ v * Lam v ^ j := mul_nonneg hv (Lam_pow_pos v j).le
  nlinarith

/-- **The product estimate** (appendix Proposition 5).  For `N + 1` independent
anticoncentrated factors on a product space,

    μ{∏ᵢ Xᵢ ≤ t}  ≤  5^N · t · Λ(t)^N.

The induction peels one coordinate off with `measurePreserving_piFinSuccAbove` and applies
`tailBound_mul`; the base case is the marginal `measurePreserving_eval`. -/
theorem tailBound_prod : ∀ (N : ℕ) {E : Fin (N+1) → Type} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ∀ i, E i → ℝ), (∀ i, Measurable (X i)) → (∀ i x, 0 ≤ X i x) →
    (∀ i, Anticonc (μ i) (X i)) →
    TailBound (Measure.pi μ) (fun x => ∏ i, X i (x i)) (5 ^ N) N := by
  intro N
  induction N with
  | zero =>
      intro E _ μ _ X hXm _ hX v hv
      have hmeasS : MeasurableSet {y : E 0 | X 0 y ≤ v} :=
        measurableSet_le (hXm 0) measurable_const
      have hset : {x : ∀ i, E i | ∏ i, X i (x i) ≤ v}
          = (Function.eval (0 : Fin 1)) ⁻¹' {y | X 0 y ≤ v} := by
        ext x
        simp [Function.eval]
      rw [hset,
        (measurePreserving_eval μ (0 : Fin 1)).measure_preimage hmeasS.nullMeasurableSet]
      simpa using hX 0 v hv
  | succ N ih =>
      intro E _ μ _ X hXm hXnn hX
      -- peel off coordinate `0`
      set e := MeasurableEquiv.piFinSuccAbove E 0 with he
      have hmp := measurePreserving_piFinSuccAbove μ (0 : Fin (N+2))
      -- the tail family
      have ihT : TailBound (Measure.pi fun i : Fin (N+1) => μ ((0 : Fin (N+2)).succAbove i))
          (fun y => ∏ i, X ((0 : Fin (N+2)).succAbove i) (y i)) (5 ^ N) N :=
        ih (fun i => μ ((0 : Fin (N+2)).succAbove i))
          (fun i => X ((0 : Fin (N+2)).succAbove i))
          (fun i => hXm _) (fun i x => hXnn _ x) (fun i => hX _)
      have hmul := tailBound_mul (μ₁ := μ 0)
        (μ₂ := Measure.pi fun i : Fin (N+1) => μ ((0 : Fin (N+2)).succAbove i))
        (X := X 0) (Y := fun y => ∏ i, X ((0 : Fin (N+2)).succAbove i) (y i))
        (hXm 0) (by fun_prop) (hXnn 0)
        (fun y => Finset.prod_nonneg fun i _ => hXnn _ _)
        (hX 0) (by positivity) ihT
      have hCle : 4 * (5:ℝ) ^ N + 1 ≤ 5 ^ (N+1) := by
        have : (1:ℝ) ≤ 5 ^ N := one_le_pow₀ (by norm_num)
        rw [pow_succ]; nlinarith
      have hmul' := hmul.mono_const hCle
      -- transport along the equivalence
      intro v hv
      -- the target set in the product space, and its preimage under the *forward* map
      set S : Set (E 0 × ∀ j : Fin (N+1), E ((0 : Fin (N+2)).succAbove j)) :=
        {p | X 0 p.1 * (∏ i, X ((0 : Fin (N+2)).succAbove i) (p.2 i)) ≤ v} with hS
      have hSmeas : MeasurableSet S := by
        refine measurableSet_le ?_ measurable_const
        exact ((hXm 0).comp measurable_fst).mul
          (Finset.measurable_prod _ fun i _ =>
            (hXm _).comp ((measurable_pi_apply i).comp measurable_snd))
      have hpre : (MeasurableEquiv.piFinSuccAbove E 0) ⁻¹' S
          = {x : ∀ i, E i | ∏ i, X i (x i) ≤ v} := by
        ext x
        simp only [Set.mem_preimage, hS, Set.mem_setOf_eq,
          MeasurableEquiv.piFinSuccAbove_apply]
        rw [Fin.prod_univ_succAbove (fun i => X i (x i)) (0 : Fin (N+2))]
        rfl
      rw [← hpre, hmp.measure_preimage hSmeas.nullMeasurableSet]
      exact hmul' v hv

/-! ### The two kinds of block

A line block carries the factor `|z|` with `z` uniform on `[-1,1]`; a plane block carries
`‖z‖²` with `z` uniform on `[-1,1]²`.  Both are anticoncentrated with constant `1`.

For the plane we avoid the area of a disc: `a² + b² ≤ v` forces `|a| ≤ √v` *and*
`|b| ≤ √v`, so the box bound `min(1,√v)² ≤ v` already gives the constant `1` — better than
the `π/4` quoted in the appendix, and with no `π`. -/

/-- The uniform probability measure on `[-1,1]`. -/
noncomputable def unif1 : Measure ℝ :=
  ENNReal.ofReal (1/2) • volume.restrict (Set.Icc (-1 : ℝ) 1)

lemma unif1_apply {s : Set ℝ} (hs : MeasurableSet s) :
    unif1 s = ENNReal.ofReal (1/2) * volume (s ∩ Set.Icc (-1 : ℝ) 1) := by
  rw [unif1, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]

instance : IsProbabilityMeasure unif1 := by
  constructor
  rw [unif1_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- `unif1 {|x| ≤ v} = min(1, v)` for `v ≥ 0`; we only need `≤`. -/
lemma unif1_abs_le {v : ℝ} (_hv : 0 ≤ v) :
    unif1 {x : ℝ | |x| ≤ v} ≤ ENNReal.ofReal (min 1 v) := by
  have hset : {x : ℝ | |x| ≤ v} = Set.Icc (-v) v := by
    ext x; simp [abs_le]
  rw [hset, unif1_apply measurableSet_Icc, Set.Icc_inter_Icc, Real.volume_Icc]
  have hmax : max (-v) (-1 : ℝ) = -(min 1 v) := by
    rcases le_total v (1:ℝ) with h | h
    · rw [min_eq_right h, max_eq_left (by linarith)]
    · rw [min_eq_left h, max_eq_right (by linarith)]
  rw [hmax, min_comm v (1:ℝ), show min 1 v - -(min 1 v) = 2 * min 1 v by ring,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  exact le_of_eq (by congr 1; ring)

/-- The uniform probability measure on the cube `[-1,1]^d`. -/
noncomputable def blockMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ => unif1)

instance (d : ℕ) : IsProbabilityMeasure (blockMeasure d) := by
  unfold blockMeasure; infer_instance

/-- **A line block is anticoncentrated.** -/
lemma anticonc_line : Anticonc (blockMeasure 1) (fun z => |z 0|) := by
  intro v hv
  have hset : {z : Fin 1 → ℝ | |z 0| ≤ v} = Set.pi Set.univ (fun _ => {x : ℝ | |x| ≤ v}) := by
    ext z
    simp [Fin.forall_fin_one]
  rw [hset, blockMeasure, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  exact le_trans (unif1_abs_le hv) (ENNReal.ofReal_le_ofReal (min_le_right _ _))

/-- **A plane block is anticoncentrated.** -/
lemma anticonc_plane : Anticonc (blockMeasure 2) (fun z => (z 0)^2 + (z 1)^2) := by
  intro v hv
  have key : ∀ w : ℝ, w^2 ≤ v → |w| ≤ Real.sqrt v := by
    intro w hw
    calc |w| = Real.sqrt (w^2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt v := Real.sqrt_le_sqrt hw
  have hsub : {z : Fin 2 → ℝ | (z 0)^2 + (z 1)^2 ≤ v}
      ⊆ Set.pi Set.univ (fun _ => {x : ℝ | |x| ≤ Real.sqrt v}) := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    rw [Set.mem_univ_pi, Fin.forall_fin_two]
    exact ⟨key _ (by nlinarith [sq_nonneg (z 1)]), key _ (by nlinarith [sq_nonneg (z 0)])⟩
  refine le_trans (measure_mono hsub) ?_
  rw [blockMeasure, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsq : (0:ℝ) ≤ Real.sqrt v := Real.sqrt_nonneg v
  refine le_trans (pow_le_pow_left₀ zero_le (unif1_abs_le hsq) 2) ?_
  rw [← ENNReal.ofReal_pow (le_min zero_le_one hsq)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total (Real.sqrt v) 1 with h | h
  · rw [min_eq_right h, Real.sq_sqrt hv]
  · rw [min_eq_left h]
    have : (1:ℝ) ≤ v := by nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg v]
    simpa using this

end MPE
