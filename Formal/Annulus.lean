import Mathlib
import Formal.Weight
import Formal.OneDim
import Formal.Dyadic
import Formal.Blocks
import Formal.DeltaFactor

/-!
# The sublevel estimate on the annulus

Appendix §8.  This file works on the **block space**

    B = ∀ i : Fin N, (Fin (kind i).dim → ℝ),

on which `volume` *is* `Measure.pi (fun i => volume)` definitionally, so the chart splitting
of the fibering argument is `measurePreserving_piFinSuccAbove` — the same tool that ran the
induction in `Formal/Blocks.lean`.

The first step is the bridge between the two measures in play: plain Lebesgue restricted to
a cube (natural for Fubini and for polar coordinates) and the product of block *probability*
measures (what the product estimate of `Formal/Blocks.lean` is stated for).  They differ by
the volume of the cube.
-/

namespace MPE

open MeasureTheory Set Finset
open scoped ENNReal Pointwise

/-- The cube `[-1,1]^d`. -/
def cube (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Icc (-1 : ℝ) 1

lemma measurableSet_cube (d : ℕ) : MeasurableSet (cube d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- `unif1` is Lebesgue on `[-1,1]` scaled by `1/2`. -/
lemma unif1_eq_smul :
    unif1 = ENNReal.ofReal (1/2) • (volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1) := rfl

/-- **The bridge.**  Lebesgue measure restricted to the cube is `2^d` times the block
probability measure. -/
lemma volume_restrict_cube (d : ℕ) :
    (volume : Measure (Fin d → ℝ)).restrict (cube d)
      = ENNReal.ofReal (2 ^ d) • blockMeasure d := by
  have hvol : (volume : Measure (Fin d → ℝ)) = Measure.pi fun _ : Fin d => (volume : Measure ℝ) :=
    volume_pi
  have h1 : (volume : Measure (Fin d → ℝ)).restrict (cube d)
      = Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1) := by
    rw [cube, hvol, Measure.restrict_pi_pi]
  rw [h1]
  refine Measure.pi_eq ?_
  intro s hs
  have hcoe : ∀ i : Fin d, unif1 (s i)
      = ENNReal.ofReal (1/2) * ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)) (s i) := by
    intro i
    rw [unif1_eq_smul, Measure.smul_apply, smul_eq_mul]
  calc (ENNReal.ofReal (2 ^ d) • blockMeasure d) (Set.univ.pi s)
      = ENNReal.ofReal (2 ^ d) * ∏ i : Fin d, unif1 (s i) := by
        rw [Measure.smul_apply, smul_eq_mul, blockMeasure, Measure.pi_pi]
    _ = ENNReal.ofReal (2 ^ d) *
          ∏ i : Fin d, (ENNReal.ofReal (1/2) *
            ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)) (s i)) := by
        rw [Finset.prod_congr rfl fun i _ => hcoe i]
    _ = (ENNReal.ofReal (2 ^ d) * ENNReal.ofReal (1/2) ^ d) *
          ∏ i : Fin d, ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)) (s i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ = ∏ i : Fin d, ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)) (s i) := by
        rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        rw [show (2:ℝ) ^ d * (1/2 : ℝ) ^ d = 1 by
          rw [← mul_pow]; norm_num]
        simp

/-- The block probability measure is concentrated on the cube. -/
lemma blockMeasure_compl_cube (d : ℕ) : blockMeasure d (cube d)ᶜ = 0 := by
  have h := volume_restrict_cube d
  have happ : (volume : Measure (Fin d → ℝ)).restrict (cube d) (cube d)ᶜ = 0 := by
    rw [Measure.restrict_apply' (measurableSet_cube d)]
    simp
  rw [h, Measure.smul_apply, smul_eq_mul] at happ
  have hne : ENNReal.ofReal ((2:ℝ) ^ d) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  exact (mul_eq_zero.mp happ).resolve_left hne

/-! ### The block space -/

variable {N : ℕ}

/-- The block space: one factor per block. -/
abbrev Blk (kind : Fin N → BlockKind) := ∀ i : Fin N, Fin (kind i).dim → ℝ

/-- The cube in the block space. -/
def bigCube (kind : Fin N → BlockKind) : Set (Blk kind) :=
  Set.univ.pi fun i => cube (kind i).dim

lemma measurableSet_bigCube (kind : Fin N → BlockKind) : MeasurableSet (bigCube kind) :=
  MeasurableSet.univ_pi fun i => measurableSet_cube _

/-- The product of the block probability measures. -/
noncomputable def blkMeasure (kind : Fin N → BlockKind) : Measure (Blk kind) :=
  Measure.pi fun i => blockMeasure (kind i).dim

instance (kind : Fin N → BlockKind) : IsProbabilityMeasure (blkMeasure kind) := by
  unfold blkMeasure; infer_instance

/-- The total dimension. -/
def totDim (kind : Fin N → BlockKind) : ℕ := ∑ i, (kind i).dim

/-- **The bridge, on the block space.** -/
lemma volume_restrict_bigCube (kind : Fin N → BlockKind) :
    (volume : Measure (Blk kind)).restrict (bigCube kind)
      = ENNReal.ofReal (2 ^ totDim kind) • blkMeasure kind := by
  have hvol : (volume : Measure (Blk kind))
      = Measure.pi fun i : Fin N => (volume : Measure (Fin (kind i).dim → ℝ)) := volume_pi
  have h1 : (volume : Measure (Blk kind)).restrict (bigCube kind)
      = Measure.pi fun i : Fin N =>
          (volume : Measure (Fin (kind i).dim → ℝ)).restrict (cube (kind i).dim) := by
    rw [bigCube, hvol, Measure.restrict_pi_pi]
  rw [h1]
  refine Measure.pi_eq ?_
  intro s hs
  have hstep : ∀ i : Fin N,
      (volume : Measure (Fin (kind i).dim → ℝ)).restrict (cube (kind i).dim) (s i)
        = ENNReal.ofReal (2 ^ (kind i).dim) * blockMeasure (kind i).dim (s i) := by
    intro i
    rw [volume_restrict_cube, Measure.smul_apply, smul_eq_mul]
  have hpow : ∏ i : Fin N, ENNReal.ofReal ((2:ℝ) ^ (kind i).dim)
      = ENNReal.ofReal ((2:ℝ) ^ totDim kind) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    congr 1
    rw [totDim, Finset.prod_pow_eq_pow_sum]
  calc (ENNReal.ofReal (2 ^ totDim kind) • blkMeasure kind) (Set.univ.pi s)
      = ENNReal.ofReal (2 ^ totDim kind) * ∏ i : Fin N, blockMeasure (kind i).dim (s i) := by
        rw [Measure.smul_apply, smul_eq_mul, blkMeasure, Measure.pi_pi]
    _ = ∏ i : Fin N, (ENNReal.ofReal (2 ^ (kind i).dim) * blockMeasure (kind i).dim (s i)) := by
        rw [Finset.prod_mul_distrib, hpow]
    _ = _ := (Finset.prod_congr rfl fun i _ => (hstep i)).symm

/-! ### The product of block factors is anticoncentrated -/

lemma BlockKind.measurable_factor (b : BlockKind) : Measurable b.factor := by
  cases b <;> · unfold BlockKind.factor; fun_prop

/-- The product of the absolute values of the block factors. -/
noncomputable def blkProd (kind : Fin N → BlockKind) (u : Blk kind) : ℝ :=
  ∏ i, |(kind i).factor (u i)|

lemma measurable_blkProd (kind : Fin N → BlockKind) : Measurable (blkProd kind) := by
  unfold blkProd
  exact Finset.measurable_prod _ fun i _ =>
    ((kind i).measurable_factor.comp (measurable_pi_apply i)).abs

lemma blkProd_nonneg (kind : Fin N → BlockKind) (u : Blk kind) : 0 ≤ blkProd kind u :=
  Finset.prod_nonneg fun i _ => abs_nonneg _

/-- **The product estimate on the block space**, for the block probability measure. -/
theorem tailBound_blkProd (kind : Fin (N+1) → BlockKind) :
    TailBound (blkMeasure kind) (blkProd kind) (5 ^ N) N :=
  tailBound_prod N (fun i => blockMeasure (kind i).dim)
    (fun i u => |(kind i).factor u|)
    (fun i => (kind i).measurable_factor.abs)
    (fun i u => abs_nonneg _)
    (fun i => (kind i).anticonc)

/-- **The product estimate for Lebesgue measure on the cube.** -/
theorem tailBound_blkProd_volume (kind : Fin (N+1) → BlockKind) :
    TailBound ((volume : Measure (Blk kind)).restrict (bigCube kind)) (blkProd kind)
      (2 ^ totDim kind * 5 ^ N) N := by
  intro v hv
  rw [volume_restrict_bigCube, Measure.smul_apply, smul_eq_mul]
  calc ENNReal.ofReal (2 ^ totDim kind) * blkMeasure kind {u | blkProd kind u ≤ v}
      ≤ ENNReal.ofReal (2 ^ totDim kind) * ENNReal.ofReal (5 ^ N * v * Lam v ^ N) :=
        mul_le_mul_left' (tailBound_blkProd kind v hv) _
    _ = ENNReal.ofReal ((2:ℝ) ^ totDim kind * (5 ^ N * v * Lam v ^ N)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (2 ^ totDim kind * 5 ^ N * v * Lam v ^ N) := by ring_nf

/-- The constant produced by absorbing the leading coefficient `γ`, on the block space. -/
noncomputable def blkGammaConst (kind : Fin (N + 1) → BlockKind) (γ : ℝ) : ℝ :=
  2 ^ totDim kind * 5 ^ N * |γ|⁻¹ * Lam |γ|⁻¹ ^ N

lemma blkGammaConst_nonneg (kind : Fin (N + 1) → BlockKind) (γ : ℝ) :
    0 ≤ blkGammaConst kind γ := by
  unfold blkGammaConst
  have := (Lam_pow_pos |γ|⁻¹ N).le
  positivity

/-- **The tail bound for `|γ ∏ᵢ factorᵢ|`**, the general-block analogue of
`tailBound_gammaProd`.  The leading coefficient is absorbed multiplicatively
(`Lam_mul_le_of_pos`); the additive form would not survive the power `N`. -/
theorem tailBound_gammaBlkProd (kind : Fin (N + 1) → BlockKind) {γ : ℝ} (hγ : γ ≠ 0) :
    TailBound ((volume : Measure (Blk kind)).restrict (bigCube kind))
      (fun u => |γ * ∏ i, (kind i).factor (u i)|) (blkGammaConst kind γ) N := by
  intro v hv
  have hγ0 : 0 < |γ| := abs_pos.mpr hγ
  have hset : {u : Blk kind | |γ * ∏ i, (kind i).factor (u i)| ≤ v}
      = {u : Blk kind | blkProd kind u ≤ |γ|⁻¹ * v} := by
    ext u
    simp only [Set.mem_setOf_eq, abs_mul, Finset.abs_prod, blkProd]
    rw [← le_div_iff₀' hγ0, div_eq_inv_mul]
  rw [hset]
  have hv' : (0:ℝ) ≤ |γ|⁻¹ * v := by positivity
  refine le_trans (tailBound_blkProd_volume kind _ hv') (ENNReal.ofReal_le_ofReal ?_)
  rcases eq_or_lt_of_le hv with rfl | hvpos
  · simp [blkGammaConst]
  have hLam : Lam (|γ|⁻¹ * v) ^ N ≤ Lam |γ|⁻¹ ^ N * Lam v ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Lam_nonneg _) (Lam_mul_le_of_pos (by positivity) hvpos) N
  calc (2:ℝ) ^ totDim kind * 5 ^ N * (|γ|⁻¹ * v) * Lam (|γ|⁻¹ * v) ^ N
      ≤ 2 ^ totDim kind * 5 ^ N * (|γ|⁻¹ * v) * (Lam |γ|⁻¹ ^ N * Lam v ^ N) := by
        refine mul_le_mul_of_nonneg_left hLam ?_
        positivity
    _ = blkGammaConst kind γ * v * Lam v ^ N := by unfold blkGammaConst; ring

/-! ### The chart cover (Obligation 6, step (i))

On the block space the norm is the sup norm, so a point of norm at least `c` has some
*Cartesian* coordinate of absolute value at least `c`.  That gives a cover by `2·totDim`
charts — one per coordinate and sign — on each of which the fibre derivative of the block
factor is bounded below by a constant:

* a line block contributes `Q(t) = t`, with `∂ₜQ = 1`;
* a plane block contributes `Q(t) = t² + b²` in the chart where `t` is the large
  coordinate, with `|∂ₜQ| = 2|t| ≥ 2c`.

No polar coordinates and no Jacobian are involved, and the fibre stays a single interval
(`[c,1]` or `[-1,-c]`), which is what `measure_chart_gen_le` consumes.  The constant `c`
comes from the *shell*: §9 rescales `‖z‖ ∈ [2⁻ʲ⁻¹R, 2⁻ʲR]` to `‖u‖ ∈ [½,1]`, so `c = ½` is a
fixed constant and no exponent is lost.  A chart cover of the full cube would instead force
`c ≈ √s` and degrade the bound to `√s`. -/

/-- Some Cartesian coordinate of a block-space point of norm `≥ c` is `≥ c` in absolute
value. -/
lemma exists_large_coord {kind : Fin N → BlockKind} {c : ℝ} (hc : 0 < c) {u : Blk kind}
    (hu : c ≤ ‖u‖) : ∃ (i : Fin N) (l : Fin (kind i).dim), c ≤ |u i l| := by
  by_contra hcon
  push_neg at hcon
  have h1 : ∀ i, ‖u i‖ < c := by
    intro i
    refine (pi_norm_lt_iff hc).mpr fun l => ?_
    rw [Real.norm_eq_abs]
    exact hcon i l
  exact absurd hu (not_le.mpr ((pi_norm_lt_iff hc).mpr h1))

/-- A large coordinate is large on one side or the other: the two halves of a chart. -/
lemma large_coord_cases {c t : ℝ} (h : c ≤ |t|) : c ≤ t ∨ t ≤ -c := by
  rcases abs_cases t with ⟨he, _⟩ | ⟨he, _⟩
  · exact Or.inl (he ▸ h)
  · exact Or.inr (by rw [he] at h; linarith)

/-- **The chart cover.**  The shell is covered by the `2·totDim` charts. -/
lemma shell_subset_iUnion_chart {kind : Fin N → BlockKind} {c : ℝ} (hc : 0 < c) :
    {u : Blk kind | c ≤ ‖u‖}
      ⊆ ⋃ p : (i : Fin N) × Fin (kind i).dim,
          ({u : Blk kind | c ≤ u p.1 p.2} ∪ {u : Blk kind | u p.1 p.2 ≤ -c}) := by
  intro u hu
  obtain ⟨i, l, hil⟩ := exists_large_coord hc hu
  refine Set.mem_iUnion.mpr ⟨⟨i, l⟩, ?_⟩
  rcases large_coord_cases hil with h | h
  · exact Or.inl h
  · exact Or.inr h

/-! ### Splitting off one coordinate of one block

`BlockKind.dim` is *defined* as `dm + 1`, so `MeasurableEquiv.piFinSuccAbove` peels one
coordinate off a block with no dependent-type cast.  Composing that with the same lemma at
the *block* level, and reassociating (`Measure.prodAssoc_prod`), presents the block space as
`ℝ × Rest` with the distinguished coordinate first — the shape `measure_chart_gen_le`
consumes. -/

/-- Peel coordinate `l` of block `i` off the block space. -/
def blkSplit (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) (l : Fin (kind i).dim) :
    Blk kind ≃ᵐ ℝ × ((Fin (kind i).dm → ℝ) × Blk fun j => kind (i.succAbove j)) :=
  (MeasurableEquiv.piFinSuccAbove (fun j : Fin (N + 1) => Fin (kind j).dim → ℝ) i).trans
    ((MeasurableEquiv.prodCongr
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (kind i).dim => ℝ) l)
        (MeasurableEquiv.refl (Blk fun j => kind (i.succAbove j)))).trans
      MeasurableEquiv.prodAssoc)

lemma blkSplit_apply (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1))
    (l : Fin (kind i).dim) (u : Blk kind) :
    blkSplit kind i l u
      = (u i l, ((fun j => u i (l.succAbove j)), fun j => u (i.succAbove j))) := rfl

theorem measurePreserving_blkSplit (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1))
    (l : Fin (kind i).dim) :
    MeasurePreserving (blkSplit kind i l) (volume : Measure (Blk kind))
      ((volume : Measure ℝ).prod
        ((volume : Measure (Fin (kind i).dm → ℝ)).prod
          (volume : Measure (Blk fun j => kind (i.succAbove j))))) := by
  have h1 := volume_preserving_piFinSuccAbove (fun j : Fin (N + 1) => Fin (kind j).dim → ℝ) i
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (kind i).dim => ℝ) l
  have h3 := h2.prod
    (MeasurePreserving.id (volume : Measure (Blk fun j => kind (i.succAbove j))))
  have h4 : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        ((ℝ × (Fin (kind i).dm → ℝ)) × Blk fun j => kind (i.succAbove j)) ≃ᵐ _)
      (((volume : Measure ℝ).prod (volume : Measure (Fin (kind i).dm → ℝ))).prod
        (volume : Measure (Blk fun j => kind (i.succAbove j))))
      ((volume : Measure ℝ).prod
        ((volume : Measure (Fin (kind i).dm → ℝ)).prod
          (volume : Measure (Blk fun j => kind (i.succAbove j))))) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  exact (h4.comp h3).comp h1

/-- The cube is a product in the split coordinates. -/
lemma bigCube_eq_preimage (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1))
    (l : Fin (kind i).dim) :
    bigCube kind = blkSplit kind i l ⁻¹'
      (Set.Icc (-1 : ℝ) 1 ×ˢ
        (cube (kind i).dm ×ˢ bigCube fun j => kind (i.succAbove j))) := by
  ext u
  simp only [Set.mem_preimage, blkSplit_apply, Set.mem_prod, bigCube, cube,
    Set.mem_univ_pi]
  rw [Fin.forall_iff_succAbove (P := fun j => ∀ k, u j k ∈ Set.Icc (-1 : ℝ) 1) i,
    Fin.forall_iff_succAbove (P := fun k => u i k ∈ Set.Icc (-1 : ℝ) 1) l]
  tauto

/-- The complement of one coordinate of block `i` in the block space. -/
abbrev BlkRest (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) :=
  (Fin (kind i).dm → ℝ) × Blk fun j => kind (i.succAbove j)

/-- Lebesgue measure on `BlkRest`, restricted to its cube. -/
noncomputable def blkRestMeasure (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) :
    Measure (BlkRest kind i) :=
  (volume : Measure (BlkRest kind i)).restrict
    (cube (kind i).dm ×ˢ bigCube fun j => kind (i.succAbove j))

instance (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) :
    SFinite (blkRestMeasure kind i) := by unfold blkRestMeasure; infer_instance

lemma blkRestMeasure_eq_prod (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) :
    blkRestMeasure kind i
      = ((volume : Measure (Fin (kind i).dm → ℝ)).restrict (cube (kind i).dm)).prod
          ((volume : Measure (Blk fun j => kind (i.succAbove j))).restrict
            (bigCube fun j => kind (i.succAbove j))) := by
  rw [blkRestMeasure]
  exact (Measure.prod_restrict _ _).symm

lemma blkRestMeasure_univ_le (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) :
    blkRestMeasure kind i Set.univ
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (kind i).dm * 2 ^ totDim fun j => kind (i.succAbove j)) := by
  rw [blkRestMeasure_eq_prod, ← Set.univ_prod_univ, Measure.prod_prod, volume_restrict_cube,
    volume_restrict_bigCube, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    measure_univ, measure_univ, mul_one, mul_one, ← ENNReal.ofReal_mul (by positivity)]

/-- The contribution of the *other* blocks to `Δ`. -/
noncomputable def blkRestFactor (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) (γ : ℝ)
    (r : BlkRest kind i) : ℝ := γ * ∏ j, (kind (i.succAbove j)).factor (r.2 j)

lemma measurable_blkRestFactor (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) (γ : ℝ) :
    Measurable (blkRestFactor kind i γ) := by
  unfold blkRestFactor
  exact measurable_const.mul (Finset.measurable_prod _ fun j _ =>
    (kind (i.succAbove j)).measurable_factor.comp
      ((measurable_pi_apply j).comp measurable_snd))

/-- **The tail bound for the other blocks.**  The first factor of `BlkRest` — the remaining
coordinate of block `i` — does not enter `blkRestFactor`, so it contributes only its mass. -/
theorem tailBound_blkRest (kind : Fin (N + 1 + 1) → BlockKind) (i : Fin (N + 1 + 1))
    {a : ℝ} (ha : a ≠ 0) :
    TailBound (blkRestMeasure kind i) (fun r => |blkRestFactor kind i a r|)
      ((2 : ℝ) ^ (kind i).dm * blkGammaConst (fun j => kind (i.succAbove j)) a) N := by
  intro v hv
  have hset : {r : BlkRest kind i | |blkRestFactor kind i a r| ≤ v}
      = Set.univ ×ˢ {w : Blk fun j => kind (i.succAbove j) |
          |a * ∏ j, (kind (i.succAbove j)).factor (w j)| ≤ v} := by
    ext r
    simp [blkRestFactor]
  rw [hset, blkRestMeasure_eq_prod, Measure.prod_prod, volume_restrict_cube,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  calc ENNReal.ofReal ((2:ℝ) ^ (kind i).dm)
        * ((volume : Measure (Blk fun j => kind (i.succAbove j))).restrict
            (bigCube fun j => kind (i.succAbove j)))
          {w | |a * ∏ j, (kind (i.succAbove j)).factor (w j)| ≤ v}
      ≤ ENNReal.ofReal ((2:ℝ) ^ (kind i).dm)
        * ENNReal.ofReal (blkGammaConst (fun j => kind (i.succAbove j)) a * v * Lam v ^ N) :=
        mul_le_mul_left' (tailBound_gammaBlkProd (fun j => kind (i.succAbove j)) ha v hv) _
    _ = ENNReal.ofReal ((2:ℝ) ^ (kind i).dm
          * (blkGammaConst (fun j => kind (i.succAbove j)) a * v * Lam v ^ N)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal ((2:ℝ) ^ (kind i).dm
          * blkGammaConst (fun j => kind (i.succAbove j)) a * v * Lam v ^ N) := by ring_nf

/-! ### The chart bound

On a product `ℝ × Rest`, with `F(t,r) = t·h(r) + G(t,r)` and `|∂ₜ G| ≤ η`, the fiber bound
of `Formal/OneDim.lean` applies wherever `|h| ≥ 2η`, and Tonelli turns it into an integral
of `min(1, s/|h|)` — which is exactly the shape the dyadic lemma consumes.

The two bounds on a fiber, `4s/|h|` from monotonicity and `2` from the length of the fiber,
are combined *before* integrating: `min(2, 4s/|h|) ≤ 4·min(1, s/|h|)`. -/

private lemma min_two_le {a : ℝ} (ha : 0 ≤ a) : min 2 (4 * a) ≤ 4 * min 1 a := by
  rcases le_total a 1 with h | h
  · rw [min_eq_right h]
    exact min_le_right _ _
  · rw [min_eq_left h]
    have : (2:ℝ) ≤ 4 := by norm_num
    exact le_trans (min_le_left _ _) (by linarith)

/-- **The chart bound.**  The part of the sublevel set of `F(t,r) = t·h(r) + G(t,r)` lying
over `{|h| ≥ 2η}` has measure at most `4 ∫ min(1, s/|h|)`. -/
theorem measure_chart_le
    {Rest : Type*} [MeasurableSpace Rest] {ν : Measure Rest} [SFinite ν]
    {h : Rest → ℝ} {G G' : ℝ → Rest → ℝ} {η s : ℝ}
    (hη : 0 < η) (hs : 0 ≤ s)
    (hG : ∀ r t, HasDerivAt (fun t => G t r) (G' t r) t)
    (hG'b : ∀ᵐ r ∂ν, ∀ t ∈ Set.Icc (-1 : ℝ) 1, |G' t r| ≤ η)
    (hSmeas : MeasurableSet
      {p : ℝ × Rest | |p.1 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ |h p.2|}) :
    (((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)).prod ν)
        {p : ℝ × Rest | |p.1 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ |h p.2|}
      ≤ 4 * ∫⁻ r, ENNReal.ofReal (min 1 (s / |h r|)) ∂ν := by
  classical
  -- the slice over a fixed `r` at which the derivative bound holds
  have hslice : ∀ r : Rest, (∀ t ∈ Set.Icc (-1 : ℝ) 1, |G' t r| ≤ η) →
      ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1))
          ((fun t => (t, r)) ⁻¹'
            {p : ℝ × Rest | |p.1 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ |h p.2|})
        ≤ ENNReal.ofReal (min 2 (4 * (s / |h r|))) := by
    intro r hbnd
    by_cases hcase : 2 * η ≤ |h r|
    · -- the fiber bound applies
      have hpre : (fun t => (t, r)) ⁻¹'
          {p : ℝ × Rest | |p.1 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ |h p.2|}
          = {t : ℝ | |t * h r + G t r| ≤ s} := by
        ext t
        simp only [Set.mem_preimage, Set.mem_setOf_eq, and_iff_left hcase]
      have hTmeas : MeasurableSet {t : ℝ | |t * h r + G t r| ≤ s} := by
        have hcont : Continuous fun t => t * h r + G t r := by
          have hGc : Continuous fun t => G t r :=
            continuous_iff_continuousAt.mpr fun t => (hG r t).continuousAt
          exact (continuous_id.mul continuous_const).add hGc
        exact (hcont.abs.measurable) measurableSet_Iic
      rw [hpre, Measure.restrict_apply hTmeas]
      -- the fiber estimate, and the trivial length bound
      have hfib : volume ({t : ℝ | |t * h r + G t r| ≤ s} ∩ Set.Icc (-1 : ℝ) 1)
          ≤ ENNReal.ofReal (4 * s / (1 * |h r|)) := by
        rw [Set.inter_comm]
        exact volume_fiber_le (convex_Icc (-1 : ℝ) 1) one_pos hη hs
          (fun t _ => hasDerivAt_id t) (fun t _ => hG r t)
          (fun t _ => le_rfl) (fun t ht => hbnd t ht) (by linarith)
      have hlen : volume ({t : ℝ | |t * h r + G t r| ≤ s} ∩ Set.Icc (-1 : ℝ) 1)
          ≤ ENNReal.ofReal 2 := by
        refine le_trans (measure_mono Set.inter_subset_right) ?_
        rw [Real.volume_Icc]
        norm_num
      rcases le_total (2:ℝ) (4 * (s / |h r|)) with hm | hm
      · rw [min_eq_left hm]; exact hlen
      · rw [min_eq_right hm]
        refine le_trans hfib (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
        rw [one_mul, mul_div_assoc]
    · -- the slice is empty
      have hpre : (fun t => (t, r)) ⁻¹'
          {p : ℝ × Rest | |p.1 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ |h p.2|} = ∅ := by
        ext t
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hc => hcase hc.2
      rw [hpre]
      simp
  calc (((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)).prod ν)
        {p : ℝ × Rest | |p.1 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ |h p.2|}
      = ∫⁻ r, ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1))
          ((fun t => (t, r)) ⁻¹'
            {p : ℝ × Rest | |p.1 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ |h p.2|}) ∂ν :=
        Measure.prod_apply_symm hSmeas
    _ ≤ ∫⁻ r, ENNReal.ofReal (4 * min 1 (s / |h r|)) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hG'b] with r hr
        refine le_trans (hslice r hr) (ENNReal.ofReal_le_ofReal ?_)
        exact min_two_le (by positivity)
    _ = 4 * ∫⁻ r, ENNReal.ofReal (min 1 (s / |h r|)) ∂ν := by
        rw [← lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
        refine lintegral_congr fun r => ?_
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- **The chart bound, general fibre.**  `measure_chart_le` generalized from `t·h` to
`Q(t,r)·h(r)`, with `∂ₜQ ≥ c₁ > 0` on a fibre interval `I ⊆ [-1,1]`.

This is what a *plane* block needs: fibring in one Cartesian coordinate `a` of the block,
`Q(a,r) = a² + b²` has `∂_a Q = 2a ≥ 2c⋆` on `{a ≥ c⋆}`.  No polar coordinates are
required — splitting the chart by *which* coordinate of the block is large suffices, and the
fibre stays a single interval on which `volume_fiber_le` applies. -/
theorem measure_chart_gen_le
    {Rest : Type*} [MeasurableSpace Rest] {ν : Measure Rest} [SFinite ν]
    {I : Set ℝ} (hI : Convex ℝ I) (hIsub : I ⊆ Set.Icc (-1 : ℝ) 1)
    (hImeas : MeasurableSet I)
    {h : Rest → ℝ} {Q Q' G G' : ℝ → Rest → ℝ} {c₁ η s : ℝ}
    (hc₁ : 0 < c₁) (hη : 0 < η) (hs : 0 ≤ s)
    (hQ : ∀ r, ∀ t ∈ I, HasDerivAt (fun t => Q t r) (Q' t r) t)
    (hG : ∀ᵐ r ∂ν, ∀ t ∈ I, HasDerivAt (fun t => G t r) (G' t r) t)
    (hQ'lb : ∀ r, ∀ t ∈ I, c₁ ≤ Q' t r)
    (hG'b : ∀ᵐ r ∂ν, ∀ t ∈ I, |G' t r| ≤ η)
    (hSmeas : MeasurableSet
      {p : ℝ × Rest | |Q p.1 p.2 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ c₁ * |h p.2|}) :
    (((volume : Measure ℝ).restrict I).prod ν)
        {p : ℝ × Rest | |Q p.1 p.2 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ c₁ * |h p.2|}
      ≤ 4 * ∫⁻ r, ENNReal.ofReal (min 1 (s / (c₁ * |h r|))) ∂ν := by
  classical
  have hslice : ∀ r : Rest, (∀ t ∈ I, HasDerivAt (fun t => G t r) (G' t r) t) →
      (∀ t ∈ I, |G' t r| ≤ η) →
      ((volume : Measure ℝ).restrict I)
          ((fun t => (t, r)) ⁻¹'
            {p : ℝ × Rest | |Q p.1 p.2 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ c₁ * |h p.2|})
        ≤ ENNReal.ofReal (min 2 (4 * (s / (c₁ * |h r|)))) := by
    intro r hder hbnd
    by_cases hcase : 2 * η ≤ c₁ * |h r|
    · have hpre : (fun t => (t, r)) ⁻¹'
          {p : ℝ × Rest | |Q p.1 p.2 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ c₁ * |h p.2|}
          = {t : ℝ | |Q t r * h r + G t r| ≤ s} := by
        ext t
        simp only [Set.mem_preimage, Set.mem_setOf_eq, and_iff_left hcase]
      have hmeasr : Measurable (fun t : ℝ => ((t, r) : ℝ × Rest)) :=
        measurable_id.prodMk measurable_const
      have hTmeas : MeasurableSet {t : ℝ | |Q t r * h r + G t r| ≤ s} := by
        have hT := hSmeas.preimage hmeasr
        rwa [hpre] at hT
      rw [hpre, Measure.restrict_apply hTmeas]
      have hfib : volume ({t : ℝ | |Q t r * h r + G t r| ≤ s} ∩ I)
          ≤ ENNReal.ofReal (4 * s / (c₁ * |h r|)) := by
        rw [Set.inter_comm]
        exact volume_fiber_le hI hc₁ hη hs (fun t ht => hQ r t ht)
          (fun t ht => hder t ht) (fun t ht => hQ'lb r t ht) (fun t ht => hbnd t ht) hcase
      have hlen : volume ({t : ℝ | |Q t r * h r + G t r| ≤ s} ∩ I) ≤ ENNReal.ofReal 2 := by
        refine le_trans (measure_mono (Set.inter_subset_right.trans hIsub)) ?_
        rw [Real.volume_Icc]
        norm_num
      rcases le_total (2:ℝ) (4 * (s / (c₁ * |h r|))) with hm | hm
      · rw [min_eq_left hm]; exact hlen
      · rw [min_eq_right hm]
        refine le_trans hfib (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
        rw [mul_div_assoc]
    · have hpre : (fun t => (t, r)) ⁻¹'
          {p : ℝ × Rest | |Q p.1 p.2 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ c₁ * |h p.2|} = ∅ := by
        ext t
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hc => hcase hc.2
      rw [hpre]
      simp
  calc (((volume : Measure ℝ).restrict I).prod ν)
        {p : ℝ × Rest | |Q p.1 p.2 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ c₁ * |h p.2|}
      = ∫⁻ r, ((volume : Measure ℝ).restrict I)
          ((fun t => (t, r)) ⁻¹'
            {p : ℝ × Rest | |Q p.1 p.2 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ c₁ * |h p.2|}) ∂ν :=
        Measure.prod_apply_symm hSmeas
    _ ≤ ∫⁻ r, ENNReal.ofReal (4 * min 1 (s / (c₁ * |h r|))) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hG, hG'b] with r hr1 hr2
        refine le_trans (hslice r hr1 hr2) (ENNReal.ofReal_le_ofReal ?_)
        exact min_two_le (by positivity)
    _ = 4 * ∫⁻ r, ENNReal.ofReal (min 1 (s / (c₁ * |h r|))) ∂ν := by
        rw [← lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
        refine lintegral_congr fun r => ?_
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- **The chart bound, evaluated.**  Feeding the tail bound on `|h|` into the dyadic lemma
turns the chart bound into `4(4C+M) · s · Λ(s)^(j+1)`: one extra power of the logarithm per
chart, exactly as in the appendix. -/
theorem measure_chart_le'
    {Rest : Type*} [MeasurableSpace Rest] {ν : Measure Rest} [SFinite ν]
    {h : Rest → ℝ} {G G' : ℝ → Rest → ℝ} {η s M C : ℝ} {j : ℕ}
    (hη : 0 < η) (hs : 0 < s) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hhmeas : Measurable h)
    (hG : ∀ r t, HasDerivAt (fun t => G t r) (G' t r) t)
    (hG'b : ∀ᵐ r ∂ν, ∀ t ∈ Set.Icc (-1 : ℝ) 1, |G' t r| ≤ η)
    (hSmeas : MeasurableSet
      {p : ℝ × Rest | |p.1 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ |h p.2|})
    (hν : ν Set.univ ≤ ENNReal.ofReal M)
    (htail : TailBound ν (fun r => |h r|) C j) :
    (((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)).prod ν)
        {p : ℝ × Rest | |p.1 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ |h p.2|}
      ≤ ENNReal.ofReal (4 * (4 * C + M) * s * Lam s ^ (j + 1)) := by
  refine le_trans (measure_chart_le hη hs.le hG hG'b hSmeas) ?_
  have hdy := lintegral_min_one_div_le (μ := ν) (Y := fun r => |h r|)
    hhmeas.abs hM hC hs j hν (fun u hu => htail u hu.le)
  calc (4 : ℝ≥0∞) * ∫⁻ r, ENNReal.ofReal (min 1 (s / |h r|)) ∂ν
      ≤ 4 * ENNReal.ofReal ((4 * C + M) * s * Lam s ^ (j + 1)) :=
        mul_le_mul_left' hdy _
    _ = ENNReal.ofReal (4 * (4 * C + M) * s * Lam s ^ (j + 1)) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
        congr 1
        ring

/-- **The discarded set.**  Over `{|h| ≤ 2η}` nothing is claimed about the fiber; the whole
slab is surrendered, and its measure is controlled by the tail bound on `|h|` alone. -/
theorem measure_discarded_le
    {Rest : Type*} [MeasurableSpace Rest] {ν : Measure Rest} [SFinite ν]
    {h : Rest → ℝ} {η C : ℝ} {j : ℕ} (hη : 0 < η)
    (htail : TailBound ν (fun r => |h r|) C j) :
    (((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)).prod ν)
        (Set.univ ×ˢ {r : Rest | |h r| ≤ 2 * η})
      ≤ ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ j)) := by
  rw [Measure.prod_prod]
  have h1 : ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)) Set.univ
      = ENNReal.ofReal 2 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    norm_num
  rw [h1]
  calc ENNReal.ofReal 2 * ν {r : Rest | |h r| ≤ 2 * η}
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal (C * (2 * η) * Lam (2 * η) ^ j) :=
        mul_le_mul_left' (htail _ (by positivity)) _
    _ = ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ j)) :=
        (ENNReal.ofReal_mul (by norm_num)).symm

/-- **The chart bound, general fibre, evaluated.**  The general-`Q` analogue of
`measure_chart_le'`: the tail bound is now required for `c₁|h|` rather than `|h|`, which is
what `measure_chart_gen_le` produces, and at the application site `c₁|h| = (c₁γ)∏ᵢ factorᵢ`
has the same shape as `h` itself. -/
theorem measure_chart_gen_le'
    {Rest : Type*} [MeasurableSpace Rest] {ν : Measure Rest} [SFinite ν]
    {I : Set ℝ} (hI : Convex ℝ I) (hIsub : I ⊆ Set.Icc (-1 : ℝ) 1)
    (hImeas : MeasurableSet I)
    {h : Rest → ℝ} {Q Q' G G' : ℝ → Rest → ℝ} {c₁ η s M C : ℝ} {j : ℕ}
    (hc₁ : 0 < c₁) (hη : 0 < η) (hs : 0 < s) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hhmeas : Measurable h)
    (hQ : ∀ r, ∀ t ∈ I, HasDerivAt (fun t => Q t r) (Q' t r) t)
    (hG : ∀ᵐ r ∂ν, ∀ t ∈ I, HasDerivAt (fun t => G t r) (G' t r) t)
    (hQ'lb : ∀ r, ∀ t ∈ I, c₁ ≤ Q' t r)
    (hG'b : ∀ᵐ r ∂ν, ∀ t ∈ I, |G' t r| ≤ η)
    (hSmeas : MeasurableSet
      {p : ℝ × Rest | |Q p.1 p.2 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ c₁ * |h p.2|})
    (hν : ν Set.univ ≤ ENNReal.ofReal M)
    (htail : TailBound ν (fun r => c₁ * |h r|) C j) :
    (((volume : Measure ℝ).restrict I).prod ν)
        {p : ℝ × Rest | |Q p.1 p.2 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ c₁ * |h p.2|}
      ≤ ENNReal.ofReal (4 * (4 * C + M) * s * Lam s ^ (j + 1)) := by
  refine le_trans
    (measure_chart_gen_le hI hIsub hImeas hc₁ hη hs.le hQ hG hQ'lb hG'b hSmeas) ?_
  have hdy := lintegral_min_one_div_le (μ := ν) (Y := fun r => c₁ * |h r|)
    (measurable_const.mul hhmeas.abs) hM hC hs j hν (fun u hu => htail u hu.le)
  calc (4 : ℝ≥0∞) * ∫⁻ r, ENNReal.ofReal (min 1 (s / (c₁ * |h r|))) ∂ν
      ≤ 4 * ENNReal.ofReal ((4 * C + M) * s * Lam s ^ (j + 1)) := mul_le_mul_left' hdy _
    _ = ENNReal.ofReal (4 * (4 * C + M) * s * Lam s ^ (j + 1)) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
        congr 1
        ring

/-- **The discarded set, general fibre interval.** -/
theorem measure_discarded_gen_le
    {Rest : Type*} [MeasurableSpace Rest] {ν : Measure Rest} [SFinite ν]
    {I : Set ℝ} (hIsub : I ⊆ Set.Icc (-1 : ℝ) 1)
    {h : Rest → ℝ} {c₁ η C : ℝ} {j : ℕ} (hη : 0 < η)
    (htail : TailBound ν (fun r => c₁ * |h r|) C j) :
    (((volume : Measure ℝ).restrict I).prod ν)
        (Set.univ ×ˢ {r : Rest | c₁ * |h r| ≤ 2 * η})
      ≤ ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ j)) := by
  rw [Measure.prod_prod]
  have h1 : ((volume : Measure ℝ).restrict I) Set.univ ≤ ENNReal.ofReal 2 := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    refine le_trans (measure_mono hIsub) ?_
    rw [Real.volume_Icc]
    norm_num
  calc ((volume : Measure ℝ).restrict I) Set.univ * ν {r : Rest | c₁ * |h r| ≤ 2 * η}
      ≤ ENNReal.ofReal 2 * ENNReal.ofReal (C * (2 * η) * Lam (2 * η) ^ j) :=
        mul_le_mul' h1 (htail _ (by positivity))
    _ = ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ j)) :=
        (ENNReal.ofReal_mul (by norm_num)).symm

/-! ### The fibre polynomial of a block

The block factor, as a function of one of its coordinates `t` with the rest `r` frozen, and
with an overall sign `σ`.  Keeping this *uniform in the kind of block* is what lets the chart
cover avoid a case distinction: `line` gives `σt`, `plane` gives `σ(t² + r₀²)`, and the sign
is `1` on the positive half of a chart and `BlockKind.negSign` on the negative half. -/

/-- The block factor in split coordinates, with a sign. -/
noncomputable def BlockKind.fib : (b : BlockKind) → ℝ → ℝ → (Fin b.dm → ℝ) → ℝ
  | .line => fun σ t _ => σ * t
  | .plane => fun σ t r => σ * (t ^ 2 + (r 0) ^ 2)

/-- Its derivative in the distinguished coordinate. -/
noncomputable def BlockKind.fibDeriv : (b : BlockKind) → ℝ → ℝ → ℝ
  | .line => fun σ _ => σ
  | .plane => fun σ t => σ * (2 * t)

/-- The sign that makes `∂ₜ fib` positive on the *negative* half of a chart. -/
def BlockKind.negSign : BlockKind → ℝ
  | .line => 1
  | .plane => -1

lemma BlockKind.negSign_sq (b : BlockKind) : b.negSign * b.negSign = 1 := by
  cases b <;> norm_num [BlockKind.negSign]

lemma BlockKind.factor_eq_fib (b : BlockKind) (σ : ℝ) (u : Fin b.dim → ℝ) (l : Fin b.dim) :
    σ * b.factor u = b.fib σ (u l) (fun j => u (l.succAbove j)) := by
  cases b with
  | line =>
      induction l using Fin.cases with
      | zero => rfl
      | succ j => exact j.elim0
  | plane =>
      induction l using Fin.cases with
      | zero => simp [BlockKind.fib, BlockKind.factor]
      | succ j =>
          induction j using Fin.cases with
          | zero =>
              have hsa : (Fin.succAbove (1 : Fin 2) (0 : Fin 1)) = 0 := by decide
              simp only [BlockKind.fib, BlockKind.factor, Fin.succ_zero_eq_one, hsa]
              ring
          | succ k => exact k.elim0

lemma BlockKind.hasDerivAt_fib (b : BlockKind) (σ : ℝ) (r : Fin b.dm → ℝ) (t : ℝ) :
    HasDerivAt (fun t => b.fib σ t r) (b.fibDeriv σ t) t := by
  cases b with
  | line => simpa [BlockKind.fib, BlockKind.fibDeriv] using (hasDerivAt_id t).const_mul σ
  | plane =>
      have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + (r 0) ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t).add_const ((r 0) ^ 2)
      simpa [BlockKind.fib, BlockKind.fibDeriv] using h1.const_mul σ

lemma BlockKind.measurable_fib (b : BlockKind) (σ : ℝ) :
    Measurable fun p : ℝ × (Fin b.dm → ℝ) => b.fib σ p.1 p.2 := by
  cases b <;> · unfold BlockKind.fib; fun_prop

lemma BlockKind.fibDeriv_pos_lb (b : BlockKind) {c t : ℝ} (hc1 : 2 * c ≤ 1)
    (ht : t ∈ Set.Icc c 1) : 2 * c ≤ b.fibDeriv 1 t := by
  obtain ⟨h1, h2⟩ := ht
  cases b <;> simp only [BlockKind.fibDeriv, one_mul] <;> linarith

lemma BlockKind.fibDeriv_neg_lb (b : BlockKind) {c t : ℝ} (hc1 : 2 * c ≤ 1)
    (ht : t ∈ Set.Icc (-1 : ℝ) (-c)) : 2 * c ≤ b.fibDeriv b.negSign t := by
  obtain ⟨h1, h2⟩ := ht
  cases b <;> simp only [BlockKind.fibDeriv, BlockKind.negSign] <;> linarith

/-- **The per-chart bound.**  Fix a block `i`, a coordinate `l` of it, a sign `σ` with
`σ² = 1`, and a fibre interval `I ⊆ [-1,1]` on which the signed block factor has derivative at
least `c₁ > 0`.  The part of the sublevel set lying over `I` then obeys the sharp bound.

The sign is what makes the *negative* half of a chart work: `|Qh + G| = |(σQ)(σh) + G|` and
`|σh| = |h|`, so the tail bound is unaffected while `∂ₜ(σQ)` becomes positive. -/
theorem measure_chart_blk_le {N j : ℕ} (kind : Fin (N + 1) → BlockKind)
    (i : Fin (N + 1)) (l : Fin (kind i).dim) {σ : ℝ} (hσ : σ * σ = 1)
    {Qb Qb' : ℝ → (Fin (kind i).dm → ℝ) → ℝ}
    (hQb : ∀ u : Fin (kind i).dim → ℝ,
      σ * (kind i).factor u = Qb (u l) (fun j => u (l.succAbove j)))
    (hQbmeas : Measurable fun p : ℝ × (Fin (kind i).dm → ℝ) => Qb p.1 p.2)
    {I : Set ℝ} (hI : Convex ℝ I) (hIsub : I ⊆ Set.Icc (-1 : ℝ) 1)
    (hImeas : MeasurableSet I)
    {c₁ : ℝ} (hc₁ : 0 < c₁)
    (hQbd : ∀ r, ∀ t ∈ I, HasDerivAt (fun t => Qb t r) (Qb' t r) t)
    (hQb'lb : ∀ r, ∀ t ∈ I, c₁ ≤ Qb' t r)
    {γ η s C M : ℝ} (hη : 0 < η) (hs : 0 < s) (hC : 0 ≤ C) (hM : 0 ≤ M)
    {E : Blk kind → ℝ} (hEmeas : Measurable E)
    {Epar : ℝ → BlkRest kind i → ℝ}
    (hE : ∀ᵐ r ∂(blkRestMeasure kind i), ∀ t ∈ I,
      HasDerivAt (fun t => E ((blkSplit kind i l).symm (t, r))) (Epar t r) t)
    (hEb : ∀ᵐ ρ ∂(blkRestMeasure kind i), ∀ t ∈ I, |Epar t ρ| ≤ η)
    (hν : blkRestMeasure kind i Set.univ ≤ ENNReal.ofReal M)
    (htail : TailBound (blkRestMeasure kind i)
      (fun r => c₁ * |blkRestFactor kind i (σ * γ) r|) C j) :
    volume ({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind
        ∩ {u | u i l ∈ I})
      ≤ ENNReal.ofReal (4 * (4 * C + M) * s * Lam s ^ (j + 1))
        + ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ j)) := by
  classical
  have hmp := measurePreserving_blkSplit kind i l
  have hhmeas : Measurable (blkRestFactor kind i (σ * γ)) :=
    measurable_blkRestFactor kind i (σ * γ)
  have hGmeas : Measurable fun p : ℝ × BlkRest kind i =>
      E ((blkSplit kind i l).symm p) := hEmeas.comp (blkSplit kind i l).symm.measurable
  have hQmeas : Measurable fun p : ℝ × BlkRest kind i => Qb p.1 p.2.1 :=
    hQbmeas.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hB₁meas : MeasurableSet {p : ℝ × BlkRest kind i |
      |Qb p.1 p.2.1 * blkRestFactor kind i (σ * γ) p.2 + E ((blkSplit kind i l).symm p)| ≤ s
        ∧ 2 * η ≤ c₁ * |blkRestFactor kind i (σ * γ) p.2|} :=
    (((hQmeas.mul (hhmeas.comp measurable_snd)).add hGmeas).abs measurableSet_Iic).inter
      (measurableSet_le measurable_const
        (measurable_const.mul (hhmeas.comp measurable_snd).abs))
  have hB₂meas : MeasurableSet ((Set.univ : Set ℝ) ×ˢ
      {r : BlkRest kind i | c₁ * |blkRestFactor kind i (σ * γ) r| ≤ 2 * η}) :=
    MeasurableSet.univ.prod
      (measurableSet_le (measurable_const.mul hhmeas.abs) measurable_const)
  have hcubmeas : MeasurableSet (I ×ˢ
      (cube (kind i).dm ×ˢ bigCube fun j => kind (i.succAbove j))) :=
    hImeas.prod ((measurableSet_cube _).prod (measurableSet_bigCube _))
  have hsub : ({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind
        ∩ {u | u i l ∈ I})
      ⊆ blkSplit kind i l ⁻¹'
        (({p : ℝ × BlkRest kind i |
            |Qb p.1 p.2.1 * blkRestFactor kind i (σ * γ) p.2
                + E ((blkSplit kind i l).symm p)| ≤ s
              ∧ 2 * η ≤ c₁ * |blkRestFactor kind i (σ * γ) p.2|}
          ∪ (Set.univ ×ˢ
              {r : BlkRest kind i | c₁ * |blkRestFactor kind i (σ * γ) r| ≤ 2 * η}))
        ∩ (I ×ˢ (cube (kind i).dm ×ˢ bigCube fun j => kind (i.succAbove j)))) := by
    rintro u ⟨⟨hu, hcube⟩, hIu⟩
    have hprod : γ * ∏ j, (kind j).factor (u j)
        = Qb (blkSplit kind i l u).1 (blkSplit kind i l u).2.1
          * blkRestFactor kind i (σ * γ) (blkSplit kind i l u).2 := by
      simp only [blkSplit_apply, blkRestFactor]
      rw [← hQb (u i), Fin.prod_univ_succAbove _ i]
      calc γ * ((kind i).factor (u i)
              * ∏ j, (kind (i.succAbove j)).factor (u (i.succAbove j)))
          = (σ * σ) * (γ * ((kind i).factor (u i)
              * ∏ j, (kind (i.succAbove j)).factor (u (i.succAbove j)))) := by
            rw [hσ, one_mul]
        _ = σ * (kind i).factor (u i)
              * (σ * γ * ∏ j, (kind (i.succAbove j)).factor (u (i.succAbove j))) := by ring
    have hEcons : E u = E ((blkSplit kind i l).symm (blkSplit kind i l u)) := by
      rw [MeasurableEquiv.symm_apply_apply]
    have hmemcub : blkSplit kind i l u
        ∈ I ×ˢ (cube (kind i).dm ×ˢ bigCube fun j => kind (i.succAbove j)) := by
      refine ⟨hIu, ?_⟩
      rw [bigCube_eq_preimage kind i l] at hcube
      exact hcube.2
    refine ⟨?_, hmemcub⟩
    rcases le_or_gt (2 * η) (c₁ * |blkRestFactor kind i (σ * γ) (blkSplit kind i l u).2|)
      with hcase | hcase
    · exact Or.inl ⟨by rw [← hprod, ← hEcons]; exact hu, hcase⟩
    · exact Or.inr ⟨Set.mem_univ _, hcase.le⟩
  calc volume ({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind
        ∩ {u | u i l ∈ I})
      ≤ volume (blkSplit kind i l ⁻¹'
        (({p : ℝ × BlkRest kind i |
            |Qb p.1 p.2.1 * blkRestFactor kind i (σ * γ) p.2
                + E ((blkSplit kind i l).symm p)| ≤ s
              ∧ 2 * η ≤ c₁ * |blkRestFactor kind i (σ * γ) p.2|}
          ∪ (Set.univ ×ˢ
              {r : BlkRest kind i | c₁ * |blkRestFactor kind i (σ * γ) r| ≤ 2 * η}))
        ∩ (I ×ˢ (cube (kind i).dm ×ˢ bigCube fun j => kind (i.succAbove j))))) :=
        measure_mono hsub
    _ = ((volume : Measure ℝ).prod (volume : Measure (BlkRest kind i)))
          (({p : ℝ × BlkRest kind i |
              |Qb p.1 p.2.1 * blkRestFactor kind i (σ * γ) p.2
                  + E ((blkSplit kind i l).symm p)| ≤ s
                ∧ 2 * η ≤ c₁ * |blkRestFactor kind i (σ * γ) p.2|}
            ∪ (Set.univ ×ˢ
                {r : BlkRest kind i | c₁ * |blkRestFactor kind i (σ * γ) r| ≤ 2 * η}))
          ∩ (I ×ˢ (cube (kind i).dm ×ˢ bigCube fun j => kind (i.succAbove j)))) :=
        hmp.measure_preimage (((hB₁meas.union hB₂meas).inter hcubmeas).nullMeasurableSet)
    _ = (((volume : Measure ℝ).restrict I).prod (blkRestMeasure kind i))
          ({p : ℝ × BlkRest kind i |
              |Qb p.1 p.2.1 * blkRestFactor kind i (σ * γ) p.2
                  + E ((blkSplit kind i l).symm p)| ≤ s
                ∧ 2 * η ≤ c₁ * |blkRestFactor kind i (σ * γ) p.2|}
            ∪ (Set.univ ×ˢ
                {r : BlkRest kind i | c₁ * |blkRestFactor kind i (σ * γ) r| ≤ 2 * η})) := by
        rw [blkRestMeasure, Measure.prod_restrict,
          Measure.restrict_apply (hB₁meas.union hB₂meas)]
    _ ≤ (((volume : Measure ℝ).restrict I).prod (blkRestMeasure kind i))
          {p : ℝ × BlkRest kind i |
              |Qb p.1 p.2.1 * blkRestFactor kind i (σ * γ) p.2
                  + E ((blkSplit kind i l).symm p)| ≤ s
                ∧ 2 * η ≤ c₁ * |blkRestFactor kind i (σ * γ) p.2|}
        + (((volume : Measure ℝ).restrict I).prod (blkRestMeasure kind i))
          (Set.univ ×ˢ {r : BlkRest kind i | c₁ * |blkRestFactor kind i (σ * γ) r| ≤ 2 * η}) :=
        measure_union_le _ _
    _ ≤ _ := by
        refine add_le_add ?_ ?_
        · exact measure_chart_gen_le' (Q := fun t r => Qb t r.1) (Q' := fun t r => Qb' t r.1)
            (G := fun t r => E ((blkSplit kind i l).symm (t, r))) (G' := Epar)
            (h := blkRestFactor kind i (σ * γ)) hI hIsub hImeas hc₁ hη hs hM hC hhmeas
            (fun r t ht => hQbd r.1 t ht) hE
            (fun r t ht => hQb'lb r.1 t ht) hEb hB₁meas hν htail
        · exact measure_discarded_gen_le hIsub hη htail

lemma BlockKind.abs_negSign (b : BlockKind) : |b.negSign| = 1 := by
  cases b <;> norm_num [BlockKind.negSign]

lemma abs_blkRestFactor_sign (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) {σ γ : ℝ}
    (hσ : |σ| = 1) (r : BlkRest kind i) :
    |blkRestFactor kind i (σ * γ) r| = |blkRestFactor kind i γ r| := by
  unfold blkRestFactor
  rw [mul_assoc, abs_mul, hσ, one_mul]

/-- **The shell estimate (Obligation 6).**  On the part of the cube where some Cartesian
coordinate is at least `c` in absolute value — which is where the shell decomposition of §9
lands after rescaling — the sublevel set of `γ ∏ᵢ factorᵢ + E` obeys the sharp bound.

The `2·totDim` charts are the `(block, coordinate, sign)` triples; on each one the signed block
factor has fibre derivative at least `2c`, a **constant**, so no exponent is lost. -/
theorem measure_sublevel_shell_le {N j : ℕ} (kind : Fin (N + 1) → BlockKind)
    {γ η s c C M : ℝ} (hη : 0 < η) (hs : 0 < s) (hc : 0 < c) (hc1 : 2 * c ≤ 1)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hMi : ∀ i, blkRestMeasure kind i Set.univ ≤ ENNReal.ofReal M)
    (hCi : ∀ i, TailBound (blkRestMeasure kind i)
      (fun r => 2 * c * |blkRestFactor kind i γ r|) C j)
    {E : Blk kind → ℝ} (hEmeas : Measurable E)
    (Epar : (i : Fin (N + 1)) → Fin (kind i).dim → ℝ → BlkRest kind i → ℝ)
    (hE : ∀ i l, ∀ᵐ r ∂(blkRestMeasure kind i), ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt
      (fun t => E ((blkSplit kind i l).symm (t, r))) (Epar i l t r) t)
    (hEb : ∀ i l, ∀ᵐ ρ ∂(blkRestMeasure kind i),
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Epar i l t ρ| ≤ η) :
    volume ({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind
        ∩ {u | c ≤ ‖u‖})
      ≤ (2 * totDim kind : ℕ)
          * (ENNReal.ofReal (4 * (4 * C + M) * s * Lam s ^ (j + 1))
            + ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ j))) := by
  classical
  have hc2 : (0:ℝ) < 2 * c := by linarith
  -- the per-chart bound, on both halves of every chart
  have hchart : ∀ (i : Fin (N + 1)) (l : Fin (kind i).dim),
      volume (({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind)
          ∩ {u | c ≤ u i l})
        + volume (({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind)
          ∩ {u | u i l ≤ -c})
      ≤ (ENNReal.ofReal (4 * (4 * C + M) * s * Lam s ^ (j + 1))
            + ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ j)))
        + (ENNReal.ofReal (4 * (4 * C + M) * s * Lam s ^ (j + 1))
            + ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ j))) := by
    intro i l
    refine add_le_add ?_ ?_
    · -- the positive half: `σ = 1`, `I = [c,1]`
      have hincl : (({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s}
              ∩ bigCube kind) ∩ {u | c ≤ u i l})
          ⊆ (({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind)
              ∩ {u | u i l ∈ Set.Icc c 1}) := fun u hu =>
        ⟨hu.1, ⟨hu.2, (hu.1.2 i (Set.mem_univ _) l (Set.mem_univ _)).2⟩⟩
      refine le_trans (measure_mono hincl) ?_
      exact measure_chart_blk_le kind i l (σ := 1) (by norm_num)
          (Qb := (kind i).fib 1) (Qb' := fun t _ => (kind i).fibDeriv 1 t)
          (fun u => (kind i).factor_eq_fib 1 u l) ((kind i).measurable_fib 1)
          (convex_Icc c 1) (Set.Icc_subset_Icc (by linarith) le_rfl) measurableSet_Icc
          hc2 (fun r t _ => (kind i).hasDerivAt_fib 1 r t)
          (fun r t ht => (kind i).fibDeriv_pos_lb hc1 ht) hη hs hC hM hEmeas
          (Epar := Epar i l)
          (by filter_upwards [hE i l] with ρ hρ
              exact fun t ht => hρ t (Set.Icc_subset_Icc (by linarith) le_rfl ht))
          (by filter_upwards [hEb i l] with ρ hρ
              exact fun t ht => hρ t (Set.Icc_subset_Icc (by linarith) le_rfl ht))
          (hMi i) (by simpa using hCi i)
    · -- the negative half: `σ = negSign`, `I = [-1,-c]`
      have hincl : (({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s}
              ∩ bigCube kind) ∩ {u | u i l ≤ -c})
          ⊆ (({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind)
              ∩ {u | u i l ∈ Set.Icc (-1 : ℝ) (-c)}) := fun u hu =>
        ⟨hu.1, ⟨(hu.1.2 i (Set.mem_univ _) l (Set.mem_univ _)).1, hu.2⟩⟩
      refine le_trans (measure_mono hincl) ?_
      refine measure_chart_blk_le kind i l (σ := (kind i).negSign) (kind i).negSign_sq
          (Qb := (kind i).fib (kind i).negSign)
          (Qb' := fun t _ => (kind i).fibDeriv (kind i).negSign t)
          (fun u => (kind i).factor_eq_fib _ u l) ((kind i).measurable_fib _)
          (convex_Icc (-1) (-c)) (Set.Icc_subset_Icc le_rfl (by linarith)) measurableSet_Icc
          hc2 (fun r t _ => (kind i).hasDerivAt_fib _ r t)
          (fun r t ht => (kind i).fibDeriv_neg_lb hc1 ht) hη hs hC hM hEmeas
          (Epar := Epar i l)
          (by filter_upwards [hE i l] with ρ hρ
              exact fun t ht => hρ t (Set.Icc_subset_Icc le_rfl (by linarith) ht))
          (by filter_upwards [hEb i l] with ρ hρ
              exact fun t ht => hρ t (Set.Icc_subset_Icc le_rfl (by linarith) ht))
          (hMi i) ?_
      have hfun : (fun r => 2 * c * |blkRestFactor kind i ((kind i).negSign * γ) r|)
          = fun r => 2 * c * |blkRestFactor kind i γ r| := by
        funext r
        rw [abs_blkRestFactor_sign kind i (kind i).abs_negSign r]
      rw [hfun]
      exact hCi i
  -- the chart cover
  have hcover : ({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind)
        ∩ {u | c ≤ ‖u‖}
      ⊆ ⋃ p : (i : Fin (N + 1)) × Fin (kind i).dim,
          ((({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind)
              ∩ {u | c ≤ u p.1 p.2})
            ∪ (({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind)
              ∩ {u | u p.1 p.2 ≤ -c})) := by
    intro u hu
    obtain ⟨i, l, hil⟩ := exists_large_coord hc hu.2
    refine Set.mem_iUnion.mpr ⟨⟨i, l⟩, ?_⟩
    rcases large_coord_cases hil with h | h
    · exact Or.inl ⟨hu.1, h⟩
    · exact Or.inr ⟨hu.1, h⟩
  -- union bound
  calc volume (({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind)
        ∩ {u | c ≤ ‖u‖})
      ≤ ∑ p : (i : Fin (N + 1)) × Fin (kind i).dim,
          volume ((({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind)
              ∩ {u | c ≤ u p.1 p.2})
            ∪ (({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind)
              ∩ {u | u p.1 p.2 ≤ -c})) :=
        le_trans (measure_mono hcover) (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _p : (i : Fin (N + 1)) × Fin (kind i).dim,
          ((ENNReal.ofReal (4 * (4 * C + M) * s * Lam s ^ (j + 1))
              + ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ j)))
            + (ENNReal.ofReal (4 * (4 * C + M) * s * Lam s ^ (j + 1))
              + ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ j)))) := by
        refine Finset.sum_le_sum fun p _ => le_trans (measure_union_le _ _) ?_
        exact hchart p.1 p.2
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_sigma]
        simp only [Fintype.card_fin]
        rw [nsmul_eq_mul]
        rw [show ∑ i : Fin (N + 1), (kind i).dim = totDim kind from rfl]
        rw [Nat.cast_mul]
        push_cast
        ring

/-- The single constant serving every chart of the shell estimate. -/
noncomputable def shellConst (kind : Fin (N + 1 + 1) → BlockKind) (c γ : ℝ) : ℝ :=
  2 ^ totDim kind * 5 ^ N * (2 * c * |γ|)⁻¹ * Lam ((2 * c * |γ|)⁻¹) ^ N

lemma shellConst_nonneg (kind : Fin (N + 1 + 1) → BlockKind) {c : ℝ} (hc : 0 ≤ c) (γ : ℝ) :
    0 ≤ shellConst kind c γ := by
  unfold shellConst
  have := (Lam_pow_pos ((2 * c * |γ|)⁻¹) N).le
  positivity

lemma dim_add_totDim_succAbove (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) :
    (kind i).dim + totDim (fun j => kind (i.succAbove j)) = totDim kind :=
  (Fin.sum_univ_succAbove (fun j => (kind j).dim) i).symm

/-- The mass of the rest is at most `2^totDim`. -/
lemma blkRestMeasure_univ_le' (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1)) :
    blkRestMeasure kind i Set.univ ≤ ENNReal.ofReal ((2:ℝ) ^ totDim kind) := by
  refine le_trans (blkRestMeasure_univ_le kind i) (ENNReal.ofReal_le_ofReal ?_)
  rw [← pow_add]
  refine pow_le_pow_right₀ (by norm_num) ?_
  have h1 := dim_add_totDim_succAbove kind i
  have h2 : (kind i).dim = (kind i).dm + 1 := rfl
  omega

/-- **The tail bound for the rest when there is only one block.**  The "rest" then carries the
constant `a`, and the bound is the trivial one — with no logarithm. -/
theorem tailBound_blkRest_one (kind : Fin 1 → BlockKind) (i : Fin 1) {a : ℝ} (ha : a ≠ 0) :
    TailBound (blkRestMeasure kind i) (fun r => |blkRestFactor kind i a r|)
      ((2 : ℝ) ^ totDim kind * |a|⁻¹) 0 := by
  intro v hv
  have ha0 : 0 < |a| := abs_pos.mpr ha
  have hconst : ∀ r : BlkRest kind i, |blkRestFactor kind i a r| = |a| := by
    intro r; unfold blkRestFactor; simp
  rcases lt_or_ge v |a| with hlt | hge
  · have hempty : {r : BlkRest kind i | |blkRestFactor kind i a r| ≤ v} = ∅ := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hconst r, not_le]
      exact hlt
    rw [hempty]
    simp
  · refine le_trans (measure_mono (Set.subset_univ _)) ?_
    refine le_trans (blkRestMeasure_univ_le' kind i) (ENNReal.ofReal_le_ofReal ?_)
    rw [pow_zero, mul_one]
    have h1 : (1:ℝ) ≤ |a|⁻¹ * v := by
      rw [← div_eq_inv_mul, le_div_iff₀ ha0, one_mul]
      exact hge
    calc (2:ℝ) ^ totDim kind = 2 ^ totDim kind * 1 := by ring
      _ ≤ 2 ^ totDim kind * (|a|⁻¹ * v) := by
          refine mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ totDim kind * |a|⁻¹ * v := by ring

/-- **The constants for the shell estimate, in all cases.**  This is what §9 consumes: the
tail exponent is `N - 1` (the number of *other* blocks, minus one), which is `0` when there is
a single block. -/
theorem exists_shell_const {N : ℕ} (kind : Fin (N + 1) → BlockKind) {γ c : ℝ} (hγ : γ ≠ 0)
    (hc : 0 < c) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
      (∀ i, blkRestMeasure kind i Set.univ ≤ ENNReal.ofReal M) ∧
      (∀ i, TailBound (blkRestMeasure kind i)
        (fun r => 2 * c * |blkRestFactor kind i γ r|) C (N - 1)) := by
  have h2c : (0:ℝ) < 2 * c := by linarith
  have hac : (2 : ℝ) * c * γ ≠ 0 := mul_ne_zero h2c.ne' hγ
  have habs : |2 * c * γ| = 2 * c * |γ| := by rw [abs_mul, abs_of_pos h2c]
  have hfun : ∀ (i : Fin (N + 1)),
      (fun r => 2 * c * |blkRestFactor kind i γ r|)
        = fun r => |blkRestFactor kind i (2 * c * γ) r| := by
    intro i
    funext r
    unfold blkRestFactor
    have hre : (2 * c * γ) * ∏ j, (kind (i.succAbove j)).factor (r.2 j)
        = (2 * c) * (γ * ∏ j, (kind (i.succAbove j)).factor (r.2 j)) := by ring
    rw [hre, abs_mul (2 * c), abs_of_pos h2c]
  cases N with
  | zero =>
      refine ⟨(2 : ℝ) ^ totDim kind * |2 * c * γ|⁻¹, (2 : ℝ) ^ totDim kind, by positivity,
        by positivity, blkRestMeasure_univ_le' kind, fun i => ?_⟩
      rw [hfun i]
      exact tailBound_blkRest_one kind i hac
  | succ N =>
      refine ⟨shellConst kind c γ, (2 : ℝ) ^ totDim kind, shellConst_nonneg kind hc.le γ,
        by positivity, blkRestMeasure_univ_le' kind, fun i => ?_⟩
      rw [hfun i]
      refine (tailBound_blkRest kind i hac).mono_const ?_
      unfold blkGammaConst shellConst
      rw [habs]
      have hnn : (0:ℝ) ≤ 5 ^ N * (2 * c * |γ|)⁻¹ * Lam ((2 * c * |γ|)⁻¹) ^ N := by
        have := (Lam_pow_pos ((2 * c * |γ|)⁻¹) N).le
        positivity
      have hpow : (2:ℝ) ^ (kind i).dm * 2 ^ totDim (fun j => kind (i.succAbove j))
          ≤ 2 ^ totDim kind := by
        rw [← pow_add]
        refine pow_le_pow_right₀ (by norm_num) ?_
        have h1 := dim_add_totDim_succAbove kind i
        have h2 : (kind i).dim = (kind i).dm + 1 := rfl
        omega
      calc (2:ℝ) ^ (kind i).dm
            * (2 ^ totDim (fun j => kind (i.succAbove j)) * 5 ^ N * (2 * c * |γ|)⁻¹
              * Lam ((2 * c * |γ|)⁻¹) ^ N)
          = ((2:ℝ) ^ (kind i).dm * 2 ^ totDim (fun j => kind (i.succAbove j)))
              * (5 ^ N * (2 * c * |γ|)⁻¹ * Lam ((2 * c * |γ|)⁻¹) ^ N) := by ring
        _ ≤ (2:ℝ) ^ totDim kind
              * (5 ^ N * (2 * c * |γ|)⁻¹ * Lam ((2 * c * |γ|)⁻¹) ^ N) :=
            mul_le_mul_of_nonneg_right hpow hnn
        _ = _ := by ring

/-- **The shell estimate with explicit constants.**  This is the form §9 consumes. -/
theorem measure_sublevel_shell_le' {N : ℕ} (kind : Fin (N + 1 + 1) → BlockKind)
    {γ η s c : ℝ} (hγ : γ ≠ 0) (hη : 0 < η) (hs : 0 < s) (hc : 0 < c) (hc1 : 2 * c ≤ 1)
    {E : Blk kind → ℝ} (hEmeas : Measurable E)
    (Epar : (i : Fin (N + 1 + 1)) → Fin (kind i).dim → ℝ → BlkRest kind i → ℝ)
    (hE : ∀ i l, ∀ᵐ r ∂(blkRestMeasure kind i), ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt
      (fun t => E ((blkSplit kind i l).symm (t, r))) (Epar i l t r) t)
    (hEb : ∀ i l, ∀ᵐ ρ ∂(blkRestMeasure kind i),
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Epar i l t ρ| ≤ η) :
    volume ({u : Blk kind | |γ * ∏ j, (kind j).factor (u j) + E u| ≤ s} ∩ bigCube kind
        ∩ {u | c ≤ ‖u‖})
      ≤ (2 * totDim kind : ℕ)
          * (ENNReal.ofReal (4 * (4 * shellConst kind c γ + 2 ^ totDim kind)
                * s * Lam s ^ (N + 1))
            + ENNReal.ofReal (2 * (shellConst kind c γ * (2 * η) * Lam (2 * η) ^ N))) := by
  have h2c : (0:ℝ) < 2 * c := by linarith
  have habs : |2 * c * γ| = 2 * c * |γ| := by
    rw [abs_mul, abs_of_pos h2c]
  have hpow : ∀ i : Fin (N + 1 + 1),
      (2:ℝ) ^ (kind i).dm * 2 ^ totDim (fun j => kind (i.succAbove j))
        ≤ 2 ^ totDim kind := by
    intro i
    rw [← pow_add]
    refine pow_le_pow_right₀ (by norm_num) ?_
    have h1 := dim_add_totDim_succAbove kind i
    have h2 : (kind i).dim = (kind i).dm + 1 := rfl
    omega
  refine measure_sublevel_shell_le kind hη hs hc hc1 (shellConst_nonneg kind hc.le γ)
    (by positivity) ?_ ?_ hEmeas Epar hE hEb
  · -- the mass of the rest
    intro i
    refine le_trans (blkRestMeasure_univ_le kind i) (ENNReal.ofReal_le_ofReal (hpow i))
  · -- the tail bound for the rest
    intro i
    have hfun : (fun r => 2 * c * |blkRestFactor kind i γ r|)
        = fun r => |blkRestFactor kind i (2 * c * γ) r| := by
      funext r
      unfold blkRestFactor
      have hre : (2 * c * γ) * ∏ j, (kind (i.succAbove j)).factor (r.2 j)
          = (2 * c) * (γ * ∏ j, (kind (i.succAbove j)).factor (r.2 j)) := by ring
      rw [hre, abs_mul (2 * c), abs_of_pos h2c]
    rw [hfun]
    refine (tailBound_blkRest kind i (mul_ne_zero h2c.ne' hγ)).mono_const ?_
    unfold blkGammaConst shellConst
    rw [habs]
    have hnn : (0:ℝ) ≤ 5 ^ N * (2 * c * |γ|)⁻¹ * Lam ((2 * c * |γ|)⁻¹) ^ N := by
      have := (Lam_pow_pos ((2 * c * |γ|)⁻¹) N).le
      positivity
    calc (2:ℝ) ^ (kind i).dm
          * (2 ^ totDim (fun j => kind (i.succAbove j)) * 5 ^ N * (2 * c * |γ|)⁻¹
            * Lam ((2 * c * |γ|)⁻¹) ^ N)
        = ((2:ℝ) ^ (kind i).dm * 2 ^ totDim (fun j => kind (i.succAbove j)))
            * (5 ^ N * (2 * c * |γ|)⁻¹ * Lam ((2 * c * |γ|)⁻¹) ^ N) := by ring
      _ ≤ (2:ℝ) ^ totDim kind
            * (5 ^ N * (2 * c * |γ|)⁻¹ * Lam ((2 * c * |γ|)⁻¹) ^ N) :=
          mul_le_mul_of_nonneg_right (hpow i) hnn
      _ = _ := by ring

/-! ### The all-lines case

When every block is a line — the case of a real spectrum — the block space is just `ℝⁿ`,
the factor is the product of the coordinates, and the fibering argument simplifies in two
ways.  The fiber derivative `∂ₜ(t·h) = h` is bounded below on the *whole* fiber `[-1,1]`,
with no `‖u‖ ≥ c⋆` restriction, so no chart cover is needed: a single coordinate direction
serves everywhere.  Consequently the estimate holds on the full cube rather than on an
annulus. -/

lemma anticonc_abs : Anticonc unif1 (fun x => |x|) := fun v hv =>
  le_trans (unif1_abs_le hv) (ENNReal.ofReal_le_ofReal (min_le_right _ _))

/-- The product of `|coordinates|` on the cube, for the uniform probability measure. -/
theorem tailBound_absProd (M : ℕ) :
    TailBound (blockMeasure (M + 1)) (fun u : Fin (M + 1) → ℝ => ∏ i, |u i|) (5 ^ M) M :=
  tailBound_prod M (fun _ => unif1) (fun _ => fun x => |x|)
    (fun _ => measurable_id.abs) (fun _ x => abs_nonneg x) (fun _ => anticonc_abs)

/-- The same for Lebesgue measure restricted to the cube. -/
theorem tailBound_absProd_volume (M : ℕ) :
    TailBound ((volume : Measure (Fin (M + 1) → ℝ)).restrict (cube (M + 1)))
      (fun u => ∏ i, |u i|) (2 ^ (M + 1) * 5 ^ M) M := by
  intro v hv
  rw [volume_restrict_cube, Measure.smul_apply, smul_eq_mul]
  calc ENNReal.ofReal ((2:ℝ) ^ (M + 1)) * blockMeasure (M + 1) {u | ∏ i, |u i| ≤ v}
      ≤ ENNReal.ofReal ((2:ℝ) ^ (M + 1)) * ENNReal.ofReal (5 ^ M * v * Lam v ^ M) :=
        mul_le_mul_left' (tailBound_absProd M v hv) _
    _ = ENNReal.ofReal ((2:ℝ) ^ (M + 1) * (5 ^ M * v * Lam v ^ M)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (2 ^ (M + 1) * 5 ^ M * v * Lam v ^ M) := by ring_nf

/-- The constant produced by absorbing the leading coefficient `γ`. -/
noncomputable def gammaConst (M : ℕ) (γ : ℝ) : ℝ :=
  2 ^ (M + 1) * 5 ^ M * |γ|⁻¹ * Lam |γ|⁻¹ ^ M

lemma gammaConst_nonneg (M : ℕ) (γ : ℝ) : 0 ≤ gammaConst M γ := by
  unfold gammaConst
  have := (Lam_pow_pos |γ|⁻¹ M).le
  positivity

/-- **The tail bound for `|γ ∏ uᵢ|`.**  The leading coefficient is absorbed by the
*multiplicative* form of the constant absorption (`Lam_mul_le_of_pos`); the naive additive
form would not survive being raised to the power `M`. -/
theorem tailBound_gammaProd (M : ℕ) {γ : ℝ} (hγ : γ ≠ 0) :
    TailBound ((volume : Measure (Fin (M + 1) → ℝ)).restrict (cube (M + 1)))
      (fun u => |γ * ∏ i, u i|) (gammaConst M γ) M := by
  intro v hv
  have hγ0 : 0 < |γ| := abs_pos.mpr hγ
  have hset : {u : Fin (M + 1) → ℝ | |γ * ∏ i, u i| ≤ v}
      = {u : Fin (M + 1) → ℝ | ∏ i, |u i| ≤ |γ|⁻¹ * v} := by
    ext u
    simp only [Set.mem_setOf_eq, abs_mul, Finset.abs_prod]
    rw [← le_div_iff₀' hγ0, div_eq_inv_mul]
  rw [hset]
  have hv' : (0:ℝ) ≤ |γ|⁻¹ * v := by positivity
  refine le_trans (tailBound_absProd_volume M _ hv') (ENNReal.ofReal_le_ofReal ?_)
  -- `Λ(|γ|⁻¹ v) ≤ Λ(|γ|⁻¹) Λ(v)`, then collect
  rcases eq_or_lt_of_le hv with rfl | hvpos
  · simp [gammaConst]
  have hLam : Lam (|γ|⁻¹ * v) ^ M ≤ Lam |γ|⁻¹ ^ M * Lam v ^ M := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Lam_nonneg _) (Lam_mul_le_of_pos (by positivity) hvpos) M
  have hC : (0:ℝ) ≤ 2 ^ (M + 1) * 5 ^ M := by positivity
  calc (2:ℝ) ^ (M + 1) * 5 ^ M * (|γ|⁻¹ * v) * Lam (|γ|⁻¹ * v) ^ M
      ≤ 2 ^ (M + 1) * 5 ^ M * (|γ|⁻¹ * v) * (Lam |γ|⁻¹ ^ M * Lam v ^ M) := by
        refine mul_le_mul_of_nonneg_left hLam ?_
        positivity
    _ = gammaConst M γ * v * Lam v ^ M := by unfold gammaConst; ring

/-! ### Balls, cubes and scaling

On `Fin n → ℝ` the norm is the sup norm, so the closed unit ball **is** the cube.  This is
what lets §9's shell decomposition land directly in the cube where the §8 estimate lives:
dithering uniformly on a sup-norm ball is dithering uniformly on a cube.  (The Lean
interface only ever requires `‖ξ‖ ≤ δ`, so which ball the dither is uniform on is a
modelling choice; the cube is the one that fits.) -/

lemma closedBall_eq_cube (n : ℕ) : {z : Fin n → ℝ | ‖z‖ ≤ 1} = cube n := by
  ext z
  simp only [Set.mem_setOf_eq, cube, Set.mem_univ_pi, Set.mem_Icc]
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  constructor
  · intro h i
    have := h i
    rw [Real.norm_eq_abs, abs_le] at this
    exact this
  · intro h i
    rw [Real.norm_eq_abs, abs_le]
    exact h i

lemma closedBall_eq_smul_cube {n : ℕ} {r : ℝ} (hr : 0 < r) :
    {z : Fin n → ℝ | ‖z‖ ≤ r} = r • cube n := by
  rw [← closedBall_eq_cube]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_smul_set]
  constructor
  · intro h
    refine ⟨r⁻¹ • z, ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
    show ‖r⁻¹ • z‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_le_iff₀ hr,
      mul_one]
    exact h
  · rintro ⟨w, hw, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc r * ‖w‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hw hr.le
      _ = r := mul_one r

/-- The `j`-th dyadic shell of the ball of radius `R`. -/
def shell (n : ℕ) (R : ℝ) (j : ℕ) : Set (Fin n → ℝ) :=
  {y | (1/2 : ℝ) ^ (j + 1) * R < ‖y‖ ∧ ‖y‖ ≤ (1/2 : ℝ) ^ j * R}

/-- **The dyadic shells cover the punctured ball.**  Every nonzero point of the ball of
radius `R` lies in some shell — the one indexed by the least `j` whose inner radius it
clears. -/
lemma punctured_ball_subset_iUnion_shell {n : ℕ} {R : ℝ} (hR : 0 < R) :
    {y : Fin n → ℝ | 0 < ‖y‖ ∧ ‖y‖ ≤ R} ⊆ ⋃ j : ℕ, shell n R j := by
  rintro y ⟨hy0, hyR⟩
  classical
  have hex : ∃ j : ℕ, (1/2 : ℝ) ^ (j + 1) * R < ‖y‖ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ‖y‖ / R)
      (by norm_num : (1/2 : ℝ) < 1)
    refine ⟨k, ?_⟩
    have hstep : (1/2 : ℝ) ^ (k + 1) ≤ (1/2 : ℝ) ^ k := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) k]
    have : (1/2 : ℝ) ^ k * R < ‖y‖ := by
      rw [← lt_div_iff₀ hR]; exact hk
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) (k+1)]
  refine Set.mem_iUnion.mpr ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; simpa using hyR
  · have hnot : ¬ ((1/2 : ℝ) ^ ((Nat.find hex - 1) + 1) * R < ‖y‖) :=
      Nat.find_min hex (by omega)
    rw [Nat.sub_add_cancel hpos] at hnot
    exact not_lt.mp hnot

/-- Scaling a set in `ℝⁿ` scales its measure by `rⁿ`. -/
lemma volume_smul_set {n : ℕ} {r : ℝ} (hr : 0 < r) (S : Set (Fin n → ℝ)) :
    volume (r • S) = ENNReal.ofReal (r ^ n) * volume S := by
  rw [Measure.addHaar_smul]
  congr 2
  rw [Module.finrank_fin_fun, abs_of_nonneg (by positivity)]

/-- **The per-shell bound.**  Rescaling the `j`-th shell by its outer radius carries it into
the cube, at the cost of the Jacobian `r_jⁿ`. -/
lemma volume_inter_shell_le {n : ℕ} {R : ℝ} (hR : 0 < R) (j : ℕ) (S : Set (Fin n → ℝ)) :
    volume (S ∩ shell n R j)
      ≤ ENNReal.ofReal (((1/2 : ℝ) ^ j * R) ^ n) *
          volume ((fun z => ((1/2 : ℝ) ^ j * R) • z) ⁻¹' S ∩ cube n) := by
  set r : ℝ := (1/2 : ℝ) ^ j * R with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hsub : S ∩ shell n R j ⊆ r • ((fun z => r • z) ⁻¹' S ∩ cube n) := by
    rintro y ⟨hyS, -, hyr⟩
    have hball : y ∈ {z : Fin n → ℝ | ‖z‖ ≤ r} := hyr
    rw [closedBall_eq_smul_cube hr0] at hball
    obtain ⟨z, hz, rfl⟩ := hball
    exact ⟨z, ⟨hyS, hz⟩, rfl⟩
  calc volume (S ∩ shell n R j) ≤ volume (r • ((fun z => r • z) ⁻¹' S ∩ cube n)) :=
        measure_mono hsub
    _ = ENNReal.ofReal (r ^ n) * volume ((fun z => r • z) ⁻¹' S ∩ cube n) :=
        volume_smul_set hr0 _

/-- **The shell sum.**  A set inside a ball is controlled by the sum of its rescaled
traces on the dyadic shells. -/
theorem volume_inter_ball_le {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    (S : Set (Fin n → ℝ)) :
    volume (S ∩ {y : Fin n → ℝ | ‖y‖ ≤ R})
      ≤ ∑' j : ℕ, ENNReal.ofReal (((1/2 : ℝ) ^ j * R) ^ n) *
          volume ((fun z => ((1/2 : ℝ) ^ j * R) • z) ⁻¹' S ∩ cube n) := by
  have hzero : volume ({(0 : Fin n → ℝ)}) = 0 := by
    have hset : ({(0 : Fin n → ℝ)} : Set (Fin n → ℝ))
        = Set.univ.pi (fun _ => ({0} : Set ℝ)) := by
      ext y
      simp [funext_iff, Set.mem_singleton_iff]
    rw [hset, volume_pi, Measure.pi_pi]
    refine Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn⟩ : Fin n)) ?_
    simp
  have hsplit : S ∩ {y : Fin n → ℝ | ‖y‖ ≤ R}
      ⊆ ({(0 : Fin n → ℝ)} : Set (Fin n → ℝ)) ∪ ⋃ j : ℕ, S ∩ shell n R j := by
    rintro y ⟨hyS, hyR⟩
    rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
    · exact Or.inl (by simpa using (norm_eq_zero.mp h0.symm))
    · have hmem := punctured_ball_subset_iUnion_shell (n := n) hR ⟨h0, hyR⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, hyS, hj⟩)
  calc volume (S ∩ {y : Fin n → ℝ | ‖y‖ ≤ R})
      ≤ volume (({(0 : Fin n → ℝ)} : Set (Fin n → ℝ)) ∪ ⋃ j : ℕ, S ∩ shell n R j) :=
        measure_mono hsplit
    _ ≤ volume ({(0 : Fin n → ℝ)} : Set (Fin n → ℝ))
        + volume (⋃ j : ℕ, S ∩ shell n R j) := measure_union_le _ _
    _ = volume (⋃ j : ℕ, S ∩ shell n R j) := by rw [hzero, zero_add]
    _ ≤ ∑' j : ℕ, volume (S ∩ shell n R j) := measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum fun j => volume_inter_shell_le hR j S

/-! ### The margin, rescaled

The event controlled by Lemma 4.8 is `{τ(y) ≤ s}` with `τ(y) = |σ(y)|/‖y‖ⁿ`.  On the shell of
outer radius `r` the substitution `y = r z` turns it into a sublevel set of the *rescaled*
function `Q + E_r`, and the factor `‖z‖ⁿ ≤ 1` is discarded — this is the step that makes the
threshold `s` scale-free. -/

/-- **The margin on a shell.**  If `σ(r z) = rⁿ (Q z + E z)` then the margin event pulls
back into the plain sublevel set of `Q + E` on the cube. -/
lemma tau_preimage_subset {n : ℕ} {σ Q E : (Fin n → ℝ) → ℝ} {r s : ℝ} (hr : 0 < r)
    (hs : 0 ≤ s) (hsplit : ∀ z, σ (r • z) = r ^ n * (Q z + E z)) :
    (fun z => r • z) ⁻¹' {y : Fin n → ℝ | |σ y| ≤ s * ‖y‖ ^ n} ∩ cube n
      ⊆ {z : Fin n → ℝ | |Q z + E z| ≤ s} ∩ cube n := by
  rintro z ⟨hz, hzc⟩
  refine ⟨?_, hzc⟩
  have hzn : ‖z‖ ≤ 1 := by rwa [← closedBall_eq_cube] at hzc
  have hz' : |σ (r • z)| ≤ s * ‖r • z‖ ^ n := hz
  rw [hsplit z, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow, abs_mul,
    abs_of_pos (by positivity : (0:ℝ) < r ^ n)] at hz'
  have hrn : (0:ℝ) < r ^ n := by positivity
  have hstep : |Q z + E z| ≤ s * ‖z‖ ^ n := by
    rw [show s * (r ^ n * ‖z‖ ^ n) = r ^ n * (s * ‖z‖ ^ n) by ring] at hz'
    exact le_of_mul_le_mul_left hz' hrn
  refine le_trans hstep ?_
  calc s * ‖z‖ ^ n ≤ s * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg z) hzn) hs
    _ = s := mul_one s

/-! ### The linear change of variables

§9 studies the degeneracy polynomial in the eigencoordinates `w = P⁻¹z`.  Passing between
the two coordinate systems multiplies Lebesgue measure by `|det P|`. -/

/-- **Linear change of variables.**  For an invertible real matrix `P`,
`vol((z ↦ P⁻¹z)⁻¹' S) = |det P| · vol S`. -/
theorem volume_preimage_mulVec {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsUnit P.det)
    (S : Set (Fin n → ℝ)) :
    volume ((fun z => P⁻¹.mulVec z) ⁻¹' S) = ENNReal.ofReal |P.det| * volume S := by
  have hdet : LinearMap.det (Matrix.toLin' P⁻¹) = (P.det)⁻¹ := by
    rw [LinearMap.det_toLin', Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hne : LinearMap.det (Matrix.toLin' P⁻¹) ≠ 0 := by
    rw [hdet]
    exact inv_ne_zero (isUnit_iff_ne_zero.mp hP)
  have hpre : (fun z => P⁻¹.mulVec z) ⁻¹' S = (Matrix.toLin' P⁻¹) ⁻¹' S := rfl
  rw [hpre, Measure.addHaar_preimage_linearMap volume hne, hdet]
  congr 2
  rw [inv_inv]

/-- **The sublevel estimate on the cube, all-lines case** (appendix §8 specialized to a real
spectrum).  For `Q(u) = γ ∏ uᵢ` and a perturbation whose derivative along the first
coordinate is at most `η`,

    vol {u ∈ [-1,1]ⁿ : |Q u + E u| ≤ s}
      ≤  C · s · Λ(s)^(n-1)  +  C · η · Λ(2η)^(n-2),

the first term from the fibered monotonicity bound and the second from the surrendered slab
`{|h| ≤ 2η}`. -/
theorem measure_sublevel_cube_le (M : ℕ) {γ η s : ℝ} (hγ : γ ≠ 0) (hη : 0 < η) (hs : 0 < s)
    {E : (Fin (M + 2) → ℝ) → ℝ} {Epar : ℝ → (Fin (M + 1) → ℝ) → ℝ}
    (hEmeas : Measurable E)
    (hE : ∀ (u' : Fin (M + 1) → ℝ) (t : ℝ),
      HasDerivAt (fun t => E (Fin.cons t u')) (Epar t u') t)
    (hEb : ∀ u' ∈ cube (M + 1), ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Epar t u'| ≤ η) :
    volume ({u : Fin (M + 2) → ℝ | |γ * (∏ i, u i) + E u| ≤ s} ∩ cube (M + 2))
      ≤ ENNReal.ofReal
          (4 * (4 * gammaConst M γ + 2 ^ (M + 1)) * s * Lam s ^ (M + 1))
        + ENNReal.ofReal (2 * (gammaConst M γ * (2 * η) * Lam (2 * η) ^ M)) := by
  classical
  set h : (Fin (M + 1) → ℝ) → ℝ := fun r => γ * ∏ j, r j with hh
  set G : ℝ → (Fin (M + 1) → ℝ) → ℝ := fun t r => E (Fin.cons t r) with hG
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 2) => ℝ) 0 with he
  have hmp : MeasurePreserving e (volume : Measure (Fin (M + 2) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin (M + 1) → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (M + 2) => ℝ) 0
  have hmeas_h : Measurable h := by
    rw [hh]
    exact measurable_const.mul
      (Finset.measurable_prod _ fun j _ => measurable_pi_apply j)
  -- the two pieces in the product space
  set B₁ : Set (ℝ × (Fin (M + 1) → ℝ)) :=
    {p | |p.1 * h p.2 + G p.1 p.2| ≤ s ∧ 2 * η ≤ |h p.2|} with hB₁
  set B₂ : Set (ℝ × (Fin (M + 1) → ℝ)) := Set.univ ×ˢ {r | |h r| ≤ 2 * η} with hB₂
  have hGmeas : Measurable fun p : ℝ × (Fin (M + 1) → ℝ) => G p.1 p.2 := by
    rw [hG]
    refine hEmeas.comp (measurable_pi_iff.mpr fun i => ?_)
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using measurable_fst
    · simp only [Fin.cons_succ]
      exact (measurable_pi_apply j).comp measurable_snd
  have hB₁meas : MeasurableSet B₁ := by
    rw [hB₁]
    exact ((((measurable_fst.mul (hmeas_h.comp measurable_snd)).add hGmeas).abs)
      measurableSet_Iic).inter
      (measurableSet_le measurable_const ((hmeas_h.comp measurable_snd).abs))
  have hB₂meas : MeasurableSet B₂ :=
    MeasurableSet.univ.prod (measurableSet_le (hmeas_h.abs) measurable_const)
  set cub : Set (ℝ × (Fin (M + 1) → ℝ)) := Set.Icc (-1 : ℝ) 1 ×ˢ cube (M + 1) with hcub
  have hcubmeas : MeasurableSet cub := measurableSet_Icc.prod (measurableSet_cube _)
  -- the target is carried into `(B₁ ∪ B₂) ∩ cub`
  have hsub : ({u : Fin (M + 2) → ℝ | |γ * (∏ i, u i) + E u| ≤ s} ∩ cube (M + 2))
      ⊆ e ⁻¹' ((B₁ ∪ B₂) ∩ cub) := by
    rintro u ⟨hu, hcube⟩
    have heu : e u = (u 0, fun j => u (Fin.succAbove 0 j)) := rfl
    have hprod : γ * (∏ i, u i) = (e u).1 * h (e u).2 := by
      rw [heu, hh]
      simp only
      rw [Fin.prod_univ_succAbove (fun i => u i) (0 : Fin (M + 2))]
      ring
    have hEcons : E u = G (e u).1 (e u).2 := by
      rw [heu, hG]
      simp only
      congr 1
      exact (Fin.cons_self_tail u).symm
    have hmemcub : e u ∈ cub := by
      rw [hcub, heu]
      constructor
      · exact (hcube 0 (Set.mem_univ _) : u 0 ∈ Set.Icc (-1:ℝ) 1)
      · intro j _
        exact hcube _ (Set.mem_univ _)
    refine ⟨?_, hmemcub⟩
    rcases le_or_gt (2 * η) |h (e u).2| with hcase | hcase
    · exact Or.inl ⟨by rw [← hprod, ← hEcons]; exact hu, hcase⟩
    · exact Or.inr ⟨Set.mem_univ _, hcase.le⟩
  -- transport and split
  calc volume ({u : Fin (M + 2) → ℝ | |γ * (∏ i, u i) + E u| ≤ s} ∩ cube (M + 2))
      ≤ volume (e ⁻¹' ((B₁ ∪ B₂) ∩ cub)) := measure_mono hsub
    _ = ((volume : Measure ℝ).prod (volume : Measure (Fin (M + 1) → ℝ)))
          ((B₁ ∪ B₂) ∩ cub) :=
        hmp.measure_preimage (((hB₁meas.union hB₂meas).inter hcubmeas).nullMeasurableSet)
    _ = (((volume : Measure ℝ).restrict (Set.Icc (-1:ℝ) 1)).prod
          ((volume : Measure (Fin (M + 1) → ℝ)).restrict (cube (M + 1)))) (B₁ ∪ B₂) := by
        rw [Measure.prod_restrict, Measure.restrict_apply (hB₁meas.union hB₂meas)]
    _ ≤ (((volume : Measure ℝ).restrict (Set.Icc (-1:ℝ) 1)).prod
          ((volume : Measure (Fin (M + 1) → ℝ)).restrict (cube (M + 1)))) B₁
        + (((volume : Measure ℝ).restrict (Set.Icc (-1:ℝ) 1)).prod
          ((volume : Measure (Fin (M + 1) → ℝ)).restrict (cube (M + 1)))) B₂ :=
        measure_union_le _ _
    _ ≤ _ := by
        have htail := tailBound_gammaProd M hγ
        have hmass : ((volume : Measure (Fin (M + 1) → ℝ)).restrict (cube (M + 1)))
            Set.univ ≤ ENNReal.ofReal ((2:ℝ) ^ (M + 1)) := by
          rw [volume_restrict_cube, Measure.smul_apply, smul_eq_mul,
            measure_univ, mul_one]
        have hae : ∀ᵐ r ∂((volume : Measure (Fin (M + 1) → ℝ)).restrict (cube (M + 1))),
            ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Epar t r| ≤ η := by
          rw [ae_restrict_iff' (measurableSet_cube _)]
          exact Filter.Eventually.of_forall fun r hr => hEb r hr
        refine add_le_add ?_ ?_
        · exact measure_chart_le' hη hs (by positivity) (gammaConst_nonneg M γ)
            hmeas_h (fun r t => hE r t) hae hB₁meas hmass htail
        · exact measure_discarded_le hη htail

/-! ### Flattening the block space

`Blk kind = ∀ i, Fin (kind i).dim → ℝ` is the *curried* form of `ℝ^{totDim kind}`.  Currying is
measure-preserving: mathlib has `MeasurableEquiv.piCurry` but not the measure statement, which
falls out of `Measure.pi_eq` because the *uncurried* preimage of a rectangle is a
rectangle-of-rectangles.  Reindexing then lands in `Fin n → ℝ`
(`volume_measurePreserving_piCongrLeft`).

This is used only to turn the change of coordinates `T : ℝⁿ ≃ₗ Blk kind` of a
`RealBlockFactorization` into a **matrix**, so that §9's Jacobian (`volume_preimage_mulVec`)
applies.  The shell estimate itself stays on `Blk kind`. -/

theorem measurePreserving_piCurry_symm {ι : Type*} [Fintype ι] {κ : ι → Type}
    [∀ i, Fintype (κ i)] :
    MeasurePreserving
      (MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => ℝ)).symm
      (volume : Measure (∀ i, κ i → ℝ)) (volume : Measure ((i : ι) × κ i → ℝ)) := by
  classical
  refine ⟨(MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => ℝ)).symm.measurable, ?_⟩
  rw [show (volume : Measure ((i : ι) × κ i → ℝ))
      = Measure.pi (fun _ => (volume : Measure ℝ)) from volume_pi]
  refine (Measure.pi_eq fun t ht => ?_).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => ℝ)).symm ⁻¹'
      (Set.univ.pi t) = Set.univ.pi (fun i => Set.univ.pi (fun l => t ⟨i, l⟩)) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    exact ⟨fun h i l => h ⟨i, l⟩, fun h p => h p.1 p.2⟩
  rw [hpre, show (volume : Measure (∀ i, κ i → ℝ))
      = Measure.pi (fun i => (volume : Measure (κ i → ℝ))) from volume_pi, Measure.pi_pi]
  have hin : ∀ i : ι, (volume : Measure (κ i → ℝ)) (Set.univ.pi (fun l => t ⟨i, l⟩))
      = ∏ l : κ i, (volume : Measure ℝ) (t ⟨i, l⟩) := by
    intro i
    rw [show (volume : Measure (κ i → ℝ))
        = Measure.pi (fun _ => (volume : Measure ℝ)) from volume_pi, Measure.pi_pi]
  rw [Finset.prod_congr rfl fun i _ => hin i]
  rw [← Finset.univ_sigma_univ]
  exact (Finset.prod_sigma Finset.univ (fun _ => Finset.univ)
    (fun p => (volume : Measure ℝ) (t p))).symm

/-- The flattened index of the block space. -/
abbrev BlkIdx (kind : Fin N → BlockKind) := (i : Fin N) × Fin (kind i).dim

lemma card_blkIdx (kind : Fin N → BlockKind) :
    Fintype.card (BlkIdx kind) = totDim kind := by
  rw [Fintype.card_sigma, totDim]
  simp

/-- An enumeration of the flattened index by `Fin n`, given `totDim kind = n`. -/
noncomputable def blkEnum (kind : Fin N → BlockKind) {n : ℕ} (h : totDim kind = n) :
    Fin n ≃ BlkIdx kind :=
  (Fintype.equivFinOfCardEq (by rw [card_blkIdx, h])).symm

/-- The block space flattened, as a measurable equivalence. -/
noncomputable def blkFlatM (kind : Fin N → BlockKind) {n : ℕ} (h : totDim kind = n) :
    Blk kind ≃ᵐ (Fin n → ℝ) :=
  (MeasurableEquiv.piCurry (fun (i : Fin N) (_ : Fin (kind i).dim) => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : BlkIdx kind => ℝ) (blkEnum kind h)).symm

theorem measurePreserving_blkFlatM (kind : Fin N → BlockKind) {n : ℕ} (h : totDim kind = n) :
    MeasurePreserving (blkFlatM kind h) (volume : Measure (Blk kind))
      (volume : Measure (Fin n → ℝ)) :=
  (((volume_measurePreserving_piCongrLeft (fun _ : BlkIdx kind => ℝ)
      (blkEnum kind h)).symm _).comp measurePreserving_piCurry_symm)

lemma blkFlatM_apply (kind : Fin N → BlockKind) {n : ℕ} (h : totDim kind = n)
    (u : Blk kind) (j : Fin n) :
    blkFlatM kind h u j = u (blkEnum kind h j).1 (blkEnum kind h j).2 := rfl

/-- The same flattening, as a linear equivalence. -/
noncomputable def blkFlatL (kind : Fin N → BlockKind) {n : ℕ} (h : totDim kind = n) :
    Blk kind ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun u := fun j => u (blkEnum kind h j).1 (blkEnum kind h j).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := fun i l => v ((blkEnum kind h).symm ⟨i, l⟩)
  left_inv u := by
    funext i l
    show u (blkEnum kind h ((blkEnum kind h).symm ⟨i, l⟩)).1
        (blkEnum kind h ((blkEnum kind h).symm ⟨i, l⟩)).2 = u i l
    rw [Equiv.apply_symm_apply]
  right_inv v := by
    funext j
    show v ((blkEnum kind h).symm ⟨(blkEnum kind h j).1, (blkEnum kind h j).2⟩) = v j
    rw [show (⟨(blkEnum kind h j).1, (blkEnum kind h j).2⟩ : BlkIdx kind) = blkEnum kind h j
        from rfl, Equiv.symm_apply_apply]

lemma blkFlatL_coe (kind : Fin N → BlockKind) {n : ℕ} (h : totDim kind = n) :
    ⇑(blkFlatL kind h) = ⇑(blkFlatM kind h) := by
  funext u j
  rw [blkFlatM_apply]
  rfl

lemma blkFlatL_apply_symm (kind : Fin N → BlockKind) {n : ℕ} (h : totDim kind = n)
    (u : Blk kind) (i : Fin N) (l : Fin (kind i).dim) :
    blkFlatL kind h u ((blkEnum kind h).symm ⟨i, l⟩) = u i l := by
  show u (blkEnum kind h ((blkEnum kind h).symm ⟨i, l⟩)).1
      (blkEnum kind h ((blkEnum kind h).symm ⟨i, l⟩)).2 = u i l
  rw [Equiv.apply_symm_apply]

/-- The flattening carries the cube to the cube. -/
lemma blkFlatL_preimage_cube (kind : Fin N → BlockKind) {n : ℕ} (h : totDim kind = n) :
    blkFlatL kind h ⁻¹' cube n = bigCube kind := by
  ext u
  simp only [Set.mem_preimage, cube, bigCube, Set.mem_univ_pi]
  refine ⟨fun hv i l => ?_, fun hu j => hu (blkEnum kind h j).1 (blkEnum kind h j).2⟩
  have := hv ((blkEnum kind h).symm ⟨i, l⟩)
  rwa [blkFlatL_apply_symm] at this

/-- And it is an isometry for the sup norms. -/
lemma norm_blkFlatL (kind : Fin N → BlockKind) {n : ℕ} (h : totDim kind = n) (u : Blk kind) :
    ‖blkFlatL kind h u‖ = ‖u‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    calc |u (blkEnum kind h j).1 (blkEnum kind h j).2|
        ≤ ‖u (blkEnum kind h j).1‖ := by
          simpa [Real.norm_eq_abs] using
            norm_le_pi_norm (u (blkEnum kind h j).1) (blkEnum kind h j).2
      _ ≤ ‖u‖ := norm_le_pi_norm u _
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun l => ?_
    rw [Real.norm_eq_abs, ← blkFlatL_apply_symm kind h u i l, ← Real.norm_eq_abs]
    exact norm_le_pi_norm _ _

end MPE
