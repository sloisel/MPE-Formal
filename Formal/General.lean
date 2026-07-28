import Mathlib
import Formal.Anticonc
import Formal.Psi
import Formal.Primary

/-!
# Theorem 4.9 for an arbitrary real spectrum

`Formal/Psi.lean` proves Theorem 4.9 when `A` has a real eigenbasis.  This file removes that
restriction, using the two general inputs proved elsewhere:

* `MPE.nonempty_realBlockFactorization_of_squarefree` — `det K_A(z) = γ ∏ᵢ factorᵢ(T z i)` for
  *any* `A` with squarefree characteristic polynomial (`Formal/Primary.lean`);
* `MPE.measure_sublevel_shell_le` — the sublevel estimate for blocks of both kinds, on the
  part of the cube where some coordinate is bounded below (`Formal/Annulus.lean`).

The glue is the *flattening* `blkFlatL` of `Formal/Annulus.lean`, which turns the change of
coordinates `T : ℝⁿ ≃ₗ Blk kind` into a linear automorphism of `ℝⁿ` — so §9's Jacobian
applies — while the shell estimate itself stays on `Blk kind`.
-/

namespace MPE

set_option maxHeartbeats 1000000

open MeasureTheory Set Finset MvPolynomial Poly
open scoped ENNReal Pointwise

/-! ### The Jacobian of a linear equivalence

`volume_preimage_mulVec` is stated for a matrix inverse; the version for an abstract linear
equivalence is what the flattening produces, and mathlib supplies it directly. -/

theorem volume_preimage_linearEquiv {n : ℕ} (L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (S : Set (Fin n → ℝ)) :
    volume ((L : (Fin n → ℝ) → (Fin n → ℝ)) ⁻¹' S)
      = ENNReal.ofReal |LinearMap.det (L.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))|
          * volume S := by
  have himg : (L : (Fin n → ℝ) → (Fin n → ℝ)) ⁻¹' S
      = (L.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) '' S := by
    ext v
    simp only [Set.mem_preimage, Set.mem_image]
    refine ⟨fun h => ⟨L v, h, by simp⟩, ?_⟩
    rintro ⟨w, hw, rfl⟩
    simpa using hw
  rw [himg]
  exact Measure.addHaar_image_linearMap (μ := (volume : Measure (Fin n → ℝ))) _ _

/-- Every linear map on `ℝⁿ` is Lipschitz, with a positive constant. -/
lemma exists_lipschitz {n : ℕ} (f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, ‖f z‖ ≤ C * ‖z‖ := by
  refine ⟨‖LinearMap.toContinuousLinearMap f‖ + 1, by positivity, fun z => ?_⟩
  have h1 := (LinearMap.toContinuousLinearMap f).le_opNorm z
  have h2 : ‖f z‖ = ‖LinearMap.toContinuousLinearMap f z‖ := rfl
  nlinarith [norm_nonneg z, norm_nonneg (LinearMap.toContinuousLinearMap f)]

/-! ### The shell decomposition, retaining the inner radius

`volume_inter_shell_le` discards the shell's *inner* radius.  The general block estimate needs
it: after rescaling by the outer radius, `‖z‖ ≥ ½`, which is what supplies the constant `c` of
the chart cover. -/

lemma volume_inter_shell_le' {n : ℕ} {R : ℝ} (hR : 0 < R) (j : ℕ) (S : Set (Fin n → ℝ)) :
    volume (S ∩ shell n R j)
      ≤ ENNReal.ofReal (((1/2 : ℝ) ^ j * R) ^ n) *
          volume ((fun z => ((1/2 : ℝ) ^ j * R) • z) ⁻¹' S ∩ cube n
            ∩ {z : Fin n → ℝ | (1/2 : ℝ) ≤ ‖z‖}) := by
  set r : ℝ := (1/2 : ℝ) ^ j * R with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hsub : S ∩ shell n R j
      ⊆ r • ((fun z => r • z) ⁻¹' S ∩ cube n ∩ {z : Fin n → ℝ | (1/2 : ℝ) ≤ ‖z‖}) := by
    rintro y ⟨hyS, hin, hyr⟩
    have hball : y ∈ {z : Fin n → ℝ | ‖z‖ ≤ r} := hyr
    rw [closedBall_eq_smul_cube hr0] at hball
    obtain ⟨z, hz, rfl⟩ := hball
    refine ⟨z, ⟨⟨hyS, hz⟩, ?_⟩, rfl⟩
    have h1 : (1/2 : ℝ) ^ (j + 1) * R < ‖r • z‖ := hin
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0] at h1
    rw [show (1/2 : ℝ) ^ (j + 1) * R = r * (1/2) by rw [hrdef, pow_succ]; ring] at h1
    show (1/2 : ℝ) ≤ ‖z‖
    nlinarith
  calc volume (S ∩ shell n R j) ≤ _ := measure_mono hsub
    _ = _ := volume_smul_set hr0 _

theorem volume_inter_ball_le' {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    (S : Set (Fin n → ℝ)) :
    volume (S ∩ {y : Fin n → ℝ | ‖y‖ ≤ R})
      ≤ ∑' j : ℕ, ENNReal.ofReal (((1/2 : ℝ) ^ j * R) ^ n) *
          volume ((fun z => ((1/2 : ℝ) ^ j * R) • z) ⁻¹' S ∩ cube n
            ∩ {z : Fin n → ℝ | (1/2 : ℝ) ≤ ‖z‖}) := by
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
    _ ≤ _ := ENNReal.tsum_le_tsum fun j => volume_inter_shell_le' hR j S

/-! ### Block factors scale -/

lemma BlockKind.factor_smul (b : BlockKind) (a : ℝ) (u : Fin b.dim → ℝ) :
    b.factor (a • u) = a ^ b.dim * b.factor u := by
  cases b with
  | line => show a * u 0 = a ^ (0 + 1) * u 0; ring
  | plane =>
      show (a * u 0) ^ 2 + (a * u 1) ^ 2 = a ^ (1 + 1) * ((u 0) ^ 2 + (u 1) ^ 2)
      ring

lemma prod_factor_smul {N : ℕ} (kind : Fin N → BlockKind) (a : ℝ) (u : Blk kind) :
    ∏ i, (kind i).factor (a • u i) = a ^ totDim kind * ∏ i, (kind i).factor (u i) := by
  rw [totDim, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (kind i).factor_smul a (u i)

/-! ### The data §9 consumes -/

/-- A linear change of coordinates on `ℝⁿ` in which `det K_A` becomes a nonzero constant times
a product of block factors, normalized so that the unit cube maps into itself and the shell
`‖z‖ ≥ ½` maps into `‖·‖ ≥ c`. -/
structure ShellData {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) where
  /-- the number of blocks, minus one -/
  Nb : ℕ
  kind : Fin (Nb + 1) → BlockKind
  htot : totDim kind = n
  /-- `z ↦ v`: the flattened block coordinates -/
  L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)
  γ : ℝ
  hγ : γ ≠ 0
  key : ∀ z, (krylov A z).det
    = γ * ∏ i, (kind i).factor ((blkFlatL kind htot).symm (L z) i)
  /-- the shell constant -/
  c : ℝ
  hc : 0 < c
  hc1 : 2 * c ≤ 1
  /-- `L` is a contraction, so the `v`-cube contains the image of the `z`-cube -/
  hcontr : ∀ z, ‖L z‖ ≤ ‖z‖
  /-- and bounded below, so the shell in `z` lands in the shell in `v` -/
  hlow : ∀ z, 2 * c * ‖z‖ ≤ ‖L z‖

/-- Scaling by a nonzero real, as a linear equivalence. -/
noncomputable def scaleEquiv {n : ℕ} {a : ℝ} (ha : a ≠ 0) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun v := a • v
  map_add' x y := by simp [smul_add]
  map_smul' c x := smul_comm a c x
  invFun v := a⁻¹ • v
  left_inv v := by simp [smul_smul, inv_mul_cancel₀ ha]
  right_inv v := by simp [smul_smul, mul_inv_cancel₀ ha]

@[simp] lemma scaleEquiv_apply {n : ℕ} {a : ℝ} (ha : a ≠ 0) (v : Fin n → ℝ) :
    scaleEquiv (n := n) ha v = a • v := rfl

/-- **Every squarefree `charpoly` gives `ShellData`.**  The factorization of
`Formal/Primary.lean` is flattened to a linear automorphism of `ℝⁿ` and then rescaled: `L` is
divided by a Lipschitz constant, and `γ` absorbs the resulting `κⁿ` (`prod_factor_smul`). -/
theorem nonempty_shellData {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hsq : Squarefree A.charpoly) : Nonempty (ShellData A) := by
  classical
  obtain ⟨F⟩ := nonempty_realBlockFactorization_of_squarefree A hsq
  obtain ⟨FN, kind, T, γ₀, hγ₀, hkey⟩ := F
  -- `finrank` forces `totDim = n`, and in particular there is at least one block
  have hfr : Module.finrank ℝ (Blk kind) = totDim kind := by
    simp [Blk, Module.finrank_pi_fintype, totDim]
  have htot : totDim kind = n := by
    have h1 := T.finrank_eq
    rw [hfr, Module.finrank_fin_fun] at h1
    exact h1.symm
  have hNpos : 0 < FN := by
    by_contra hcon
    have h0 : FN = 0 := by omega
    have huniv : (Finset.univ : Finset (Fin FN)) = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_univ, Fintype.card_fin, h0]
    rw [totDim, huniv, Finset.sum_empty] at htot
    omega
  obtain ⟨Nb, rfl⟩ : ∃ Nb, FN = Nb + 1 := ⟨FN - 1, by omega⟩
  -- the flattened automorphism
  set L₀ : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := T.trans (blkFlatL kind htot) with hL₀
  obtain ⟨K, hK0, hK⟩ := exists_lipschitz (L₀ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  obtain ⟨K', hK'0, hK'⟩ := exists_lipschitz (L₀.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  set κ : ℝ := max K 1 with hκdef
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hκK : K ≤ κ := le_max_left _ _
  set L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    L₀.trans (scaleEquiv (a := κ⁻¹) (by positivity)) with hLdef
  have hLapp : ∀ z, L z = (κ⁻¹ : ℝ) • L₀ z := fun _ => rfl
  have hLnorm : ∀ z, ‖L z‖ = κ⁻¹ * ‖L₀ z‖ := by
    intro z
    rw [hLapp, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < κ⁻¹)]
  have hprod0 : (0:ℝ) < κ * K' := by positivity
  refine ⟨{
    Nb := Nb
    kind := kind
    htot := htot
    L := L
    γ := γ₀ * κ ^ n
    hγ := mul_ne_zero hγ₀ (by positivity)
    c := 1 / (2 * (κ * K' + 1))
    hc := by positivity
    hc1 := ?_
    key := ?_
    hcontr := ?_
    hlow := ?_ }⟩
  · intro z
    have hTz : (blkFlatL kind htot).symm (L₀ z) = T z := by
      show (blkFlatL kind htot).symm (blkFlatL kind htot (T z)) = T z
      rw [LinearEquiv.symm_apply_apply]
    have hu : (blkFlatL kind htot).symm (L z) = (κ⁻¹ : ℝ) • (T z) := by
      rw [hLapp, map_smul, hTz]
    have h1 : ∏ i, (kind i).factor ((blkFlatL kind htot).symm (L z) i)
        = (κ⁻¹ : ℝ) ^ n * ∏ i, (kind i).factor (T z i) := by
      rw [hu]
      simp only [Pi.smul_apply]
      rw [prod_factor_smul kind (κ⁻¹) (T z), htot]
    have hκn : (κ : ℝ) ^ n * (κ⁻¹ : ℝ) ^ n = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hκ0), one_pow]
    rw [h1, hkey z]
    calc γ₀ * ∏ i, (kind i).factor (T z i)
        = (γ₀ * ((κ : ℝ) ^ n * (κ⁻¹ : ℝ) ^ n)) * ∏ i, (kind i).factor (T z i) := by
          rw [hκn, mul_one]
      _ = γ₀ * κ ^ n * ((κ⁻¹ : ℝ) ^ n * ∏ i, (kind i).factor (T z i)) := by ring
  · rw [show 2 * (1 / (2 * (κ * K' + 1))) = 1 / (κ * K' + 1) by field_simp]
    rw [div_le_one (by positivity)]
    linarith
  · intro z
    rw [hLnorm z]
    have h1 : ‖L₀ z‖ ≤ κ * ‖z‖ :=
      le_trans (hK z) (mul_le_mul_of_nonneg_right hκK (norm_nonneg z))
    calc κ⁻¹ * ‖L₀ z‖ ≤ κ⁻¹ * (κ * ‖z‖) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖z‖ := by field_simp
  · intro z
    rw [hLnorm z]
    have h1 : ‖z‖ ≤ K' * ‖L₀ z‖ := by simpa using hK' (L₀ z)
    have hL₀n : (0:ℝ) ≤ ‖L₀ z‖ := norm_nonneg _
    have hstep : (κ⁻¹ * ‖L₀ z‖) * (κ * K') = K' * ‖L₀ z‖ := by
      field_simp
      try ring
    have key : ‖z‖ ≤ (κ⁻¹ * ‖L₀ z‖) * (κ * K' + 1) := by
      have hnn : (0:ℝ) ≤ κ⁻¹ * ‖L₀ z‖ := by positivity
      nlinarith [h1, hstep, hnn]
    rw [show 2 * (1 / (2 * (κ * K' + 1))) * ‖z‖ = ‖z‖ / (κ * K' + 1) by field_simp,
      div_le_iff₀ (by positivity)]
    exact key

/-! ### The chart split is a coordinate update

`measure_sublevel_shell_le` asks for the derivative of the perturbation along
`t ↦ (blkSplit kind i l).symm (t, ρ)`.  In the *flattened* coordinates that curve is
`t ↦ Function.update v κ t` for the single index `κ` corresponding to `(i, l)`, which is
exactly the shape `LowDeg.exists_deriv_update` produces. -/

lemma blkSplit_symm_update {N : ℕ} (kind : Fin (N + 1) → BlockKind) (i : Fin (N + 1))
    (l : Fin (kind i).dim) (t : ℝ) (ρ : BlkRest kind i) :
    (blkSplit kind i l).symm (t, ρ)
      = Function.update ((blkSplit kind i l).symm (0, ρ)) i
          (Function.update (((blkSplit kind i l).symm (0, ρ)) i) l t) := by
  classical
  set u₀ := (blkSplit kind i l).symm (0, ρ) with hu₀
  have h0 : blkSplit kind i l u₀ = (0, ρ) := by rw [hu₀, MeasurableEquiv.apply_symm_apply]
  have h0' := h0
  rw [blkSplit_apply] at h0'
  have hb : (fun j => u₀ i (l.succAbove j)) = ρ.1 := congrArg (fun p => p.2.1) h0'
  have hw : (fun j => u₀ (i.succAbove j)) = ρ.2 := congrArg (fun p => p.2.2) h0'
  have hbs : blkSplit kind i l
      (Function.update u₀ i (Function.update (u₀ i) l t)) = (t, ρ) := by
    rw [blkSplit_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show Function.update u₀ i (Function.update (u₀ i) l t) i l = t
      rw [Function.update_self, Function.update_self]
    · show (fun j => Function.update u₀ i (Function.update (u₀ i) l t) i (l.succAbove j)) = ρ.1
      rw [← hb]
      funext j
      rw [Function.update_self, Function.update_of_ne (Fin.succAbove_ne l j)]
    · show (fun j => Function.update u₀ i (Function.update (u₀ i) l t) (i.succAbove j)) = ρ.2
      rw [← hw]
      funext j
      rw [Function.update_of_ne (Fin.succAbove_ne i j)]
  rw [← hbs, MeasurableEquiv.symm_apply_apply]

lemma blkFlatL_blkSplit_symm {N n : ℕ} (kind : Fin (N + 1) → BlockKind)
    (htot : totDim kind = n) (i : Fin (N + 1)) (l : Fin (kind i).dim) (t : ℝ)
    (ρ : BlkRest kind i) :
    blkFlatL kind htot ((blkSplit kind i l).symm (t, ρ))
      = Function.update (blkFlatL kind htot ((blkSplit kind i l).symm (0, ρ)))
          ((blkEnum kind htot).symm ⟨i, l⟩) t := by
  classical
  set u₀ := (blkSplit kind i l).symm (0, ρ) with hu₀
  rw [blkSplit_symm_update kind i l t ρ, ← hu₀]
  funext j
  show Function.update u₀ i (Function.update (u₀ i) l t)
      (blkEnum kind htot j).1 (blkEnum kind htot j).2
    = Function.update (fun j' => u₀ (blkEnum kind htot j').1 (blkEnum kind htot j').2)
        ((blkEnum kind htot).symm ⟨i, l⟩) t j
  by_cases hj : j = (blkEnum kind htot).symm ⟨i, l⟩
  · subst hj
    rw [Function.update_self,
      show blkEnum kind htot ((blkEnum kind htot).symm (⟨i, l⟩ : BlkIdx kind))
        = (⟨i, l⟩ : BlkIdx kind) from Equiv.apply_symm_apply _ _]
    show Function.update u₀ i (Function.update (u₀ i) l t) i l = t
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hj]
    have hpne : blkEnum kind htot j ≠ (⟨i, l⟩ : BlkIdx kind) := fun hc => hj (by
      rw [← hc, Equiv.symm_apply_apply])
    rcases hp : blkEnum kind htot j with ⟨i', l'⟩
    rw [hp] at hpne
    by_cases hii : i' = i
    · subst hii
      have hll : l' ≠ l := fun hc => hpne (by rw [hc])
      show Function.update u₀ i' (Function.update (u₀ i') l t) i' l' = u₀ i' l'
      rw [Function.update_self, Function.update_of_ne hll]
    · show Function.update u₀ i (Function.update (u₀ i) l t) i' l' = u₀ i' l'
      rw [Function.update_of_ne hii]

/-! ### The rescaled shell estimate for general blocks -/

section Nine

variable {M : ℕ} {A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
  {q : Fin (M + 2) → MvPolynomial (Fin (M + 2)) ℝ}

/-- The matrix of `L.symm`, so that `z = Pm *ᵥ v`.  This is what lets the polynomial
substitution `remHat` of §9 be used verbatim. -/
noncomputable def ShellData.Pm (D : ShellData A) : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ :=
  Matrix.toLin'.symm (D.L.symm : (Fin (M + 2) → ℝ) →ₗ[ℝ] (Fin (M + 2) → ℝ))

lemma ShellData.Pm_mulVec (D : ShellData A) (v : Fin (M + 2) → ℝ) :
    D.Pm.mulVec v = D.L.symm v := by
  have h : Matrix.toLin' D.Pm = (D.L.symm : (Fin (M + 2) → ℝ) →ₗ[ℝ] (Fin (M + 2) → ℝ)) := by
    rw [ShellData.Pm, LinearEquiv.apply_symm_apply]
  calc D.Pm.mulVec v = Matrix.toLin' D.Pm v := (Matrix.toLin'_apply _ _).symm
    _ = _ := by rw [h]; rfl

/-- There are at most `n` blocks. -/
lemma ShellData.Nb_le (D : ShellData A) : D.Nb ≤ M + 1 := by
  have h1 : D.Nb + 1 ≤ totDim D.kind := by
    rw [totDim]
    calc D.Nb + 1 = ∑ _i : Fin (D.Nb + 1), 1 := by simp
      _ ≤ ∑ i : Fin (D.Nb + 1), (D.kind i).dim :=
          Finset.sum_le_sum fun i _ => (D.kind i).dim_pos
  rw [D.htot] at h1
  omega

/-- **The rescaled shell estimate, general blocks.**  The analogue of `shell_cube_bound`, with
the eigenbasis replaced by `ShellData` and the all-lines cube estimate by
`measure_sublevel_shell_le`.  The two constants do not depend on `r` or `s`. -/
theorem shell_cube_bound_gen (D : ShellData A)
    {S Rm : (Fin (M + 2) → ℝ) → ℝ} {cR ρ : ℝ} (hcR : 0 ≤ cR) (hlead : leadConst A ≠ 0)
    (hS : ∀ y, S y = leadConst A * (krylov A y).det + Rm y)
    (hRmeas : Measurable Rm)
    (hRderiv : ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ κ : Fin (M + 2),
      ∃ g : ℝ → (Fin (M + 2) → ℝ) → ℝ,
        (∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 →
            HasDerivAt (fun t => Rm (D.Pm.mulVec (r • Function.update v κ t)) / r ^ (M + 2))
              (g t v) t)
          ∧ ∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 → |g t v| ≤ cR * r) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ r s : ℝ, 0 < r → r ≤ ρ → 0 < s →
      volume ({z : Fin (M + 2) → ℝ | |S (r • z)| ≤ s * r ^ (M + 2)} ∩ cube (M + 2)
          ∩ {z : Fin (M + 2) → ℝ | (1/2 : ℝ) ≤ ‖z‖})
        ≤ ENNReal.ofReal (C₁ * s * Lam s ^ (M + 1))
          + ENNReal.ofReal (C₂ * (2 * ((cR + 1) * r))
              * Lam (2 * ((cR + 1) * r)) ^ M) := by
  classical
  have hΓ : leadConst A * D.γ ≠ 0 := mul_ne_zero hlead D.hγ
  obtain ⟨C, Mc, hC, hMc, hMi, hCi⟩ := exists_shell_const D.kind hΓ D.hc
  set J : ℝ := |LinearMap.det (D.L.symm : (Fin (M + 2) → ℝ) →ₗ[ℝ] (Fin (M + 2) → ℝ))|
    with hJdef
  have hJ0 : (0:ℝ) ≤ J := abs_nonneg _
  set tot : ℝ := ((2 * totDim D.kind : ℕ) : ℝ) with htotdef
  have htot0 : (0:ℝ) ≤ tot := by rw [htotdef]; positivity
  refine ⟨J * (tot * (4 * (4 * C + Mc))), J * (tot * (2 * C)), by positivity, by positivity, ?_⟩
  intro r s hr hr1 hs
  set η := (cR + 1) * r with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  set Γ : ℝ := leadConst A * D.γ with hΓdef
  -- the perturbation, read in block coordinates
  set rem : (Fin (M + 2) → ℝ) → ℝ :=
    fun w => Rm (D.Pm.mulVec (r • w)) / r ^ (M + 2) with hremdef
  have hremmeas : Measurable rem := by
    rw [hremdef]
    refine Measurable.div_const ?_ _
    exact hRmeas.comp ((Matrix.mulVecLin D.Pm).continuous_of_finiteDimensional.measurable.comp
      (measurable_const_smul r))
  set E : Blk D.kind → ℝ := fun u => rem (blkFlatL D.kind D.htot u) with hEdef
  have hcoe : ∀ u : Blk D.kind,
      (blkFlatM D.kind D.htot) u = blkFlatL D.kind D.htot u := fun u => by rw [blkFlatL_coe]
  have hEmeas : Measurable E := by
    have h1 : E = fun u => rem (blkFlatM D.kind D.htot u) := by
      rw [hEdef]; funext u; rw [hcoe]
    rw [h1]
    exact hremmeas.comp (blkFlatM D.kind D.htot).measurable
  -- the coordinate derivatives of the perturbation
  choose g hg1 hg2 using fun κ : Fin (M + 2) => hRderiv r hr hr1 κ
  set Epar : (i : Fin (D.Nb + 1)) → Fin (D.kind i).dim → ℝ → BlkRest D.kind i → ℝ :=
    fun i l t ρ => g ((blkEnum D.kind D.htot).symm ⟨i, l⟩) t
      (blkFlatL D.kind D.htot ((blkSplit D.kind i l).symm (0, ρ))) with hEpardef
  -- every chart base point, updated in its own coordinate, stays in the unit cube
  have hkey : ∀ i l, ∀ᵐ ρ ∂(blkRestMeasure D.kind i), ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ‖Function.update (blkFlatL D.kind D.htot ((blkSplit D.kind i l).symm (0, ρ)))
        ((blkEnum D.kind D.htot).symm ⟨i, l⟩) t‖ ≤ 1 := by
    intro i l
    rw [blkRestMeasure,
      ae_restrict_iff' ((measurableSet_cube _).prod (measurableSet_bigCube _))]
    refine Filter.Eventually.of_forall fun ρ hρ t ht => ?_
    have hv₀ : (blkSplit D.kind i l).symm (0, ρ) ∈ bigCube D.kind := by
      rw [bigCube_eq_preimage D.kind i l, Set.mem_preimage, MeasurableEquiv.apply_symm_apply]
      exact ⟨by norm_num, hρ⟩
    have hb1 : ‖blkFlatL D.kind D.htot ((blkSplit D.kind i l).symm (0, ρ))‖ ≤ 1 := by
      have h2 : blkFlatL D.kind D.htot ((blkSplit D.kind i l).symm (0, ρ)) ∈ cube (M + 2) := by
        rw [← Set.mem_preimage, blkFlatL_preimage_cube]
        exact hv₀
      rwa [← closedBall_eq_cube] at h2
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    by_cases hj : j = (blkEnum D.kind D.htot).symm ⟨i, l⟩
    · rw [hj, Function.update_self, abs_le]
      exact ht
    · rw [Function.update_of_ne hj]
      refine le_trans ?_ hb1
      simpa [Real.norm_eq_abs] using norm_le_pi_norm
        (blkFlatL D.kind D.htot ((blkSplit D.kind i l).symm (0, ρ))) j
  have hEfun : ∀ i l ρ, (fun t => E ((blkSplit D.kind i l).symm (t, ρ)))
      = fun t => Rm (D.Pm.mulVec
          (r • Function.update (blkFlatL D.kind D.htot ((blkSplit D.kind i l).symm (0, ρ)))
            ((blkEnum D.kind D.htot).symm ⟨i, l⟩) t)) / r ^ (M + 2) := by
    intro i l ρ
    funext t'
    rw [hEdef]
    simp only [hremdef]
    rw [blkFlatL_blkSplit_symm]
  have hE : ∀ i l, ∀ᵐ ρ ∂(blkRestMeasure D.kind i), ∀ t ∈ Set.Icc (-1 : ℝ) 1, HasDerivAt
      (fun t => E ((blkSplit D.kind i l).symm (t, ρ))) (Epar i l t ρ) t := by
    intro i l
    filter_upwards [hkey i l] with ρ hρ t ht
    rw [hEfun i l ρ, hEpardef]
    exact hg1 _ _ t (hρ t ht)
  have hEb : ∀ i l, ∀ᵐ ρ ∂(blkRestMeasure D.kind i),
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Epar i l t ρ| ≤ η := by
    intro i l
    filter_upwards [hkey i l] with ρ hρ t ht
    have hbnd := hg2 _ _ t (hρ t ht)
    rw [hEpardef, hηdef]
    nlinarith [hbnd, hr.le]
  -- the splitting in the flattened block coordinates
  have hsplit : ∀ v : Fin (M + 2) → ℝ,
      S (r • (D.Pm.mulVec v)) / r ^ (M + 2)
        = Γ * ∏ i, (D.kind i).factor ((blkFlatL D.kind D.htot).symm v i) + rem v := by
    intro v
    have hrn : (r:ℝ) ^ (M + 2) ≠ 0 := by positivity
    have hLw : D.L (D.Pm.mulVec v) = v := by
      rw [D.Pm_mulVec, LinearEquiv.apply_symm_apply]
    have hrem : rem v = Rm (r • (D.Pm.mulVec v)) / r ^ (M + 2) := by
      show Rm (D.Pm.mulVec (r • v)) / r ^ (M + 2) = Rm (r • (D.Pm.mulVec v)) / r ^ (M + 2)
      rw [Matrix.mulVec_smul]
    rw [hrem, hS, det_krylov_smul, D.key (D.Pm.mulVec v), hLw, hΓdef]
    field_simp
    try ring
  -- the target set is carried into the shell set
  set W : Set (Blk D.kind) :=
    {u : Blk D.kind | |Γ * ∏ i, (D.kind i).factor (u i) + E u| ≤ s} ∩ bigCube D.kind
      ∩ {u | D.c ≤ ‖u‖} with hWdef
  set V : Set (Fin (M + 2) → ℝ) :=
    {v | |Γ * ∏ i, (D.kind i).factor ((blkFlatL D.kind D.htot).symm v i)
        + rem v| ≤ s} ∩ cube (M + 2) ∩ {v | D.c ≤ ‖v‖} with hVdef
  have hVmeas : MeasurableSet V := by
    rw [hVdef]
    refine MeasurableSet.inter (MeasurableSet.inter ?_ (measurableSet_cube _)) ?_
    · refine measurableSet_le (Measurable.abs ?_) measurable_const
      refine Measurable.add ?_ hremmeas
      refine measurable_const.mul (Finset.measurable_prod _ fun i _ => ?_)
      have hsm : Measurable fun v : Fin (M + 2) → ℝ => (blkFlatL D.kind D.htot).symm v := by
        have hfe : (fun v : Fin (M + 2) → ℝ => (blkFlatL D.kind D.htot).symm v)
            = fun v => (blkFlatM D.kind D.htot).symm v := by
          funext v
          apply (blkFlatM D.kind D.htot).injective
          rw [hcoe, LinearEquiv.apply_symm_apply, MeasurableEquiv.apply_symm_apply]
        rw [hfe]
        exact (blkFlatM D.kind D.htot).symm.measurable
      exact (D.kind i).measurable_factor.comp ((measurable_pi_apply i).comp hsm)
    · exact measurableSet_le measurable_const measurable_norm
  have hWeq : (blkFlatM D.kind D.htot : Blk D.kind → (Fin (M + 2) → ℝ)) ⁻¹' V = W := by
    ext u
    rw [Set.mem_preimage, hVdef, hWdef, hcoe u]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, LinearEquiv.symm_apply_apply,
      norm_blkFlatL]
    rw [← Set.mem_preimage (f := fun w : Blk D.kind => blkFlatL D.kind D.htot w),
      blkFlatL_preimage_cube]
    try rfl
  have hsub : ({z : Fin (M + 2) → ℝ | |S (r • z)| ≤ s * r ^ (M + 2)} ∩ cube (M + 2)
        ∩ {z : Fin (M + 2) → ℝ | (1/2 : ℝ) ≤ ‖z‖})
      ⊆ (D.L : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ)) ⁻¹' V := by
    rintro z ⟨⟨hz, hzc⟩, hzn⟩
    have hzn1 : ‖z‖ ≤ 1 := by rwa [← closedBall_eq_cube] at hzc
    have hPv : D.Pm.mulVec (D.L z) = z := by
      rw [D.Pm_mulVec, LinearEquiv.symm_apply_apply]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show |Γ * ∏ i, (D.kind i).factor ((blkFlatL D.kind D.htot).symm (D.L z) i)
        + rem (D.L z)| ≤ s
      rw [← hsplit (D.L z), hPv, abs_div,
        abs_of_pos (by positivity : (0:ℝ) < r ^ (M + 2)), div_le_iff₀ (by positivity)]
      simpa [mul_comm] using hz
    · show D.L z ∈ cube (M + 2)
      rw [← closedBall_eq_cube]
      exact le_trans (D.hcontr z) hzn1
    · show D.c ≤ ‖D.L z‖
      have hc0 : (0:ℝ) ≤ 2 * D.c := by have := D.hc; linarith
      have h1 : 2 * D.c * (1/2 : ℝ) ≤ 2 * D.c * ‖z‖ := mul_le_mul_of_nonneg_left hzn hc0
      have h2 := D.hlow z
      linarith
  -- and the shell estimate applies
  have hshell := measure_sublevel_shell_le D.kind hη hs D.hc D.hc1 hC hMc hMi hCi hEmeas
    Epar hE hEb
  have hexp1 : Lam s ^ (D.Nb - 1 + 1) ≤ Lam s ^ (M + 1) :=
    pow_le_pow_right₀ (one_le_Lam s) (by have := D.Nb_le; omega)
  have hexp2 : Lam (2 * η) ^ (D.Nb - 1) ≤ Lam (2 * η) ^ M :=
    pow_le_pow_right₀ (one_le_Lam _) (by have := D.Nb_le; omega)
  calc volume ({z : Fin (M + 2) → ℝ | |S (r • z)| ≤ s * r ^ (M + 2)} ∩ cube (M + 2)
        ∩ {z : Fin (M + 2) → ℝ | (1/2 : ℝ) ≤ ‖z‖})
      ≤ volume ((D.L : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ)) ⁻¹' V) := measure_mono hsub
    _ = ENNReal.ofReal J * volume V := volume_preimage_linearEquiv D.L V
    _ = ENNReal.ofReal J * volume W := by
        rw [← hWeq,
          (measurePreserving_blkFlatM D.kind D.htot).measure_preimage hVmeas.nullMeasurableSet]
    _ ≤ ENNReal.ofReal J * ((2 * totDim D.kind : ℕ)
          * (ENNReal.ofReal (4 * (4 * C + Mc) * s * Lam s ^ (D.Nb - 1 + 1))
            + ENNReal.ofReal (2 * (C * (2 * η) * Lam (2 * η) ^ (D.Nb - 1))))) := by
        exact mul_le_mul_right hshell _
    _ ≤ _ := by
        rw [mul_add, ← ENNReal.ofReal_natCast (2 * totDim D.kind),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          mul_add, ← ENNReal.ofReal_mul hJ0, ← ENNReal.ofReal_mul hJ0]
        refine add_le_add (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal ?_)
        · rw [← htotdef]
          have h1 : tot * (4 * (4 * C + Mc) * s * Lam s ^ (D.Nb - 1 + 1))
              ≤ tot * (4 * (4 * C + Mc) * s * Lam s ^ (M + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ htot0
            refine mul_le_mul_of_nonneg_left hexp1 (by positivity)
          calc J * (tot * (4 * (4 * C + Mc) * s * Lam s ^ (D.Nb - 1 + 1)))
              ≤ J * (tot * (4 * (4 * C + Mc) * s * Lam s ^ (M + 1))) :=
                mul_le_mul_of_nonneg_left h1 hJ0
            _ = J * (tot * (4 * (4 * C + Mc))) * s * Lam s ^ (M + 1) := by ring
        · rw [← htotdef]
          have h1 : tot * (2 * (C * (2 * η) * Lam (2 * η) ^ (D.Nb - 1)))
              ≤ tot * (2 * (C * (2 * η) * Lam (2 * η) ^ M)) := by
            refine mul_le_mul_of_nonneg_left ?_ htot0
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            refine mul_le_mul_of_nonneg_left hexp2 (by positivity)
          calc J * (tot * (2 * (C * (2 * η) * Lam (2 * η) ^ (D.Nb - 1))))
              ≤ J * (tot * (2 * (C * (2 * η) * Lam (2 * η) ^ M))) :=
                mul_le_mul_of_nonneg_left h1 hJ0
            _ = J * (tot * (2 * C)) * (2 * η) * Lam (2 * η) ^ M := by ring

/-- **Lemma 4.8 from a shell bound.**  The shell-summing half of `lemma7_volume`, isolated so
that it serves the general block estimate as well as the all-lines one.  `cc` is the constant
in `η = cc · r`. -/
theorem lemma7_of_shell {S : (Fin (M + 2) → ℝ) → ℝ} {C₁ C₂ cc ρ : ℝ} (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hcc : 1 ≤ cc) (_hρ0 : 0 < ρ)
    (hbnd : ∀ r s : ℝ, 0 < r → r ≤ ρ → 0 < s →
      volume ({z : Fin (M + 2) → ℝ |
          |S (r • z)| ≤ s * r ^ (M + 2)} ∩ cube (M + 2)
          ∩ {z : Fin (M + 2) → ℝ | (1/2 : ℝ) ≤ ‖z‖})
        ≤ ENNReal.ofReal (C₁ * s * Lam s ^ (M + 1))
          + ENNReal.ofReal (C₂ * (2 * (cc * r)) * Lam (2 * (cc * r)) ^ M)) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ R s : ℝ, 0 < R → R ≤ ρ → 0 < s → s ≤ 1 →
      volume ({y : Fin (M + 2) → ℝ |
          |S y| ≤ s * ‖y‖ ^ (M + 2)} ∩ {y | ‖y‖ ≤ R})
        ≤ ENNReal.ofReal (CA * R ^ (M + 2) *
            (s * Lam s ^ (M + 1) + R * Lam R ^ M)) := by
  classical
  have hcc0 : (0:ℝ) < cc := lt_of_lt_of_le one_pos hcc
  set D₂ : ℝ := C₂ * 2 * cc with hD₂
  have hD₂0 : (0:ℝ) ≤ D₂ := by rw [hD₂]; positivity
  refine ⟨C₁ * dyadicConst (M + 2) 0
      + D₂ * Lam (2 * cc) ^ M * dyadicConst (M + 3) M + 1, ?_, ?_⟩
  · have h1 := dyadicConst_nonneg (M + 2) 0
    have h2 := dyadicConst_nonneg (M + 3) M
    have h3 := (Lam_pow_pos (2 * cc) M).le
    positivity
  intro R s hR hR1 hs hs1
  set a : ℝ := C₁ * (R ^ (M + 2) * (s * Lam s ^ (M + 1))) with hadef
  set b : ℝ := D₂ * (R ^ (M + 3) * Lam (2 * cc * R) ^ M) with hbdef
  have hLamsp : (0:ℝ) < Lam s ^ (M + 1) := Lam_pow_pos s (M + 1)
  have hLamcR : (0:ℝ) < Lam (2 * cc * R) ^ M := Lam_pow_pos _ M
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  refine le_trans (volume_inter_ball_le' (by omega) hR _) ?_
  have hshell : ∀ j : ℕ,
      ENNReal.ofReal (((1/2 : ℝ) ^ j * R) ^ (M + 2)) *
        volume ((fun z => ((1/2 : ℝ) ^ j * R) • z) ⁻¹'
          {y : Fin (M + 2) → ℝ |
            |S y| ≤ s * ‖y‖ ^ (M + 2)} ∩ cube (M + 2)
          ∩ {z : Fin (M + 2) → ℝ | (1/2 : ℝ) ≤ ‖z‖})
      ≤ ENNReal.ofReal
          (a * (((1:ℝ)/2) ^ ((M + 2) * j) * (1 + j) ^ 0)
            + b * (((1:ℝ)/2) ^ ((M + 3) * j) * (1 + j) ^ M)) := by
    intro j
    set r : ℝ := (1/2 : ℝ) ^ j * R with hrdef
    have hr : 0 < r := by rw [hrdef]; positivity
    have hr1 : r ≤ ρ := by
      rw [hrdef]
      have h2 : ((1:ℝ)/2) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith [hR1, hR.le]
    have hsub : ((fun z => r • z) ⁻¹'
        {y : Fin (M + 2) → ℝ | |S y| ≤ s * ‖y‖ ^ (M + 2)}
        ∩ cube (M + 2) ∩ {z : Fin (M + 2) → ℝ | (1/2 : ℝ) ≤ ‖z‖})
        ⊆ {z : Fin (M + 2) → ℝ |
            |S (r • z)| ≤ s * r ^ (M + 2)} ∩ cube (M + 2)
          ∩ {z : Fin (M + 2) → ℝ | (1/2 : ℝ) ≤ ‖z‖} := by
      rintro z ⟨⟨hz, hzc⟩, hzs⟩
      refine ⟨⟨?_, hzc⟩, hzs⟩
      have hzn : ‖z‖ ≤ 1 := by rwa [← closedBall_eq_cube] at hzc
      have hz' : |S (r • z)| ≤ s * ‖r • z‖ ^ (M + 2) := hz
      refine le_trans hz' ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
      have hzp : ‖z‖ ^ (M + 2) ≤ 1 := pow_le_one₀ (norm_nonneg z) hzn
      have hr0 : (0:ℝ) ≤ r ^ (M + 2) := by positivity
      calc s * (r ^ (M + 2) * ‖z‖ ^ (M + 2)) ≤ s * (r ^ (M + 2) * 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hs.le
            exact mul_le_mul_of_nonneg_left hzp hr0
        _ = s * r ^ (M + 2) := by ring
    refine le_trans (mul_le_mul_right (measure_mono hsub) _) ?_
    refine le_trans (mul_le_mul_right (hbnd r s hr hr1 hs) _) ?_
    set X₁ : ℝ := C₁ * s * Lam s ^ (M + 1) with hX₁
    set X₂ : ℝ := C₂ * (2 * (cc * r)) * Lam (2 * (cc * r)) ^ M with hX₂
    have hX₁0 : 0 ≤ X₁ := by rw [hX₁]; positivity
    have hX₂0 : 0 ≤ X₂ := by
      rw [hX₂]; have := (Lam_pow_pos (2 * (cc * r)) M).le; positivity
    have hcollapse : ENNReal.ofReal (r ^ (M + 2)) *
        (ENNReal.ofReal X₁ + ENNReal.ofReal X₂)
        = ENNReal.ofReal (r ^ (M + 2) * (X₁ + X₂)) := by
      rw [← ENNReal.ofReal_add hX₁0 hX₂0, ← ENNReal.ofReal_mul (by positivity)]
    rw [hcollapse]
    refine ENNReal.ofReal_le_ofReal ?_
    have hrpow : r ^ (M + 2) = R ^ (M + 2) * ((1:ℝ)/2) ^ ((M + 2) * j) := by
      rw [hrdef, mul_pow, ← pow_mul, mul_comm j (M + 2)]; ring
    have hetar : 2 * (cc * r) = (2 * cc * R) * ((1:ℝ)/2) ^ j := by rw [hrdef]; ring
    have hsplit : ((1:ℝ)/2 : ℝ) ^ ((M + 3) * j)
        = ((1:ℝ)/2) ^ ((M + 2) * j) * ((1:ℝ)/2) ^ j := by
      rw [← pow_add]; ring_nf
    have hi : r ^ (M + 2) * X₁ = a * (((1:ℝ)/2) ^ ((M + 2) * j) * (1 + j) ^ 0) := by
      rw [hadef, hrpow, hX₁]; ring
    have hLamη : Lam (2 * (cc * r)) ^ M ≤ Lam (2 * cc * R) ^ M * (1 + j) ^ M := by
      rw [hetar, ← mul_pow]
      exact pow_le_pow_left₀ (Lam_nonneg _) (Lam_mul_half_pow_le (by positivity) j) M
    have hii : r ^ (M + 2) * X₂ ≤ b * (((1:ℝ)/2) ^ ((M + 3) * j) * (1 + j) ^ M) := by
      have hstep : X₂ ≤ (C₂ * ((2 * cc * R) * ((1:ℝ)/2) ^ j))
          * (Lam (2 * cc * R) ^ M * (1 + j) ^ M) := by
        rw [hX₂]
        have h1 : (0:ℝ) ≤ C₂ * (2 * (cc * r)) := by positivity
        refine le_trans (mul_le_mul_of_nonneg_left hLamη h1) ?_
        rw [hetar]
      calc r ^ (M + 2) * X₂
          ≤ r ^ (M + 2) * ((C₂ * ((2 * cc * R) * ((1:ℝ)/2) ^ j))
              * (Lam (2 * cc * R) ^ M * (1 + j) ^ M)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = b * (((1:ℝ)/2) ^ ((M + 3) * j) * (1 + j) ^ M) := by
            rw [hbdef, hD₂, hrpow, hsplit]; ring
    have hexpand : r ^ (M + 2) * (X₁ + X₂) = r ^ (M + 2) * X₁ + r ^ (M + 2) * X₂ := by ring
    rw [hexpand]
    linarith [hi.le, hii]
  refine le_trans (ENNReal.tsum_le_tsum hshell) ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    (summable_dyadic_pair (n := M + 2) (p := M) (by omega) a b)]
  rw [tsum_dyadic_pair (by omega) a b]
  refine ENNReal.ofReal_le_ofReal ?_
  set CA : ℝ := C₁ * dyadicConst (M + 2) 0
      + D₂ * Lam (2 * cc) ^ M * dyadicConst (M + 3) M + 1 with hCAdef
  have hdc1 : (0:ℝ) ≤ dyadicConst (M + 2) 0 := dyadicConst_nonneg _ _
  have hdc2 : (0:ℝ) ≤ dyadicConst (M + 3) M := dyadicConst_nonneg _ _
  have hL2c : (0:ℝ) ≤ Lam (2 * cc) ^ M := (Lam_pow_pos (2 * cc) M).le
  set P₁ : ℝ := R ^ (M + 2) * (s * Lam s ^ (M + 1)) with hP₁
  set P₂ : ℝ := R ^ (M + 2) * (R * Lam R ^ M) with hP₂
  have hP₁0 : (0:ℝ) ≤ P₁ := by
    rw [hP₁]
    exact mul_nonneg (by positivity) (mul_nonneg hs.le (Lam_pow_pos s (M + 1)).le)
  have hP₂0 : (0:ℝ) ≤ P₂ := by
    rw [hP₂]
    exact mul_nonneg (by positivity) (mul_nonneg hR.le (Lam_pow_pos R M).le)
  have hnn2 : (0:ℝ) ≤ D₂ * Lam (2 * cc) ^ M * dyadicConst (M + 3) M :=
    mul_nonneg (mul_nonneg hD₂0 hL2c) hdc2
  have hnn1 : (0:ℝ) ≤ C₁ * dyadicConst (M + 2) 0 := mul_nonneg hC₁ hdc1
  have hCA1 : C₁ * dyadicConst (M + 2) 0 ≤ CA := by rw [hCAdef]; linarith
  have hCA2 : D₂ * Lam (2 * cc) ^ M * dyadicConst (M + 3) M ≤ CA := by rw [hCAdef]; linarith
  have h1 : a * dyadicConst (M + 2) 0 ≤ CA * P₁ := by
    have heq : a * dyadicConst (M + 2) 0 = (C₁ * dyadicConst (M + 2) 0) * P₁ := by
      rw [hadef, hP₁]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hCA1 hP₁0
  have h2 : b * dyadicConst (M + 3) M ≤ CA * P₂ := by
    have hLamcR' : Lam (2 * cc * R) ^ M ≤ Lam (2 * cc) ^ M * Lam R ^ M := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Lam_nonneg _) (Lam_mul_le_of_pos (by positivity) hR) M
    have hb : b * dyadicConst (M + 3) M
        ≤ (D₂ * Lam (2 * cc) ^ M * dyadicConst (M + 3) M) * P₂ := by
      rw [hbdef, hP₂]
      have hfac : D₂ * (R ^ (M + 3) * Lam (2 * cc * R) ^ M) * dyadicConst (M + 3) M
          = (D₂ * (R ^ (M + 2) * R) * dyadicConst (M + 3) M) * Lam (2 * cc * R) ^ M := by
        ring
      have hfac' : D₂ * Lam (2 * cc) ^ M * dyadicConst (M + 3) M
            * (R ^ (M + 2) * (R * Lam R ^ M))
          = (D₂ * (R ^ (M + 2) * R) * dyadicConst (M + 3) M)
            * (Lam (2 * cc) ^ M * Lam R ^ M) := by ring
      rw [hfac, hfac']
      exact mul_le_mul_of_nonneg_left hLamcR' (by positivity)
    exact le_trans hb (mul_le_mul_of_nonneg_right hCA2 hP₂0)
  have hfinal : CA * R ^ (M + 2) * (s * Lam s ^ (M + 1) + R * Lam R ^ M)
      = CA * P₁ + CA * P₂ := by rw [hP₁, hP₂]; ring
  rw [hfinal]
  linarith

/-- **Lemma 4.8, probability form, for an arbitrary real spectrum.** -/
theorem lemma7_prob_gen {Sig Rm : (Fin (M + 2) → ℝ) → ℝ} (D : ShellData A)
    {cR ρ : ℝ} (hcR : 0 ≤ cR) (hρ0 : 0 < ρ) (hlead : leadConst A ≠ 0)
    (hS : ∀ y, Sig y = leadConst A * (krylov A y).det + Rm y)
    (hRmeas : Measurable Rm)
    (hRderiv : ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ κ : Fin (M + 2),
      ∃ g : ℝ → (Fin (M + 2) → ℝ) → ℝ,
        (∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 →
            HasDerivAt (fun t => Rm (D.Pm.mulVec (r • Function.update v κ t)) / r ^ (M + 2))
              (g t v) t)
          ∧ ∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 → |g t v| ≤ cR * r) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ δ s : ℝ, 0 < δ → 2 * δ ≤ ρ → 0 < s → s ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ →
        blockMeasure (M + 2) {b | |Sig (x + δ • b)| ≤ s * ‖x + δ • b‖ ^ (M + 2)}
          ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
              (s * Lam s ^ (M + 1) + δ * Lam δ ^ M)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hbnd⟩ := shell_cube_bound_gen D hcR hlead hS hRmeas hRderiv
  refine lemma7_prob (Sig := Sig) (lemma7_of_shell (cc := cR + 1) hC₁ hC₂ (by linarith) hρ0 ?_)
  intro r s hr hr1 hs
  exact hbnd r s hr hr1 hs

/-- The polynomial instance of `lemma7_prob_gen`. -/
theorem lemma7_prob_poly (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1)) (D : ShellData A) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ δ s : ℝ, 0 < δ → 2 * δ ≤ 1 → 0 < s → s ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ →
        blockMeasure (M + 2)
            {b | |MvPolynomial.eval (x + δ • b) (sigtPoly A q)|
                ≤ s * ‖x + δ • b‖ ^ (M + 2)}
          ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
              (s * Lam s ^ (M + 1) + δ * Lam δ ^ M)) := by
  have hRderiv : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ κ : Fin (M + 2),
      ∃ g : ℝ → (Fin (M + 2) → ℝ) → ℝ,
        (∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 →
            HasDerivAt (fun t => MvPolynomial.eval (D.Pm.mulVec (r • Function.update v κ t))
              (sigRem A q) / r ^ (M + 2)) (g t v) t)
          ∧ ∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 →
              |g t v| ≤ derivBound (remHat A q D.Pm) * r := by
    intro r hr hr1 κ
    obtain ⟨g, hg1, hg2⟩ := (lowDeg_remHat hq D.Pm).exists_deriv_update hr hr1 κ
    refine ⟨g, fun v t _ => ?_, fun v t hv => hg2 v t hv⟩
    have hfun : (fun t => MvPolynomial.eval (D.Pm.mulVec (r • Function.update v κ t))
        (sigRem A q) / r ^ (M + 2))
        = fun t => MvPolynomial.eval (r • Function.update v κ t) (remHat A q D.Pm)
            / r ^ (M + 2) := by
      funext t'
      rw [remHat, eval_bind₁_lin]
    rw [hfun]
    exact hg1 v t
  exact lemma7_prob_gen D (Sig := fun y => MvPolynomial.eval y (sigtPoly A q))
    (Rm := fun y => MvPolynomial.eval y (sigRem A q)) (ρ := 1) (derivBound_nonneg _)
    one_pos (leadConst_ne_zero hA) (fun y => eval_sigtPoly y)
    (MvPolynomial.continuous_eval _).measurable hRderiv

/-- **Theorem 4.9, for an arbitrary real matrix with distinct eigenvalues.**

This is the paper's Theorem 4.9 in full: `Squarefree A.charpoly` is the hypothesis "`A` has `n`
distinct eigenvalues" (over the perfect field `ℝ` the two are equivalent), with *no*
assumption that the spectrum is real.  The exponent of `δ` is exactly `1` and the logarithms
are kept — this is not a pure-power weakening. -/
theorem theorem3 (hq : ∀ i, LowDeg 2 (q i)) (hA : IsUnit (A - 1))
    (hsq : Squarefree A.charpoly)
    (B : SharpBound (cycleData hq hA)) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ 1 →
      (∀ m, 8 * B.C₁ * (sched δ θ m) ^ (2 - θ) ≤ 1) →
      (∀ m, 16 * B.C₂ * (sched δ θ m) ^ (3 - θ) ≤ 1) →
      ((δ ^ (1:ℝ)) ^ (θ - 1) * θ ^ (M + 1) ≤ 1 / 2) →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
            {ω | ∃ m, ¬ ‖xProc (cycleData hq hA) x₀ δ θ m ω‖ ≤ sched δ θ m}
          ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) := by
  obtain ⟨D⟩ := nonempty_shellData (by omega) A hsq
  obtain ⟨Cst, hCst, hmain⟩ := theorem3_of_lemma7 (cycleData hq hA) rfl (fun _ => rfl)
    (eval_sigtPoly_zero hq) (measurable_cycleData_S hq hA) (measurable_cycleData_tau hq hA)
    (lemma7_prob_poly hq hA D) B hθ1 hθ2
  refine ⟨Cst, hCst, fun δ hδ hδ1 h2δ hslack hs1 hratio x₀ hx₀ =>
    hmain δ hδ hδ1 h2δ h2δ h2δ hslack hs1 hratio x₀ hx₀⟩

/-- **Theorem 4.9, with the cycle data supplied abstractly.**

The same statement as `theorem3`, but taking the `CycleData`, its denominator's splitting
`σ̃ = leadConst A · Δ + R`, and a derivative bound on `R` as hypotheses rather than
constructing them from a polynomial map.  This is the form the `C³` development instantiates;
`theorem3` is the polynomial instance. -/
theorem theorem3_gen {Sig Rm : (Fin (M + 2) → ℝ) → ℝ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (D : ShellData A)
    (C : CycleData (Fin (M + 2) → ℝ)) (hd : C.d = M + 2) (hsig : ∀ y, C.sigt y = Sig y)
    (hz : Sig 0 = 0) (hSmeas : Measurable C.S) (hτmeas : Measurable C.τ)
    (hlead : leadConst A ≠ 0)
    (hS : ∀ y, Sig y = leadConst A * (krylov A y).det + Rm y)
    (hRmeas : Measurable Rm)
    {cR : ℝ} (hcR : 0 ≤ cR)
    (hRderiv : ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ κ : Fin (M + 2),
        ∃ g : ℝ → (Fin (M + 2) → ℝ) → ℝ,
          (∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 →
              HasDerivAt (fun t => Rm (D.Pm.mulVec (r • Function.update v κ t)) / r ^ (M + 2))
                (g t v) t)
            ∧ ∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 → |g t v| ≤ cR * r)
    (B : SharpBound C) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * δ ≤ 1 → 2 * δ ≤ ρ → 2 * δ ≤ C.ρ₁ →
      (∀ m, 8 * B.C₁ * (sched δ θ m) ^ (2 - θ) ≤ 1) →
      (∀ m, 16 * B.C₂ * (sched δ θ m) ^ (3 - θ) ≤ 1) →
      ((δ ^ (1:ℝ)) ^ (θ - 1) * θ ^ (M + 1) ≤ 1 / 2) →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
            {ω | ∃ m, ¬ ‖xProc C x₀ δ θ m ω‖ ≤ sched δ θ m}
          ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) := by
  exact theorem3_of_lemma7 C hd hsig hz hSmeas hτmeas
    (lemma7_prob_gen D hcR hρ0 hlead (fun y => hS y) hRmeas hRderiv) B hθ1 hθ2

end Nine

end MPE
