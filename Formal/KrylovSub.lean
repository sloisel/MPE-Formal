import Mathlib
import Formal.Sublevel
import Formal.DeltaFactor

/-!
# The sublevel bound for the Krylov determinant

`Δ_A(y) = det K_A(y)` is the leading form of `σ̃`.  Because `K_A` is *linear* in `y`, the
restriction of `Δ_A` to a line is the determinant of a matrix pencil, so
`Sublevel.detPencil` gives its degree and — the point — its leading coefficient
`Δ_A(v)`, the *same* on every line in direction `v`.  `Sublevel.sublevel_dir` then converts
that into the anticoncentration estimate.

The only hypothesis is that `A` is nonderogatory: `Δ_A(v) ≠ 0` for some `v`.  Rescaling
and shearing normalise `v` to have first coordinate `1`, which is what makes the shear
unipotent and the change of variables free.
-/

namespace MPE

open MeasureTheory Matrix Polynomial

variable {n : ℕ}

/-! ### The Krylov matrix is linear -/

lemma krylov_smul' (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (z : Fin n → ℝ) :
    krylov A (r • z) = r • krylov A z := by
  ext i j
  simp only [krylov_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [Matrix.mulVec_smul]
  rfl

lemma krylov_add_smul (A : Matrix (Fin n) (Fin n) ℝ) (a v : Fin n → ℝ) (t : ℝ) :
    krylov A (a + t • v) = krylov A a + t • krylov A v := by
  ext i j
  simp only [krylov_apply, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec_add, Matrix.mulVec_smul]

/-! ### The line restriction of `Δ_A` -/

/-- The restriction of `y ↦ det K_A(y)` to the line `a + t v`. -/
noncomputable def krylovPoly (A : Matrix (Fin n) (Fin n) ℝ) (a v : Fin n → ℝ) :
    Polynomial ℝ :=
  detPencil (krylov A a) (krylov A v)

lemma krylovPoly_eval (A : Matrix (Fin n) (Fin n) ℝ) (a v : Fin n → ℝ) (t : ℝ) :
    (krylovPoly A a v).eval t = (krylov A (a + t • v)).det := by
  rw [krylovPoly, detPencil_eval, krylov_add_smul]

lemma krylovPoly_natDegree_le (A : Matrix (Fin n) (Fin n) ℝ) (a v : Fin n → ℝ) :
    (krylovPoly A a v).natDegree ≤ n :=
  detPencil_natDegree_le _ _

/-- **The leading coefficient is `Δ_A(v)`, independent of the base point `a`.** -/
lemma krylovPoly_coeff (A : Matrix (Fin n) (Fin n) ℝ) (a v : Fin n → ℝ) :
    (krylovPoly A a v).coeff n = (krylov A v).det :=
  detPencil_coeff _ _

/-! ### Continuity -/

lemma continuous_det_krylov (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun y : Fin n → ℝ => (krylov A y).det := by
  refine Continuous.matrix_det ?_
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [krylov_apply, Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)

lemma measurable_det_krylov (A : Matrix (Fin n) (Fin n) ℝ) :
    Measurable fun y : Fin n → ℝ => (krylov A y).det :=
  (continuous_det_krylov A).measurable

/-! ### Normalising the direction

Homogeneity lets us rescale `v`, and the line `v + t e₀` meets `{Δ_A ≠ 0}` off a finite
set, so a direction with first coordinate `1` is always available. -/

/-- **A good direction can be normalised to have first coordinate `1`.** -/
theorem exists_good_dir {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hA : ∃ v, (krylov A v).det ≠ 0) :
    ∃ w : Fin (n + 1) → ℝ, w 0 = 1 ∧ (krylov A w).det ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := hA
  set e : Fin (n + 1) → ℝ := Pi.single 0 1 with hedef
  set p : Polynomial ℝ := krylovPoly A v e with hpdef
  have hp0 : p.eval 0 = (krylov A v).det := by
    rw [hpdef, krylovPoly_eval]; simp
  have hpne : p ≠ 0 := by
    intro h
    rw [h] at hp0
    simp at hp0
    exact hv hp0.symm
  -- avoid the finitely many roots of `p`, and the one point where the first coordinate dies
  have hfin : ({t : ℝ | p.IsRoot t} ∪ {-(v 0)}).Finite :=
    (Polynomial.finite_setOf_isRoot hpne).union (Set.finite_singleton _)
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff,
    not_or] at ht
  obtain ⟨hroot, hzero⟩ := ht
  set z : Fin (n + 1) → ℝ := v + t • e with hzdef
  have hz0 : z 0 = v 0 + t := by rw [hzdef]; simp [hedef]
  have hz0ne : z 0 ≠ 0 := by
    rw [hz0]
    intro h
    exact hzero (by linarith)
  have hzdet : (krylov A z).det ≠ 0 := by
    have : (krylov A z).det = p.eval t := by rw [hpdef, krylovPoly_eval, hzdef]
    rw [this]
    exact hroot
  -- rescale
  have hscale : (krylov A ((z 0)⁻¹ • z)).det = ((z 0)⁻¹) ^ (n + 1) * (krylov A z).det := by
    rw [krylov_smul', Matrix.det_smul, Fintype.card_fin]
  refine ⟨(z 0)⁻¹ • z, ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hz0ne
  · rw [hscale]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hz0ne)) hzdet

/-! ### The bound -/

/-- **The anticoncentration bound for `Δ_A = det K_A`.**  On the box of half-width `K`, the
set where `|Δ_A|` is at most `ε` has measure at most a constant times `ε^{1/(n+1)}`. -/
theorem sublevel_krylov {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {v : Fin (n + 1) → ℝ} (hv0 : v 0 = 1) (hv : (krylov A v).det ≠ 0)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    volume {y : Fin (n + 1) → ℝ | |(krylov A y).det| ≤ ε ∧ ∀ i, |y i| ≤ K}
      ≤ ENNReal.ofReal ((2 * (K * (1 + ‖v‖))) ^ n) *
        ENNReal.ofReal (4 * (n + 1) *
          (ε / |(krylov A v).det|) ^ (((n : ℝ) + 1)⁻¹)) := by
  have hres := sublevel_dir (n := n) (d := n + 1) (Nat.succ_pos n) hv
    (measurable_det_krylov A) hv0 (fun a => krylovPoly A a v)
    (fun a => krylovPoly_natDegree_le A a v)
    (fun a => krylovPoly_coeff A a v)
    (fun a t => (krylovPoly_eval A a v t).symm) hK hε
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rwa [hcast] at hres

end MPE
