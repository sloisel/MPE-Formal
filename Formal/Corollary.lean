import Mathlib
import Formal.Gen
import Formal.Quad
import Formal.General

/-!
# The paper's Theorem 4.9: quadratic order

Running `δₘ₊₁ = K δₘ²` with `K = max(8C₁,1)` instead of the doubly-exponential schedule
gives order exactly `2`, with the *same* failure probability `C δ Λ(δ)^(n-1)`.

The proof is the one of Theorem 4.9 with two inputs changed: the contraction step
(`quad_step`, from `contraction_quadratic`) and the series ratio (`β = Kδ`, `λ = 2`,
from `qsched_le` and `Lam_qsched_le`).  Everything else — the anticoncentration bound, the
schedule induction, the Tonelli reduction — is the schedule-generic machinery of
`Gen.lean`.

See `../../corollary.tex` §5.2 (Obligations 4 and 5).
-/

namespace MPE

open MeasureTheory Metric Set
open scoped ENNReal

section Step

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **(Q4) The contraction step for the quadratic schedule**, in the shape `dither_gen` and
`hPsiGen` consume.  This is `contraction_quadratic` plus `SharpBound.bound`. -/
theorem quad_step (C : CycleData E) (B : SharpBound C) {K δ : ℝ}
    (hK : 8 * B.C₁ ≤ K) (hK1 : 1 ≤ K) (hδ : 0 < δ)
    (hρ : ∀ m, 2 * qsched K δ m ≤ C.ρ₁) :
    ∀ (m : ℕ) (z : E), 0 < ‖z‖ → ‖z‖ ≤ 2 * qsched K δ m →
      16 * B.C₂ / K * qsched K δ m ≤ C.τ z →
      ‖C.S z‖ ≤ qsched K δ (m + 1) := by
  intro m z hz0 hzle hτ
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hdm : 0 < qsched K δ m := qsched_pos hK0 hδ m
  have hC₂ := B.hC₂
  have hs0 : 0 < 16 * B.C₂ / K * qsched K δ m := by positivity
  have hτ0 : 0 < C.τ z := lt_of_lt_of_le hs0 hτ
  obtain ⟨-, hσ⟩ := C.pos_of_τ_pos hτ0
  have hzρ : ‖z‖ ≤ C.ρ₁ := le_trans hzle (hρ m)
  have hb := B.bound z hz0 hzρ hσ
  have hdiv : B.C₂ * ‖z‖ ^ 3 / C.τ z
      ≤ B.C₂ * ‖z‖ ^ 3 / (16 * B.C₂ / K * qsched K δ m) :=
    div_le_div_of_nonneg_left (by positivity) hs0 hτ
  have hcq := contraction_quadratic B.hC₁ B.hC₂ hdm hK0 hz0 hzle (by linarith)
  rw [qsched_succ hK0.ne' δ m]
  linarith

/-- **The second clause of Theorem 4.9: the system is nonsingular.**  With the enlarged
threshold `s m = max(16C₂/K, 2M₀)·δₘ` of the paper, every good cycle has `τ(y) ≥ M₀‖y‖`,
which is the hypothesis of the paper's Lemma 4.4(ii); so `D(y) ≠ 0`, the cycle is the
extrapolate rather than merely its cleared form, and MPE agrees with RRE there.

`hDne` is Lemma 4.4(ii) itself, supplied as a hypothesis exactly as `SharpBound.bound` is
Lemma 4.4(iii). -/
theorem quad_nonsingular {Ω : Type*} [MeasurableSpace Ω] (C : CycleData E)
    {Dfun : E → ℝ} {M₀ : ℝ} {d s : ℕ → ℝ} (hM₀ : 0 ≤ M₀)
    (x y : ℕ → Ω → E)
    (h0 : ∀ ω, ‖x 0 ω‖ ≤ d 0)
    (hcycle : ∀ m ω, x (m + 1) ω = C.S (y m ω))
    (hdither : ∀ m ω, ‖y m ω - x m ω‖ ≤ d m)
    (hstep : ∀ (m : ℕ) (z : E), 0 < ‖z‖ → ‖z‖ ≤ 2 * d m → s m ≤ C.τ z →
      ‖C.S z‖ ≤ d (m + 1))
    (hs0 : ∀ m, 0 < s m) (hsM : ∀ m, 2 * M₀ * d m ≤ s m)
    (hdρ : ∀ m, 2 * d m ≤ C.ρ₁)
    (hDne : ∀ z : E, 0 < ‖z‖ → ‖z‖ ≤ C.ρ₁ → M₀ * ‖z‖ ≤ C.τ z → Dfun z ≠ 0) :
    ∀ (m : ℕ) (ω : Ω), (∀ j ≤ m, ω ∈ goodGen C s y j) → Dfun (y m ω) ≠ 0 := by
  intro m ω hω
  have hmarg := margin_dominates_of_good C x y h0 hcycle hdither hstep hs0 hM₀ hsM m ω hω
  have hτ0 : 0 < C.τ (y m ω) := lt_of_lt_of_le (hs0 m) (hω m (le_refl m))
  obtain ⟨hypos, -⟩ := C.pos_of_τ_pos hτ0
  have hxm : ‖x m ω‖ ≤ d m :=
    norm_le_of_good_gen C x y h0 hcycle hdither hstep hs0 m ω fun j hj => hω j (le_of_lt hj)
  have hyle : ‖y m ω‖ ≤ C.ρ₁ := by
    have hsplit : y m ω = x m ω + (y m ω - x m ω) := by abel
    refine le_trans ?_ (hdρ m)
    calc ‖y m ω‖ = ‖x m ω + (y m ω - x m ω)‖ := by rw [← hsplit]
      _ ≤ ‖x m ω‖ + ‖y m ω - x m ω‖ := norm_add_le _ _
      _ ≤ d m + d m := add_le_add hxm (hdither m ω)
      _ = 2 * d m := by ring
  exact hDne (y m ω) hypos hyle hmarg

/-- **The contraction step for any threshold at least `16C₂/K`.**  Enlarging the margin only
helps condition (a); this is what lets Theorem 4.9 take
`s m = max(16C₂/K, 2M₀)·δₘ` and so also control `D`. -/
theorem quad_step' (C : CycleData E) (B : SharpBound C) {K δ c : ℝ}
    (hK : 8 * B.C₁ ≤ K) (hK1 : 1 ≤ K) (hδ : 0 < δ) (hc : 16 * B.C₂ / K ≤ c)
    (hρ : ∀ m, 2 * qsched K δ m ≤ C.ρ₁) :
    ∀ (m : ℕ) (z : E), 0 < ‖z‖ → ‖z‖ ≤ 2 * qsched K δ m →
      c * qsched K δ m ≤ C.τ z →
      ‖C.S z‖ ≤ qsched K δ (m + 1) := by
  intro m z hz0 hzle hτ
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hdm : 0 < qsched K δ m := qsched_pos hK0 hδ m
  refine quad_step C B hK hK1 hδ hρ m z hz0 hzle (le_trans ?_ hτ)
  exact mul_le_mul_of_nonneg_right hc hdm.le

end Step

section Assembly

variable {M : ℕ}

open Poly

/-- **The two terms of `hΨ` collapse**, for the quadratic schedule: both are linear in
`δₘ`, so the `s`-term differs from the `δ`-term only by the constant `c Λ(c)^(M+1)`. -/
lemma quad_term_le {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    (c * t) * Lam (c * t) ^ (M + 1) + t * Lam t ^ M
      ≤ (c * Lam c ^ (M + 1) + 1) * (t * Lam t ^ (M + 1)) := by
  have hL : Lam (c * t) ≤ Lam c * Lam t := Lam_mul_le_of_pos hc ht
  have h1 : (c * t) * Lam (c * t) ^ (M + 1)
      ≤ c * Lam c ^ (M + 1) * (t * Lam t ^ (M + 1)) := by
    have hpow : Lam (c * t) ^ (M + 1) ≤ (Lam c * Lam t) ^ (M + 1) :=
      pow_le_pow_left₀ (Lam_nonneg _) hL (M + 1)
    have hct : (0:ℝ) ≤ c * t := by positivity
    calc (c * t) * Lam (c * t) ^ (M + 1) ≤ (c * t) * (Lam c * Lam t) ^ (M + 1) :=
          mul_le_mul_of_nonneg_left hpow hct
      _ = c * Lam c ^ (M + 1) * (t * Lam t ^ (M + 1)) := by rw [mul_pow]; ring
  have h2 : t * Lam t ^ M ≤ t * Lam t ^ (M + 1) :=
    mul_le_mul_of_nonneg_left (Lam_pow_le_pow (Nat.le_succ M)) ht.le
  nlinarith [h1, h2]

/-- **The paper's Theorem 4.9.**  With the quadratic schedule `δₘ₊₁ = Kδₘ²`, the failure
probability is still `C δ Λ(δ)^(n-1)`: order `2` at no cost in reliability. -/
theorem corollary_quad {Sig : (Fin (M + 2) → ℝ) → ℝ} {ρ : ℝ}
    (C : CycleData (Fin (M + 2) → ℝ)) (hd : C.d = M + 2) (hsig : ∀ y, C.sigt y = Sig y)
    (hz : Sig 0 = 0) (hSmeas : Measurable C.S) (hτmeas : Measurable C.τ)
    (h7 : ∃ CA : ℝ, 0 < CA ∧ ∀ δ s : ℝ, 0 < δ → 2 * δ ≤ ρ → 0 < s → s ≤ 1 →
      ∀ x : Fin (M + 2) → ℝ, ‖x‖ ≤ δ →
        blockMeasure (M + 2)
            {b | |Sig (x + δ • b)| ≤ s * ‖x + δ • b‖ ^ (M + 2)}
          ≤ ENNReal.ofReal (CA * 2 ^ (M + 3) *
              (s * Lam s ^ (M + 1) + δ * Lam δ ^ M)))
    (B : SharpBound C) {cth : ℝ} (hcth0 : 0 < cth)
    (hcth : 16 * B.C₂ / max (8 * B.C₁) 1 ≤ cth)
    (P : (Fin (M + 2) → ℝ) → Prop)
    (hPz : ∀ z : Fin (M + 2) → ℝ, 0 < ‖z‖ → ‖z‖ ≤ C.ρ₁ → cth * (2:ℝ)⁻¹ * ‖z‖ ≤ C.τ z →
      P z) :
    ∃ Cst : ℝ, 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        max (8 * B.C₁) 1 * δ * 2 ^ (M + 1) ≤ 1 / 2 →
        cth * δ ≤ 1 →
        2 * δ ≤ ρ → 2 * δ ≤ C.ρ₁ →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
            {ω | ∃ m, ¬ ‖xProcG C x₀ (qsched (max (8 * B.C₁) 1) δ) m ω‖
                  ≤ qsched (max (8 * B.C₁) 1) δ m
                ∨ ¬ P (yProcG C x₀ (qsched (max (8 * B.C₁) 1) δ) m ω)}
          ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) := by
  classical
  obtain ⟨CA, hCA0, hCA⟩ := slice_bound C hd hsig hz h7
  set K : ℝ := max (8 * B.C₁) 1 with hKdef
  have hK1 : (1:ℝ) ≤ K := le_max_right _ _
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hKC : 8 * B.C₁ ≤ K := le_max_left _ _
  set c : ℝ := cth with hcdef
  have hc0 : 0 < c := hcth0
  set D : ℝ := c * Lam c ^ (M + 1) + 1 with hDdef
  have hD0 : 0 < D := by have := Lam_pos c; rw [hDdef]; positivity
  refine ⟨CA * 2 ^ (M + 3) * D * 2, by
    have h2 : (0:ℝ) < (2:ℝ) ^ (M + 3) := by positivity
    exact mul_pos (mul_pos (mul_pos hCA0 h2) hD0) two_pos, ?_⟩
  intro δ hδ hδ1 hratio hs1δ h2δρ h2δρ₁ x₀ hx₀
  -- the schedule and the thresholds
  set d : ℕ → ℝ := qsched K δ with hddef
  set s : ℕ → ℝ := fun m => c * d m with hsdef
  have hKδ : K * δ ≤ 1 := by nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := M + 1)]
  have hd0 : ∀ m, 0 < d m := fun m => qsched_pos hK0 hδ m
  have hdle : ∀ m, d m ≤ δ := by
    intro m
    have h := qsched_le hK1 hδ hKδ m
    have hpow : (K * δ) ^ m ≤ 1 := pow_le_one₀ (by positivity) hKδ
    calc d m ≤ δ * (K * δ) ^ m := h
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hpow hδ.le
      _ = δ := mul_one δ
  have hs0 : ∀ m, 0 < s m := fun m => mul_pos hc0 (hd0 m)
  have hsle1 : ∀ m, s m ≤ 1 := by
    intro m
    calc s m = c * d m := rfl
      _ ≤ c * δ := mul_le_mul_of_nonneg_left (hdle m) hc0.le
      _ ≤ 1 := hs1δ
  have hρm : ∀ m, 2 * d m ≤ ρ := fun m => by linarith [hdle m]
  have hρ₁m : ∀ m, 2 * d m ≤ C.ρ₁ := fun m => by linarith [hdle m]
  have hx₀d : ‖x₀‖ ≤ d 0 := by rw [hddef, qsched_zero hK0.ne']; exact hx₀
  -- the contraction step
  have hstep := quad_step' C B hKC hK1 hδ hcth hρ₁m
  -- `hΨ` and the union bound
  have hpsi := hPsiGen C x₀ hd0 hs0 hsle1 hx₀d hstep hSmeas hτmeas hρm hCA
  have hdither : ∀ m ω, ‖yProcG C x₀ d m ω - xProcG C x₀ d m ω‖ ≤ d m :=
    fun m ω => norm_yProcG_sub C x₀ d hd0 m ω
  have hcycle : ∀ m ω, xProcG C x₀ d (m + 1) ω = C.S (yProcG C x₀ d m ω) :=
    fun m ω => xProcG_succ C x₀ d m ω
  have hPgood : ∀ (k : ℕ) (ω : ℕ → Fin (M + 2) → ℝ),
      (∀ j ≤ k, ω ∈ goodGen C s (yProcG C x₀ d) j) → P (yProcG C x₀ d k ω) := by
    intro k ω hω
    have hmarg := margin_dominates_of_good (M₀ := cth * (2:ℝ)⁻¹) C
      (xProcG C x₀ d) (yProcG C x₀ d) (fun _ => hx₀d) hcycle hdither hstep hs0
      (by positivity) (fun j => by
        have : cth * (2:ℝ)⁻¹ * d j * 2 = cth * d j := by ring
        nlinarith [(hd0 j).le, hcth0.le]) k ω hω
    have hτ0 : 0 < C.τ (yProcG C x₀ d k ω) :=
      lt_of_lt_of_le (hs0 k) (hω k (le_refl k))
    obtain ⟨hypos, -⟩ := C.pos_of_τ_pos hτ0
    have hxk := norm_le_of_good_gen C (xProcG C x₀ d) (yProcG C x₀ d)
      (fun _ => hx₀d) hcycle hdither hstep hs0 k ω fun j hj => hω j (le_of_lt hj)
    have hyle : ‖yProcG C x₀ d k ω‖ ≤ C.ρ₁ := by
      refine le_trans ?_ (hρ₁m k)
      have hsplit : yProcG C x₀ d k ω
          = xProcG C x₀ d k ω + (yProcG C x₀ d k ω - xProcG C x₀ d k ω) := by abel
      calc ‖yProcG C x₀ d k ω‖ = _ := by rw [← hsplit]
        _ ≤ ‖xProcG C x₀ d k ω‖ + ‖yProcG C x₀ d k ω - xProcG C x₀ d k ω‖ := norm_add_le _ _
        _ ≤ d k + d k := add_le_add hxk (hdither k ω)
        _ = 2 * d k := by ring
    exact hPz _ hypos hyle hmarg
  have hmain := dither_gen_full C
    (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
    (xProcG C x₀ d) (yProcG C x₀ d) _ P
    (fun _ => hx₀d) hcycle hdither hstep hs0 hPgood hpsi
  refine le_trans hmain ?_
  -- collapse the two terms
  have hterm : ∀ m : ℕ,
      ENNReal.ofReal (CA * 2 ^ (M + 3) * (s m * Lam (s m) ^ (M + 1) + d m * Lam (d m) ^ M))
      ≤ ENNReal.ofReal ((CA * 2 ^ (M + 3) * D) * (d m * Lam (d m) ^ (M + 1))) := by
    intro m
    refine ENNReal.ofReal_le_ofReal ?_
    have h := quad_term_le (M := M) hc0 (hd0 m)
    have hcnn : (0:ℝ) ≤ CA * 2 ^ (M + 3) := by positivity
    calc CA * 2 ^ (M + 3) * (s m * Lam (s m) ^ (M + 1) + d m * Lam (d m) ^ M)
        ≤ CA * 2 ^ (M + 3) * (D * (d m * Lam (d m) ^ (M + 1))) :=
          mul_le_mul_of_nonneg_left h hcnn
      _ = CA * 2 ^ (M + 3) * D * (d m * Lam (d m) ^ (M + 1)) := by ring
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  -- sum the single log-weighted series
  have hβ : ∀ m, d m ≤ δ * (K * δ) ^ m := fun m => qsched_le hK1 hδ hKδ m
  have hΛ : ∀ m, Lam (d m) ≤ 2 ^ m * Lam δ := fun m => Lam_qsched_le hK1 hδ hKδ m
  have hrat : K * δ * 2 ^ (M + 1) ≤ 1 / 2 := hratio
  have hsum := geometric_domination_one (δ := δ) (β := K * δ) (lam := 2) (k := M + 1)
    (t := d) hδ (by positivity) (by norm_num) hd0 hβ hΛ hrat
  have hsummable : Summable fun m : ℕ => d m * Lam (d m) ^ (M + 1) := by
    have := summable_sched_gen (δ := δ) (p := (1:ℝ)) (β := K * δ) (lam := 2) (k := M + 1)
      (t := d) hδ zero_le_one (by positivity) (by norm_num) hd0 hβ hΛ
      (by rwa [Real.rpow_one])
    simpa only [Real.rpow_one] using this
  have hnn0 : (0:ℝ) ≤ CA * 2 ^ (M + 3) * D :=
    mul_nonneg (mul_nonneg hCA0.le (by positivity)) hD0.le
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun m => mul_nonneg hnn0 (mul_nonneg (hd0 m).le (Lam_pow_pos _ _).le))
    (hsummable.mul_left _), tsum_mul_left]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnn : (0:ℝ) ≤ CA * 2 ^ (M + 3) * D := by positivity
  calc CA * 2 ^ (M + 3) * D * ∑' m : ℕ, d m * Lam (d m) ^ (M + 1)
      ≤ CA * 2 ^ (M + 3) * D * (2 * (δ * Lam δ ^ (M + 1))) :=
        mul_le_mul_of_nonneg_left hsum hnn
    _ = CA * 2 ^ (M + 3) * D * 2 * δ * Lam δ ^ (M + 1) := by ring

/-- **Theorem 4.9 from the shell data**, mirroring `theorem3_gen`: the anticoncentration
hypothesis is supplied by `lemma7_prob_gen` rather than assumed. -/
theorem corollary_quad_gen {A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ}
    {Sig Rm : (Fin (M + 2) → ℝ) → ℝ} {ρ : ℝ} (hρ0 : 0 < ρ)
    (Dsh : ShellData A)
    (C : CycleData (Fin (M + 2) → ℝ)) (hd : C.d = M + 2) (hsig : ∀ y, C.sigt y = Sig y)
    (hz : Sig 0 = 0) (hSmeas : Measurable C.S) (hτmeas : Measurable C.τ)
    (hlead : leadConst A ≠ 0)
    (hS : ∀ y, Sig y = leadConst A * (krylov A y).det + Rm y)
    (hRmeas : Measurable Rm)
    {cR : ℝ} (hcR : 0 ≤ cR)
    (hRderiv : ∀ r : ℝ, 0 < r → r ≤ ρ → ∀ κ : Fin (M + 2),
        ∃ g : ℝ → (Fin (M + 2) → ℝ) → ℝ,
          (∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 →
              HasDerivAt (fun t => Rm (Dsh.Pm.mulVec (r • Function.update v κ t)) / r ^ (M + 2))
                (g t v) t)
            ∧ ∀ v t, ‖(Function.update v κ t : Fin (M + 2) → ℝ)‖ ≤ 1 → |g t v| ≤ cR * r)
    (B : SharpBound C) {cth : ℝ} (hcth0 : 0 < cth)
    (hcth : 16 * B.C₂ / max (8 * B.C₁) 1 ≤ cth)
    (P : (Fin (M + 2) → ℝ) → Prop)
    (hPz : ∀ z : Fin (M + 2) → ℝ, 0 < ‖z‖ → ‖z‖ ≤ C.ρ₁ → cth * (2:ℝ)⁻¹ * ‖z‖ ≤ C.τ z →
      P z) :
    ∃ Cst : ℝ, 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        max (8 * B.C₁) 1 * δ * 2 ^ (M + 1) ≤ 1 / 2 →
        cth * δ ≤ 1 →
        2 * δ ≤ ρ → 2 * δ ≤ C.ρ₁ →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
        (Measure.infinitePi (fun _ : ℕ => blockMeasure (M + 2)))
            {ω | ∃ m, ¬ ‖xProcG C x₀ (qsched (max (8 * B.C₁) 1) δ) m ω‖
                  ≤ qsched (max (8 * B.C₁) 1) δ m
                ∨ ¬ P (yProcG C x₀ (qsched (max (8 * B.C₁) 1) δ) m ω)}
          ≤ ENNReal.ofReal (Cst * δ * Lam δ ^ (M + 1)) :=
  corollary_quad C hd hsig hz hSmeas hτmeas
    (lemma7_prob_gen Dsh hcR hρ0 hlead hS hRmeas hRderiv) B hcth0 hcth P hPz

end Assembly

end MPE
