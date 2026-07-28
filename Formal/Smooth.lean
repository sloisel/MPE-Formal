import Mathlib

/-!
# Vanishing to higher order, from the mean value inequality

The `C³` version of Theorem 4.9 replaces exact degree counting (`Formal/Degree.lean`'s `LowDeg`)
by estimates on Taylor remainders.  Mathlib has **no multivariate Taylor theorem with
remainder** — `Analysis/Calculus/Taylor.lean` is `f : ℝ → ℝ` only — but none is needed: every
estimate wanted here is an iterated application of the mean value inequality on the segment
`[0,x]`, which is `Convex.norm_image_sub_le_of_norm_fderiv_le`.

The one workhorse is `norm_le_of_fderiv_le`: if `g 0 = 0` and `‖Dg‖ = O(‖·‖^p)` then
`‖g‖ = O(‖·‖^(p+1))`.  Applying it three times, to `D²f - D²f 0`, then to `Df - A - D²f 0 ·`,
then to `f - A· - q₂`, turns `f ∈ C³` into a second-order expansion with the two bounds the
construction needs.  The point is that the number of derivatives used is fixed at three,
independent of the dimension.
-/

namespace MPE

open Set Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The segment `[0,x]` -/

lemma norm_le_of_mem_segment_zero {x z : E} (hz : z ∈ segment ℝ (0 : E) x) : ‖z‖ ≤ ‖x‖ := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  rw [smul_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  calc b * ‖x‖ ≤ 1 * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
        linarith
    _ = ‖x‖ := one_mul _

lemma segment_zero_subset_closedBall {x : E} {R : ℝ} (hx : ‖x‖ ≤ R) :
    segment ℝ (0 : E) x ⊆ closedBall (0 : E) R := fun z hz => by
  rw [mem_closedBall, dist_zero_right]
  exact le_trans (norm_le_of_mem_segment_zero hz) hx

/-! ### The workhorse

If `g` vanishes at the origin and its derivative is `O(‖·‖^p)`, then `g` is `O(‖·‖^(p+1))`.
The mean value inequality is applied on the *segment* `[0,x]`, not on the whole ball: that is
what keeps the bound proportional to `‖x‖^(p+1)` rather than to `R^p‖x‖`. -/

theorem norm_le_of_fderiv_le {g : E → F} {K R : ℝ} {p : ℕ} (hK : 0 ≤ K)
    (hg0 : g 0 = 0)
    (hdiff : ∀ z ∈ closedBall (0 : E) R, DifferentiableAt ℝ g z)
    (hbd : ∀ z ∈ closedBall (0 : E) R, ‖fderiv ℝ g z‖ ≤ K * ‖z‖ ^ p)
    {x : E} (hx : ‖x‖ ≤ R) :
    ‖g x‖ ≤ K * ‖x‖ ^ (p + 1) := by
  have hsub : segment ℝ (0 : E) x ⊆ closedBall (0 : E) R := segment_zero_subset_closedBall hx
  have hmv : ‖g x - g 0‖ ≤ (K * ‖x‖ ^ p) * ‖x - 0‖ := by
    refine (convex_segment (0 : E) x).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => hdiff z (hsub hz)) (fun z hz => ?_) ?_ ?_
    · refine le_trans (hbd z (hsub hz)) ?_
      refine mul_le_mul_of_nonneg_left ?_ hK
      exact pow_le_pow_left₀ (norm_nonneg z) (norm_le_of_mem_segment_zero hz) p
    · exact left_mem_segment ℝ (0 : E) x
    · exact right_mem_segment ℝ (0 : E) x
  rw [hg0, sub_zero, sub_zero] at hmv
  calc ‖g x‖ ≤ K * ‖x‖ ^ p * ‖x‖ := hmv
    _ = K * ‖x‖ ^ (p + 1) := by rw [pow_succ]; ring

/-- The same, one order lower: a `C¹` map whose derivative is bounded is Lipschitz from the
origin. -/
theorem norm_le_of_fderiv_le_const {g : E → F} {K R : ℝ} (hK : 0 ≤ K) (hg0 : g 0 = 0)
    (hdiff : ∀ z ∈ closedBall (0 : E) R, DifferentiableAt ℝ g z)
    (hbd : ∀ z ∈ closedBall (0 : E) R, ‖fderiv ℝ g z‖ ≤ K)
    {x : E} (hx : ‖x‖ ≤ R) :
    ‖g x‖ ≤ K * ‖x‖ := by
  have := norm_le_of_fderiv_le (p := 0) hK hg0 hdiff (by simpa using hbd) hx
  simpa using this

/-! ### Bounding a continuous derivative on a closed ball

The constants above come from compactness: a `Cᵏ` map has bounded iterated derivatives on the
closed unit ball. -/

theorem exists_fderiv_bound_of_contDiffOn {g : E → F} [FiniteDimensional ℝ E] {R : ℝ}
    (hR : 0 ≤ R) (hg : ContDiffOn ℝ 1 g (closedBall (0 : E) R))
    (hopen : ∀ z ∈ closedBall (0 : E) R, DifferentiableAt ℝ g z)
    (hcont : ContinuousOn (fun z => fderiv ℝ g z) (closedBall (0 : E) R)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ closedBall (0 : E) R, ‖fderiv ℝ g z‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hcont
  refine ⟨max K 0, le_max_right _ _, fun z hz => le_trans (hK z hz) (le_max_left _ _)⟩

/-! ### Iterates

The construction forms `f^0,…,f^{n+2}`, so every estimate has to survive a fixed number of
compositions.  Two facts suffice, both by induction with the mean value inequality: the
iterates stay in the ball and grow at most geometrically, and two maps that agree to order `3`
have iterates that agree to order `3`.

Note the shrinking domain: `f^j` is controlled only for `‖x‖ ≤ R / L^j`.  In the polynomial
development `ρ₁ = 1`; here it becomes a small constant, which is why `CycleData.ρ₁` is a field
rather than hardwired. -/

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The iterates stay in the ball and grow at most geometrically. -/
theorem norm_iter_le {f : G → G} {L R : ℝ} (hR : 0 ≤ R) (hL : 1 ≤ L) (hf0 : f 0 = 0)
    (hdiff : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ f z)
    (hbd : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ f z‖ ≤ L) :
    ∀ (j : ℕ) (x : G), ‖x‖ ≤ R / L ^ j → ‖f^[j] x‖ ≤ L ^ j * ‖x‖ := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL
  intro j
  induction j with
  | zero => intro x _; simp
  | succ j ih =>
      intro x hx
      have hLj : (0:ℝ) < L ^ j := pow_pos hL0 j
      have hstep : L ^ j ≤ L ^ (j + 1) := pow_le_pow_right₀ hL (Nat.le_succ j)
      have hxj : ‖x‖ ≤ R / L ^ j := le_trans hx (by gcongr)
      have hij := ih x hxj
      -- the previous iterate is still in the ball
      have hmem : f^[j] x ∈ closedBall (0 : G) R := by
        rw [mem_closedBall, dist_zero_right]
        refine le_trans hij ?_
        calc L ^ j * ‖x‖ ≤ L ^ j * (R / L ^ (j + 1)) :=
              mul_le_mul_of_nonneg_left hx hLj.le
          _ = R / L := by rw [pow_succ]; field_simp
          _ ≤ R := by
              rw [div_le_iff₀ hL0]
              nlinarith
      -- one more application of the mean value inequality, at the point `f^[j] x`
      have hone : ‖f (f^[j] x)‖ ≤ L * ‖f^[j] x‖ := by
        have hseg : ‖(f^[j] x : G)‖ ≤ R := by
          rw [mem_closedBall, dist_zero_right] at hmem; exact hmem
        exact norm_le_of_fderiv_le_const hL0.le hf0 hdiff hbd hseg
      rw [Function.iterate_succ_apply']
      calc ‖f (f^[j] x)‖ ≤ L * ‖f^[j] x‖ := hone
        _ ≤ L * (L ^ j * ‖x‖) := mul_le_mul_of_nonneg_left hij hL0.le
        _ = L ^ (j + 1) * ‖x‖ := by rw [pow_succ]; ring

/-- **Two maps agreeing to order `3` have iterates agreeing to order `3`.**  This is the
value half of the comparison estimate: it lets a `C³` map be compared with its quadratic
Taylor truncation through the `n+2` iterations the construction forms.  The constant grows
geometrically in the number of iterations, which is harmless because that number is fixed. -/
theorem norm_iter_sub_le {f g : G → G} {L R e : ℝ} (hR : 0 ≤ R) (hL : 1 ≤ L) (he : 0 ≤ e)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfd : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ f z)
    (hgd : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ g z)
    (hfb : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ f z‖ ≤ L)
    (hgb : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ g z‖ ≤ L)
    (hfg : ∀ z ∈ closedBall (0 : G) R, ‖f z - g z‖ ≤ e * ‖z‖ ^ 3) :
    ∀ (j : ℕ) (x : G), ‖x‖ ≤ R / L ^ j →
      ‖f^[j] x - g^[j] x‖ ≤ e * j * L ^ (3 * j) * ‖x‖ ^ 3 := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL
  intro j
  induction j with
  | zero => intro x _; simp
  | succ j ih =>
      intro x hx
      have hLj : (0:ℝ) < L ^ j := pow_pos hL0 j
      have hstep : L ^ j ≤ L ^ (j + 1) := pow_le_pow_right₀ hL (Nat.le_succ j)
      have hxj : ‖x‖ ≤ R / L ^ j := le_trans hx (by gcongr)
      have hxn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
      -- both previous iterates lie in the ball
      have hball : ∀ h : G → G, h 0 = 0 →
          (∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ h z) →
          (∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ h z‖ ≤ L) →
          ‖h^[j] x‖ ≤ L ^ j * ‖x‖ ∧ h^[j] x ∈ closedBall (0 : G) R := by
        intro h h0 hd hb
        have hj := norm_iter_le hR hL h0 hd hb j x hxj
        refine ⟨hj, ?_⟩
        rw [mem_closedBall, dist_zero_right]
        refine le_trans hj ?_
        calc L ^ j * ‖x‖ ≤ L ^ j * (R / L ^ (j + 1)) :=
              mul_le_mul_of_nonneg_left hx hLj.le
          _ = R / L := by rw [pow_succ]; field_simp
          _ ≤ R := by rw [div_le_iff₀ hL0]; nlinarith
      obtain ⟨hfj, hfmem⟩ := hball f hf0 hfd hfb
      obtain ⟨-, hgmem⟩ := hball g hg0 hgd hgb
      have hprev := ih x hxj
      -- split into "`f` versus `g` at the same point" and "`g` is `L`-Lipschitz"
      have hsplit : f (f^[j] x) - g (g^[j] x)
          = (f (f^[j] x) - g (f^[j] x)) + (g (f^[j] x) - g (g^[j] x)) := by abel
      have h1 : ‖f (f^[j] x) - g (f^[j] x)‖ ≤ e * (L ^ j * ‖x‖) ^ 3 := by
        refine le_trans (hfg _ hfmem) ?_
        refine mul_le_mul_of_nonneg_left ?_ he
        exact pow_le_pow_left₀ (norm_nonneg _) hfj 3
      have h2 : ‖g (f^[j] x) - g (g^[j] x)‖ ≤ L * ‖f^[j] x - g^[j] x‖ :=
        (convex_closedBall (0 : G) R).norm_image_sub_le_of_norm_fderiv_le hgd hgb hgmem hfmem
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hsplit]
      have hkey : e * (L ^ j * ‖x‖) ^ 3 + L * (e * j * L ^ (3 * j) * ‖x‖ ^ 3)
          ≤ e * ((j + 1 : ℕ) : ℝ) * L ^ (3 * (j + 1)) * ‖x‖ ^ 3 := by
        have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hexp : L ^ (3 * (j + 1)) = L ^ (3 * j) * L ^ 3 := by
          rw [← pow_add, Nat.mul_succ]
        have hcube : (L ^ j * ‖x‖) ^ 3 = L ^ (3 * j) * ‖x‖ ^ 3 := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm j 3]
        rw [hexp, hcube]
        have hLj3 : (0:ℝ) < L ^ (3 * j) := pow_pos hL0 _
        have hx3 : (0:ℝ) ≤ ‖x‖ ^ 3 := by positivity
        have hjn : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have hL3 : L ≤ L ^ 3 := by nlinarith [sq_nonneg L, sq_nonneg (L - 1)]
        nlinarith [mul_nonneg (mul_nonneg he hjn) (mul_nonneg hLj3.le hx3),
          mul_nonneg he (mul_nonneg hLj3.le hx3)]
      refine le_trans (le_trans (norm_add_le _ _) (add_le_add h1 ?_)) hkey
      exact le_trans h2 (mul_le_mul_of_nonneg_left hprev hL0.le)

/-! ### Derivatives of iterates

The same induction with the chain rule in place of the mean value inequality. -/

/-- The `j`-th iterate of a point of norm `≤ R/L^(j+1)` lies in the ball. -/
lemma iter_mem_closedBall {f : G → G} {L R : ℝ} (hR : 0 ≤ R) (hL : 1 ≤ L) (hf0 : f 0 = 0)
    (hdiff : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ f z)
    (hbd : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ f z‖ ≤ L)
    {j : ℕ} {x : G} (hx : ‖x‖ ≤ R / L ^ (j + 1)) :
    f^[j] x ∈ closedBall (0 : G) R := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL
  have hLj : (0:ℝ) < L ^ j := pow_pos hL0 j
  have hstep : L ^ j ≤ L ^ (j + 1) := pow_le_pow_right₀ hL (Nat.le_succ j)
  have hxj : ‖x‖ ≤ R / L ^ j := le_trans hx (by gcongr)
  rw [mem_closedBall, dist_zero_right]
  refine le_trans (norm_iter_le hR hL hf0 hdiff hbd j x hxj) ?_
  calc L ^ j * ‖x‖ ≤ L ^ j * (R / L ^ (j + 1)) := mul_le_mul_of_nonneg_left hx hLj.le
    _ = R / L := by rw [pow_succ]; field_simp
    _ ≤ R := by rw [div_le_iff₀ hL0]; nlinarith

/-- The iterates are differentiable, with derivative bounded by `L^j`. -/
theorem iter_differentiableAt {f : G → G} {L R : ℝ} (hR : 0 ≤ R) (hL : 1 ≤ L) (hf0 : f 0 = 0)
    (hdiff : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ f z)
    (hbd : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ f z‖ ≤ L) :
    ∀ (j : ℕ) (x : G), ‖x‖ ≤ R / L ^ j →
      DifferentiableAt ℝ (f^[j]) x ∧ ‖fderiv ℝ (f^[j]) x‖ ≤ L ^ j := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL
  intro j
  induction j with
  | zero =>
      intro x _
      have h0 : (f^[0]) = (id : G → G) := by funext z; simp
      refine ⟨by rw [h0]; exact differentiableAt_id, ?_⟩
      rw [h0, fderiv_id]
      simpa using ContinuousLinearMap.norm_id_le
  | succ j ih =>
      intro x hx
      have hmem : f^[j] x ∈ closedBall (0 : G) R :=
        iter_mem_closedBall hR hL hf0 hdiff hbd hx
      have hstep : L ^ j ≤ L ^ (j + 1) := pow_le_pow_right₀ hL (Nat.le_succ j)
      have hLj : (0:ℝ) < L ^ j := pow_pos hL0 j
      have hxj : ‖x‖ ≤ R / L ^ j := le_trans hx (by gcongr)
      obtain ⟨hdj, hnj⟩ := ih x hxj
      have hfun : (f^[j + 1]) = f ∘ (f^[j]) := Function.iterate_succ' f j
      refine ⟨by rw [hfun]; exact (hdiff _ hmem).comp x hdj, ?_⟩
      rw [hfun, fderiv_comp x (hdiff _ hmem) hdj]
      calc ‖(fderiv ℝ f (f^[j] x)).comp (fderiv ℝ (f^[j]) x)‖
          ≤ ‖fderiv ℝ f (f^[j] x)‖ * ‖fderiv ℝ (f^[j]) x‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ L * L ^ j := mul_le_mul (hbd _ hmem) hnj (norm_nonneg _) hL0.le
        _ = L ^ (j + 1) := by rw [pow_succ]; ring

/-- **The derivative half of the comparison.**  Besides the hypotheses of `norm_iter_sub_le`
this needs `Dg` Lipschitz — i.e. `g` of class `C²` — which is where the second of the three
available derivatives is spent.

The constant is stated uniformly for `j ≤ N` rather than `j`-by-`j`.  That is not cosmetic: the
recursion is `c_{j+1} ≤ B + L·c_j`, and it telescopes to `c_j ≤ B·j·L^j` only when `B` does not
itself depend on `j`. -/
theorem norm_fderiv_iter_sub_le {f g : G → G} {L L₂ R e : ℝ} (N : ℕ)
    (hR : 0 ≤ R) (hL : 1 ≤ L) (he : 0 ≤ e) (hL₂ : 0 ≤ L₂)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfd : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ f z)
    (hgd : ∀ z ∈ closedBall (0 : G) R, DifferentiableAt ℝ g z)
    (hfb : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ f z‖ ≤ L)
    (hgb : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ g z‖ ≤ L)
    (hfg : ∀ z ∈ closedBall (0 : G) R, ‖f z - g z‖ ≤ e * ‖z‖ ^ 3)
    (hfgd : ∀ z ∈ closedBall (0 : G) R, ‖fderiv ℝ f z - fderiv ℝ g z‖ ≤ e * ‖z‖ ^ 2)
    (hglip : ∀ a ∈ closedBall (0 : G) R, ∀ b ∈ closedBall (0 : G) R,
      ‖fderiv ℝ g a - fderiv ℝ g b‖ ≤ L₂ * ‖a - b‖) :
    ∀ j ≤ N, ∀ x : G, ‖x‖ ≤ R / L ^ N → ‖x‖ ≤ 1 →
      ‖fderiv ℝ (f^[j]) x - fderiv ℝ (g^[j]) x‖
        ≤ (e * L ^ (3 * N) + L₂ * e * (N : ℝ) * L ^ (4 * N)) * j * L ^ j * ‖x‖ ^ 2 := by
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL
  set B : ℝ := e * L ^ (3 * N) + L₂ * e * (N : ℝ) * L ^ (4 * N) with hBdef
  have hB0 : (0:ℝ) ≤ B := by
    rw [hBdef]
    have h1 : (0:ℝ) < L ^ (3 * N) := pow_pos hL0 _
    have h2 : (0:ℝ) < L ^ (4 * N) := pow_pos hL0 _
    have h3 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    positivity
  intro j
  induction j with
  | zero =>
      intro _ x _ _
      have h0 : (f^[0]) = (id : G → G) := by funext z; simp
      have h0' : (g^[0]) = (id : G → G) := by funext z; simp
      rw [h0, h0']
      simp
  | succ j ih =>
      intro hjN x hx hx1
      have hjle : j ≤ N := by omega
      have hLN : (0:ℝ) < L ^ N := pow_pos hL0 N
      have hstep : L ^ (j + 1) ≤ L ^ N := pow_le_pow_right₀ hL hjN
      have hxj : ‖x‖ ≤ R / L ^ (j + 1) := le_trans hx (by gcongr)
      have hxj' : ‖x‖ ≤ R / L ^ j := le_trans hx (by gcongr)
      have hxn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
      have hx2 : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
      have hfmem : f^[j] x ∈ closedBall (0 : G) R :=
        iter_mem_closedBall hR hL hf0 hfd hfb hxj
      have hgmem : g^[j] x ∈ closedBall (0 : G) R :=
        iter_mem_closedBall hR hL hg0 hgd hgb hxj
      obtain ⟨hdfj, hnfj⟩ := iter_differentiableAt hR hL hf0 hfd hfb j x hxj'
      obtain ⟨hdgj, hngj⟩ := iter_differentiableAt hR hL hg0 hgd hgb j x hxj'
      have hval := norm_iter_sub_le hR hL he hf0 hg0 hfd hgd hfb hgb hfg j x hxj'
      have hprev := ih hjle x hx hx1
      have hfj := norm_iter_le hR hL hf0 hfd hfb j x hxj'
      have hffun : (f^[j + 1]) = f ∘ (f^[j]) := Function.iterate_succ' f j
      have hgfun : (g^[j + 1]) = g ∘ (g^[j]) := Function.iterate_succ' g j
      rw [hffun, hgfun, fderiv_comp x (hfd _ hfmem) hdfj, fderiv_comp x (hgd _ hgmem) hdgj]
      set Af := fderiv ℝ f (f^[j] x) with hAf
      set Ag := fderiv ℝ g (g^[j] x) with hAg
      set Ag' := fderiv ℝ g (f^[j] x) with hAg'
      set Bf := fderiv ℝ (f^[j]) x with hBf
      set Bg := fderiv ℝ (g^[j]) x with hBg
      have hsplit : Af.comp Bf - Ag.comp Bg
          = (Af - Ag').comp Bf + ((Ag' - Ag).comp Bf + Ag.comp (Bf - Bg)) := by
        ext z
        simp only [ContinuousLinearMap.coe_comp', ContinuousLinearMap.add_apply,
          ContinuousLinearMap.sub_apply, Function.comp_apply, ContinuousLinearMap.map_sub]
        abel
      rw [hsplit]
      -- the three terms of the chain rule
      have hT1 : ‖(Af - Ag').comp Bf‖ ≤ (e * L ^ (3 * N)) * ‖x‖ ^ 2 := by
        refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        have hstep1 : ‖Af - Ag'‖ ≤ e * (L ^ j * ‖x‖) ^ 2 := by
          refine le_trans (hfgd _ hfmem) ?_
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hfj 2) he
        calc ‖Af - Ag'‖ * ‖Bf‖ ≤ (e * (L ^ j * ‖x‖) ^ 2) * L ^ j :=
              mul_le_mul hstep1 hnfj (norm_nonneg _) (by positivity)
          _ = e * L ^ (3 * j) * ‖x‖ ^ 2 := by
              have h1 : (L ^ j * ‖x‖) ^ 2 = L ^ (2 * j) * ‖x‖ ^ 2 := by
                rw [mul_pow, ← pow_mul, Nat.mul_comm j 2]
              have h2 : L ^ (2 * j) * L ^ j = L ^ (3 * j) := by
                rw [← pow_add]; congr 1; omega
              rw [h1]
              calc e * (L ^ (2 * j) * ‖x‖ ^ 2) * L ^ j
                  = e * (L ^ (2 * j) * L ^ j) * ‖x‖ ^ 2 := by ring
                _ = e * L ^ (3 * j) * ‖x‖ ^ 2 := by rw [h2]
          _ ≤ e * L ^ (3 * N) * ‖x‖ ^ 2 := by gcongr
      have hT2 : ‖(Ag' - Ag).comp Bf‖ ≤ (L₂ * e * (N : ℝ) * L ^ (4 * N)) * ‖x‖ ^ 2 := by
        refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        have hstep2 : ‖Ag' - Ag‖ ≤ L₂ * (e * j * L ^ (3 * j) * ‖x‖ ^ 3) :=
          le_trans (hglip _ hfmem _ hgmem) (mul_le_mul_of_nonneg_left hval hL₂)
        have hjn : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
        calc ‖Ag' - Ag‖ * ‖Bf‖ ≤ (L₂ * (e * j * L ^ (3 * j) * ‖x‖ ^ 3)) * L ^ j :=
              mul_le_mul hstep2 hnfj (norm_nonneg _) (by positivity)
          _ = L₂ * e * (j:ℝ) * L ^ (4 * j) * ‖x‖ ^ 3 := by
              have h2 : L ^ (3 * j) * L ^ j = L ^ (4 * j) := by
                rw [← pow_add]; congr 1; omega
              calc L₂ * (e * (j:ℝ) * L ^ (3 * j) * ‖x‖ ^ 3) * L ^ j
                  = L₂ * e * (j:ℝ) * (L ^ (3 * j) * L ^ j) * ‖x‖ ^ 3 := by ring
                _ = L₂ * e * (j:ℝ) * L ^ (4 * j) * ‖x‖ ^ 3 := by rw [h2]
          _ ≤ L₂ * e * (N:ℝ) * L ^ (4 * N) * ‖x‖ ^ 2 := by
              have hx32 : ‖x‖ ^ 3 ≤ ‖x‖ ^ 2 := by
                rw [pow_succ]; nlinarith [pow_nonneg hxn 2]
              have hjN' : (j:ℝ) ≤ (N:ℝ) := Nat.cast_le.mpr hjle
              have hpw : L ^ (4 * j) ≤ L ^ (4 * N) := pow_le_pow_right₀ hL (by omega)
              gcongr <;> positivity
      have hT3 : ‖Ag.comp (Bf - Bg)‖ ≤ L * (B * j * L ^ j * ‖x‖ ^ 2) := by
        refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
        exact mul_le_mul (hgb _ hgmem) hprev (norm_nonneg _) hL0.le
      refine le_trans (le_trans (norm_add_le _ _)
        (add_le_add hT1 (le_trans (norm_add_le _ _) (add_le_add hT2 hT3)))) ?_
      -- collect: `B‖x‖² + L·B j L^j‖x‖² ≤ B (j+1) L^(j+1)‖x‖²`
      have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hone : (1:ℝ) ≤ L ^ (j + 1) := one_le_pow₀ hL
      have hjn : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have hLj1 : (0:ℝ) < L ^ (j + 1) := pow_pos hL0 _
      have hrw : L * (B * (j:ℝ) * L ^ j * ‖x‖ ^ 2) = B * (j:ℝ) * L ^ (j + 1) * ‖x‖ ^ 2 := by
        rw [pow_succ]; ring
      rw [hrw, hBdef]
      nlinarith [mul_nonneg hB0 hx2, mul_nonneg (mul_nonneg hB0 hjn) hx2,
        mul_nonneg (mul_nonneg hB0 hjn) (mul_nonneg hLj1.le hx2), mul_nonneg hB0 hx2]

/-! ## `Van`: the quantitative analogue of `LowDeg`

`Formal/Degree.lean`'s `LowDeg k p` says every monomial of `p` has degree at least `k`.  Its
`C³` counterpart is a pair of bounds, on the value and on the derivative:

    Van ρ k C g   ↔   ‖g y‖ ≤ C‖y‖^(k+1)  and  ‖Dg y‖ ≤ C‖y‖^k   on the ball of radius ρ.

So `Van ρ k C` reads "`g` vanishes to order `k+1`".  The point of carrying the derivative bound
inside the predicate is that the whole `LowDeg` calculus then transfers — sums, products,
determinants, adjugates, `mulVec` — with the *same* bookkeeping of orders, and the analytic
content is confined to the two constructors below.

The indexing is by `k` rather than by the order `k+1` to keep every exponent a `ℕ` sum: there
is no truncated subtraction anywhere. -/

/-- `g` vanishes to order `k+1` at the origin, quantitatively, on the ball of radius `ρ`. -/
structure Van (ρ : ℝ) (k : ℕ) (C : ℝ) (g : E → F) : Prop where
  diff : ∀ y ∈ closedBall (0 : E) ρ, DifferentiableAt ℝ g y
  val : ∀ y ∈ closedBall (0 : E) ρ, ‖g y‖ ≤ C * ‖y‖ ^ (k + 1)
  der : ∀ y ∈ closedBall (0 : E) ρ, ‖fderiv ℝ g y‖ ≤ C * ‖y‖ ^ k

namespace Van

variable {ρ : ℝ} {k k' : ℕ} {C C' : ℝ} {g h : E → F}

/-- The constant may be enlarged. -/
lemma mono_const (hg : Van ρ k C g) (hCC : C ≤ C') : Van ρ k C' g where
  diff := hg.diff
  val := fun y hy =>
    le_trans (hg.val y hy) (mul_le_mul_of_nonneg_right hCC (by positivity))
  der := fun y hy =>
    le_trans (hg.der y hy) (mul_le_mul_of_nonneg_right hCC (by positivity))

/-- The order may be lowered, on a ball of radius at most `1`. -/
lemma mono_exp (hg : Van ρ k C g) (hρ : ρ ≤ 1) (hC : 0 ≤ C) (hk : k' ≤ k) :
    Van ρ k' C g where
  diff := hg.diff
  val := fun y hy => by
    have hy1 : ‖y‖ ≤ 1 := by
      rw [mem_closedBall, dist_zero_right] at hy; exact le_trans hy hρ
    refine le_trans (hg.val y hy) (mul_le_mul_of_nonneg_left ?_ hC)
    exact pow_le_pow_of_le_one (norm_nonneg y) hy1 (by omega)
  der := fun y hy => by
    have hy1 : ‖y‖ ≤ 1 := by
      rw [mem_closedBall, dist_zero_right] at hy; exact le_trans hy hρ
    refine le_trans (hg.der y hy) (mul_le_mul_of_nonneg_left ?_ hC)
    exact pow_le_pow_of_le_one (norm_nonneg y) hy1 hk

lemma add (hg : Van ρ k C g) (hh : Van ρ k C' h) : Van ρ k (C + C') (fun y => g y + h y) where
  diff := fun y hy => (hg.diff y hy).add (hh.diff y hy)
  val := fun y hy => by
    refine le_trans (norm_add_le _ _) ?_
    rw [add_mul]
    exact add_le_add (hg.val y hy) (hh.val y hy)
  der := fun y hy => by
    have hd : HasFDerivAt (fun z => g z + h z) (fderiv ℝ g y + fderiv ℝ h y) y :=
      (hg.diff y hy).hasFDerivAt.add (hh.diff y hy).hasFDerivAt
    rw [hd.fderiv]
    refine le_trans (norm_add_le _ _) ?_
    rw [add_mul]
    exact add_le_add (hg.der y hy) (hh.der y hy)

lemma neg (hg : Van ρ k C g) : Van ρ k C (fun y => -g y) where
  diff := fun y hy => (hg.diff y hy).neg
  val := fun y hy => by rw [norm_neg]; exact hg.val y hy
  der := fun y hy => by
    have hd : HasFDerivAt (fun z => -g z) (-fderiv ℝ g y) y :=
      (hg.diff y hy).hasFDerivAt.neg
    rw [hd.fderiv, norm_neg]
    exact hg.der y hy

lemma sub (hg : Van ρ k C g) (hh : Van ρ k C' h) : Van ρ k (C + C') (fun y => g y - h y) := by
  have hres := hg.add hh.neg
  simpa [sub_eq_add_neg] using hres

/-- **Products add orders.**  `Van k` times `Van k'` is `Van (k + k' + 1)`: the value bound
multiplies, and the product rule contributes two cross terms, hence the factor `2`. -/
lemma mul {a b : E → ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (ha : Van ρ k C a) (hb : Van ρ k' C' b) :
    Van ρ (k + k' + 1) (2 * (C * C')) (fun y => a y * b y) where
  diff := fun y hy => (ha.diff y hy).mul (hb.diff y hy)
  val := fun y hy => by
    have hpw : ‖y‖ ^ (k + 1) * ‖y‖ ^ (k' + 1) = ‖y‖ ^ (k + k' + 1 + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [norm_mul]
    calc ‖a y‖ * ‖b y‖ ≤ (C * ‖y‖ ^ (k + 1)) * (C' * ‖y‖ ^ (k' + 1)) :=
          mul_le_mul (ha.val y hy) (hb.val y hy) (norm_nonneg _) (by positivity)
      _ = (C * C') * (‖y‖ ^ (k + 1) * ‖y‖ ^ (k' + 1)) := by ring
      _ = (C * C') * ‖y‖ ^ (k + k' + 1 + 1) := by rw [hpw]
      _ ≤ 2 * (C * C') * ‖y‖ ^ (k + k' + 1 + 1) := by
          nlinarith [pow_nonneg (norm_nonneg y) (k + k' + 1 + 1), mul_nonneg hC hC']
  der := fun y hy => by
    have hd : HasFDerivAt (fun z => a z * b z)
        (a y • fderiv ℝ b y + b y • fderiv ℝ a y) y :=
      (ha.diff y hy).hasFDerivAt.mul (hb.diff y hy).hasFDerivAt
    rw [hd.fderiv]
    refine le_trans (norm_add_le _ _) ?_
    have hpw : ‖y‖ ^ (k + 1) * ‖y‖ ^ k' = ‖y‖ ^ (k + k' + 1) := by
      rw [← pow_add]; congr 1; omega
    have hpw' : ‖y‖ ^ (k' + 1) * ‖y‖ ^ k = ‖y‖ ^ (k + k' + 1) := by
      rw [← pow_add]; congr 1; omega
    have h1 : ‖a y • fderiv ℝ b y‖ ≤ (C * ‖y‖ ^ (k + 1)) * (C' * ‖y‖ ^ k') := by
      rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul (ha.val y hy) (hb.der y hy) (norm_nonneg _) (by positivity)
    have h2 : ‖b y • fderiv ℝ a y‖ ≤ (C' * ‖y‖ ^ (k' + 1)) * (C * ‖y‖ ^ k) := by
      rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul (hb.val y hy) (ha.der y hy) (norm_nonneg _) (by positivity)
    calc ‖a y • fderiv ℝ b y‖ + ‖b y • fderiv ℝ a y‖
        ≤ (C * ‖y‖ ^ (k + 1)) * (C' * ‖y‖ ^ k') + (C' * ‖y‖ ^ (k' + 1)) * (C * ‖y‖ ^ k) :=
          add_le_add h1 h2
      _ = (C * C') * (‖y‖ ^ (k + 1) * ‖y‖ ^ k') + (C * C') * (‖y‖ ^ (k' + 1) * ‖y‖ ^ k) := by
          ring
      _ = 2 * (C * C') * ‖y‖ ^ (k + k' + 1) := by rw [hpw, hpw']; ring

/-- The same for a scalar times a vector-valued map. -/
lemma smul {a : E → ℝ} {b : E → F} (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (ha : Van ρ k C a) (hb : Van ρ k' C' b) :
    Van ρ (k + k' + 1) (2 * (C * C')) (fun y => a y • b y) where
  diff := fun y hy => (ha.diff y hy).smul (hb.diff y hy)
  val := fun y hy => by
    have hpw : ‖y‖ ^ (k + 1) * ‖y‖ ^ (k' + 1) = ‖y‖ ^ (k + k' + 1 + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs]
    calc ‖a y‖ * ‖b y‖ ≤ (C * ‖y‖ ^ (k + 1)) * (C' * ‖y‖ ^ (k' + 1)) :=
          mul_le_mul (ha.val y hy) (hb.val y hy) (norm_nonneg _) (by positivity)
      _ = (C * C') * (‖y‖ ^ (k + 1) * ‖y‖ ^ (k' + 1)) := by ring
      _ = (C * C') * ‖y‖ ^ (k + k' + 1 + 1) := by rw [hpw]
      _ ≤ 2 * (C * C') * ‖y‖ ^ (k + k' + 1 + 1) := by
          nlinarith [pow_nonneg (norm_nonneg y) (k + k' + 1 + 1), mul_nonneg hC hC']
  der := fun y hy => by
    have hd : HasFDerivAt (fun z => a z • b z)
        (a y • fderiv ℝ b y + (fderiv ℝ a y).smulRight (b y)) y :=
      (ha.diff y hy).hasFDerivAt.smul (hb.diff y hy).hasFDerivAt
    rw [hd.fderiv]
    refine le_trans (norm_add_le _ _) ?_
    have hpw : ‖y‖ ^ (k + 1) * ‖y‖ ^ k' = ‖y‖ ^ (k + k' + 1) := by
      rw [← pow_add]; congr 1; omega
    have hpw' : ‖y‖ ^ (k' + 1) * ‖y‖ ^ k = ‖y‖ ^ (k + k' + 1) := by
      rw [← pow_add]; congr 1; omega
    have h1 : ‖a y • fderiv ℝ b y‖ ≤ (C * ‖y‖ ^ (k + 1)) * (C' * ‖y‖ ^ k') := by
      rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul (ha.val y hy) (hb.der y hy) (norm_nonneg _) (by positivity)
    have h2 : ‖(fderiv ℝ a y).smulRight (b y)‖ ≤ (C' * ‖y‖ ^ (k' + 1)) * (C * ‖y‖ ^ k) := by
      rw [ContinuousLinearMap.norm_smulRight_apply, mul_comm]
      exact mul_le_mul (hb.val y hy) (ha.der y hy) (norm_nonneg _) (by positivity)
    calc ‖a y • fderiv ℝ b y‖ + ‖(fderiv ℝ a y).smulRight (b y)‖
        ≤ (C * ‖y‖ ^ (k + 1)) * (C' * ‖y‖ ^ k') + (C' * ‖y‖ ^ (k' + 1)) * (C * ‖y‖ ^ k) :=
          add_le_add h1 h2
      _ = (C * C') * (‖y‖ ^ (k + 1) * ‖y‖ ^ k') + (C * C') * (‖y‖ ^ (k' + 1) * ‖y‖ ^ k) := by
          ring
      _ = 2 * (C * C') * ‖y‖ ^ (k + k' + 1) := by rw [hpw, hpw']; ring

lemma zero_van : Van ρ k 0 (fun _ : E => (0 : F)) where
  diff := fun _ _ => differentiableAt_const 0
  val := fun y _ => by simp
  der := fun y _ => by
    have : fderiv ℝ (fun _ : E => (0 : F)) y = 0 := fderiv_const_apply 0
    rw [this]
    simp

lemma const_mul {a : E → ℝ} (c : ℝ) (ha : Van ρ k C a) :
    Van ρ k (|c| * C) (fun y => c * a y) where
  diff := fun y hy => (differentiableAt_const c).mul (ha.diff y hy)
  val := fun y hy => by
    rw [norm_mul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (ha.val y hy) (abs_nonneg c)
  der := fun y hy => by
    have hd : HasFDerivAt (fun z => c * a z) (c • fderiv ℝ a y) y := by
      simpa using ((ha.diff y hy).hasFDerivAt).const_mul c
    rw [hd.fderiv, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (ha.der y hy) (abs_nonneg c)

/-- A finite sum, with the constants adding. -/
lemma sum {ι : Type*} (s : Finset ι) {g : ι → E → F} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, Van ρ k C (g i)) :
    Van ρ k (s.card * C) (fun y => ∑ i ∈ s, g i y) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (zero_van : Van ρ k 0 (fun _ : E => (0 : F)))
  | insert a s ha ih =>
      have hstep := (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hfun : (fun y => ∑ i ∈ insert a s, g i y)
          = fun y => g a y + ∑ i ∈ s, g i y := by
        funext y; rw [Finset.sum_insert ha]
      rw [hfun]
      refine hstep.mono_const ?_
      rw [Finset.card_insert_of_notMem ha]
      push_cast
      ring_nf
      rfl

/-- **A product of `m+1` factors each vanishing linearly vanishes to order `m+1`.**  Each
application of the product rule costs a factor `2`, hence the constant. -/
lemma prod_fin (hC : 0 ≤ C) : ∀ (m : ℕ) (a : Fin (m + 1) → E → ℝ),
    (∀ i, Van ρ 0 C (a i)) →
      Van ρ m (2 ^ m * C ^ (m + 1)) (fun y => ∏ i, a i y) := by
  intro m
  induction m with
  | zero =>
      intro a ha
      have hfun : (fun y => ∏ i : Fin 1, a i y) = a 0 := by
        funext y; simp
      rw [hfun]
      simpa using ha 0
  | succ m ih =>
      intro a ha
      have htail := ih (fun i => a i.succ) (fun i => ha i.succ)
      have hhead := ha 0
      have hstep := hhead.mul hC (by positivity) htail
      rw [Nat.zero_add] at hstep
      have hfun : (fun y => ∏ i : Fin (m + 1 + 1), a i y)
          = fun y => a 0 y * ∏ i : Fin (m + 1), a i.succ y := by
        funext y; rw [Fin.prod_univ_succ]
      rw [hfun]
      refine hstep.mono_const (le_of_eq ?_)
      rw [pow_succ, pow_succ]
      ring

/-- **Comparison of products.**  Two products of `m+1` linearly-vanishing factors, whose
corresponding factors agree to order `3`, agree to order `m+3` — that is, they gain the
*full* two extra orders on top of the naive `m+1`.  This is the engine of the `C³`
argument: it is what lets a `C³` map be replaced by its quadratic Taylor truncation
everywhere in the MPE construction without losing the sharp exponent.

Telescoping one factor at a time: `a₀·A - b₀·B = (a₀-b₀)·A + b₀·(A-B)`. -/
lemma prod_sub {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (d : ℕ) :
    ∀ (m : ℕ) (a b : Fin (m + 1) → E → ℝ),
      (∀ i, Van ρ 0 C (a i)) → (∀ i, Van ρ 0 C (b i)) →
      (∀ i, Van ρ d D (fun y => a i y - b i y)) →
      ∃ K : ℝ, 0 ≤ K ∧ Van ρ (m + d) K (fun y => (∏ i, a i y) - ∏ i, b i y) := by
  intro m
  induction m with
  | zero =>
      intro a b _ _ hab
      refine ⟨D, hD, ?_⟩
      have hfun : (fun y => (∏ i : Fin 1, a i y) - ∏ i : Fin 1, b i y)
          = fun y => a 0 y - b 0 y := by funext y; simp
      rw [hfun, Nat.zero_add]
      exact hab 0
  | succ m ih =>
      intro a b ha hb hab
      obtain ⟨K, hK, hAB⟩ := ih (fun i => a i.succ) (fun i => b i.succ)
        (fun i => ha i.succ) (fun i => hb i.succ) (fun i => hab i.succ)
      have hpc : (0:ℝ) ≤ 2 ^ m * C ^ (m + 1) := mul_nonneg (by positivity) (pow_nonneg hC _)
      have hprodA := Van.prod_fin hC m (fun i => a i.succ) (fun i => ha i.succ)
      have h1 := Van.mul hD hpc (hab 0) hprodA
      have h2 := Van.mul hC hK (hb 0) hAB
      rw [show d + m + 1 = m + 1 + d from by omega] at h1
      rw [show 0 + (m + d) + 1 = m + 1 + d from by omega] at h2
      refine ⟨2 * (D * (2 ^ m * C ^ (m + 1))) + 2 * (C * K), ?_, ?_⟩
      · have := mul_nonneg hD hpc
        have := mul_nonneg hC hK
        linarith
      · have hsum := h1.add h2
        have hpa : ∀ y, (∏ i : Fin (m + 1 + 1), a i y) = a 0 y * ∏ i : Fin (m + 1), a i.succ y :=
          fun y => Fin.prod_univ_succ (fun i => a i y)
        have hpb : ∀ y, (∏ i : Fin (m + 1 + 1), b i y) = b 0 y * ∏ i : Fin (m + 1), b i.succ y :=
          fun y => Fin.prod_univ_succ (fun i => b i y)
        have hfun : (fun y => (∏ i : Fin (m + 1 + 1), a i y) - ∏ i : Fin (m + 1 + 1), b i y)
            = fun y => (a 0 y - b 0 y) * (∏ i : Fin (m + 1), a i.succ y)
                + b 0 y * ((∏ i : Fin (m + 1), a i.succ y) - ∏ i : Fin (m + 1), b i.succ y) := by
          funext y
          rw [hpa y, hpb y]
          ring
        rw [hfun]
        exact hsum


/-- Postcomposition with a fixed continuous linear map. -/
lemma clm_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (hC : 0 ≤ C) (hg : Van ρ k C g) :
    Van ρ k (‖L‖ * C) (fun y => L (g y)) where
  diff := fun y hy => L.differentiableAt.comp y (hg.diff y hy)
  val := fun y hy => by
    calc ‖L (g y)‖ ≤ ‖L‖ * ‖g y‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (C * ‖y‖ ^ (k + 1)) := mul_le_mul_of_nonneg_left (hg.val y hy) (norm_nonneg L)
      _ = ‖L‖ * C * ‖y‖ ^ (k + 1) := by ring
  der := fun y hy => by
    have hd : HasFDerivAt (fun z => L (g z)) (L.comp (fderiv ℝ g y)) y :=
      L.hasFDerivAt.comp y (hg.diff y hy).hasFDerivAt
    rw [hd.fderiv]
    calc ‖L.comp (fderiv ℝ g y)‖ ≤ ‖L‖ * ‖fderiv ℝ g y‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖L‖ * (C * ‖y‖ ^ k) := mul_le_mul_of_nonneg_left (hg.der y hy) (norm_nonneg L)
      _ = ‖L‖ * C * ‖y‖ ^ k := by ring

/-- **Precomposition with an `L`-Lipschitz map fixing the origin.**  Vanishing order is
preserved; the constant picks up `L^(k+1)`. -/
lemma comp {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {g : E' → F} {h : E → E'} {ρ' L : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hg : Van ρ' k C g)
    (hmap : ∀ y ∈ closedBall (0 : E) ρ, h y ∈ closedBall (0 : E') ρ')
    (hdiff : ∀ y ∈ closedBall (0 : E) ρ, DifferentiableAt ℝ h y)
    (hval : ∀ y ∈ closedBall (0 : E) ρ, ‖h y‖ ≤ L * ‖y‖)
    (hder : ∀ y ∈ closedBall (0 : E) ρ, ‖fderiv ℝ h y‖ ≤ L) :
    Van ρ k (C * L ^ (k + 1)) (fun y => g (h y)) where
  diff := fun y hy => (hg.diff (h y) (hmap y hy)).comp y (hdiff y hy)
  val := fun y hy => by
    have hpow : ‖h y‖ ^ (k + 1) ≤ (L * ‖y‖) ^ (k + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) (hval y hy) _
    calc ‖g (h y)‖ ≤ C * ‖h y‖ ^ (k + 1) := hg.val _ (hmap y hy)
      _ ≤ C * (L * ‖y‖) ^ (k + 1) := mul_le_mul_of_nonneg_left hpow hC
      _ = C * L ^ (k + 1) * ‖y‖ ^ (k + 1) := by rw [mul_pow]; ring
  der := fun y hy => by
    have hd : HasFDerivAt (fun z => g (h z))
        ((fderiv ℝ g (h y)).comp (fderiv ℝ h y)) y :=
      (hg.diff (h y) (hmap y hy)).hasFDerivAt.comp y (hdiff y hy).hasFDerivAt
    rw [hd.fderiv]
    have hpow : ‖h y‖ ^ k ≤ (L * ‖y‖) ^ k := pow_le_pow_left₀ (norm_nonneg _) (hval y hy) _
    calc ‖(fderiv ℝ g (h y)).comp (fderiv ℝ h y)‖
        ≤ ‖fderiv ℝ g (h y)‖ * ‖fderiv ℝ h y‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * ‖h y‖ ^ k) * L :=
          mul_le_mul (hg.der _ (hmap y hy)) (hder y hy) (norm_nonneg _) (by positivity)
      _ ≤ (C * (L * ‖y‖) ^ k) * L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) hL
      _ = C * L ^ (k + 1) * ‖y‖ ^ k := by rw [mul_pow, pow_succ]; ring


/-- A continuous linear map vanishes linearly, with constant its operator norm. -/
lemma of_clm (L : E →L[ℝ] F) : Van ρ 0 ‖L‖ (fun y => L y) where
  diff := fun _ _ => L.differentiableAt
  val := fun y _ => by simpa using L.le_opNorm y
  der := fun y _ => by rw [L.fderiv]; simp

/-- A single coordinate of a `Van` map into a finite product. -/
lemma pi_apply {ι : Type*} [Fintype ι] {g' : E → (ι → ℝ)} (hC : 0 ≤ C)
    (hg : Van ρ k C g') (i : ι) : Van ρ k C (fun y => g' y i) := by
  set P : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i with hP
  have hproj : ‖P‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      simpa [hP] using norm_le_pi_norm x i
  have h := Van.clm_comp P hC hg
  have hfun : (fun y => P (g' y)) = fun y => g' y i := rfl
  rw [hfun] at h
  exact h.mono_const (by nlinarith [norm_nonneg P])

end Van

/-- **The determinant bound.**  If every entry of an `(m+1) × (m+1)` matrix of functions
vanishes linearly at the origin, the determinant vanishes to order `m+1`.  This is the
`C³` counterpart of `LowDeg.det`, and the proof is the same: expand by permutations. -/
theorem Van.det {ρ C : ℝ} {m : ℕ} {M : Matrix (Fin (m + 1)) (Fin (m + 1)) (E → ℝ)}
    (hC : 0 ≤ C) (hM : ∀ i j, Van ρ 0 C (M i j)) :
    Van ρ m ((m + 1).factorial * (1 * (2 ^ m * C ^ (m + 1))))
      (fun y => Matrix.det (fun i j => M i j y)) := by
  classical
  have hfun : (fun y => Matrix.det (fun i j => M i j y))
      = fun y => ∑ σ : Equiv.Perm (Fin (m + 1)),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i y := by
    funext y
    rw [Matrix.det_apply']
  rw [hfun]
  have hterm : ∀ σ : Equiv.Perm (Fin (m + 1)), σ ∈ Finset.univ →
      Van ρ m (1 * (2 ^ m * C ^ (m + 1)))
        (fun y => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M (σ i) i y) := by
    intro σ _
    have hp := Van.prod_fin hC m (fun i => M (σ i) i) (fun i => hM (σ i) i)
    have habs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
    have := Van.const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ)) hp
    rwa [habs] at this
  have hsum := Van.sum (ρ := ρ) (k := m) Finset.univ (by positivity) hterm
  refine hsum.mono_const (le_of_eq ?_)
  congr 1
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]



/-- **The analytic constructor.**  A `C²` map minus its linearisation at the origin vanishes to
order `2`.  Everything else in the `C³` development is `Van` calculus on top of this. -/
theorem van_sub_fderiv {f : E → F} {ρ K : ℝ} (hK : 0 ≤ K) (hf0 : f 0 = 0)
    (hdiff : ∀ y ∈ closedBall (0 : E) ρ, DifferentiableAt ℝ f y)
    (hlip : ∀ y ∈ closedBall (0 : E) ρ, ‖fderiv ℝ f y - fderiv ℝ f 0‖ ≤ K * ‖y‖) :
    Van ρ 1 K (fun y => f y - fderiv ℝ f 0 y) where
  diff := fun y hy => (hdiff y hy).sub (ContinuousLinearMap.differentiableAt _)
  val := fun y hy => by
    have hy' : ‖y‖ ≤ ρ := by rw [mem_closedBall, dist_zero_right] at hy; exact hy
    have hz0 : (fun y => f y - fderiv ℝ f 0 y) 0 = 0 := by
      show f 0 - fderiv ℝ f 0 0 = 0
      rw [hf0, map_zero, sub_zero]
    refine norm_le_of_fderiv_le (g := fun y => f y - fderiv ℝ f 0 y) (p := 1) hK hz0 ?_ ?_ hy'
    · exact fun z hz => (hdiff z hz).sub (ContinuousLinearMap.differentiableAt _)
    · intro z hz
      have hd : HasFDerivAt (fun w => f w - fderiv ℝ f 0 w)
          (fderiv ℝ f z - fderiv ℝ f 0) z :=
        (hdiff z hz).hasFDerivAt.sub ((fderiv ℝ f 0).hasFDerivAt)
      rw [hd.fderiv]
      simpa using hlip z hz
  der := fun y hy => by
    have hd : HasFDerivAt (fun w => f w - fderiv ℝ f 0 w)
        (fderiv ℝ f y - fderiv ℝ f 0) y :=
      (hdiff y hy).hasFDerivAt.sub ((fderiv ℝ f 0).hasFDerivAt)
    rw [hd.fderiv]
    simpa using hlip y hy

/-- **Comparison of determinants.**  Two matrices of linearly-vanishing functions whose
entries agree to order `3` have determinants agreeing to order `m+3`. -/
theorem Van.det_sub {ρ C D : ℝ} {m d : ℕ}
    {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) (E → ℝ)}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : ∀ i j, Van ρ 0 C (M i j)) (hN : ∀ i j, Van ρ 0 C (N i j))
    (hMN : ∀ i j, Van ρ d D (fun y => M i j y - N i j y)) :
    ∃ K : ℝ, 0 ≤ K ∧ Van ρ (m + d) K
      (fun y => Matrix.det (fun i j => M i j y) - Matrix.det (fun i j => N i j y)) := by
  classical
  choose K hK0 hKv using fun σ : Equiv.Perm (Fin (m + 1)) =>
    Van.prod_sub (ρ := ρ) hC hD d m (fun i => M (σ i) i) (fun i => N (σ i) i)
      (fun i => hM (σ i) i) (fun i => hN (σ i) i) (fun i => hMN (σ i) i)
  set Ktot : ℝ := ∑ σ : Equiv.Perm (Fin (m + 1)), K σ with hKtot
  have hKtot0 : 0 ≤ Ktot := Finset.sum_nonneg fun σ _ => hK0 σ
  have hle : ∀ σ : Equiv.Perm (Fin (m + 1)), K σ ≤ Ktot := fun σ =>
    Finset.single_le_sum (f := K) (fun τ _ => hK0 τ) (Finset.mem_univ σ)
  refine ⟨(Fintype.card (Equiv.Perm (Fin (m + 1))) : ℝ) * Ktot, by positivity, ?_⟩
  have hfun : (fun y => Matrix.det (fun i j => M i j y) - Matrix.det (fun i j => N i j y))
      = fun y => ∑ σ : Equiv.Perm (Fin (m + 1)),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((∏ i, M (σ i) i y) - ∏ i, N (σ i) i y) := by
    funext y
    rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [hfun]
  have hterm : ∀ σ : Equiv.Perm (Fin (m + 1)), σ ∈ Finset.univ →
      Van ρ (m + d) Ktot
        (fun y => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((∏ i, M (σ i) i y) - ∏ i, N (σ i) i y)) := by
    intro σ _
    have habs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
    have := Van.const_mul (((Equiv.Perm.sign σ : ℤ) : ℝ)) (hKv σ)
    rw [habs, one_mul] at this
    exact this.mono_const (hle σ)
  have hsum := Van.sum (ρ := ρ) (k := m + d) Finset.univ hKtot0 hterm
  refine hsum.mono_const (le_of_eq ?_)
  rw [Finset.card_univ]

end MPE
