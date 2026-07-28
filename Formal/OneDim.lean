import Mathlib

/-!
# The one-dimensional sublevel bound

Appendix §3.  If `g` has derivative bounded below by `c > 0` on an interval `I`, then
`{t ∈ I : |g t| ≤ s}` has measure at most `2s/c`.

The proof bounds the *diameter* of the sublevel set by the mean value theorem: two points
of the set have `g`-values within `2s`, and the derivative bound converts that into a bound
on their distance.  Because a diameter bound is what comes out, no decomposition of the
sublevel set into intervals is ever needed — which is what lets the fibering argument of
`Formal/Annulus.lean` work with a single interval per fiber.
-/

namespace MPE

open MeasureTheory Set

/-- A set of reals whose points are pairwise within `D` has measure at most `D`.
(`0 ≤ D` is not needed: if `S` is nonempty it follows from `h`.) -/
lemma volume_le_of_diam_le {S : Set ℝ} {D : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, y - x ≤ D) :
    volume S ≤ ENNReal.ofReal D := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · simp
  · -- `S` is bounded below by `t₀ - D`
    have hbdd : BddBelow S := ⟨t₀ - D, fun y hy => by have := h y hy t₀ ht₀; linarith⟩
    set a := sInf S with ha
    have hlow : ∀ y ∈ S, a ≤ y := fun y hy => csInf_le hbdd hy
    have hhigh : ∀ y ∈ S, y ≤ a + D := by
      intro y hy
      have : y - D ≤ a := le_csInf ⟨t₀, ht₀⟩ (fun z hz => by have := h z hz y hy; linarith)
      linarith
    calc volume S ≤ volume (Icc a (a + D)) :=
          measure_mono fun y hy => ⟨hlow y hy, hhigh y hy⟩
      _ = ENNReal.ofReal D := by rw [Real.volume_Icc]; ring_nf

/-- **The one-dimensional sublevel bound.**  If `g' ≥ c > 0` on a convex set `I ⊆ ℝ`, then
`{t ∈ I : |g t| ≤ s}` has measure at most `2s/c`.

No monotonicity is assumed: it is a consequence of the derivative bound. -/
theorem volume_sublevel_le {I : Set ℝ} (hI : Convex ℝ I) {g g' : ℝ → ℝ} {c s : ℝ}
    (hc : 0 < c) (hs : 0 ≤ s)
    (hd : ∀ x ∈ I, HasDerivAt g (g' x) x)
    (hlb : ∀ x ∈ I, c ≤ g' x) :
    volume (I ∩ {t | |g t| ≤ s}) ≤ ENNReal.ofReal (2 * s / c) := by
  refine volume_le_of_diam_le ?_
  rintro x ⟨hxI, hxs⟩ y ⟨hyI, hys⟩
  simp only [Set.mem_setOf_eq] at hxs hys
  rcases le_or_gt y x with hxy | hxy
  · have : (0:ℝ) ≤ 2 * s / c := by positivity
    linarith
  -- `x < y`; apply the mean value theorem on `[x, y] ⊆ I`
  have hsub : Icc x y ⊆ I := hI.ordConnected.out hxI hyI
  have hcont : ContinuousOn g (Icc x y) := fun z hz =>
    ((hd z (hsub hz)).continuousAt).continuousWithinAt
  have hderiv : ∀ z ∈ Ioo x y, HasDerivAt g (g' z) z := fun z hz =>
    hd z (hsub (Ioo_subset_Icc_self hz))
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g g' hxy hcont hderiv
  have hξI : ξ ∈ I := hsub (Ioo_subset_Icc_self hξ)
  have hcξ : c ≤ (g y - g x) / (y - x) := hslope ▸ hlb ξ hξI
  have hyx : 0 < y - x := by linarith
  have h1 : c * (y - x) ≤ g y - g x := by
    rw [le_div_iff₀ hyx] at hcξ; linarith
  have h2 : g y - g x ≤ 2 * s := by
    have hx := abs_le.mp hxs
    have hy := abs_le.mp hys
    linarith [hx.1, hy.2]
  rw [le_div_iff₀ hc]
  linarith

/-- The same bound when the derivative is bounded *above* by `-c`, obtained by applying
`volume_sublevel_le` to `-g`. -/
theorem volume_sublevel_le' {I : Set ℝ} (hI : Convex ℝ I) {g g' : ℝ → ℝ} {c s : ℝ}
    (hc : 0 < c) (hs : 0 ≤ s)
    (hd : ∀ x ∈ I, HasDerivAt g (g' x) x)
    (hub : ∀ x ∈ I, g' x ≤ -c) :
    volume (I ∩ {t | |g t| ≤ s}) ≤ ENNReal.ofReal (2 * s / c) := by
  have hset : I ∩ {t | |g t| ≤ s} = I ∩ {t | |(-g) t| ≤ s} := by
    ext t; simp [abs_neg]
  rw [hset]
  refine volume_sublevel_le hI hc hs (fun x hx => ((hd x hx).neg)) (fun x hx => ?_)
  have := hub x hx; simpa using (by linarith : c ≤ -g' x)

/-- The form used in the fibering argument: `|g'| ≥ c` together with a *known sign* for the
dominant term.  Here the hypothesis is packaged as a disjunction, which is exactly what the
application produces (`(∂ₜq)·h` has a definite sign and dominates `∂ₜE`). -/
theorem volume_sublevel_le_of_abs {I : Set ℝ} (hI : Convex ℝ I) {g g' : ℝ → ℝ} {c s : ℝ}
    (hc : 0 < c) (hs : 0 ≤ s)
    (hd : ∀ x ∈ I, HasDerivAt g (g' x) x)
    (hsign : (∀ x ∈ I, c ≤ g' x) ∨ (∀ x ∈ I, g' x ≤ -c)) :
    volume (I ∩ {t | |g t| ≤ s}) ≤ ENNReal.ofReal (2 * s / c) := by
  rcases hsign with h | h
  · exact volume_sublevel_le hI hc hs hd h
  · exact volume_sublevel_le' hI hc hs hd h

/-- **The fiber bound.**  Along a fiber the function is `F t = q t · h + E t`, where `h` is
constant along the fiber, `q` has derivative at least `c₁ > 0`, and the perturbation has
derivative at most `η` in modulus.  Where `2η ≤ c₁|h|` the derivative of `F` has modulus at
least `c₁|h|/2` and a constant sign, so

    vol {t ∈ I : |F t| ≤ s}  ≤  4s / (c₁ |h|).

This is the only one-dimensional input to the fibering argument, and it serves both kinds of
block: for a line `q t = t` and `c₁ = 1`; for a plane `q ρ = ρ²` and `c₁ = 2c⋆` on the region
`ρ ≥ c⋆`. -/
theorem volume_fiber_le {I : Set ℝ} (hI : Convex ℝ I) {q q' E E' : ℝ → ℝ}
    {h c₁ η s : ℝ} (hc₁ : 0 < c₁) (hη : 0 < η) (hs : 0 ≤ s)
    (hq : ∀ t ∈ I, HasDerivAt q (q' t) t)
    (hE : ∀ t ∈ I, HasDerivAt E (E' t) t)
    (hq'lb : ∀ t ∈ I, c₁ ≤ q' t)
    (hE'b : ∀ t ∈ I, |E' t| ≤ η)
    (hh : 2 * η ≤ c₁ * |h|) :
    volume (I ∩ {t | |q t * h + E t| ≤ s}) ≤ ENNReal.ofReal (4 * s / (c₁ * |h|)) := by
  have habs : 0 < |h| := by nlinarith
  have hderiv : ∀ t ∈ I, HasDerivAt (fun t => q t * h + E t) (q' t * h + E' t) t :=
    fun t ht => ((hq t ht).mul_const h).add (hE t ht)
  have hbound : ENNReal.ofReal (2 * s / (c₁ * |h| / 2))
      = ENNReal.ofReal (4 * s / (c₁ * |h|)) := by
    congr 1
    field_simp
    ring
  rw [← hbound]
  rcases lt_trichotomy h 0 with hneg | hzero | hpos
  · -- `h < 0`: the derivative is at most `-(c₁|h|/2)`
    have hab : |h| = -h := abs_of_neg hneg
    refine volume_sublevel_le' hI (by positivity) hs hderiv (fun t ht => ?_)
    have h1 : q' t * h ≤ c₁ * h := by nlinarith [hq'lb t ht]
    have h2 : E' t ≤ η := le_of_abs_le (hE'b t ht)
    rw [hab] at hh ⊢
    linarith
  · exact absurd hzero (by intro hc; rw [hc] at habs; simp at habs)
  · -- `h > 0`: the derivative is at least `c₁|h|/2`
    have hab : |h| = h := abs_of_pos hpos
    refine volume_sublevel_le hI (by positivity) hs hderiv (fun t ht => ?_)
    have h1 : c₁ * h ≤ q' t * h := by nlinarith [hq'lb t ht]
    have h2 : -η ≤ E' t := neg_le_of_abs_le (hE'b t ht)
    rw [hab] at hh ⊢
    linarith

end MPE
