import Mathlib
import Formal.CThree
import Formal.SevenFull
import Formal.Undithered

/-!
# What is proved

This file exists to be **read**.  Its theorems have statements that mention *no definition
from this development* — only mathlib notions
(`Matrix`, `Matrix.adjugate`, `Matrix.det`, `ContDiffOn`, `fderiv`, `LinearMap.toMatrix'`,
`Measure.pi`, `Measure.infinitePi`, `volume`, `Real.log`, `‖·‖`).  Every object of the
construction is introduced by an explicit defining equation in the hypotheses, so that a
reader who accepts mathlib can audit the claim without reading anything else.

**Every proof in this file is a one-line reference**: the work is in `Formal/CThree.lean`.
Lean has no notion of "stated but unproved" — the only way to write a statement without
proving it is `axiom`, which *assumes* it and shows up in `#print axioms`.  So a statement
file is one whose proof bodies are single references, which is what this is.

Two mechanical checks complete the audit, and are run at the bottom of this file:

* `#print axioms` — the theorem must depend only on `propext`, `Classical.choice`,
  `Quot.sound`.  Anything else (in particular `sorryAx`) would mean a hole.
* `lake build` succeeding — the kernel has checked every proof term.

## Which paper theorem is which

The paper (after the revision that promoted the quadratic corollary) states four theorems:
3.1 (the counterexample), 4.7 (dithered restarts, `C²`, no spectral hypothesis beyond
`I - A` invertible and `A` nonderogatory), 4.9 (quadratic order under simple spectrum), and
5.5 (the undithered algorithm).  Their formalizations are:

| paper | Lean |
| --- | --- |
| Theorem 4.7 | `mpe_dithered`, below |
| Theorem 4.9 | `mpe_quadratic`, below |
| Theorem 5.5 | `mpe_undithered`, below |

`mpe_quadratic` formalizes **both** clauses of the paper's Theorem 4.9.  Its failure event
is the union of the two: the schedule invariant `‖xₖ‖ ≤ δₖ` breaking, *or* the
least-squares system being singular (`det U = 0`) at some cycle.  Both are controlled by
the same good event, because the threshold `sₘ = max(16C₂/K, 2M₀)·δₘ` is of the same order
as `δₘ` — which is exactly what the doubly-exponential schedule `δₘ = δ^(θᵐ)` of
Theorem 4.7 could not achieve, its threshold there being `δₘ^(3-θ) ≪ δₘ`.


Theorem 4.9 assumes `f` is `C²` near `0`, and that is what these theorems assume:
`ContDiffOn ℝ 2 f (Metric.ball 0 R)` together with `f 0 = 0`.  There is no polynomial
hypothesis anywhere.  (Both the paper and this statement originally said `C³`; the proof
needs `Df` Lipschitz at `0` and nothing more, so both were weakened to `C²`.)

One hypothesis is *not* part of "`f` is `C²` near `0`", and is flagged rather than buried:
`Measurable f`.  The dithered process is defined by the **global** map `f`, and a
`C²`-on-a-ball hypothesis says nothing about `f` away from the origin — without some global
regularity the failure event need not even be measurable.  Any continuous iteration satisfies
it.  Nothing else about `f` outside the ball is used.

## What `mpe_dithered` says (Theorem 4.7)

Let `f` be `C²` near `0` on `ℝⁿ` (`n = M+2`) with `f 0 = 0`, let `A = Df(0)`, assume `A - I`
is invertible and `A` nonderogatory.  Run *minimal polynomial extrapolation with dithered
restarts*: from `xₖ`, dither to `yₖ = xₖ + δₖ ξₖ` with `ξₖ` uniform on the cube `[-1,1]ⁿ`,
and let `xₖ₊₁ = S yₖ` be the MPE extrapolant, in cleared form.  With the doubly-exponential
schedule `δₖ = δ^(θᵏ)`, `θ ∈ (1,2)`,

    P[ ∃ k, ‖xₖ‖ > δₖ ]  ≤  C · δ^((2-θ)/n)

for all small `δ`, from *every* starting point with `‖x₀‖ ≤ δ`.  Under the stronger
hypothesis that `A` has `n` distinct eigenvalues, `mpe_quadratic` improves this to exponent
`1` (with logarithms) on a genuinely quadratic schedule.

## The MPE cycle, spelled out

`u_j(y) = f^{j+1}(y) - f^j(y)` for `j < n`; `U(y)` is the `n × n` matrix with those columns.
Cramer's rule applied to the (generally singular) system `U c = -u_n`, `c_n = 1` gives the
*cleared* coefficients

    c̃_j = adj(U) (-u_n) at j  (j < n),      c̃_n = det U,

and the cleared numerator and denominator are `Ñ = ∑_{j≤n} c̃_j f^j` and `σ̃ = ∑_{j≤n} c̃_j`,
so that `S = Ñ / σ̃` wherever `σ̃ ≠ 0`.  Clearing is the whole point: `σ̃` may vanish, and the
theorem is a statement about how rarely the dither lands near its zero set.
-/

-- Nothing in this file may be invented by the elaborator: every identifier in the statement
-- is either declared here or comes from mathlib.
set_option autoImplicit false

namespace MPE

open MeasureTheory

-- The dimension is `n = M + 2`; writing it this way makes `n ≥ 2` true by construction.
variable {M : ℕ}

/-- **The paper's Theorem 4.7 (dithered restarts).**  `f` is `C²` near its fixed point, and
the only spectral hypotheses are that `I - A` is invertible and that `A` is nonderogatory
(`hnd`: some Krylov matrix of `A` is invertible).  There is no simple-spectrum assumption
and no logarithm in the bound.  From *every* starting point with `‖x₀‖ ≤ δ` — it may be
adversarial, and may lie on the breakdown set — the dithered process with the schedule
`δₖ = δ^(θᵏ)` satisfies `‖xₖ‖ ≤ δₖ` for all `k` with probability at least
`1 - Cst·δ^((2-θ)/n)`. -/
theorem mpe_dithered
    -- the iteration: `C²` near its fixed point `0`, and measurable elsewhere
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 2 f (Metric.ball 0 R))
    -- the linear part `A = Df(0)`, invertible at `1` and nonderogatory
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1))
    (hnd : ∃ v : Fin (M + 2) → ℝ,
      Matrix.det (Matrix.of fun i j : Fin (M + 2) => ((A ^ (j : ℕ)).mulVec v) i) ≠ 0)
    -- the MPE matrix, the cleared coefficients, denominator and numerator
    (U : (Fin (M + 2) → ℝ) → Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hU : ∀ y i j, U y i j = f^[(j : ℕ) + 1] y i - f^[(j : ℕ)] y i)
    (c : ℕ → (Fin (M + 2) → ℝ) → ℝ)
    (hcAdj : ∀ (j : Fin (M + 2)) y,
      c (j : ℕ) y = (U y).adjugate.mulVec (fun i => -(f^[M + 3] y i - f^[M + 2] y i)) j)
    (hcDet : ∀ y, c (M + 2) y = (U y).det)
    (sg : (Fin (M + 2) → ℝ) → ℝ) (Nt : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hsg : ∀ y, sg y = ∑ j ∈ Finset.range (M + 3), c j y)
    (hNt : ∀ y, Nt y = ∑ j ∈ Finset.range (M + 3), c j y • f^[j] y)
    -- the dither schedule exponent
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ dstar Cst : ℝ, 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
      -- the dithered process: `x₀`, then `xₖ₊₁ = S (xₖ + δₖ · clamp ωₖ)`, `S = Ñ/σ̃`
      ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
        (∀ ω, x 0 ω = x₀) →
        (∀ k ω, x (k + 1) ω
          = (sg (x k ω + (δ ^ (θ ^ k)) • fun i => max (-1) (min 1 (ω k i))))⁻¹
            • Nt (x k ω + (δ ^ (θ ^ k)) • fun i => max (-1) (min 1 (ω k i)))) →
        -- the dither `ωₖ` is uniform on the cube `[-1,1]ⁿ`, independently in `k`
        (Measure.infinitePi fun _ : ℕ =>
            Measure.pi fun _ : Fin (M + 2) =>
              ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
            {ω | ∃ k, δ ^ (θ ^ k) < ‖x k ω‖}
          ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / ((M : ℝ) + 2))) :=
  mpe_dithered_C2_stmt f hR hf0 hmeas hf A hAdef hA hnd U hU c hcAdj hcDet sg Nt hsg hNt
    hθ1 hθ2

/-- **The paper's Theorem 4.9 (quadratic order).**  Same setup as `mpe_dithered`, but under
the stronger hypothesis that `A` has `n` distinct eigenvalues (`hsq`), and with the schedule
`δ₀ = δ`, `δₖ₊₁ = K δₖ²` — order exactly `2`.  The failure probability improves to
`C δ (1 + log⁺(1/δ))^(n-1)`: exponent `1`, uniformly in `n` and in `θ`.

`K` is existentially quantified alongside `δ_*` and `C`, since the paper's `K = max(8C₁,1)`
depends on the one-cycle constant `C₁`; the paper notes that any larger value also works. -/
theorem mpe_quadratic
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 2 f (Metric.ball 0 R))
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1)) (hsq : Squarefree A.charpoly)
    (U : (Fin (M + 2) → ℝ) → Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hU : ∀ y i j, U y i j = f^[(j : ℕ) + 1] y i - f^[(j : ℕ)] y i)
    (c : ℕ → (Fin (M + 2) → ℝ) → ℝ)
    (hcAdj : ∀ (j : Fin (M + 2)) y,
      c (j : ℕ) y = (U y).adjugate.mulVec (fun i => -(f^[M + 3] y i - f^[M + 2] y i)) j)
    (hcDet : ∀ y, c (M + 2) y = (U y).det)
    (sg : (Fin (M + 2) → ℝ) → ℝ) (Nt : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hsg : ∀ y, sg y = ∑ j ∈ Finset.range (M + 3), c j y)
    (hNt : ∀ y, Nt y = ∑ j ∈ Finset.range (M + 3), c j y • f^[j] y) :
    ∃ K dstar Cst : ℝ, 1 ≤ K ∧ 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
      -- the quadratic schedule: `δ₀ = δ`, `δₖ₊₁ = K δₖ²`
      ∀ dl : ℕ → ℝ, dl 0 = δ → (∀ k, dl (k + 1) = K * (dl k) ^ 2) →
      -- the dithered process, with that schedule
      ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
        (∀ ω, x 0 ω = x₀) →
        (∀ k ω, x (k + 1) ω
          = (sg (x k ω + (dl k) • fun i => max (-1) (min 1 (ω k i))))⁻¹
            • Nt (x k ω + (dl k) • fun i => max (-1) (min 1 (ω k i)))) →
        (Measure.infinitePi fun _ : ℕ =>
            Measure.pi fun _ : Fin (M + 2) =>
              ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
            -- the failure event: the schedule invariant breaks, *or* the least-squares
            -- system is singular at some cycle
            {ω | ∃ k, dl k < ‖x k ω‖
                  ∨ Matrix.det (U (x k ω + dl k • fun i => max (-1) (min 1 (ω k i)))) = 0}
          ≤ ENNReal.ofReal (Cst * δ * (1 + max 0 (-Real.log δ)) ^ (M + 1)) :=
  Nonempty.elim (nonempty_smoothData hR hf0 hmeas (hf.of_le (by norm_num))) fun D =>
    D.mpe_quadratic_C3_proof A hAdef hA hsq U hU c hcAdj hcDet sg Nt hsg hNt


/-- **The paper's Theorem 5.5 (the undithered algorithm).**  No dither: the orbit is
deterministic and the only randomness is the starting point, drawn uniformly from the ball
of radius `ρ`.  Under Hypotheses 5.1 and 5.2 — here `hA2` and `hA3`, conditions on the
degeneracy form `Q` and the leading form `G`, both given by defining equations — with
probability at least `1 - Cst ρ^(1/(n(β+1)))` every cycle is defined (`σ̃ ≠ 0` and
`det U ≠ 0`) and each squares the error, so the decay is doubly exponential. -/
theorem mpe_undithered
    -- the iteration: `C³` near its fixed point `0`, and measurable elsewhere
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 3 f (Metric.ball 0 R))
    -- the linear part `A = Df(0)`, invertible at `1` and nonderogatory
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1))
    (hnd : ∃ v : Fin (M + 2) → ℝ,
      Matrix.det (Matrix.of fun i j : Fin (M + 2) => ((A ^ (j : ℕ)).mulVec v) i) ≠ 0)
    -- the MPE matrix, the cleared coefficients, denominator and numerator
    (U : (Fin (M + 2) → ℝ) → Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hU : ∀ y i j, U y i j = f^[(j : ℕ) + 1] y i - f^[(j : ℕ)] y i)
    (c : ℕ → (Fin (M + 2) → ℝ) → ℝ)
    (hcAdj : ∀ (j : Fin (M + 2)) y,
      c (j : ℕ) y = (U y).adjugate.mulVec (fun i => -(f^[M + 3] y i - f^[M + 2] y i)) j)
    (hcDet : ∀ y, c (M + 2) y = (U y).det)
    (sg : (Fin (M + 2) → ℝ) → ℝ) (Nt : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hsg : ∀ y, sg y = ∑ j ∈ Finset.range (M + 3), c j y)
    (hNt : ∀ y, Nt y = ∑ j ∈ Finset.range (M + 3), c j y • f^[j] y)
    -- the degeneracy form `Q̃ = p_A(1)·det K`, `K(v) = [(A-I)v, …, (A-I)A^{n-1}v]`
    (Q : (Fin (M + 2) → ℝ) → ℝ)
    (hQ : ∀ v, Q v = A.charpoly.eval 1 *
      Matrix.det (Matrix.of fun i j : Fin (M + 2) => (((A - 1) * A ^ (j : ℕ)).mulVec v) i))
    -- the quadratic Taylor part of `f` at `0`, and the leading form `G = Δ·N⁽²⁾`
    (q₂ : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hq₂ : ∀ x, q₂ x = (1/2 : ℝ) • ((fderiv ℝ (fderiv ℝ f) 0) x) x)
    (G : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hG : ∀ v, G v =
      Matrix.det (Matrix.of fun i j : Fin (M + 2) => (((A - 1) * A ^ (j : ℕ)).mulVec v) i) •
        (A - 1)⁻¹.mulVec
          (-∑ j ∈ Finset.range (M + 3), A.charpoly.coeff j • q₂ ((A ^ j).mulVec v)))
    -- Hypotheses 5.1 (comparable vanishing) and 5.2 (the degeneracy takes the power `β`)
    {c₀ C₀ c₃ β : ℝ} (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hc₃ : 0 < c₃)
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hA2 : ∀ v : Fin (M + 2) → ℝ, ‖v‖ = 1 → c₀ * |Q v| ≤ ‖G v‖ ∧ ‖G v‖ ≤ C₀ * |Q v|)
    (hA3 : ∀ v : Fin (M + 2) → ℝ, ‖v‖ = 1 → Q v ≠ 0 →
      c₃ * |Q v| ^ β ≤ |Q (‖G v‖⁻¹ • G v)|) :
    ∃ Cst ρ₀ : ℝ, 0 < Cst ∧ 0 < ρ₀ ∧ 4 * C₀ * ρ₀ ≤ 1 / 2 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      -- `x₀ = ρ·b` with `b` uniform on the cube `[-1,1]ⁿ`; the orbit is deterministic
      (Measure.pi fun _ : Fin (M + 2) =>
          ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
        {b : Fin (M + 2) → ℝ | ¬ ∀ k : ℕ,
            sg ((fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b)) ≠ 0 ∧
            (U ((fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b))).det ≠ 0 ∧
            ‖(fun y => (sg y)⁻¹ • Nt y)^[k + 1] (ρ • b)‖
              ≤ 4 * C₀ * ‖(fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b)‖ ^ 2 ∧
            ‖(fun y => (sg y)⁻¹ • Nt y)^[k] (ρ • b)‖
              ≤ (4 * C₀ * ‖ρ • b‖) ^ (2 ^ k) / (4 * C₀)}
        ≤ ENNReal.ofReal (Cst * ρ ^ ((β + 1)⁻¹ * ((M : ℝ) + 2)⁻¹)) :=
  SmoothData3.mpe_undithered_stmt f hR hf0 hmeas hf A hAdef hA hnd U hU c hcAdj hcDet
    sg Nt hsg hNt Q hQ q₂ hq₂ G hG hc₀ hC₀ hc₃ hβ0 hβ2 hA2 hA3

/-! ### The mechanical checks

These run on every `lake build`.  The first prints the axioms the theorem rests on; anything
beyond `propext`, `Classical.choice`, `Quot.sound` — in particular `sorryAx` — would appear
here.  The second **fails the build** if any definition of this development ever creeps into
the statement, which is what makes the file's claim to be self-contained maintainable rather
than a one-off. -/

#print axioms mpe_dithered
#print axioms mpe_quadratic
#print axioms mpe_undithered

open Lean in
run_cmd do
  for nm in [`MPE.mpe_dithered, `MPE.mpe_quadratic, `MPE.mpe_undithered] do
    let info ← Lean.getConstInfo nm
    let mine := info.type.getUsedConstants.filter fun c => (`MPE).isPrefixOf c
    unless mine.isEmpty do
      throwError "the statement of {nm} is not self-contained: it mentions {mine}"

end MPE
