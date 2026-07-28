import Mathlib
import Formal.CThree
import Formal.SevenFull
import Formal.Undithered
import Formal.GramFull

/-!
# What is proved

This file exists to be **read**.  Its theorems have statements that mention *no definition
from this development* — only mathlib notions
(`Matrix`, `Matrix.det`, `Matrix.adjugate`, `Matrix.cramer`, `Matrix.transpose`,
`Matrix.charpoly`, `minpoly`, `Squarefree`, `ContDiffOn`, `fderiv`, `LinearMap.toMatrix'`,
`Measure.pi`, `Measure.infinitePi`, `volume`, `Real.log`, `‖·‖`).  Every object of the
construction is introduced by an explicit defining equation in the hypotheses, so that a
reader who accepts mathlib can audit the claim without reading anything else.

**Every proof in this file is a one-line reference.**  The work is in
`Formal/GramFull.lean` (Theorem 4.7), `Formal/CThree.lean` (4.9) and
`Formal/Undithered.lean` (5.5).
Lean has no notion of "stated but unproved" — the only way to write a statement without
proving it is `axiom`, which *assumes* it and shows up in `#print axioms`.  So a statement
file is one whose proof bodies are single references, which is what this is.

Two mechanical checks complete the audit, and are run at the bottom of this file:

* `#print axioms` — the theorem must depend only on `propext`, `Classical.choice`,
  `Quot.sound`.  Anything else (in particular `sorryAx`) would mean a hole.
* `lake build` succeeding — the kernel has checked every proof term.

## Which paper theorem is which

The paper states four theorems: 3.1 (the counterexample), 4.7 (dithered restarts, `C²`, no
spectral hypothesis beyond `I - A` invertible), 4.9 (quadratic order under simple spectrum),
and 5.5 (the undithered algorithm).  The three probabilistic ones are formalized, one Lean
theorem each; the counterexample is not:

| paper | Lean |
| --- | --- |
| Theorem 4.7 | `mpe_dithered`, below |
| Theorem 4.9 | `mpe_quadratic`, below |
| Theorem 5.5 | `mpe_undithered`, below |

`mpe_dithered` is Theorem 4.7 as the paper states it: the window is `k = deg m_A` — so `A`
may be **derogatory** — the cleared form is built from the normal matrix `Γ = UᵀU` by
Cramer's rule, the degeneracy form is `Δ = det(KᵀK)` of degree `d = 2k` (the paper's
`(2.5)`), and the failure probability is `C·δ^((2-θ)/d) = C·δ^((2-θ)/(2k))`.

The paper adds a parenthetical for the nonderogatory case: at `k = n` one may instead take
`c̃ = adj(U)(-u_n)` and the smaller `Δ = det K` of degree `n` (`(2.6)`), which multiplies
`D`, `c̃`, `σ̃`, `Ñ` by `det U`, leaves `S` unchanged, and improves the exponent to
`(2-θ)/n`.  That variant is proved in this development too — `mpe_dithered_C2_stmt` in
`Formal/SevenFull.lean`, an independent proof, not a corollary — but it is not restated
here: this file carries exactly one Lean theorem per paper theorem.

`mpe_quadratic` formalizes **all** clauses of the paper's Theorem 4.9.  Its failure event
is the union of the three: the schedule invariant `‖xₖ‖ ≤ δₖ` breaking, the least-squares
system being singular (`det U = 0`) at some cycle — the paper's "the system `(2.3)`
being nonsingular, so that MPE and RRE agree" — or a cycle being undefined in the cleared
form (`σ̃ = 0`).  All three are controlled by the same good event; `det U ≠ 0` needs the
threshold `sₘ = max(16C₂/K, 2M₀)·δₘ` to be of the same order as `δₘ` — which is exactly
what the doubly-exponential schedule `δₘ = δ^(θᵐ)` of Theorem 4.7 could not achieve, its
threshold there being `δₘ^(3-θ) ≪ δₘ`.  This is why the 4.7 event carries only the `σ̃`
clause: on 4.7's schedule the margin is too small to keep `det U ≠ 0`, and the paper's 4.7
accordingly claims definedness of the cleared form only.


Theorems 4.7 and 4.9 assume `f` is `C²` near `0`: `ContDiffOn ℝ 2 f (Metric.ball 0 R)`
together with `f 0 = 0`.  There is no polynomial hypothesis anywhere.  (Both the paper and
this statement originally said `C³` for 4.9; the proof needs `Df` Lipschitz at `0` and
nothing more, so both were weakened to `C²`.)  Theorem 5.5 is the exception: the paper
states it for `C³`, and `mpe_undithered` assumes `ContDiffOn ℝ 3` to match.

One hypothesis is *not* part of "`f` is `C²` near `0`", and is flagged rather than buried:
`Measurable f`.  The dithered process is defined by the **global** map `f`, and a
`C²`-on-a-ball hypothesis says nothing about `f` away from the origin — without some global
regularity the failure event need not even be measurable.  Any continuous iteration satisfies
it.  Nothing else about `f` outside the ball is used.

## What `mpe_dithered` says (Theorem 4.7)

Let `f` be `C²` near `0` on `ℝⁿ` (`n = M+2`) with `f 0 = 0`, let `A = Df(0)`, and assume
`A - I` is invertible.  That is the *entire* spectral hypothesis.  Let `k = deg m_A` be the
degree of the minimal polynomial of `A` — the paper's window; `k = n` exactly when `A` is
nonderogatory, and `k < n` otherwise.  At a general window `U(y)` is the `n × k` matrix with
columns `u_j`, the normal matrix is `Γ = UᵀU`, and Cramer's rule on `Γ c = b`,
`b = -Uᵀ u_k`, gives the cleared coefficients

    c̃_j = det(Γ with column j replaced by b)  (j < k),      c̃_k = det Γ,

equivalently `c̃ = adj(Γ)b`, the paper's display; and `Ñ = ∑_{j≤k} c̃_j f^j`,
`σ̃ = ∑_{j≤k} c̃_j` — the paper's `σ̃ = D + ∑_{j<k} c̃_j` and `Ñ = ∑_{j<k} c̃_j f^j + D f^k`,
since `c̃_k = D = det Γ`.  Each cycle dithers to
`y_m = x_m + δ_m ξ_m`, `ξ_m` uniform on the cube `[-1,1]ⁿ`, and extrapolates to
`x_{m+1} = S(y_m)`, `S = Ñ/σ̃`.  The conclusion covers both clauses of the paper's theorem —
some cycle undefined (`σ̃(y_m) = 0`, where the junk value `0⁻¹ = 0` would otherwise let the
process continue silently), or the schedule invariant breaking:

    P[ ∃ m, ‖x_m‖ > δ_m  or  σ̃(y_m) = 0 ]  ≤  C · δ^((2-θ)/(2k)),

the exponent being `(2-θ)/d` for `d = deg Δ` and `Δ = det(KᵀK)` of degree `2k`.  On the
complement, every cycle is defined and `‖x_m‖ ≤ δ_m` — the paper's conclusion verbatim.

**Nothing is assumed about `Δ`.**  That `Δ ≢ 0` — the paper's Lemma 4.2(i) — is *derived*
from `k = deg m_A` inside the proof, via the existence of a vector whose annihilator is the
minimal polynomial (`MPE.exists_ann_eq_minpoly`).  Likewise `m_A(1) ≠ 0` and `k ≤ n` are
derived, from `A - I` invertible and from `m_A ∣ χ_A`.

Under the stronger hypothesis that `A` has `n` distinct eigenvalues, `mpe_quadratic`
improves the exponent to `1` (with logarithms) on a genuinely quadratic schedule.

## The MPE cycle at the full window, spelled out

`mpe_quadratic` and `mpe_undithered` are full-window theorems — 4.9 assumes `n` distinct
eigenvalues and 5.5 assumes `A` nonderogatory, so `k = n` in both — and there the paper
takes the adjugate form of the parenthetical above.  Spelled out:

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

/-- **The paper's Theorem 4.7.**  `f` is `C²` near its fixed point `0` and measurable
elsewhere; `A = Df(0)`; `I - A` is invertible.  That is every spectral hypothesis — `A` may
be **derogatory**.  The window is the paper's, `k = deg m_A` (`hk`, with `k` written `kk+1`
so that `k ≥ 1` holds by construction).

From *every* starting point with `‖x₀‖ ≤ δ` — it may be adversarial, and may lie on the
breakdown set — with probability at least `1 - Cst·δ^((2-θ)/(2k))` over the dither, **every
cycle is defined** (`σ̃ ≠ 0` at every dithered point, so the division in `S = Ñ/σ̃` is
genuine) **and** `‖x_m‖ ≤ δ_m` for all `m`.

Nothing is assumed about the degeneracy form: the paper's Lemma 4.2(i) is derived from
`hk` inside the proof. -/
theorem mpe_dithered
    -- the iteration: `C²` near its fixed point `0`, and measurable elsewhere
    (f : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    {R : ℝ} (hR : 0 < R) (hf0 : f 0 = 0) (hmeas : Measurable f)
    (hf : ContDiffOn ℝ 2 f (Metric.ball 0 R))
    -- the linear part `A = Df(0)`, invertible at `1`.  No other spectral hypothesis.
    (A : Matrix (Fin (M + 2)) (Fin (M + 2)) ℝ)
    (hAdef : A = LinearMap.toMatrix'
      (fderiv ℝ f 0 : (Fin (M + 2) → ℝ) →L[ℝ] (Fin (M + 2) → ℝ)).toLinearMap)
    (hA : IsUnit (A - 1))
    -- the window is the degree of the minimal polynomial
    {kk : ℕ} (hk : kk + 1 = (minpoly ℝ A).natDegree)
    -- the `n × k` matrix of increments, its normal matrix, and the right-hand side
    (U : (Fin (M + 2) → ℝ) → Matrix (Fin (M + 2)) (Fin (kk + 1)) ℝ)
    (hU : ∀ y i j, U y i j = f^[(j : ℕ) + 1] y i - f^[(j : ℕ)] y i)
    (Gm : (Fin (M + 2) → ℝ) → Matrix (Fin (kk + 1)) (Fin (kk + 1)) ℝ)
    (hGm : ∀ y, Gm y = (U y).transpose * U y)
    (b : (Fin (M + 2) → ℝ) → Fin (kk + 1) → ℝ)
    (hb : ∀ y j, b y j
      = -∑ l : Fin (M + 2), U y l j * (f^[kk + 2] y l - f^[kk + 1] y l))
    -- the cleared coefficients, by Cramer's rule on `Γ c = b`
    (c : ℕ → (Fin (M + 2) → ℝ) → ℝ)
    (hcCramer : ∀ (j : Fin (kk + 1)) y, c (j : ℕ) y = (Gm y).cramer (b y) j)
    (hcDet : ∀ y, c (kk + 1) y = (Gm y).det)
    -- the cleared denominator and numerator
    (sg : (Fin (M + 2) → ℝ) → ℝ) (Nt : (Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ))
    (hsg : ∀ y, sg y = ∑ j ∈ Finset.range (kk + 2), c j y)
    (hNt : ∀ y, Nt y = ∑ j ∈ Finset.range (kk + 2), c j y • f^[j] y)
    -- the dither schedule exponent
    {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ dstar Cst : ℝ, 0 < dstar ∧ 0 < Cst ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ dstar →
      ∀ x₀ : Fin (M + 2) → ℝ, ‖x₀‖ ≤ δ →
      -- the dithered process: `x₀`, then `x_{m+1} = S (x_m + δ_m · clamp ω_m)`, `S = Ñ/σ̃`
      ∀ x : ℕ → (ℕ → Fin (M + 2) → ℝ) → (Fin (M + 2) → ℝ),
        (∀ ω, x 0 ω = x₀) →
        (∀ m ω, x (m + 1) ω
          = (sg (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i))))⁻¹
            • Nt (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i)))) →
        -- the dither `ω_m` is uniform on the cube `[-1,1]ⁿ`, independently in `m`
        (Measure.infinitePi fun _ : ℕ =>
            Measure.pi fun _ : Fin (M + 2) =>
              ENNReal.ofReal (1 / 2) • volume.restrict (Set.Icc (-1 : ℝ) 1))
            -- the failure event: the schedule invariant breaks, *or* some cycle is
            -- undefined (`σ̃ = 0` at the dithered point)
            {ω | ∃ m, δ ^ (θ ^ m) < ‖x m ω‖
                  ∨ sg (x m ω + (δ ^ (θ ^ m)) • fun i => max (-1) (min 1 (ω m i))) = 0}
          ≤ ENNReal.ofReal (Cst * δ ^ ((2 - θ) / (2 * (kk : ℝ) + 2))) :=
  Smooth.mpe_dithered_gram_stmt f hR hf0 hmeas hf A hAdef hA hk U hU Gm hGm b hb
    c hcCramer hcDet sg Nt hsg hNt hθ1 hθ2

/-- **The paper's Theorem 4.9 (quadratic order).**  Same iteration and dither as
`mpe_dithered`, but under the stronger hypothesis that `A` has `n` distinct eigenvalues
(`hsq`), at the full window `k = n` in the adjugate form, and with the schedule
`δ₀ = δ`, `δₖ₊₁ = K δₖ²` — order exactly `2`.  The failure probability improves to
`C δ (1 + log⁺(1/δ))^(n-1)`: exponent `1`, uniformly in `n` and in `θ`.  On the good event
every cycle is defined in the cleared form (`σ̃ ≠ 0`) *and* the least-squares system is
nonsingular (`det U ≠ 0`, so MPE and RRE agree at every cycle), and `‖xₖ‖ ≤ δₖ`.

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
            -- system is singular, *or* some cycle is undefined in the cleared form
            {ω | ∃ k, dl k < ‖x k ω‖
                  ∨ Matrix.det (U (x k ω + dl k • fun i => max (-1) (min 1 (ω k i)))) = 0
                  ∨ sg (x k ω + dl k • fun i => max (-1) (min 1 (ω k i))) = 0}
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
