# Research round 25: mapping the space of responses across the data manifold — what would maximum beauty and depth take?

## The user's direction (verbatim)

"Continue, but make sure we are tackling core features of the change in posterior expectation values
with the change in the data distribution that allow us to "map" the space of responses across the
data manifold (ideally, all the way from the "featureless" distribution of maximal entropy to our
actual data distribution). What would it take to do this with maximum beauty and depth?"

## Setting (as formalised, all sorry-free in Lean/Mathlib)

Prior `π` on a measurable space `X` (weights), loss `L_q : X → ℝ` depending on a data distribution `q`,
response `ρ_{t,q} ∝ e^{-t L_q} π`, posterior expectations `⟨φ⟩_{t,q}`. Data manifold = the set of `q`;
the response map is `q ↦ ρ_{t,q}`. Mixture lines `q_s = (1−s) q₀ + s q₁` give `L_s = L₀ + s Δ`
(`pathLoss L₀ Δ s`), exponential families in `s`; affine families `L_a = L₀ + ∑ aᵢ Rᵢ` (contrasts `Rᵢ`
bounded), mean map `m(a) = (⟨Rᵢ⟩_{t,a})ᵢ`, response form `G_a(v,u) = t² Cov_a(R_v, R_u)`, Fisher speed
of a path `g_t(s) = t² Var_{t,s}(L̇_s)`, thermodynamic length `ℓ = ∫ √g_t`.

**The featureless distribution is loss-neutral** (`L` constant on the support): the mixture line from it
to `q` is the temperature line `s ↦ s·t L_q` (`priorExp_neutral`, `mixExp_neutral`), so "from the
featureless distribution to the data distribution" is literally the temperature line of the loss `L_q`.

## What is landed (since round 24, the exact layer is complete)

1. Three scales of thermodynamic distance: O(1) (fixed minimiser, shape metric `½ tr(AΣBΣ)`:
   `ShapeMetricLimit`, `GaussianShapeMetric`, `BoundedDistance`), `√λ log t` along the featureless line
   (`ThermoLengthAsymptotic`, `ThermoLengthFromBase`; concrete instance `AnharmonicFeaturelessLaw`:
   separable anharmonic on ℝ^d with Gaussian prior, `(∫_{s₀}^t √Var_u)/log t → √(d/2)`), `√t` between
   different truths (`SqrtIntegralConvergence`).
2. Global convexity / Legendre / entropy duality of the affine family (`AffineConvexity`,
   `EntropyDuality`: `F(a) − a·m(a) = ⟨L₀⟩_a + KL(P_a‖π)/t`, `KL(P_a‖P_b) = A(b) − A(a) + t(b−a)·m(a)`),
   `∫₀¹ t Var_s = ⟨Δ⟩₀ − ⟨Δ⟩₁` (`IntegratedSusceptibility`), `ℓ ≤ √(⟨Δ⟩₀ − ⟨Δ⟩₁)`.
3. **The mean map is a local chart** (`MeanMapInjective`, `MeanMapFDeriv`, `MeanMapJacobian`,
   `MeanMapChart`): globally injective; Fréchet differentiable with `Dm(a)[v]ᵢ = −t Cov_a(Rᵢ, R_v)
   = −(1/t) G_a(eᵢ, v)`; Jacobian injective for non-degenerate contrasts; Jacobian continuous
   (dominated convergence) ⇒ strictly differentiable ⇒ inverse function theorem: local inverse
   `m⁻¹` with `D(m⁻¹) = (Dm)⁻¹`, `map m (𝓝 a₀) = 𝓝 (m a₀)`.
4. Singular layer for the two-monomial wall `w^p + a w^q` (`0<q<p`) on the half line, flat prior:
   window isometry (`wall_window_length`: the length of `[c₀t^{-σ*}, c₁t^{-σ*}]` is `∫ √Var_c(y^q) dc`
   exactly, `σ* = 1 − q/p`), Gamma tails, receding wall `ℓ_t/log t → σ*√(1/q) = √(σ*(λ₊ − λ_wall))`
   (weak: `WallRecedes`; strong: `WallRecedesStrong`, `∃K, ℓ_t − σ*√(1/q) log t → K`), spectator
   directions (`SpectatorWall`), and the two-coupling singular response chart (`WallChart`: the
   response form pulled back by the chart Jacobian `t^{-σ_q}, t^{-σ_r}` is exactly the profile Fisher
   matrix `Cov_{c,d}(y^{eᵢ}, y^{eⱼ})`).

## Remaining from round 24

Negative chamber (`√t` with `K₋(A)`; needs a half-line regular Laplace instance with real exponents —
the seabed's Laplace machinery is for smooth potentials on ℝ^d / polynomial anharmonic; ~400 lines);
multiplicity correction `ℓ = √λ log t − (m−1)/(2√λ) log log t + O(1)`; uniform Laplace `C` (≥600).

## An observation on the featureless line

On the featureless (temperature) line everything depends only on the **law of the loss** under the
prior (the state density): `Z(u) = ∫ e^{-u ℓ} dν_L(ℓ)` is the Laplace transform of `ν_L = L_*(π μ)`.
So the featureless→data leg of the map is governed by the singularity of the state density at
`ℓ = 0`, whose exponents are exactly Watanabe's `(λ, m)`. An exactly solvable multiplicity model: state
density `ℓ^{λ−1}(−log ℓ)^{m−1}` on `(0,1)`; for `λ = 1, m = 2`, `Z(u) = (log u + γ + E₁(u))/u`, and
`u² Var_u(L) = 1 − 1/g − 1/g²` up to `e^{-u}` terms with `g = log u + γ`, so
`ℓ_t = log t − ½ log log t + O(1)`: thermodynamic length detects multiplicity. Formalisable with
truncated Gamma integrals `∫₀^u s^k e^{-s} (log u − log s) ds` (~500 lines for `λ = 1, m = 2`; general
`λ` via incomplete Gamma, general `m` via `(log u − log s)^{m−1}` binomially).

## Questions

1. **The deep formulation.** What is the most beautiful and deep mathematical statement of "mapping the
   space of responses across the data manifold from the featureless distribution to the data
   distribution"? Candidates: (i) the temperature line as the canonical path, its thermodynamic length
   `D_t(q) = ∫₀¹ √(t² Var_{s}(L_q)) ds` as a "distance from featurelessness" functional of `q`, and its
   properties (monotone in `t`, asymptotics `√λ log t − (m−1)/(2√λ) log log t + O(1)`, subadditivity,
   behaviour under mixtures of `q`); (ii) the response manifold as an immersed submanifold of the
   Fisher–Rao manifold of posteriors, with the response form as the pullback metric, and the question
   whether mixture lines are geodesics; (iii) the state-density / Laplace-transform structure theorem
   (everything on the featureless line is a Mellin/Laplace problem in one variable, with `(λ, m)` as
   the singularity data) and a Tauberian theorem `u² Var_u(L) → λ` from `Z ~ C u^{-λ}(log u)^{m−1}`
   (with what derivative control?); (iv) a global "atlas" statement: the union of the mean-map charts
   over the affine families, transition maps, and the singular charts at the walls. Which of these (or
   what else) is the core, and what is the precise theorem list?

2. **Rank the next targets** by (beauty + depth) / Lean cost, given the seabed: (a) the exactly solvable
   multiplicity model (`λ = 1, m = 2`, then general); (b) the state-density structure theorem
   (`priorExp` on the neutral line = expectation under the tilted law `e^{-uℓ} ν_L`, all of
   `ThermoLengthAsymptotic` restated for one-dimensional laws) plus a Tauberian variance theorem;
   (c) the negative chamber; (d) the global open embedding of the affine family (`m` is a
   homeomorphism onto an open set: injective + local homeomorphism); (e) geodesic characterisation of
   mixture lines; (f) "distance from featurelessness" functional properties; (g) something we have not
   thought of that a geometer would consider the essential object here.

3. **The multiplicity law.** Confirm `ℓ_t = √λ log t − (m−1)/(2√λ) log log t + O(1)` for the state
   density `ℓ^{λ−1}(−log ℓ)^{m−1}` (exactly), and give the cleanest derivation of `u² Var_u(L) =
   λ − (m−1)/log u + O(1/log² u)` that formalises: is it better to compute `Z, Z', Z''` as truncated
   Gamma-type integrals in `s = uℓ`, or to use the exponential-family identity `Var = d²/du² log Z`
   with an exact `Z` (incomplete Gamma / `E₁`), or a Tauberian route? What is the precise `O(1/log² u)`
   remainder bound with an explicit constant?

4. **Two-sided profile.** For the profile `e^{-(y^p + c y^q)}` with `c < 0` (the negative side of the
   window), moments are still finite; is the window isometry `ℓ_t(−c₋t^{-σ*}, c₊t^{-σ*}) =
   ∫_{−c₋}^{c₊} h(c) dc` worth stating (it is already a special case of our exact identity for any real
   window), and is there a nontrivial statement about `h(c)` as `c → −∞` (the crossover to the
   negative chamber, `h(c) ~ K|c|^{?}`) that closes the picture between the wall window and the `√t`
   chamber?

Please answer with concrete theorem statements, proof sketches at the level of the key identities,
Lean-feasibility remarks (Mathlib: incomplete Gamma exists as `Real.Gamma`/`integral_rpow_mul_exp_neg`
lemmas; `E₁` does not), and a ranked plan of at most six items.
