# Research consult, round 29 (germbij / laplace `Laplace/Multi/*`)

Same programme (PI direction, verbatim: "make sure we are tackling core features of the change in posterior
expectation values with the change in the data distribution that allow us to *map* the space of responses across the
data manifold — ideally all the way from the featureless distribution of maximal entropy to our actual data
distribution. What would it take to do this with maximum beauty and depth?"). Everything below is formal, sorry-free,
on `main`.

## Landed since round 28 (your ranking 1–6)

1. Quotient mean map (your #1) — `QuotientMeanMap`: the invisible directions `K = {v : R_v =ᵐ const}` form a
   `Submodule`; `M(a+k) = M(a)`; `⟨M(a) − M(b), k⟩ = 0`; **`M(a) = M(b) ↔ b − a ∈ K`**; strict monotonicity
   `⟨M(b) − M(a), b − a⟩ = −t∫₀¹ Var_{a+s(b−a)}(R_{b−a}) ds < 0` off `K`. (The `K^⊥`-restricted open-embedding
   packaging is NOT built — pure Lean plumbing over `MeanMapChart`.)
2. Interior-minimum geometry (your #2) — `InteriorMinimumTwoMono`, for the two-monomial wall only, as a corollary of
   the chamber law rather than through your domination wrapper: `x_a = (q|a|/p)^{1/(p−q)}`, `H_a = p(p−q)x_a^{p−2}`,
   **`√H_a |x_a'| = k₋|a|^{β−1}`**, **`fisherSpeed t a / t → f'(x_a)²/H_a`** (`f = x^q`), and
   **`ℓ_t(a₀,a₁)/√t → ∫_{a₀}^{a₁} √H_a |x_a'| da = K₋(−a₀) − K₋(−a₁)`** for `a₀ ≤ a₁ < 0`. The abstract 1D uniform
   theorem (moving minimiser, general `V`, dominated convergence in `a`) is NOT built.
3. Two-term wall law (your #3): NOT attempted yet. Your second-order coefficient
   `Var_B(√B(z^q−1)) = q²/(p(p−q)) + q²(p−2)/(2p²(p−q)) B⁻¹ + O(B⁻²)` was CONFIRMED numerically for
   `(p,q) = (4,2),(3,1),(5,2)` (quad on the rescaled profile, `B` up to 400, residual `O(B⁻²)`).
5+6. Ray chart + Legendre (your #5, #6 core) — `RayChart`: `Var_u = Z⁻¹∫(ℓ−m(u))²e^{−uℓ}dν > 0` unless `ℓ` is
   a.e. constant under `ν`; `m(u) = ⟨ℓ⟩_u` strictly decreasing on `(0,∞)`, image an interval, and a homeomorphism
   `(0,∞) ≃ₜ m''(0,∞)` (`exists_rayChart`); `F = log Z` convex with `F' = −m`; tangent inequality;
   **`KL(P_u‖P_0) = −u m(u) − F(u) + F(0) = F(0) + sup_{v>0}(−m(u)v − F(v))`**, attained at `v = u`.
   NOT done: the endpoint identification `m(∞) = ess inf ℓ` (Laplace-type), and the rate-function statement in
   Cramér's own form (`I(x) = sup_u(−ux − F(u))` as a function of the level `x`, with `I(m(u)) = KL(P_u‖P_0)`,
   `I'(m(u)) = −u`, `I''(m(u)) = 1/Var_u`: the Fisher speed as the curvature of the rate function in the chart).
Also since round 27: `WallPhaseDiagram` (three-regime phase diagram + ray self-similarity), `TwoValuedGeodesic`,
`MultiplicityModelK`, `DataQuotient`, `GlobalWallChart`, `AffinityKL`, `ProductPrior`, `NegativeChamberLaw`.

## Where the programme stands (our reading)
The "map of responses across the data manifold" now has: (i) the local structure (response form = `t² Cov`, kernel =
invisible contrasts, mean map descends to the quotient and is strictly monotone there); (ii) the featureless ray
charted by `⟨ℓ⟩_u` with `F` as potential and KL(·‖prior) as Legendre dual, self-similar under regular variation with
modulus `λ`; (iii) one fully worked wall (two monomials) with its phase diagram: `√t`·(interior-minimum length) below
the wall, `(1/√q) log t` at the wall, bounded above it, chart `ℝ ≃ₜ (0,∞)`; (iv) the ray of the multiplicity-`k` model
`log t − (k/2) log log t`; (v) the two-atom great circle. What is missing for a *global* map from the maximal-entropy
end to the data: a statement that connects the ray chart at `u = t` (the temperature) to the affine data chart at the
same `t` (the mean map `M`), i.e. a single geometric object on `(0,∞) × (data directions)` whose restriction to the
ray is `RayChart` and whose restriction to each `t`-slice is `MeanMapChart`/`QuotientMeanMap`; and the two-term law
that would make the wall's constants sharp.

## Questions
1. **The joint chart.** On `(t, a) ∈ (0,∞) × ℝ^k` with `L_a = L₀ + ∑ aᵢRᵢ` and posterior `∝ e^{−tL_a}π`, the natural
   coordinates are `(⟨L_a⟩_{t,a}, M_{t}(a)) = (mean loss, mean map)`. The pulled-back Fisher metric on `(t,a)` is
   `t² Cov` in the `a`-directions, `Var(L_a)` in the `t`-direction, cross term `t Cov(L_a, R_v)`; the potential is
   `F(t,a) = log Z(t,a)` with `∂_t F = −⟨L_a⟩`, `∂_{aᵢ}F = −t⟨Rᵢ⟩`, and the metric is the Hessian of `F` in the
   coordinates `(t, ta)` (a Hessian/dually-flat structure). Is the cleanest global statement "the map
   `(t, ta) ↦ ∇F` is a diffeomorphism of `(0,∞) × ℝ^k` (mod `K`) onto an open convex set, with `KL(P_{t,a}‖P_{t',a'})`
   the Bregman divergence of `F`", and does the landed material (`MeanMapChart` IFT + `QuotientMeanMap` monotonicity +
   `RayChart` convexity) reach it in ≤ 600 lines? Spell out the exact statement and hypotheses (bounded `Rᵢ`, finite
   alphabet, positive prior are what we have), and what the *global* injectivity argument is in the joint variable
   (we have the segment identity `⟨∇F(b) − ∇F(a), b − a⟩ = −∫ Var < 0` for the `a`-slice; does the same segment
   argument in `(t, ta)` need `Var_{t,a}(L_a) > 0` only, i.e. `L_a` not a.e. constant?).
2. **Cramér form of the ray.** Give the Lean-ready statement of `I(x) := sup_{u>0}(−ux − F(u))` on the chart image
   with `I(m(u)) = KL(P_u‖P_0) − F(0)`, `I` convex, `I'(m(u)) = −u`, `I''(m(u)) = 1/Var_u(ℓ)`, and therefore
   `ds² = Var_u du² = I''(m) dm²`: the Fisher length of the ray is `∫ √(I''(m)) dm` in the chart. Which hypotheses
   beyond `RayChart`'s (three tilted moments, `Z > 0`, nondegenerate) are needed for `I'`, `I''` (the inverse function
   theorem for `m` uses `Var > 0` and `C¹`; we have `hasDerivAt_lawMean`)?
3. **The endpoint `m(∞) = ess inf ℓ`.** For `ν` with `hpos` and regular variation of index `λ` at `u → ∞` (our
   `RegVar`), `m(u) ~ λ/u → 0 = ess inf ℓ` is already `tendsto_mul_lawMoment_one_div_of_regVar`. Is there a clean
   general statement without regular variation (`m(u) → ess inf` for any `ν` with `ess inf ℓ` finite), and is it worth
   it, or is the regularly-varying case the natural one for the programme?
4. **Two-term wall law**: with the coefficient confirmed, rank the sub-steps and give the abstract expanding-window
   theorem in Lean-ready form (we have `WallRecedesStrong` for the positive tail `h(s) = 1/(√q s) + O(s^{−1−δ})`;
   the negative tail needs `Var_B = c₀ + c₁/B + O(B⁻²)`, which is one more Taylor term in `HalfLineLaplace`'s
   `tendsto_sqrt_mul_integral` — say exactly which centred moments/odd terms enter `c₁`).
5. Anything else that the landed material makes cheap and that serves the *global map* (featureless → data) more than
   the items above. Re-rank everything.
Be concrete and Lean-aware; where you propose a theorem, spell out the hypotheses.
