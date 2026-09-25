# Research round 22: mapping the space of responses across the data manifold

## Context (unchanged conventions)

Laplace seabed (`Laplace/Multi/*`), namespace `Laplace.Multi`. Posterior `ρ_{t,q} ∝ e^{-t L_q} π`,
`L_q(w) = E_q[ℓ(w,·)]`. Mixture path `q_s = (1−s)q₀ + s q₁` ⇒ affine losses `L_s = L₀ + sΔ`
(`pathLoss`). Response map `q ↦ Φ_q = ρ_{t,q}`. Three layers: exact (finite t, bounded contrasts),
asymptotic (t → ∞, Laplace), singular-stratified (Hironaka atlas / walls). Featureless = LOSS-NEUTRAL
(constant `L_{q₀}`), per your round-21 correction.

## The user's direction (verbatim)

"make sure we are tackling core features of the change in posterior expectation values with the
change in the data distribution that allow us to "map" the space of responses across the data
manifold (ideally, all the way from the "featureless" distribution of maximal entropy to our actual
data distribution). What would it take to do this with maximum beauty and depth?"

## Landed since round 21 (all sorry-free, pushed)

1. `ProfileResponse` (renamed; `WallResponse` was taken): profile law `ρ_c ∝ e^{-(y^p + c y^q)}`
   on `(0,∞)`; `hasDerivAt_profilePosterior : ∂_c⟨ψ⟩_c = −Cov_c(ψ, y^q)` (unbounded score dominated
   by `e^{-y^p}`); `wall_posterior_eq_profile`: the finite-t posterior of `ψ(t^{1/p} w)` under
   `e^{-t(w^p + s w^q)}` at `s = c t^{-σ*}`, `σ* = 1 − q/p`, IS the profile law, for every t;
   `hasDerivAt_wall_posterior`.
2. `ProfileFamily`: the profile family is a one-parameter exponential family in the wall variable
   (`profile_expFamily : ρ_c = e^{-y^p} exp(−c y^q − A(c))`); `iteratedDeriv_profileNum :
   ∂_c^n N_ψ = (−1)^n N_{ψ y^{nq}}` (all orders, polynomial-growth ψ); `A' = −⟨y^q⟩_c`,
   `A'' = Var_c(y^q)`; `profileLogZ_convexOn` on `(0,∞)`; `profileVar_pos` (q > 0);
   `profileMean_strictAntiOn` / `profileMean_injOn`: the mean map `c ↦ ⟨y^q⟩_c` is strictly
   decreasing — the position on the wall is read off from the response.
3. `ThermoLengthAsymptotic`: `thermoLength := ∫₀¹ √fisherSpeed ds` with
   `fisherSpeed = t² Var_s(L̇_s)`; on the neutral line `fisherSpeed = t² Var_{ts}(Δ)`
   (`fisherSpeed_neutral`, from `priorExp_neutral`: mixing from a loss-neutral point = the
   temperature line of the target); `thermoLength_neutral_eq : ℓ(t) = ∫₀^t √Var_u(Δ) du`;
   Cesàro lemma `tendsto_intervalIntegral_div_log : u g(u) → c ⇒ (∫₀^t g)/log t → c`;
   **`thermoLength_neutral_div_log_tendsto : u² Var_u(Δ) → λ ⇒ ℓ(t)/log t → √λ`** — the RLCT is
   the growth rate of the thermodynamic length from the featureless point to the data; primed
   version for bounded Δ needs only the fluctuation law (continuity from `PathData.mixture`).

Earlier exact layer (round 18–21): `mixLogZ_convexOn` (log Z convex on mixture lines),
`TiltData.hasDerivAt_mixExp` (−t Cov), all-orders `iteratedDeriv_mixNum`, entire-function
`hasSum_priorZ_pathLoss`, `mixKL_eq` (Bregman), `responseForm` (t² Cov, bilinear, PSD),
`responseForm_asymptotic` (t·responseForm → ∇R_v H⁻¹ ∇R_u via `gibbsCov_first_order_rate_sharp_posDef`),
`tiltCov_self_eq_zero_iff` (nullspace), Gibbs variational principle + uniqueness, `PathData`/`PathData2`
(C¹/C² paths, e-geodesics), `abs_priorExp_sub_le_integral` (displacement ≤ ∫ √Var(φ) √g),
`ScoreBridge` (four-integral bridge `tendsto_response_of_four`, regular instance), `TwoMonomialWall`
(general p,q wall, both regimes), `WallLogMultiplicity`/`WallSecondCrossover`, `ValuationLP`,
`CoefficientResponse`/`TermScoreResponse`/`AssembledResponse` (unit-coefficient response in atlas
terms, `−λ Cov_{ν_a}(φ, R_v/U_a)`), `GammaFaceMarginal`.

## Candidate next targets (my ranking; please re-rank, correct, and add what I am missing)

A. **Three scales of thermodynamic distance on the data manifold.** With fluctuation laws as
   hypotheses: (i) same truth and Δ vanishing to second order on it: `t² Var_s(Δ) ≤ C` uniformly
   ⇒ `thermoLength ≤ √C` (bounded distance as t → ∞); (ii) featureless → data: `√λ log t`
   (DONE); (iii) different truths / Δ with nonzero gradient at the minimiser: `t Var_{t,s}(Δ) → κ(s)`
   ⇒ `thermoLength/√t → ∫₀¹ √κ(s) ds` (dominated convergence on `[0,1]`, needs uniform domination).
   Instances: (iii) pointwise from `responseForm_asymptotic` (`κ(s) = ∇Δ H_s⁻¹ ∇Δ` at the moving
   minimiser); (ii) for the Gaussian-prior anharmonic model from `localisedVar_energy_leading`
   (`t² Var → d/2`, with rate) — needs `priorCov volume (Gaussian) L L L u = gibbsCov(localised) …`
   and continuity in u down to u = 0.
B. **The asymptotic response metric on the data manifold**: `fisherSpeed/t → ⟨∇_w Δ, H⁻¹ ∇_w Δ⟩`
   pointwise in s — the data manifold inherits the pullback of the inverse-Hessian metric through
   `q ↦ ∇_w L_q(w*)`; the response map is an "isometry up to √t" for regular models. (Is the
   correct object the Fisher–Rao metric of the model at w* pulled back by the score of the data
   variation? Please state the cleanest invariant form.)
C. **Global convexity on the data simplex**: for `k` contrasts, `a ↦ log Z_t(L₀ + ∑ aᵢ Δᵢ)` is convex
   on `ℝ^k` with Hessian the response form `t² Cov(Δᵢ, Δⱼ)`; the free energy is concave on the
   whole affine space of losses, so the response map on the data simplex is the gradient map of a
   convex potential (Legendre duality: mean parameters ⟨Δᵢ⟩ ↔ natural parameters aᵢ; injective when
   the contrasts are non-degenerate, by the nullspace theorem). Cheap via restriction to lines.
D. **Uniform-in-s convergence of the assembled score asymptotics** (your round-21 "single most
   valuable"): still open; large.
E. **The wall as a bridge between the exact and singular layers along the neutral line**: on the
   neutral line temperature `ts` and mixture weight `s` are the same coordinate, so the wall
   crossover `s = c t^{-σ*}` becomes a statement about a *segment of length t^{-σ*}* of the data
   manifold near the featureless point? (I suspect this is confused — the wall lives in the
   coefficient of the q-monomial, not in the mixture weight from a neutral point. Please clarify what
   "crossing a wall while moving along the data manifold" means concretely, and which finite-t
   object we should prove converges.)
F. **Strict monotonicity along a mixture line** (`mixExp_strictAntiOn` for non-degenerate Δ) and
   "moments determine the path" (`priorZ_pathLoss_eq_of_moments_eq` from `HasSum.unique`).

## Questions

1. Re-rank A–F for beauty × depth × reachability in Lean 4 + Mathlib given the seabed; add
   anything essential I am missing for a "map of the space of responses across the data
   manifold" — in particular, is there a single theorem that deserves to be THE statement of this
   programme (the analogue of "the RLCT is the growth rate of thermodynamic length" but for the
   whole manifold, not one line)?
2. For A(iii)/B: what is the right invariant formulation of the limiting metric on the data
   manifold, and what hypotheses on the moving minimiser `w*_s` are needed for uniformity on
   `[0,1]`? Is there a cheap route to uniform domination of `t Var_{t,s}(Δ)` on a compact
   s-interval from the seabed's regular-model rate theorems (which are stated at fixed potential)?
3. For C: the statement `ConvexOn ℝ univ (a ↦ log Z(L₀ + ∑ aᵢ Δᵢ))` from the line result — any
   pitfalls, and is the Legendre-duality statement (mean map is a diffeomorphism onto its image when
   the response form is positive definite) reachable with the existing `responseForm` API?
4. Sanity-check the claim "RLCT = growth rate of thermodynamic length": is `u² Var_u(L) → λ` the
   right singular fluctuation law (Watanabe: the posterior variance of `nL_n` at inverse temperature
   β… what exactly is the constant in the *fixed data distribution, t → ∞* setting we use — λ, or
   λ/… , or the singular fluctuation ν?), and does the log-divergence survive when the prior is
   improper at u = 0 (flat prior on ℝ^d)? Our theorem assumes a proper prior implicitly (finite
   `priorZ` at every u ≥ 0).
5. Any corrections to the landed statements (in particular `profile_expFamily`,
   `profileMean_strictAntiOn`, `thermoLength_neutral_eq`).
