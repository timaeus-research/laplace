# Research consult, round 96 — after programme F (the information cost of a response journey)

You are Astra, ranking the next mathematics for the germbij response-map programme, formalised in Lean 4 (Mathlib, laplace seabed, modules `Laplace/Multi/Response*.lean`). Everything below is proved, sorry-free.

## The user's standing direction (verbatim)

"Continue, but make sure we are tackling core features of the change in posterior expectation values with the change in the data distribution that allow us to "map" the space of responses across the data manifold (ideally, all the way from the "featureless" distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum beauty and depth?"

And the user's resolution story: two sources of shifts of the structural coordinate — varying the truth vs sampling; chambers unresolvable when sampling variance exceeds chamber size.

## Setting (unchanged)

Reference law `ν` on `X`, bounded features `S : J → X → ℝ`, direction space `W = 𝕍 = dirSpan ν 1 S`, family `P_θ = ν.tilted(−⟨θ,S⟩)`, mean map `m`, response `Φ(g) = m⁻¹(E_{ν.tilted g} S)`, Fisher form `G_θ(u,v) = Cov_{P_θ}(⟨u,S⟩,⟨v,S⟩)`, chart derivative `A_θ = −Cov` operator with `G_θ(u,v) = −⟨u, A_θ v⟩`, third operator `T_θ`, m-Christoffel `C_θ(u,v) = A_θ⁻¹ T_θ(u,v)`, α-connections `Γ^α = ((1−α)/2) C`, α-curvature `R^α = −((1−α²)/4)[C(u,C(v,w)) − C(v,C(u,w))]`, sectional curvature `fisherSectional θ u v`.

## Programme F, all landed (round 95 plan, executed 2026-09-27)

F1 `ResponseInformationHessian`: `K_g(θ) = KL(ρ_g ‖ P_θ)`; `DK_g(θ) = ⟨·, E_{ρ_g}S − m(θ)⟩`; `D²K_g(θ)[u,v] = G_θ(u,v)`; `DK_g(θ) = 0 ↔ θ = Φ(g)`; strictly convex along natural lines.

F2 `ResponseFeaturelessJourney`: mixture journey `ρ_t = (1−t)ν + tρ_g`; response `θ_t = m⁻¹(m₀ + tΔ)`, `Δ = E_{ρ_g}S − m₀`; mean-affine; `C^∞` on an open domain ⊇ [0,1]; `θ' = A⁻¹Δ`; `θ'' + C(θ',θ') = 0` (global m-geodesic).

F3 `ResponseInformationAction`: `d/dt KL(P_{θ_t}‖ν) = −⟨θ_t,Δ⟩`, `G_{θ_t}(θ',θ') = −⟨θ',Δ⟩`;
`KL(P_{Φ(g)}‖ν) = ∫₀¹(1−t)G_{θ_t}(θ',θ')dt`, `KL(ν‖P_{Φ(g)}) = ∫₀¹ t G dt`, Jeffreys `= ∫₀¹ G`;
HEADLINE `KL(ρ_g‖ν) = KL(ρ_g‖P_{Φ(g)}) + ∫₀¹(1−t)G_{θ_t}(θ'_t,θ'_t)dt`; `L_F² ≤ Jeffreys`.
(Only the featureless endpoint θ₀ = 0 is done; the general model-endpoint action `KL(P_{θ₁}‖P_{θ₀}) = ∫(1−t)G` along the mean-affine path is not.)

F4 `ResponseTruthShiftResolution`: for a fixed law and any baseline `b ≠ ⟨a,M_D⟩`: `P((M̂_n − b)(M_D − b) ≤ 0) ≤ Var_D⟨a,S⟩/(n(M_D−b)²)`; along a data path with `c(t) = E_{ρ_t}⟨a,S⟩`, `c'(0) = d ≠ 0`: eventually `P((M̂_t − c(0)) d ≤ 0) ≤ 4 Var_t/(n d² t²)`; `4V ≤ ε n d² t²` ⇒ correct sign w.p. ≥ 1−ε; truth velocity of an exponential journey `= Cov_{ρ_0}(⟨a,S⟩, ⟨a'_0,h⟩)`.

F5 `ResponseSimplexCurvature`: under the ABSTRACT hypothesis `SaturatedAt θ` (centred scores `f_u = ⟨u,S⟩ − E_θ⟨u,S⟩` closed under products up to constants: ∀u v ∃c, `f_u f_v − G(u,v) = f_c` P_θ-a.e.): `C(u,v) = −c`; `G(C(u,v),C(x,y)) = E[f_uf_vf_xf_y] − G(u,v)G(x,y)`; `G(R^α(u,v)w,x) = ((1−α²)/4)(G(u,x)G(v,w) − G(v,x)G(u,w))`; `K = 1/4` on nondegenerate planes.
(NOT done: the concrete instance — X finite, ν charging every point, features an affine basis ⇒ SaturatedAt. In the seabed `W = dirSpan` is the orthogonal complement of the ν-a.e.-constant directions and `dirProjL` projects `J → ℝ` onto it, changing `dirLoss` by an a.e. constant.)

F6 `ResponseFisherEnergyStationarity`: `C2Path` (θ, V, A), `TestField` (C² scalar vanishing off (0,1); `ofBump` from `ContDiffBump`), `testVariation` `Θ = θ + (sφ)z` as a `FisherVariation`; `E'(0) = −∫₀¹ φ G_θ(z, θ''+½C(θ',θ'))`; vanishing pairings ⇒ LC acceleration = 0 on (0,1); `StationaryFixedEndpoints ↔ LC geodesic on (0,1)`.

Earlier programmes (D, E) give: α-connections, curvature, `DataLaw ≃ₕ W` (contractible fibres), KL Pythagoras of the response, fibre second jet, Hellinger/spherical distance `2 arccos ρ ≤ Fisher length`, wall-crossing and exact face-hit probabilities, first variation of the Fisher energy.

## Questions

Q1. AUDIT. Are any of the F statements mathematically dishonest or vacuous as summarised? In particular: (a) F5's abstract `SaturatedAt` — is it exactly the right hypothesis, and does the finite affine-basis family really satisfy it a.e. (with `W` the complement of null directions)? Sketch the cleanest Lean route to the concrete instance. (b) F4's hypotheses on the sample family `Xs : ℝ → ℕ → Ω → X` (i.i.d. per `t` on a common `P`) — is anything lost?

Q2. WHAT NEXT. Programme F closed the "information cost of the journey" story. Propose the next coherent programme of ~6 modules that deepens the user's direction (mapping the space of responses across the data manifold from the featureless law to the data, and the resolution story), ranked by beauty/depth per Lean cost. Candidates I see: (i) the general model-endpoint action and a "response distance" `d(θ₀,θ₁)² ≤ Jeffreys`; (ii) a global statement over the whole data manifold: the map `DataLaw → W` with its fibres and the information decomposition as a function on `DataLaw` (defect + action), its continuity/smoothness in the data law; (iii) second-order response to a truth shift with sampling — the chamber-resolution story with the Fisher-normalised trace `d_eff/n` replacing `V`; (iv) the featureless journey's Fisher length vs the geodesic distance (comparison, since it is an m-geodesic, not LC); (v) curvature of the response quotient beyond saturated families: bounds `|K| ≤` third-cumulant Gram ratios; (vi) the finite saturation instance. Please rank, give precise statements, proof routes via the existing API, and cautions (what is false).

Q3. Give a headline theorem for the note's response-map section as it now stands, one displayed formula, and say whether the "featureless = maximal entropy" reading needs a caveat.
