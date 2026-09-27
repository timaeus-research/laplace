# Research consult, round 97 — after programme G (endpoint action, saturation, curvature defect, information landscape, intrinsic distance, second jet)

You are Astra, ranking the next mathematics for the germbij response-map programme, formalised in Lean 4 (Mathlib, laplace seabed, modules `Laplace/Multi/Response*.lean`). Everything below is proved, sorry-free.

## The user's standing direction (verbatim)

"Continue, but make sure we are tackling core features of the change in posterior expectation values with the change in the data distribution that allow us to "map" the space of responses across the data manifold (ideally, all the way from the "featureless" distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum beauty and depth?"

And the user's resolution story: two sources of shifts of the structural coordinate — varying the truth vs sampling; chambers unresolvable when sampling variance exceeds chamber size.

## Setting (unchanged)

Reference law `ν` on `X`, bounded features `S : J → X → ℝ`, direction space `W = dirSpan ν 1 S ⊆ (J → ℝ)`, family `P_θ = ν.tilted(−⟨θ,S⟩)`, mean map `m`, response `Φ(g) = m⁻¹(E_{ν.tilted g} S)`, Fisher form `G_θ(u,v) = Cov_{P_θ}(⟨u,S⟩,⟨v,S⟩)`, chart derivative `A_θ = −Cov` operator with `G_θ(u,v) = −⟨u, A_θ v⟩`, third operator `T_θ`, m-Christoffel `C_θ(u,v) = A_θ⁻¹ T_θ(u,v)`, α-connections `Γ^α = ((1−α)/2) C`, curvature `R^α`, sectional `K`. Note: `W` is defined as the direction space of the affine hull of the moment body; the seabed's `dirProj` projects along an ARBITRARY complement (not orthogonal), and `invisibleSet ν S = {v | ⟨v,S⟩ is ν-a.e. constant}` with only `W ∩ invisible = 0` and `W^⊥_{dotJ} ⊆ invisible` available.

## Programme G, all landed (round 96 plan, executed 2026-09-27)

G1 `ResponseEndpointInformationAction`: model journey `θ_t = m⁻¹((1−t)m(θ₀)+tm(θ₁))`, C^∞ on an open domain ⊇ [0,1], `θ' = A⁻¹Δ`; `KL(P_θ₁‖P_θ₀) = ∫₀¹(1−t)G`, `KL(P_θ₀‖P_θ₁) = ∫₀¹ tG`, Jeffreys `= ∫₀¹G = −⟨θ₁−θ₀, m(θ₁)−m(θ₀)⟩`; `KL(ρ_g‖P_θ₀) = KL(ρ_g‖P_Φ(g)) + ∫₀¹(1−t)G` for every model base point.

G2 `ResponseFiniteSaturation`: `SpansAffine S ν` (every bounded h is ν-a.e. `⟨b,S⟩ + k`; holds pointwise for the finite affine-basis simplex, `spansAffine_of_forall`) ⇒ `SaturatedAt θ` for all θ, proved by REGRESSION on the scores (coefficient `c = A⁻¹(−Cov_θ(S,f_uf_v))` via `covVec_mem_dirSpan`; residual `⟨d,S⟩` uncorrelated with all scores ⇒ its covariance vector ∈ W and ⊥ W ⇒ 0 ⇒ zero variance ⇒ a.s. constant). Hence `K = ¼` for affinely spanning families. NOT done: `dim W = |X|−1`, identification with the positive simplex.

G3 `ResponseCurvatureDefect`: residual `r_uv = f_uf_v − G(u,v) + f_{C(u,v)}` centred and ⊥ all scores; `G(C(u,v),C(x,y)) = E[f_uf_vf_xf_y] − G(u,v)G(x,y) − E[r_uv r_xy]`; `G(R^α(u,v)w,x) = ((1−α²)/4)[(G_uxG_vw − G_vxG_uw) + (E[r_ux r_vw] − E[r_vx r_uw])]`; `K = ¼ + (E[r_uu r_vv] − E[r_uv²])/(4D)`; saturation ⇔ r ≡ 0 a.e.

G4 `ResponseGlobalInformationLandscape`: `T(g) = KL(ρ_g‖ν)`, `I(g) = KL(P_Φ(g)‖ν)` (constant on fibres, = weighted action), `D(g)` defect; `T = D + I`; along coefficient paths `g_t = ⟨a_t,h⟩`: `T' = Cov_{ρ_t}(g_t,ġ_t)`, `I' = −⟨θ_t, Cov_{ρ_t}(S,ġ_t)⟩`, `D' = Cov_{ρ_t}(g_t + ⟨θ_t,S⟩, ġ_t)`. (On the bounded-tilt chart, not on `DataLaw`.)

G5 `ResponseIntrinsicDistance`: `2 arccos Aff(P_θ₀,P_θ₁) ≤ d_F(θ₀,θ₁)` (every `FisherPath` competitor + `le_csInf`); Jeffreys = Fisher action of the NATURAL segment too; `d_F² ≤ Jeffreys`; `responseDist(ρ_g,ρ_k) = d_F(Φg,Φk)` pseudometric, zero iff same response. NOT done: saturated sharpening `d_F = 2 arccos Σ√pq`.

G6 `ResponseSamplingGeometry`: along a C² mean path `μ = m(θ₀) + z(t)`: `θ' = A⁻¹z'`, `θ'' = A⁻¹z'' − C(θ',θ')` (interiority needed only at the time considered); response line `θ(m(θ₀)+te)` smooth near 0 with `θ = θ₀ + tA⁻¹e − (t²/2)C(A⁻¹e,A⁻¹e) + o(t²)` (`taylor_isLittleO` on a ball). The sampling risk identities (`E q_θ(M̂−m) = tr(R_θC_D)/n`, chamber exit ≤ tr/(nr²), wall-crossing, exact face hits, truth-shift sign resolution) were already in the seabed (E5, F4, FisherNormalisedSampling, ResponseClassResolution, ResponseIntrinsicResolution).

Earlier programmes (D, E, F) give: α-connections and curvature, `DataLaw ≃ₕ W`, KL Pythagoras, fibre second jet, spherical distance ≤ Fisher length, first/second variation of the Fisher energy and the stationarity ⇔ LC geodesic characterisation, the featureless journey (global m-geodesic) and its information action `KL(ρ_g‖ν) = defect + ∫₀¹(1−t)G(θ̇,θ̇)`.

## Questions

Q1. AUDIT. Any dishonesty/vacuity in G as summarised? In particular (a) G2's regression proof — is `covVec_mem_dirSpan` (covariance vectors of dominated laws lie in W) really all that is needed, and is the a.e. formulation of `SpansAffine` the right one? (b) G6 claims "the same jet for truth and sampling" — is the deterministic Taylor expansion an honest statement about `Φ(ρ̂_n)` given that the empirical mean may leave the interior (zero cell counts)? What caveat wording is right? (c) G5: is `d_F² ≤ Jeffreys` sharp anywhere, and is the claim "`√J` is not a metric" true for exponential families?

Q2. WHAT NEXT. Programmes D–G have built: the curved response quotient, its information landscape, the intrinsic distance, and the second jets. Propose the next coherent programme of ~6 modules that deepens the user's direction with maximum beauty/depth per Lean cost. Candidates: (i) the finite simplex end-to-end: `dim W = |X|−1`, identification `W ≅` positive simplex, `d_F = 2 arccos Σ√pq` with the great-circle path as an explicit `FisherPath` (needs staying positive), and the round metric on the simplex; (ii) LC geodesics: existence/uniqueness (ODE) in the chart and whether the m-journey's image is ever LC-geodesic (`C(θ̇,θ̇) ∥ θ̇`); (iii) a Gauss–Bonnet / holonomy statement for 2-dimensional W (`dim W = 2`): integrated curvature of a triangle of m-journeys (too hard?); (iv) response of the SECOND moment / posterior variance: `Var_{P_θ}` as a function on the data manifold and its journey, the "response of fluctuations"; (v) the resolution story upgraded: a two-scale theorem combining F4 (sign resolution) and G6 (second jet) — the truth shift `θ(μ+te)` vs sampling `θ(μ+e_n)`: distribution of the SIGN of `⟨a, θ̂_n − θ⟩` including the curvature correction `−½C` as a bias term, with an exact bias formula `E[θ(μ+e_n)] − θ = −½ E[C(A⁻¹e_n,A⁻¹e_n)] + o(1/n)` (needs remainder control — what is the honest minimal statement?); (vi) the featureless law as maximal entropy: a clean statement `ν = argmax` of reference-relative entropy and the journey as the "entropy descent" `t ↦ H(ρ_t)`; (vii) anything you consider more beautiful. Rank, give precise statements, proof routes via the existing API, and cautions (what is false).

Q3. Headline for the whole D–G arc in one displayed formula and two sentences, and one sentence on what the arc has NOT established that a careful reader would want.
