# Research consult, round 98 — after programme H (observable transport, max-entropy potential, saturated identification, geodesic criterion, two-scale certificate)

You are Astra, ranking the next mathematics for the germbij response-map programme, formalised in Lean 4 (Mathlib, laplace seabed, modules `Laplace/Multi/Response*.lean`). Everything below is proved, sorry-free.

## Standing direction (user, verbatim)

"Continue, but make sure we are tackling core features of the change in posterior expectation values with the change in the data distribution that allow us to "map" the space of responses across the data manifold (ideally, all the way from the "featureless" distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum beauty and depth?" Plus the resolution story (truth shift vs sampling; chambers unresolvable when sampling variance exceeds chamber size).

## Setting (unchanged; see rounds 96–97)

`ν`, bounded `S : J → X → ℝ`, `W = dirSpan`, `P_θ = ν.tilted(−⟨θ,S⟩)`, mean map `m`, response `Φ(g) = m⁻¹(E_{ρ_g}S)`, Fisher form `G`, `A_θ = −Cov`, third operator `T`, m-Christoffel `C = A⁻¹T`, curvature `R^α`, score residual `r_uv = f_uf_v − G(u,v) + f_{C(u,v)}`.

## Programme H, landed 2026-09-27

H1 `ResponseObservableTransport`: along a response line `θ_t = m⁻¹(m(θ₀)+te)`, `V_t = A⁻¹e`: `d/dt E_{θ_t}F = −Cov(F,⟨V_t,S⟩)`; `d²/dt² E_{θ_t}F = E[(F−EF) r_{V_tV_t}]`; `|E[(F−EF)r]| ≤ √VarF √E[r²]`; SATURATION ⇔ the second response of every bounded observable in every direction vanishes (converse tests `F = r`); `d/dt Var F = −T(F,F,⟨V_t,S⟩)`. (Not done: mixed directions by polarisation; second derivative of the variance.)

H2 `ResponseMaximumEntropyPotential`: `−KL(ρ_g‖ν) ≤ 0` with equality iff `ρ_g = ν`; the model law of a response has the largest relative entropy in its fibre (equality iff `ρ_g = P_Φ(g)`); `𝓘(t) = KL(P_{θ_t}‖ν)` along response lines has `𝓘' = −⟨θ_t,e⟩`, `𝓘'' = G_{θ_t}(V_t,V_t) ≥ 0`; along the featureless journey the model information is monotone on [0,1]. (Counterexample to monotonicity along the power-tilt path NOT formalised.)

H3 abstract, `ResponseSaturatedIdentification`: under `SpansAffine` (every bounded h is ν-a.e. `⟨b,S⟩+k`) every data law is a model law, `ρ_g = P_{Φ(g)}` (a.e. affine representation ⇒ `ρ_g = P_{−b}`; means agree ⇒ `−b − Φ(g)` invisible ⇒ same family member); defect ≡ 0; `lawResponse` injective ⇒ `DataLaw ν ≃ₜ W` (inverse `modelLaw`). NOT done: `dim W = |X|−1`, barycentric identification with the positive simplex.

`ResponseLineGeodesicCriterion` (your deferred corollary): response lines and the featureless journey are LC-geodesic at t iff `C(θ',θ') = 0` iff `T(θ',θ') = 0`.

H6 core, `ResponseTwoScaleCertificate`: generic `exists_quadratic_remainder` (C² on an open set ∋ 0 in a proper normed space ⇒ `‖F z − F 0 − DF(0)z‖ ≤ K‖z‖²` on a ball); for the inverse mean map `‖m⁻¹(m(θ₀)+z) − θ₀ − A⁻¹z‖ ≤ K‖z‖²`; THE CERTIFICATE `ℓ(θ̂) − ℓ(θ₀) ≥ tℓ(A⁻¹e) − ‖ℓ‖‖A⁻¹‖r − ‖ℓ‖K(|t|‖e‖+r)²` for `θ̂ = m⁻¹(m(θ₀)+te+ξ)`, `‖ξ‖ ≤ r`, `‖te+ξ‖ ≤ δ`; positive certificate ⇒ `ℓθ₀ < ℓθ̂`. NOT done: probability of `‖ξ‖ ≤ r` in this norm (existing bounds are in the Fisher-normalised `samplingEnergy`), cubic remainder, H5 bias formula, two-scale CLT.

NOT started: H4 `ResponseSimplexSphere` (`d_F = 2 arccos Σ√pq`), H5 `ResponseLocalizedSamplingBias`.

## Questions

Q1. AUDIT of H as summarised (honesty, vacuity, missing hypotheses). In particular: (a) H3's identification uses the seabed's `invisibleSet` and `familyMeasure_add_of_invisible` — is "every data law is a model law" the right statement, and does it really need nothing about finiteness of X? (b) H6: the certificate is stated with an arbitrary norm on W (the sup norm of the ambient coordinates restricted to W) while the sampling bounds are Fisher-normalised — what is the cleanest honest bridge (norm equivalence on finite-dimensional W with explicit constants from the Fisher form at θ₀)? (c) H1's "saturation ⇔ universal flatness" — vacuity check: is the converse's test function `F = r_uv` legitimate (bounded, yes) and is the equivalence pointwise in θ as stated?

Q2. WHAT NEXT. The arc D–H has built the curved response quotient, its information landscape, intrinsic distance, second jets, observable transport, entropy potential and the two-scale certificate. Propose the next coherent programme of ~6 modules with maximum beauty/depth per Lean cost. Candidates: (i) H4 simplex sphere (explicit great-circle FisherPath, `d_F = 2 arccos Σ√pq`; cost: finite-X atom bookkeeping, density identification `P_{θ_t} = p_t` pointwise); (ii) H5 localised bias (cubic remainder + moment bookkeeping for a random vector in W); (iii) the Fisher-norm bridge for the certificate: `‖ξ‖_G ≤ r` events with the existing `tr(R_θ C_D)/(n r²)` bound, giving a fully probabilistic two-scale sign theorem; (iv) mixed second responses `D²𝓡_F[e,d] = E[(F−EF) r_uv]` by polarisation and the symmetric bilinear "response Hessian of observables"; (v) the second derivative of the variance along response lines `E[(F−EF)² r_uu] − 2(d/dt EF)²` and concavity of posterior variance in saturated families; (vi) `dim W = |supp ν| − 1` and the simplex identification; (vii) the Gauss-type identity in α-form for the featureless journey: integrated curvature along the journey and a comparison between the m-journey length and d_F (`L_F − d_F ≤ ∫ ‖C(θ',θ')‖…`?) — is there an honest such estimate?; (viii) anything more beautiful you see. Rank, give precise statements, proof routes via the existing API, and cautions.

Q3. Headline for the whole D–H arc (one displayed formula + two sentences), and the single most important thing a careful reader would still want.
