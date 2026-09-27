# Research consult, round 99 — after programme I (noise bridge, probabilistic resolution, observable Hessian, saturated dimension)

You are Astra, ranking the next mathematics for the germbij response-map programme, formalised in Lean 4 (Mathlib, laplace seabed, `Laplace/Multi/Response*.lean`). Everything below is proved, sorry-free.

## Standing direction (user, verbatim)

"Continue, but make sure we are tackling core features of the change in posterior expectation values with the change in the data distribution that allow us to "map" the space of responses across the data manifold (ideally, all the way from the "featureless" distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum beauty and depth?" Plus the resolution story (truth shift vs sampling; chambers unresolvable when sampling variance exceeds chamber size).

## Setting: as in rounds 96–98 (ν, bounded S, W = dirSpan, P_θ = ν.tilted(−⟨θ,S⟩), m, Φ, G, A, T, C, R^α, residual r_uv, modelScore f_w, SpansAffine, SaturatedAt).

## Programme I, landed 2026-09-27

I1+I2 `ResponseFisherNoiseBridge`: `meanNoiseEnergy θ z = G_θ(A⁻¹z,A⁻¹z)` = seabed `samplingEnergy`; coercivity `∃ c > 0, c‖v‖² ≤ G_θ(v,v)` on W; `‖z‖ ≤ (‖A‖/√c)√q(z)`, `|ℓ(A⁻¹z)| ≤ (‖ℓ‖/√c)√q(z)`; certificate in Fisher radius; Chebyshev `P(q ≥ r²) ≤ τ/(nr²)`; THE PROBABILISTIC RESOLUTION THEOREM `measureReal_sign_certified_ge`: data mean `m(θ₀)+te`, positive certificate at radius r, `|t|‖e‖ + (‖A‖/√c) r ≤ δ` ⇒ `P(ℓθ₀ < ℓ(θr M̂_n)) ≥ 1 − τ/(nr²)` (event = the empirical mean lies in the local chart and the response crosses the wall in the truth direction). Constants use one coercivity constant, not the sharp sups.

I3 `ResponseObservableHessian`: residual bilinear in (u,v); `secondResponse F θ u v = E[(F−EF) r_uv]` symmetric bilinear, mixed = polarisation of diagonal (algebraic; no C² statement); variance Hessian along response lines `d²/dt² Var F = E[(F−EF)² r_VV] − 2(d/dt EF)²`; residual-flat ⇒ `ConcaveOn` of the variance on intervals in the domain.

I5 (part 1) `ResponseSaturatedDimension`: `exists_modelScore_eq_of_spansAffine` (every bounded h is P_θ-a.e. `E_θh + f_w` for a unique w ∈ W); finite X with all atoms charged: `scoreEval : W →ₗ (X → ℝ)` injective with range = ker(mean functional) ⇒ `finrank W = card X − 1`. NOT done: barycentric identification W ≅ Δ°, featureless journey = mixture `(1−t)ν + tp`.

Also landed since round 97: `ResponseLineGeodesicCriterion` (mean-straight journeys LC-geodesic at t ⇔ C(θ',θ') = 0), H6 core `ResponseTwoScaleCertificate` (generic quadratic remainder; certificate), H3 abstract `ResponseSaturatedIdentification` (SpansAffine ⇒ every data law is a model law; DataLaw ≃ₜ W).

NOT started: I4 `ResponseLocalizedSamplingBias`, I6 `ResponseSimplexSphere`.

## Questions

Q1. AUDIT of I as summarised. In particular (a) the probabilistic resolution theorem's event and hypotheses — is "the empirical mean lies in the local chart" correctly captured by `‖te + ξ‖ ≤ δ` with δ from the remainder lemma whose ball lies in the domain (the theorem's conclusion only asserts the sign inequality for `θr M̂_n`; `θr` is defined everywhere as chartVInv ∘ toV, garbage outside Ω) — what should the honest statement include about existence? (b) I3's variance concavity: the hypothesis is `∀ t ∈ Icc a b, E[(F−EF)² r_{V_tV_t}] = 0` (residual-flatness pairing with (F−EF)², not r ≡ 0) — is that the right hypothesis? (c) the dimension theorem's hypotheses (Fintype X, MeasurableSingletonClass, all atoms charged, SpansAffine) — anything vacuous?

Q2. WHAT NEXT. Options: (i) I6 simplex sphere (`d_F = 2 arccos Σ√pq`; needs W ≅ Δ° identification + great-circle FisherPath + Fisher speed identification via `P_{θ_t} = p_t` pointwise); (ii) I4 localised bias (cubic remainder + 4th-moment bookkeeping); (iii) THE TESTING LOWER BOUND: two data laws in different response chambers at Fisher distance ~ r are indistinguishable from n samples unless n r² ≳ 1 — the existing seabed has `ResponseProductAffinity` (n-sample testing error ≥ (1 − √(1 − A^{2n}))/2 via affinity A of the two laws) and `sphericalDist ≤ Fisher length` (E4/G5) — so a lower bound `A(P_θ₀,P_θ₁) ≥ cos(d_F/2)` and error ≥ (1 − √(1 − cos^{2n}(d_F/2)))/2 may be nearly free: is it, and what is the honest two-sided resolution statement (certificate ⇒ resolved w.p. ≥ 1 − τ/(nr²); two model laws at intrinsic distance d ⇒ any test errs w.p. ≥ (1 − √(1 − cos^{2n}(d/2)))/2)? (iv) the barycentric identification of the saturated finite family with the positive simplex and the featureless journey as the mixture (1−t)ν + tp; (v) the "information geometry of the response quotient" summary theorem tying D–I together: a single structure `ResponseGeometry` bundling metric, connections, curvature, information potential, distance, with the saturated case as an instance; (vi) anything more beautiful. Rank ~6 modules by beauty/depth per Lean cost with precise statements, proof routes via the API, cautions.

Q3. The headline of the D–I arc in one displayed formula + two sentences; and the single thing a careful reader would still want.
