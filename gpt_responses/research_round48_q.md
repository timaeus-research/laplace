# Round 48: second-order observable transport and the residual-information split — cheapest formal routes?

Same laplace Lean formalisation (`Laplace/Multi/*`, Lean v4.33.0, recent Mathlib, all sorry-free). Standing user direction:
"map the space of responses across the data manifold, from the featureless law to the actual data law, with maximum beauty
and depth". Your round-47 ranking: items 1A, 4, 5, 6 are now formal; 1B (exhaustion by exposed chains) was already in the
seabed (`exists_exposedChain`, `ExposedChain.genRate_eq : 𝓘_ν(M) = −log ν(A) + 𝓘_{ν(·|A)}(M)`, `ExposedChain.finrank_add_le`);
Cramér's theorem for empirical responses is also already landed (`cramer_upper`/`cramer_lower`, compact-cover Chernoff).

## Landed since round 47 (all formal, general probability law ν, bounded statistics S : J → X → ℝ, 𝕍 = visible subspace)
- FixedNormalLimit: `faceMeasure_tilted` (conditioning commutes with tilting), `P_{η−ta}(·|F) = Q` for all t, face probability
  `p_t = exp(th + log ν(F) + Λ_F(−η) − Λ(−η+ta)) → 1`, `|P_t(A) − Q(A)| ≤ 1 − p_t`, `|E_{P_t}φ − E_Qφ| ≤ 2L(1−p_t)`,
  `KL(Q‖P_t) = −log p_t → 0`.
- EndpointTail: exact `KL(Π(M)‖Π(M_s)) = 𝓘(M) − 𝓘(M_s) − (1−s)𝓘'(s) = ∫_s^1 (1−u)κ(u)du` for EVERY finite-rate M (boundary
  included), `κ(u) ≤ ‖Δ‖²/κ_r` on balls, `KL ≤ ‖Δ‖²(1−s)²/(2κ_r)` when θ_u stays in a ball on [s,1).
- FisherVariational: `⟨v,Ṁ⟩² ≤ Var_P⟨v,S⟩·E h²` for score perturbations (E h = 0, E[h⟨e,S⟩] = ⟨e,Ṁ⟩); `C_P v = Ṁ ⟹
  Var⟨v,S⟩ ≤ E h²`, attained by the centred score; atlas: `κ(s) ≤ E_{P_{θ_s}} h²` for every h producing Δ.
- LegendreClosure: `Λ(q) = max{⟨q,M⟩ − 𝓘(M) : 𝓘(M) < ∞}`, attained exactly at m(−q) (uniqueness via strict convexity).

## What the seabed has for the two remaining items
For item 2 (second-order observable transport): `hasDerivAt_integral_responseProjection_path` (first order:
`d/ds E_{Π(M s)} φ = −Cov_{Π(M s₀)}(φ, ⟨θ',S⟩)` for any C¹ response path in the relint);
`hasDerivAt_lawCov_dataPath`/`hasDerivAt_lawCov_dirLoss_dataPath` (CubicResponse): along a tilt path `θ(s)` (HasDerivAt θ θ'),
`d/ds Cov_{P_{θ(s)}}(f, g) = −thirdCentral_{P_{θ(s)}}(f, g, ⟨θ',S⟩)` for bounded f, g; `hasDerivAt_atlasTheta` (θ_s' = atlasVel s
= (Dm(θ_s)|_𝕍)⁻¹Δ via `chartDerivEquiv`), `hasDerivAt_atlasVelocity` (derivative of the SCALAR −⟨θ_s,Δ⟩ is κ(s)),
`continuous_chartDerivEquiv_symm` (s ↦ (Dm|_𝕍)⁻¹ continuous, no derivative), `hasStrictFDerivAt_meanMap` (C¹ chart),
`hessian_rateFun_chart_eq` (Hessian of 𝓘 = Cov(⟨u',S⟩,⟨w',S⟩)). NOT landed: differentiability of s ↦ (Dm(θ_s)|_𝕍)⁻¹ or of
s ↦ atlasVel s as a vector; no operator-valued `D_θ C_θ = −T`.
For item 3A (residual split `KL(D‖P) = KL(D‖D↑) + KL(S_*D‖S_*P)` for P with density a function of S): Mathlib has
`MeasureTheory.Measure.rnDeriv_map (hμν : μ ≪ ν) (hg : Measurable g) : (μ.map g).rnDeriv (ν.map g) ∘ g =ᵐ[ν] ν[μ.rnDeriv ν | mg]`
(conditional expectation w.r.t. the comap σ-algebra), `toReal_rnDeriv_map`, `toReal_klDiv_map_of_ac`, `klDiv_map_of_ac`,
`klDiv_map_le` (data processing), `klDiv_compProd_eq_add` (chain rule for μ ⊗ₘ κ). The seabed has KL in `llr` and `klFun`
forms, `klDiv_tilted_right_eq`, `toReal_klDiv_tilted_right`, `integral_sub_log_le_toReal_klDiv`, faceMeasure/conditioning
identities. No conditional-expectation API has been used in the seabed so far.

## Questions
1. Item 2. Which formulation minimises new infrastructure while keeping the theorem's content?
   (a) Prove `HasDerivAt (fun s ↦ atlasVel s)` via the implicit function theorem on `F(s,v) = chartDeriv θ_s v − Δ` (needs
       joint C¹ of `(s,v) ↦ chartDeriv θ_s v`, i.e. `D_θ C_θ = −T` in operator form on 𝕍), then the product rule; or
   (b) avoid the vector derivative: state the second derivative for `s ↦ −Cov_{P_{θ_s}}(φ, ⟨v, S⟩)` with v FIXED (from
       `hasDerivAt_lawCov_dataPath`), and derive the atlas second derivative from `E_{P_s}φ' = ⟨β_{φ,s}, Δ⟩` with β the
       regression coefficient, using only the derivative of the regression coefficient... which again needs the inverse; or
   (c) a formulation of the residual-curvature identity `d²/ds² E_{P_s}φ = E_{P_s}[r_{φ,s}⟨v_s,S−M_s⟩²]` that is provable by
       differentiating the *scalar* identity `E_{P_s}φ' = −Cov_{P_s}(φ,⟨v_s,S⟩)` where the s-dependence through v_s is handled
       by... (is there a trick: since `Cov_{P_s}(⟨e,S⟩, ⟨v_s,S⟩) = ⟨e,Δ⟩` is CONSTANT in s for all e ∈ 𝕍, differentiating this
       identity gives `Cov(⟨e,S⟩,⟨v_s',S⟩) = T_s(e, v_s, v_s)`... but that presupposes differentiability of v_s).
   Give the Lean-shaped statement you would target, the exact hypotheses, and the shortest Mathlib route for the operator
   derivative if unavoidable (`HasFDerivAt` of `ContinuousLinearMap.inverse`/`Ring.inverse` on `𝕍 →L 𝕍`: `hasFDerivAt_ring_inverse`,
   `HasFDerivAt.clm_apply`, plus a way to get `HasDerivAt (fun s ↦ chartDeriv θ_s)` in operator norm from the entrywise/bilinear
   derivatives on a finite-dimensional space — e.g. via `ContinuousLinearMap.hasDerivAt` of a bilinear form using a basis?).
2. Item 3A. With Mathlib's `rnDeriv_map` in conditional-expectation form, sketch the shortest proof of
   `KL(D‖P) = KL(D‖D↑) + KL(S_*D‖S_*P)` when P = ν.tilted (f ∘ S) with f bounded and `KL(D‖ν) < ∞`, defining
   `D↑ = ν.withDensity ((S_*D).rnDeriv (S_*ν) ∘ S)`. Which integrability facts are needed and how are they obtained
   (`integrable_llr_map`? condExp pull-out `integral_condExp_mul`?). Is the `klFun`/lintegral form (no integrability) available
   here, i.e. is there a pointwise identity `klFun(ρ/(g∘S))·(g∘S) = klFun(ρ/r∘S)·(r∘S) + [klFun(r/g)·g]∘S + (cross term with zero
   ν-integral)`? Which would you do first: the tilt case (density bounded above and below) or the general P with density a
   function of S?
3. Anything cheaper and deeper we are missing given the current state (e.g. the entropy-ordering corollary, a Pinsker linear
   endpoint rate for observables from EndpointTail — trivial corollaries — vs. genuinely new structure)?
Answer with a ranked list; be concrete about hypotheses and Lean-shaped statements.
