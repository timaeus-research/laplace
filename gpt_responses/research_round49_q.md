# Round 49: the response atlas after the residual split — what next, and what would you write?

Same laplace Lean formalisation (`Laplace/Multi/*`, Lean v4.33.0, recent Mathlib, all sorry-free). Standing user direction:
"map the space of responses across the data manifold, from the featureless law to the actual data law, with maximum beauty
and depth". Your round-48 ranking is now fully landed.

## Landed since round 48 (all formal, general probability law ν, bounded statistics S : J → X → ℝ, 𝕍 = visible subspace)
- ObservableCurvature: `d/ds E_{P_{θ_s}}φ = −Cov(φ,⟨θ_s',S⟩)` along any C¹ path; `d/ds Cov_{P_{θ_s}}(f,g) = −T(f,g,⟨θ_s',S⟩)`;
  atlas: `F'(s) = −Cov_{P_s}(φ,⟨v_s,S⟩)`, `F''(s₀) = T_{P_{s₀}}(r₀,⟨v_{s₀},S⟩,⟨v_{s₀},S⟩)` with the frozen residual
  `r₀ = φ − ⟨β₀,S⟩` (regression coefficient supplied by the chart via the dual-annihilator argument). No inverse differentiated.
- StatisticLift: `D↑ = ν.withDensity (d(S_*D)/d(S_*ν) ∘ S)`; `S_*D↑ = S_*D`, `D ≪ D↑`; base split `KL(D‖ν) = KL(D‖D↑) + KL(S_*D‖S_*ν)`;
  `KL(D↑‖ν) = KL(S_*D‖S_*ν)`; lift = unique least-informative realisation of a statistic law; bounded-tilt residual split.
- ResidualInformation / GeneralResidualSplit: residual split for ANY probability law `P = ν.withDensity (g∘S)` (unbounded g);
  every finite-rate projection is `ν.withDensity (g ∘ S)` (exposed chain sets are preimages `S⁻¹B`); hence
  `KL(D‖Π(M_D)) = KL(D‖D↑) + KL(S_*D‖S_*Π(M_D))` for EVERY finite-information data law (boundary included);
  tower law `KL(D‖D↑ᵀ) = KL(D‖D↑ˢ) + KL(D↑ˢ‖D↑ᵀ)` for `T = h∘S`.
- Earlier (rounds 41–47): moment body & relint chart (C¹, Legendre), entropy projection = rate, information decomposition,
  generalised Pythagoras, mixture bridge, endpoint certificate + Pinsker, conditioning chain rule & exposed chains (exhaustion),
  fixed-normal limit (TV + exact KL), boundary escape + normal cone, Bregman family KL, response susceptibility, basepoint
  curvature, quadratic lower bound, cubic tensor, invisible-information derivative, dual Fisher metric (Hessian), data-Fisher
  budget, complete information budget `𝓘(M) = ∫₀¹(1−s)κ`, `KL(D‖Π) = ∫₀¹(1−s)[𝓕_data − κ]`, inverse stability `κ_r = e^{−2Br}λ₀`,
  strict convexity on the finite domain (mixture compensation), Legendre closure, exact endpoint tail `KL(Π(M)‖Π(M_s)) = ∫_s^1(1−u)κ`
  + quadratic bound on balls, variational Fisher (minimal cost), Cramér upper/lower bounds for empirical responses.

## Questions
1. Taking stock: is there now a complete, defensible "response atlas from the featureless law to the data law"? State in a
   few sentences what the atlas IS, in the terms that the formal layer supports, and the one or two claims a referee would
   still push on.
2. Rank the next 4–6 theorems (precise, Lean-shaped, hypotheses, proof routes reusing the landed layer). Candidates:
   (a) the invisible information along the bridge: `R_s = KL(D_s‖ν) − 𝓘(M_s)` (mixture bridge `D_s = (1−s)ν + sD`), its exact
       modulus `(1−s)H − δI_s ≤ R_1 − R_s ≤ (1−s)H + h₂(s) − δI_s` from mixture compensation (your 3B), and the split of `R_s` into
       fibre + marginal parts at each `s` (the fibre part of `D_s` — how does `D_s↑` relate to `D↑`? `(D_s)↑ = (1−s)ν + sD↑`?
       is the fibre information along the mixture bridge `KL(D_s‖D_s↑)` monotone/convex in `s`?);
   (b) the Fisher tangent/fibre decomposition as an L²(P) orthogonal projection (your round-47 item 5 in full): the visible score
       space `{⟨v,S−M⟩}`, its Fisher-orthogonal complement, `‖h‖² = ⟨A h, C⁻¹ A h⟩ + ‖h − Ph‖²`, and its relation to the
       fibre/marginal split (is the fibre information second-order the L² norm of the fibre component of the score?);
   (c) the second-order expansion of the invisible information along tilt paths `D_s = ν.tilted (s h)`:
       `KL(D_s‖Π(M_{D_s})) = ½ s² Var_ν(h − ⟨β,S⟩) + o(s²)` — i.e. the fibre+marginal information is, to second order, the residual
       variance of the score after visible regression (ties (b) to the landed `residual_variance`/`hasDerivAt_deriv_invisible_dataPath_zero`);
   (d) differential geometry packaging: dual affine structures (e/m), the cubic tensor as the difference of the two connections
       `∇* − ∇`, Amari–Chentsov symmetry from `thirdCentral_comm`, and the statement that the straight path of the atlas is
       m-affine while tilt segments are e-affine — what is provable cheaply and what would be misleading;
   (e) an operational sample-level theorem tying the atlas to data: with n samples, the empirical response `M̂_n = E_{D̂_n} S`
       and `Π(M̂_n)` — consistency `Π(M̂_n) → Π(M_D)` (in KL or TV) via the landed Lipschitz inverse chart and the endpoint
       results, plus the Cramér rate for `P(M̂_n ∈ F)`;
   (f) anything else you consider deeper (e.g. the lift as a Markov/Doob-type projection, the fibre information as a
       "conditional KL" under a regular conditional distribution when X is standard Borel, or a duality between the fibre
       part and a supremum over bounded functions of S).
3. Which would be the third centrepiece of the paper section, after the budget and the fixed-normal/exposed-chain boundary
   completion? Give a suggested order of the section's subsections with the landed theorem names.
Answer with a ranked list; be concrete about hypotheses and Lean-shaped statements.
