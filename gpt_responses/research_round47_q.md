# Round 47: the response atlas — what is the next layer of depth?

Same laplace Lean formalisation (`Laplace/Multi/*`, Lean v4.33.0, recent Mathlib, all sorry-free). Standing direction from the
user: "map the space of responses across the data manifold, ideally all the way from the featureless distribution of maximal
entropy to our actual data distribution, with maximum beauty and depth". Your round-46 ranking is now landed (items 1–5);
item 6 (C^∞) deliberately deferred per your advice.

## Landed since round 46 (all formal, general probability law ν, bounded statistics S : J → X → ℝ, 𝕍 = visible subspace)
1. **Complete information budget** (VisibleBudget, InformationBudget):
   `𝓘(M) = ∫₀¹ (1−s) κ(s) ds` in ℝ≥0∞ (κ = curvature of the straight path, `Var_{P_{θ_s}}⟨θ_s',S⟩`), and
   `KL(D ‖ Π(M_D)) = ∫₀¹ (1−s)[𝓕_data(s) − κ(s)] ds` as a real Bochner integral (both integrands integrable, the difference is
   the invisible information density). Also `gap_ge_atlasVelocity`: `(1−r)(−⟨θ_r,Δ⟩) ≤ 𝓘(M) − 𝓘(M_r)`.
2. **Generalised Pythagoras** (ProjectionPythagoras): `KL(D ‖ P_η) = KL(D ‖ Π(M_D)) + KL(Π(M_D) ‖ P_η)` for every family member.
3. **Quantitative inverse stability** (TiltDensityBounds, InverseStability): `e^{−2Br} ≤ dP_θ/dν ≤ e^{2Br}` on `‖θ‖ ≤ r`;
   `Var_{P_θ} g ≥ e^{−2Br} Var_ν g`; coercivity `λ₀ > 0` of `C_0` on 𝕍 (compactness of the unit sphere); strong monotonicity
   `κ_r ‖θ−η‖² ≤ ⟨θ−η, m(η)−m(θ)⟩` and Lipschitz inverse `κ_r ‖θ−η‖ ≤ ‖m(θ)−m(η)‖` with `κ_r = e^{−2Br}λ₀`.
4. **Boundary escape + normal cone** (BoundaryEscape, NormalCone): for finite-rate `M ∉ relint K`, `‖θ(M_s)‖ → ∞` as s↑1
   (compactness + chart image = relint). General normal-cone theorem: if `‖θ_n‖ → ∞`, `m(θ_n) → M`, `θ_n/‖θ_n‖ → u`, then
   `⟨u, M⟩ ≤ c` for every c with `ν(⟨u,S⟩ < c+ε) > 0 ∀ε` (Laplace-principle bound from `KL(P_θ‖ν) ≥ 0`), hence
   `⟨u, x − M⟩ ≥ 0` on the moment body. Atlas instance for the normalised natural coordinates.
5. **Mixture compensation + strict convexity** (MixtureCompensation): `a KL(P₀‖ν) + b KL(P₁‖ν) = KL(Q‖ν) + a KL(P₀‖Q) + b KL(P₁‖Q)`
   for `Q = aP₀+bP₁` in ℝ≥0∞ with NO integrability hypotheses (pointwise klFun identity); gap identity
   `a𝓘(M₀)+b𝓘(M₁) = 𝓘(aM₀+bM₁) + [a KL(P₀‖Q) + b KL(P₁‖Q) + KL(Q‖Π(aM₀+bM₁))]`; **strict convexity of 𝓘 on its whole finite
   domain** (boundary strata included).
Earlier layers (rounds 41–46): moment body & relint chart (C¹, Legendre), entropy projection = rate, information
decomposition, mixture bridge, endpoint KL certificate + Pinsker (events and bounded observables), conditioning chain rule &
exposed-face certificate, Bregman form of the family KL, response susceptibility, basepoint curvature (regression/residual
variance), quadratic lower bound `𝓘(M) ≥ ‖M−m₀‖²/(2B²)`, cubic response tensor, invisible-information derivative & curvature,
dual Fisher metric (Hessian of 𝓘 on the relint, positive definite), data-Fisher budget `KL(D‖ν) = ∫₀¹ (1−s)𝓕_data(s) ds`.

## Still open
- Fixed-normal conditioning limit: `P_{η − t a} → e^{−⟨η,S⟩} 1_F ν / Z` for an exposed maximising face F of positive mass.
- C^∞ / `D_θ C_θ[w] = −T_θ(·,·,w)` (deferred).

## Questions
1. Taking stock again: with the budget, Pythagoras, stability, boundary escape/normal cone and strict convexity all formal,
   what is now the single deepest missing statement for "the response atlas from the featureless law to the data law"?
   Be demanding: which theorem would a referee ask for first?
2. Rank the next 4–6 theorems with precise Mathlib-flavoured statements, hypotheses, and proof routes that reuse the landed
   layer. Candidates we see (stress-test each; say if any is wrong as phrased or not worth doing):
   (a) **the full response map of the data law**: for a data law D of finite information and ANY observable φ bounded,
       the path `s ↦ E_{Π(M_s)} φ` from `E_ν φ` to `E_{Π(M_D)} φ` — its derivative `−Cov_{Π(M_s)}(φ, ⟨θ_s',S⟩)` (landed on
       s<1), its endpoint value at s=1 (landed via Pinsker), and a **second-order/curvature formula** for it
       (`d²/ds² E φ` in terms of the cubic tensor and the covariance), plus the statement that the visible part of φ (its
       regression on S) is what moves: `E_{Π(M_s)} φ − E_ν φ = ⟨β_φ, M_s − m₀⟩ + (nonlinear remainder bounded by ...)`.
   (b) **the invisible information at the endpoint**: `KL(D‖Π(M_D))` as the limit of `KL(D_s‖Π(M_s))` along the mixture bridge
       with a rate, and its interpretation as the information in D orthogonal to S (a "residual information" identity:
       `KL(D‖ν) − 𝓘(M_D)` equals the KL of D w.r.t. the *conditional* structure ... is there a clean conditional-KL identity
       `KL(D‖Π(M_D)) = E_D[KL(D(·|S)‖ν(·|S))]`-type statement when the tilt is a function of S? — i.e. `Π(M_D)` and `ν` have
       the same conditional law given S, so the invisible information is exactly the conditional KL given S).
   (c) **the fixed-normal conditioning limit** above (ties tilts to conditioning; the seabed has faceMeasure, ExposedChain,
       conditioning chain rule).
   (d) **a dual/Legendre statement on the whole finite domain**: `𝓘(M) = sup_q [⟨q,M⟩ − Λ(q)]` is the definition; the
       converse `Λ(q) = sup_M [⟨q,M⟩ − 𝓘(M)]` (Fenchel biconjugation) on 𝕍, with attainment at `M = m(−q)`; and
       `Λ` C¹ with `∇Λ = −m` — probably cheap given the landed layer, and completes the duality picture.
   (e) **the geodesic packaging**: mixtures of laws are m-geodesics and Π maps them to straight segments of responses
       (landed implicitly via mean_mixture); tilt segments are e-geodesics fixed by Π; the two families of paths through a
       response point and the Pythagorean orthogonality between them at Π(M).
   (f) **quantitative endpoint rate**: `KL(Π(M)‖Π(M_s)) ≤ 𝓘(M) − 𝓘(M_s) ≤ (1−s)·(something explicit)` when the rate is
       differentiable at 1 (interior M), and the `O((1−s)²)` form from the budget.
3. Among (a)–(f), which are genuinely new mathematics (vs. bookkeeping), and which would you put in the paper section
   "the response atlas" as the second centrepiece after the budget?
4. Anything we are missing entirely that a differential-geometric or large-deviations reader would expect?
Answer with a ranked list; be concrete about hypotheses and Lean-shaped statements.
