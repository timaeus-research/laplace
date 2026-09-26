# Round 46: the response map from the featureless law to the data — what remains?

Same laplace Lean formalisation (`Laplace/Multi/*`, Lean v4.33.0, Mathlib recent, all sorry-free). Standing direction from the user:
"map the space of responses across the data manifold, ideally all the way from the featureless distribution of maximal
entropy to our actual data distribution, with maximum beauty and depth". Your round-45 ranking is now essentially done.

## Landed since round 45 (all formal)
- ResponsePathDifferential: for ANY response path `M : ℝ → J → ℝ` with `M s − m₀ ∈ 𝕍`, differentiable at s₀ with `M s₀ ∈ relint`:
  `θ' = (Dm(θ)|_𝕍)⁻¹ M'`, `d/ds 𝓘(M s) = −⟨θ(M s₀), M'⟩`; `obsV φ v = E_{P_{θ(v)}} φ` has `D(obsV φ)[u] = −Cov_θ(φ, ⟨(Dm|_𝕍)⁻¹u, S⟩)`;
  `Π_ν(M) = familyMeasure (θ(M))` on the relint; `d/ds E_{Π(M s)} φ = −Cov_{Π(M s₀)}(φ, ⟨θ', S⟩)`.
- ChartContinuity: `θ ↦ chartDeriv θ` and `θ ↦ (chartDerivEquiv θ).symm` continuous (C¹ chart).
- StraightPathAtlas: `M_s = (1−s)m₀ + sM` in relint for s<1; `θ_s` C¹ on [0,1) with `θ_s' = (Dm|_𝕍)⁻¹Δ`; `d/ds 𝓘(M_s) = −⟨θ_s, Δ⟩`;
  curvature `κ(s) = Var_{P_{θ_s}}⟨θ_s', S⟩ ≥ 0` continuous; **`𝓘(M_r) = ∫₀ʳ (r−s) κ(s) ds`** and `→ 𝓘(M)` as r↑1;
  `KL((1−b)ν + bD ‖ ν) = 𝓘(M_b) + KL(D_b ‖ Π(M_b))`.
- PinskerEvent / PinskerObservable: Hoeffding `log E e^g ≤ E g + r²/2`; `2(μA − ηA)² ≤ KL`; `(E_μF − E_ηF)² ≤ 2L² KL`;
  along the bridge every event probability and every bounded posterior expectation of `Π(M_s)` converges to that of `Π(M)`
  with modulus `𝓘(M) − 𝓘(M_s)`.
- DualFisherMetric: `∇𝓘(m₀+v) = −θ(v)` eventually; Hessian `D_v[∇𝓘(w)][u] = Cov_θ(⟨u',S⟩,⟨w',S⟩)`, `u' = (Dm|_𝕍)⁻¹u`; symmetric,
  positive definite on 𝕍.
- DataFisherBudget: `x log x − x + 1 = ∫₀¹ (1−s)(x−1)²/(1−s+sx) ds` (x ≥ 0); **`KL(D‖ν) = ∫₀¹ (1−s) 𝓕_data(s) ds`** in ℝ≥0∞,
  `𝓕_data(s) = ∫ (f−1)²/(1−s+sf) dν`.
- Earlier (rounds 41–45): moment body, intrinsic chart bijection & differentiability, entropy projection = rate, Pythagorean
  minimiser, information decomposition, mixture bridge, endpoint KL certificate, conditioning chain rule & exposed-face certificate,
  Bregman form of the family KL, response susceptibility along tilt paths, basepoint curvature (regression, residual variance),
  quadratic information lower bound `𝓘(M) ≥ ‖M−m₀‖²/(2B²)`, cubic response tensor, invisible information derivative & curvature.

## Still open from round 45
- item 2b: inverse-stability constant `κ_r = e^{−2Br} λ₀` on balls (density bound of `P_θ` w.r.t. `ν`, variance comparison,
  coercivity of `C_0` on the unit sphere of 𝕍, segment integration).
- item 6: strict-convexity gap identity `(1−t)𝓘(M₀) + t𝓘(M₁) − 𝓘(M_t) = (1−t)KL(P₀‖Q_t) + tKL(P₁‖Q_t) + KL(Q_t‖Π(M_t))` at boundary
  points (needs the mixture compensation identity for KL with general densities).

## Questions
1. Taking stock: does the landed layer now "map the space of responses across the data manifold from the featureless law to the
   data law" in the sense you'd defend to a demanding referee? What is the single most important missing theorem, if any?
2. Rank the next 4–6 theorems (precise Mathlib-flavoured statements, hypotheses, proof routes reusing the landed layer). Candidates:
   (a) the two open items above; (b) a "response-manifold" packaging: `𝕍` with the Fisher metric `C_θ`, the responses with `C⁻¹`,
       the e- and m-geodesics (tilt segments in θ, straight segments in M), and the statement that `Π` maps m-geodesics of laws
       (mixtures) to m-geodesics of responses while e-geodesics of the family are fixed — with the generalised Pythagorean
       theorem `KL(D‖P_η) = KL(D‖Π(E_D S)) + KL(Π(E_D S)‖P_η)` for every family member `P_η` (not only `η = 0`);
   (c) the invisible information as a Bregman/"missing-Fisher" integral: `KL(D‖Π(M_D)) = ∫₀¹ (1−s)[𝓕_data(s) − κ(s)] ds` in one
       statement (both budgets exist; the subtraction needs finiteness), and its second-order expansion `= ½ Var_ν(h − g) s² + o(s²)`
       along tilt paths;
   (d) higher regularity: the chart is C^∞ (or at least C²), with the cubic tensor as the derivative of the Fisher metric —
       `D_θ C_θ[w] = T_θ(·,·,w)`; (e) the moment-body boundary: what happens to `θ_s` as s↑1 for a boundary response of finite rate
       (divergence along the exposed-face normal), tying the exposed-face certificate to the atlas; (f) an "entropy-ordering"
       statement: along the straight path `KL(Π(M_s)‖ν)` and the entropy `H(Π(M_s))` (relative to ν) are monotone, and the
       representatives form a nested family of exponential tilts.
3. Stress-test (b), (c), (e): correct as phrased? Any hidden hypotheses?
4. Which of these would you write up as the centrepiece of a paper section titled "the response atlas", and in what order?
Answer with a ranked list; be concrete.
