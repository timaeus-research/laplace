# Research round 77: the facet accessibility theorem, the total response length from featureless to data, and what is deepest now

## Landed since round 76 (laplace `Laplace/Multi/*`, sorry-free, warning-free, pushed)
- **ResponseBregman**: `toReal_klDiv_responseProjection_eq` (`D(q_M‖q_N) = I(M) − I(N) + ⟨θ(N), M − N⟩`), tangent inequality, symmetrised form.
- **ResponseDefectPythagoras**: `klDiv_responseProjection_eq_add` (`D(ρ‖q_N) = D(ρ‖q_{E_ρS}) + D(q_{E_ρS}‖q_N)`), KL contraction
  `D(Πρ‖q_N) ≤ D(ρ‖q_N)`, `responseDefect_eq_iInf` (`ℰ(t) = inf_N D(ρ_t‖q_N)`).
- **FisherPathBounds** (your rank 1): `dotJ_eq_lawCov_dirLoss_responseScore` (`⟨u, v⟩ = Cov_{q_M}(⟨u,S⟩, score_v)`),
  `sq_dotJ_le_lawCov_mul_fisher` (`⟨u,v⟩² ≤ Var_{q_M}⟨u,S⟩ · |v|²_{F,M}`), `abs_dotJ_le_sqrt_lawCov_mul_sqrt_fisher`.
- **ResponseSpeedDistortion** (your rank 4): `dataThetaVel` (`θ'_t = (Dm(θ_t)|_𝕍)⁻¹ Cov_{ρ_t}(S,h)`), `hasDerivAt_dataTheta_vel`,
  `responseSpeedSq hS ν hh t := Var_{P_{θ_t}}⟨θ'_t, S⟩`, **`responseSpeedSq_eq_neg_dotJ`** (`|q'_t|²_F = −⟨θ'_t, Cov_{ρ_t}(S,h)⟩`),
  `responseSpeedSq_nonneg`, `responseSpeedSq_eq_div_of_unique` (1-D: `Cov_{ρ_t}(S,h)²/Var_{q_t}(S)`).
- **ThreePointNotContracting** (your counterexample): uniform law on `Fin 3`, `S = x − 1`, `h = 1_{x=2}`, `t₀ = log 4`:
  `dataTheta_eq` (`θ(m_{t₀}) = −log x₀`, `x₀ = (1+√13)/2`, through the inverse chart), **`responseSpeedSq_gt_dataSpeedSq`**
  (`Var_{ρ_{t₀}} h < |q'_{t₀}|²_F`): the response projection is not Fisher-contracting off the family.
- **ResponseDefectEvolution** (your rank 5, the exact identity): **`hasDerivAt_deriv_responseDefect`**: for every `t`,
  `ℰ''(t) = Var_{ρ_t}(h) − |q'_t|²_F + Cov_{ρ_t}((h − E_{ρ_t}h)², t h + ⟨θ_t, S⟩)`
  (data speed² − response speed² + off-family correction, the covariance of the squared centred score with `log dρ_t/dq_t`);
  `deriv_deriv_responseDefect_le` (`ℰ'' ≤ Var_{ρ_t} h + correction`). At `t = 0` it reduces to the residual-variance theorem.
- Earlier: `RayVarianceSandwich` (`raySpeedSq_sandwich`, `sqrt_raySpeedSq_comparable`: along the fixed-normal ray `θ − t u`,
  `√Var_{P_{θ−tu}}⟨u,S⟩ ≍ √slackMoment₂(t)` with constants `√faceMass/(faceMass + offFaceMass(0))` and `1/√faceMass`),
  `RayFisherLengthClassification` (`lintegral_sqrt_raySpeedSq_lt_top_iff`: `∫₀^∞ √Var_{P_{θ−tu}}⟨u,S⟩ dt < ∞ ⟺ Σ_k √a_k < ∞`,
  `a_k` the dyadic shell masses of the slack `β − ⟨u,S⟩` under the reference weight), `VertexGapCriterion`
  (`tendsto_meanMap_iff_faceMean_and_vertexGaps`: for a charged polytope with vertex set `V`, exposed face
  `F = P ∩ {⟨u,·⟩ = β}`, `M ∈ ri F`: `E_{P_{η_n}} S → M ⟺ E_{P_{η_n}(·|A)} S → M ∧ ⟨η_n, v − v₀⟩ → +∞ for every uncharged vertex v`
  (`v₀` a charged vertex, `A` the face fibre)), `PolytopeResponseTransport`, `SusceptibilityFisherBound`, `ResponseAtlas`
  (`ChargedPolytopeAtlas`), minimal faces, face order, `L^p`/Hellinger comparisons.

## Our objects (for precise statements)
`X` measurable, `ν` a probability measure, `S : J → X → ℝ` bounded (`hS : ∀ j, Bdd (S j)`), `J` finite; `Pfam θ = ν.tilted(⟨θ,S⟩)`
(exponential family through `ν`, natural parameter `θ : J → ℝ`, NOT assumed identifiable: `dirSpan ν 1 S` is the direction of the
affine span of the moment body, and the chart `chartV/chartVInv` is a bijection `dirSpan → ri(moment body)`); `meanMap η = E_{Pfam η} S`;
`responseProjection hS ν M = q_M` for `M ∈ ri(moment body)`, `responseTheta M = θ(M) ∈ dirSpan`; `lawCov ρ f g`;
`dirLoss S u x = ⟨u, S(x)⟩`; `raySpeedSq S ν θ u t = Var_{Pfam(θ − t u)}⟨u,S⟩`; a charged polytope: finite `V`, `statPoint S x ∈ conv V`
a.e., every vertex charged (`0 < ν{S ∈ statFibre v}` after tightening); `faceMeasure`, `faceMass`, `offFaceMass`, `faceDens`;
`minimalFacePoly V M`, `exists_exposing_polytope`, `responseProjection_eq_faceMeasure_of_exposed`. Fisher speed of a `C¹` natural-parameter
path `η : ℝ → J → ℝ` at `s`: `Var_{Pfam(η s)}⟨η' s, S⟩` (this is `lawCov (Pfam (η s)) (dirLoss S (η' s)) (dirLoss S (η' s))`).

## Questions
1. **FacetFisherAccess, precisely.** Your round-76 statement: "if `F` is a facet and `M ∈ ri F`, then `q_M` is accessible by some
   finite-Fisher-length interior path iff the normal ray producing `q_M` has finite Fisher length". Please give the statement in OUR
   objects, with every hypothesis: (a) how to say "facet" — codimension one of `aff F` inside `aff P` (`= m₀ + dirSpan`)?, or simply
   `dim dirSpan = dim(aff F direction) + 1`? Do we need identifiability (`dirSpan = J → ℝ`) or is it enough to work inside `dirSpan`
   and quotient nothing? (b) what is "the normal ray producing `q_M`": `θ_M − t u` with `θ_M ∈ dirSpan` chosen so that the face
   measure `Pfam(θ_M)(·|A)` has mean `M` — existence of such `θ_M` is our `exists_faceMeasure_tilted_eq_responseProjection`? (c) the
   path class: `η : ℝ → dirSpan` (or `J → ℝ`) `C¹` on `[0, 1)` with `meanMap (η s) → M` as `s → 1⁻`, length `∫₀¹ √Var_{P_{η s}}⟨η' s,S⟩ ds`.
   Then the proof, lemma by lemma, each with a Lean-shaped statement:
   - the decomposition `η_s = r_s u + v_s` with `v_s ⟂ u` (in what inner product — Euclidean on `J → ℝ`? or `u`-orthogonal inside `dirSpan`?);
     from `tendsto_meanMap_iff_faceMean_and_vertexGaps`, `⟨η_s, v − v₀⟩ → +∞` for uncharged `v` and the face means converge — how exactly does
     this give `r_s → +∞` and `v_s → v_M` (bounded, convergent tangential part) in the FACET case, and where does codimension one enter?
     (My guess: on a facet the face-tangential natural parameter is identifiable modulo `u`, and the face-mean convergence pins `v_s`
     through the face chart; the uncharged-vertex gaps `⟨r_s u + v_s, v − v₀⟩ = r_s⟨u, v − v₀⟩ + ⟨v_s, v − v₀⟩ → ∞` with `⟨u, v − v₀⟩ < 0`
     and `v_s` bounded then force `r_s → −∞` in the sign convention `θ − t u`.)
   - the key comparability: for `S` bounded and `v` in a compact set, `dPfam(r u + v)/dPfam(r u + v_M)` is bounded above and below by
     constants (since `|⟨v − v_M, S⟩| ≤ ‖v − v_M‖ ‖S‖`), hence `Var_{P_{ru+v}}⟨u,S⟩ ≍ Var_{P_{ru+v_M}}⟨u,S⟩` uniformly — is this the whole
     "bounded tangential tilt" step? Give the exact inequality (`e^{-2c} Var_ref ≤ Var ≤ e^{2c} Var_ref`? — variances are not monotone under
     density ratios; the correct statement is presumably through the centred second moment, `Var_P f ≤ E_P (f − E_Q f)² ≤ e^{c} E_Q (f − E_Q f)²`).
   - the Schur complement step: `Var_{P}⟨η',S⟩ ≥ (r')² · (C_nn − C_nT C_TT⁻¹ C_Tn)` where `n = u`-direction, `T` = face-tangential; we have
     `sq_dotJ_le_lawCov_mul_fisher` in the OTHER direction. What is the cleanest Lean route to `C_nT C_TT⁻¹ C_Tn = o(C_nn)`: is it
     `|Cov(⟨u,S⟩, ⟨w,S⟩)| ≤ √Var⟨u,S⟩ · √Var⟨w,S⟩` plus "Var⟨w,S⟩ stays bounded below on the face (`C_TT` nondegenerate at the limit)"
     plus "Cov(⟨u,S⟩,⟨w,S⟩) → 0 relative to √Var⟨u,S⟩ because off-face mass → 0"? Please write the estimate with explicit constants.
   - assembling: `|η'_s|_F ≥ c |r'_s| √V_ray(r_s)` eventually, then a change of variables `∫ |r'_s| √V_ray(r_s) ds ≥ ∫ √V_ray(r) dr` over
     the range of `r` (monotone `r` not needed: for a `C¹` path hitting every large `r`, `∫ |r'| g(r) ds ≥ ∫ g(r) dr` by the coarea/
     Banach indicatrix inequality — is there a simpler route, e.g. restrict to the last-passage times or use only the easy inequality
     `∫ |r'| g(r) ds ≥ ∫_{r_0}^{R} g(r) dr` for every `R` via `intervalIntegral.integral_comp_mul_deriv` on monotone pieces)? What is the
     minimal-pain Lean statement of this real-analysis step?
   - the converse (finite ray ⇒ accessible): the ray IS a path with `meanMap → M` — from which of our theorems (`exists_ray_tendsto_responseProjection_of_mem_polytope`?) does `meanMap(θ_M − t u) → M` follow?
2. **The total response length from featureless to data.** Along the data path `ρ_t = ν.tilted(t h)`, `t ∈ [0,∞)`, the response path
   `q_t = q_{m_t}` has speed `|q'_t|_F` (`responseSpeedSq`). Define `L_resp = ∫₀^∞ |q'_t|_F dt`, the Fisher length of the response path from
   the featureless law to the response of the limiting data law (`ρ_∞` = `ν` conditioned on `argmax h`, whose response may sit on the
   boundary of the moment body). (a) Is `L_resp < ∞` exactly when the LIMIT response `q_{m_∞}` is at finite Fisher distance from the
   interior (so that, on a facet, `L_resp < ∞ ⟺ Σ√a_k < ∞` for the face-fibre layers)? Or can the data path be a bad (oscillating)
   path of infinite length to an accessible boundary response? (Is the response path along a tilt ray monotone enough — `m_t` moves along
   the one-parameter family `E_{ν.tilted(th)} S`, whose natural-parameter image `θ_t` in the family is a curve, not a ray.) (b) Is there
   an inequality between `L_resp` and the DATA length `L_data = ∫₀^∞ √Var_{ρ_t} h dt` (which is finite iff `ν` has a "gap" at the maximum
   of `h`: `Var_{ρ_t} h` decays like the shell masses of `max h − h`)? The three-point example shows no pointwise contraction; is there a
   global bound `L_resp ≤ C·L_data` or a counterexample to any such bound? (c) Which of these is a theorem we can land?
3. **Re-rank for depth** given all of the above: (i) `FacetFisherAccess`; (ii) the charged-square counterexample (heavy: a dyadic cloud,
   two shell classifications, an explicit diagonal path); (iii) `L_resp` finiteness/comparison (question 2); (iv) flags / lexicographic
   exposure as the natural-parameter compactification; (v) the intrinsic Fisher completion of the atlas as a metric space (Cauchy
   completion of `ri P` under `d_F`) and its relation to the `L¹`/Hellinger completion; (vi) anything else you consider fundamental and
   reachable under the standing directive ("map the space of responses across the data manifold, from the featureless law of maximal
   entropy to the actual data law, with maximum beauty and depth"). One paragraph of Lean route each; for the top item, the precise
   statement with our objects.
