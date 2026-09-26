# Research round 75: the vertex-gap criterion, and what remains deepest after the Fisher classification

## Landed since round 74 (laplace `Laplace/Multi/*`, sorry-free, warning-free, pushed)
- **PolytopeResponseTransport** (your rank 1, Statements 1 and 3): `continuousOn_integral_responseProjection` (bounded
  observables: `M ↦ E_{q_M}F` continuous on the whole charged polytope, via `obsL1 ∘ projL1`),
  `integral_responseProjection_atlasPath_sub_eq` (`E_{q_{M_r}}F − E_νF = ∫₀^r lin_{F,M_s}(M − m₀) ds`, `r < 1`, for every `M` of
  finite rate), **`tendsto_integral_linForm_atlasPath`** (for EVERY `M ∈ P`: `E_{q_M}F − E_νF = lim_{r↑1} ∫₀^r lin_{F,M_s}(M−m₀) ds`).
  (Statement 2, the interior facewise derivative, already existed: `ObservableHessian.hasFDerivAt_integral_response` gives
  `D[M ↦ E_{q_M}F] = covCLM ∘ R_M` on the direction space; `ResponseTransport.hasDerivAt_integral_response_path` along paths.)
- **SusceptibilityFisherBound**: `abs_linForm_le_sqrt_var_mul_sqrt` (`|lin_{F,M}(u)| ≤ √Var_{q_M}F · √⟨u, C_M⁻¹u⟩`),
  `abs_integral_responseProjection_sub_featureless_le` (`|E_{q_M}F − E_νF| ≤ ‖F‖_∞ · L` when the straight path has Fisher
  length ≤ L, for every completed response on a charged polytope).
- **RayVarianceSandwich**: `raySpeedSq_eq` (`Var_{p_t}(g) = C₂/(A+B) − (C₁/(A+B))²`), `slackMoment_one_sq_le` (`C₁² ≤ B C₂`),
  `raySpeedSq_sandwich`, `sqrt_raySpeedSq_comparable` (`√A/(A+B₀) √C₂ ≤ √Var ≤ √C₂/√A`, `t ≥ 0`).
- **ShellMassClassification** (your rank 3, exactly as you described): `ENNReal.rpow_tsum_le_tsum_rpow`, dyadic shells,
  `lintegral_sqrt_secondMomentE_le` (`∫₀^∞ √C₂ ≤ 4 Σ √a_k`), `tsum_sqrt_shellMass_le` (`Σ √a_k ≤ 2e ∫_{1/R}^∞ √C₂`),
  `lintegral_sqrt_secondMomentE_lt_top_iff`; **RayFisherLengthClassification**: `lintegral_sqrt_raySpeedSq_lt_top_iff`
  (`∫^∞ √Var_{p_t}⟨u,S⟩ < ∞ ↔ Σ_k √a_k < ∞` on the seabed's natural rays), tail/whole equivalence.
- Everything earlier: the atlas (`ChargedPolytopeAtlas`), minimal faces, exposure, face order, density bound, `L^p`, rays.

## Objects available for the vertex-gap criterion (your rank 2)
- `familyMeasure ν 1 0 S 1 θ` = `ν.tilted(−⟨θ,S⟩)` (density `famDens S ν θ = e^{−⟨θ,S⟩}/Z(θ)`), `meanMap ν 1 0 S 1 θ` its mean;
  `dirSpan ν 1 S` = the direction space `L` of the moment body (a `Submodule ℝ (J → ℝ)`, closed, finite-dim);
  `responseTheta … hS M : dirSpan` = the natural parameter of `M ∈ ri(momentBody)` (chart `relintChart : dirSpan ≃ₜ ri(momentBody)`);
  all of these are available for ANY probability reference measure, in particular for the face law `faceMeasure ν F =
  ν(·| ⟨u,S⟩ = β)`, whose moment body is the exposed face `F_u = conv{v ∈ V : ⟨u,v⟩ = β}` (`momentBody_faceMeasure_eq_of_exposed`)
  and whose `dirSpan` is therefore `L_F`; `responseProjection_eq_faceMeasure_of_exposed` (`q_M` = projection of `ν_F`);
  `exists_faceMeasure_tilted_eq_responseProjection` (`q_M = ν_F.tilted(−⟨θ,S⟩)`); charged vertex fibres `statFibre S v`,
  `ae_statPoint_mem_essRange` (`S(x) ∈ P` a.e.), `mem_convexHull_iff_exists_vertexWeights`; `tendsto_projL1_of_tendsto` (`L¹`
  continuity of `M ↦ dq_M/dν` on `P`); `famDens_ray`, `faceMass`, `offFaceMass`; the seabed has NO inner-product structure on
  `J → ℝ` (it uses `dotJ` and `Submodule`s of `J → ℝ` with the sup norm; `BiasForm.dirProj` is a projection onto `dirSpan` along a
  CHOSEN complement `Submodule.exists_isCompl`, not orthogonal).

## Questions
1. **Complement-free formulation.** We would like to state your vertex-gap criterion WITHOUT the orthogonal split
   `η = τ + ζ`, as: for `η_n : ℕ → J → ℝ`, `M ∈ ri F_u` (`F_u` exposed by `u,β` with a charged fibre), `v₀ ∈ V ∩ F_u`:
   `meanMap_ν(η_n) → M  ⟺  meanMap_{ν_F}(η_n) → M  ∧  ∀ v ∈ V∖F_u, ⟨η_n, v₀ − v⟩ → +∞`,
   where `meanMap_{ν_F}(η) = E_{ν_F.tilted(−⟨η,S⟩)} S` (the mean of the face-conditional tilt). Is this equivalent to your
   formulation (the face chart `η_F` being a homeomorphism `L_F ≃ ri F`, the face-conditional tilt depends on `η` only through
   its pairing with `L_F`)? Is it TRUE as stated (both directions), and what exactly is needed of `M` (`ri F_u` vs merely `F_u`)?
2. **Proof route in our objects.** (⇒) from `meanMap η_n → M`: `P_{η_n} = q_{meanMap η_n}` (interior), `L¹`-convergence to `q_M`
   by `tendsto_projL1_of_tendsto`; then (a) the face-conditional laws `P_{η_n}(·|F)` converge in `L¹` to `q_M` (which is carried
   by the fibre) — is the cleanest Lean statement "conditioning on a set of q_M-full measure is `L¹`-continuous at `q_M`"? and
   (b) the vertex gap via `P_{η_n}(S=v)/P_{η_n}(S=v₀) = e^{−⟨η_n,v−v₀⟩} ν(S=v)/ν(S=v₀) → q_M(S=v)/q_M(S=v₀) = 0`. (⇐) the
   "uniform domination from the finite vertex inequalities": please make precise the pointwise bound on the off-face relative
   weight `e^{⟨η_n, v₀ − S(x)⟩}` in terms of the vertex gaps and the tangential boundedness (we cannot choose the convex
   representation of `S(x)` measurably; is that a problem for dominated convergence?), and the exact statement of the DCT step.
   Give the 3–5 lemmas you would write, in Lean-shaped form, using the objects above.
3. **Face flags / iterated scales.** After the vertex-gap criterion, what is the precise statement about flags `F₁ ⊃ F₂ ⊃ …`
   (a sequence `η_n` whose gaps diverge at different rates), and does anything beyond the single-face criterion + the face
   order (`q_M ≪ q_N ↔ F_M ⊆ F_N`) carry real new content?
4. **Re-ranking.** With the atlas, transport, the Fisher bound and the exact Fisher classification landed, re-rank the
   remaining directions for the standing directive ("map the space of responses across the data manifold, from the featureless
   law to the data law, with maximum beauty and depth"): (A) vertex-gap criterion, (E) response potential `I(M) = D(q_M‖ν)`
   with `∇I = η(M)`, `D²I = C_M⁻¹` (we have `hasDerivAt_atlasRate`: `d/ds I(M_s) = −⟨θ_s, Δ⟩`, `hasDerivAt_atlasVelocity`:
   `d²/ds² I(M_s) = ⟨Δ, C⁻¹Δ⟩`, and `hasFDerivAt_genRate_chart` in chart coordinates — is the remaining content only the
   coordinate-free packaging?), (F) the Fisher length of the STRAIGHT path `M_s` to a boundary point (as opposed to the natural
   ray): is there a shell-type criterion, and is it different (the straight path is a different curve in θ-space)?, (G) the
   "featureless → data" direction as a DATA-LAW path `ρ_t = ν.tilted(t h)` (the seabed has `dataTheta`, `dataCov`,
   `hasDerivAt_genRate_dataPath`): what is the deep theorem there — e.g. the response map `t ↦ q_{E_{ρ_t}S}` compared with `ρ_t`
   itself, the "response defect" `D(ρ_t ‖ q_{E_{ρ_t}S})` and its evolution?, (H) anything else. Give a one-paragraph Lean route
   for your top choice.
