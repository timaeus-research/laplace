# Research round 79: after the facet accessibility theorem — the data-ray strengthening and what is deepest now

## Landed since round 78 (laplace `Laplace/Multi/*`, sorry-free, warning-free, pushed)
- **FacetSchurBound** (your Lemma D, scalar): `facet_schur_bound`: `Var_q(a₀ ℓ + f) ≥ a₀² Var_q ℓ (1 − 4κ ε/p)` for `ℓ ≥ 0`,
  `p = q{ℓ = 0} > 0`, `ε = q{ℓ = 0}ᶜ`, `|f| ≤ K`, `K² ≤ κ Var_q f`.
- **RayTiltInvariance** (your §6): `lintegral_sqrt_raySpeedSq_lt_top_iff_tilt`: finite Fisher length of a normal ray is independent
  of the tangential lift (accessibility all-or-nothing on `ri F`).
- **FaceGauge** (your Lemma B): `faceTheta η ∈ T'` (face natural coordinate of the face mean), `familyMeasure_faceMeasure_faceTheta`
  (`P^A_η = P^A_{faceTheta η}`), `tendsto_faceTheta` (continuity of the inverse face chart), the FACET hypothesis in the form
  `T' = W ∩ u^⊥` (`hT : ∀ w ∈ W, ⟨w,u⟩ = 0 → w ∈ T'`, plus `u ∈ W`), `normalDepth η = −⟨η,u⟩/⟨u,u⟩` (LINEAR, because face directions
  are `u`-orthogonal), `eq_faceTheta_sub_smul` (`η = faceTheta η − normalDepth η • u` on `W`), `tendsto_normalDepth_atTop`
  (off-face vertex gap ⇒ depth → ∞), `tendsto_faceTheta_normalDepth_of_tendsto_meanMap`.
- **FaceMassConcentration**: `P_{v_i − r_i u}(A) → 1` for `v_i → v_M`, `r_i → ∞` (any filter), via the ray and a vanishing bounded tilt.
- **FaceCoercivity**: `q(A) Var_{q(·|A)} f ≤ Var_q f`; conditioning commutes with tilting; `exists_coercive_familyMeasure`
  (`Var_{P_θ}⟨w,S⟩ ≥ λ‖w‖²` on the direction space, by compactness); `eventually_coercive_of_components` (uniform `λ` along
  `v_i − r_i u`).
- **FacetFisherAccess**: `lintegral_sqrt_raySpeedSq_lt_top_of_path` (forward; `C¹` path `η : ℝ → W` on `[0,∞)`, means → `M ∈ ri F`,
  `∫⁻_0^∞ √Var_{P_{η s}}⟨η'_s,S⟩ < ⊤` ⇒ `∫⁻_0^∞ √raySpeedSq(0,u,r) < ⊤`), `tendsto_meanMap_ray`,
  `exists_path_of_lintegral_sqrt_raySpeedSq_lt_top` (converse: the ray `v_M − s u`), and **`facet_fisher_access_iff`** — THE FACET
  ACCESSIBILITY THEOREM (both directions), exactly your §1.2 statement (path class: `C¹` on `Ici 0` with parameter → ∞, length as an
  `lintegral`, no integrability hypothesis).
  Proof note: the a.e. slack `ℓ = β − ⟨u,S⟩` was replaced by its positive part `ℓ⁺` (pointwise `≥ 0`) with `lawCov_congr_ae` and
  `{ℓ⁺ = 0} =ᵐ A`; the ℕ-indexed vertex-gap criterion was transported to the real parameter by `tendsto_iff_seq_tendsto`.

## Questions
1. **The data-ray strengthening (your §5).** With `ρ_t = ν.tilted(t h)`, `h ≤ H`, `p_* = ν{h = H} > 0`, the response path is
   `θ_t = dataTheta t ∈ W` (`C¹` with derivative `θ'_t = dataThetaVel t = (Dm(θ_t)|_W)⁻¹ Cov_{ρ_t}(S,h)`, `hasDerivAt_dataTheta_vel`),
   `meanMap θ_t = E_{ρ_t} S → M := E_ν[S | h = H]` (`tendsto_integral_dataPath_atTop`), and its Fisher speed is `responseSpeedSq t`
   (`= Var_{P_{θ_t}}⟨θ'_t,S⟩ = −⟨θ'_t, Cov_{ρ_t}(S,h)⟩`). So the FORWARD direction (`∫⁻ √responseSpeedSq < ⊤ ⇒ ray finite`) is the
   landed theorem applied to `η = dataTheta`, provided `ContinuousOn dataThetaVel (Ici 0)`. Is there a slick proof of continuity of
   `t ↦ (Dm(θ_t)|_W)⁻¹ Cov_{ρ_t}(S,h)`? (We have `continuous_meanMapDeriv`, `hasStrictFDerivAt_chartVInv` at every point, and in
   one dimension `scalarThetaVel = −Cov/Var` with `Var > 0`. Options: (a) `HasStrictFDerivAt` everywhere ⇒ `C¹` (is there a Mathlib
   lemma? `contDiffAt_one_iff`/`HasStrictFDerivAt.continuousAt_fderiv`?); (b) continuity of inversion on `ContinuousLinearEquiv`s
   (`ContinuousLinearMap.inverse` is continuous at units: Mathlib `ContinuousLinearMap.continuousAt_inverse`? name?); (c) avoid the
   inverse: `θ'_t` is characterised by `Dm(θ_t) θ'_t = Cov_{ρ_t}(S,h)` and continuity follows from an open-mapping/uniqueness
   argument.) Which route is least painful in Lean 4/Mathlib, precisely?
   For the REVERSE direction (ray finite ⇒ the data path's response has finite length) you sketched the one-sided radial-variation
   argument with block identities `m_T' = −C v' − b r'`, `a' = ⟨b,v'⟩ − V r'`, `H r' = ⟨b, C⁻¹ m_T'⟩ − a'`, `a' ≤ a E_{ρ_t} d` (from
   the data identity), `√V (r')₋ ≤ 2(a/√V)(E d + (2B/λ)‖m_T'‖)`, then `g(r)|r'| = (G∘r)' + 2 g(r)(r')₋`. Please give this as a
   sequence of Lean-shaped lemmas in OUR objects (we now have `normalDepth = −⟨θ,u⟩/⟨u,u⟩` linear, so `r'_t = −⟨θ'_t,u⟩/⟨u,u⟩`
   explicitly; `v'_t = θ'_t + r'_t u ∈ T'`; `dataCov t = Cov_{ρ_t}(S,h) = Dm(θ_t) θ'_t`; the Schur bound `facet_schur_bound`;
   `DataDissipation`: `∫₀^∞ E_{ρ_t}(H−h) dt = log(1/p_*)`, `∫₀^∞ ‖dataCov t‖ < ∞`). In particular: (i) how to express `a_t := E_{ρ_t} ℓ`
   with `ℓ = β − ⟨u,S⟩` and get `a'_t = −Cov_{ρ_t}(ℓ, h) ≤ a_t E_{ρ_t}(H − h)`; (ii) the cleanest scalar form of
   `H r' = ⟨b, C⁻¹ m_T'⟩ − a'` — can we avoid `C⁻¹` by pairing the identity `dataCov t = Dm(θ_t)(v'_t − r'_t u)` with a suitable
   vector (e.g. with `u` itself: `⟨u, dataCov t⟩ = −Cov_{q}(⟨u,S⟩, ⟨v'−r'u, S⟩) = −Cov_q(⟨u,S⟩,⟨v',S⟩) + r' Var_q⟨u,S⟩`, so
   `r' Var_q⟨u,S⟩ = ⟨u, dataCov t⟩ + Cov_q(⟨u,S⟩,⟨v',S⟩)` and `|Cov_q(⟨u,S⟩,⟨v',S⟩)| ≤ 2B a_t ‖v'‖` — then we only need a bound on
   `‖v'_t‖` in terms of `‖dataCov t‖` and `a_t r'_t` via coercivity … is the resulting system closable without matrices?).
   Also `⟨u, dataCov t⟩ = Cov_{ρ_t}(⟨u,S⟩, h) = −a'_t`!! (since `d/dt E_{ρ_t}⟨u,S⟩ = Cov_{ρ_t}(⟨u,S⟩,h)`), so
   `r' Var_q⟨u,S⟩ = −a' + Cov_q(⟨u,S⟩,⟨v',S⟩)`. Please check and complete the argument in this scalar form, and state the theorem
   (`∫⁻ √responseSpeedSq < ⊤ ↔ ∫⁻ √raySpeedSq(0,u,·) < ⊤` under: charged polytope, facet, `M = E[S|h=H] ∈ ri F`, `h` bounded with
   charged top set).
2. **Re-rank for depth** after the facet theorem: (i) the data-ray strengthening; (ii) the intrinsic Fisher completion of the atlas
   (definition of the intrinsic length metric on `ri P` from our `responseSpeedSq`/`lawCov` speeds, proof that it is a metric, its
   completion, the map to the Hellinger completion); (iii) the charged-square counterexample in codimension two; (iv) flags;
   (v) "which facets are accessible" in the charged case as a function of the layer geometry (e.g. finitely many atoms per shell ⇒
   accessible iff …; polynomial layers); (vi) anything else. One paragraph of Lean route each; for the top item, the precise
   statement with our objects.
