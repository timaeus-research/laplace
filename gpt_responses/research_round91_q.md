# Round 91 — programme A is complete; plan programme B (second-order calculus of the response map)

You are Astra, research advisor on the Lean formalisation (laplace seabed, `Laplace/Multi/*`) of the germbij note on
the response map over the data manifold. Programme A (finite-range stratification) from round 90 has landed in full:

- `FiniteRangeFaceGeometry` (A1): `momentBody_eq_convexHull_of_finiteRange`, support gap `faceGap`, `ae_face_or_le_sub_gap`.
- `FiniteRangeRayDecay` (A2): `offFaceMass_le_exp` (`B_t ≤ e^{−δt}B_0`), `raySpeedSq_le_exp`, `integrableOn_sqrt_raySpeedSq_of_finiteRange`.
- `ExposedFaceRayEndpoint` (A3, abstract, no finite range): `rayEndpoint` (a finite-length normal ray `θ − su`, `θ,u ∈ W`,
  has a completion endpoint), `meanExt_rayEndpoint = m_F(θ)`, `accessible_of_ray`, `completionLaw_rayEndpoint = P^F_θ`.
- `FiniteRangeAllFacesAccessible` (A4): Riesz step `exists_mem_dotJ_eq_on W u` (an exposing vector is replaced by one in `W`
  differing by a constant on the vertices), `face_accessible_of_finiteRange` (every exposed face with a tight vertex, any
  codimension), `exists_meanExt_eq_of_mem_ri_face_finiteRange`, `meanExt_surjective_of_finiteRange`,
  `range_meanExt_eq_convexHull_of_finiteRange`.
- `FiniteRangeFaceIncidence` (A5): `isExtreme_face`, `minimalFacePoly_eq_of_mem_ri_face`, `closure_faceStratum_eq_preimage`
  (`closure X_F = meanExt⁻¹(F)`), `closure_faceStratum_eq_iUnion` (`= ⋃_{E ⊆ F} X_E`), `faceStratum_subset_closure_iff`
  (`X_E ⊆ closure X_F ⇔ E ⊆ F`); lower inclusion via A4 inside the face model + `faceEmbedExt` + `meanExt_injective`.
- `FiniteRangeCompletionAtlas` (A6): `iUnion_faceStratum_of_finiteRange` (all faces), `faceStratum_eq_or_disjoint_of_finiteRange`,
  `exists_faceStratum_eq_range_of_finiteRange` (`X_F = range j_F`), `range_completionLaw_eq_of_finiteRange` (completion laws =
  face-family laws of all faces), `completionLaw_injective_of_finiteRange`, `bijOn_meanExt_of_finiteRange` (`meanExt : Ŵ → conv V`
  bijective; no homeomorphism claim, as you asked).

Your round-90 sketch of programme B (six modules: `ResponseCumulantCalculus`, `ResponseHessian`, `ResponseMixtureAffine`,
`ResponseExponentialDefect`, `ResponseFisherCurvature`, `ResponseHigherDefectVariation`) with the Hessian formula
`D²η_ρ[h,k] = C_q⁻¹(κ_ρ(S,h,k) − κ_q(S,⟨a_h,S⟩,⟨a_k,S⟩))`, `a_h = C_q⁻¹ Cov_ρ(S,h)`, is now the target. Before writing
Lean I need the plan adapted to what the seabed ALREADY has (a lot of second-order material exists from earlier arcs)
and to its conventions.

## Conventions (fixed; please state everything in these)
- Bounded features `S : J → X → ℝ` (`hS : ∀ j, Bdd (S j)`), base law `ν` (probability). `dirLoss S u x = ∑ u i * S i x = ⟨u,S(x)⟩`.
- The family `Pfam θ = ν.tilted (−dirLoss S θ)` (NOTE THE SIGN: `θ` is minus the natural parameter), θ ranging over
  `W = dirSpan ν 1 S` (direction space of the moment body). `meanMap θ = E_{Pfam θ} S` (`mean`), `chartDeriv θ v` = its
  derivative (`CD`), `chartDerivEquiv θ` (`CDE`, an iso of `W`), `responseTheta M = θr M` (inverse of the mean map on the open
  moment body), `hasStrictFDerivAt_responseTheta_add : HasStrictFDerivAt (z ↦ θr (M + z)) ((CDE (θr M)).symm) 0`.
- Data laws are bounded tilts `ρ_g = ν.tilted g` (`Bdd g`); the response `responseOf g = θr (E_{ρ_g} S) ∈ W`;
  `forcing g k = Cov_{ρ_g}(S, k) ∈ W`; `responseVel hg hk = (CDE (responseOf g)).symm (forcing g k)`; the pulled-back form
  `pullbackForm hg hk = fisherVar (responseOf g) (responseVel)` (= `Cov_{ρ_g}(⟨−DΦ[k],S⟩, k)`), bilinear version `pullbackBilin`.
- Journeys: coefficient paths `ρ_t = ν.tilted (a t • h)` (`coeffResponse`, `hasDerivAt_coeffResponse` with velocity `a'(t) •
  responseVel`); the canonical e-journey `ν.tilted (t log q)` from ν to D (`CanonicalDataJourney`); the mixture journey
  `mixLaw = (1−t)ν + tD`, `mixResponse t = θr(m_ν + t(m_D − m_ν))`, `hasDerivAt_mixResponse` with velocity `(CDE)⁻¹(m_D − m_ν)`.
- `lawCov ρ f g`, `fisherVar S ν θ w = Var_{Pfam θ}⟨w,S⟩`, `thirdCentral ρ g k f = E_ρ[(g−Eg)(k−Ek)(f−Ef)]` (CubicResponse),
  `hasDerivAt_lawCov_tilted : d/ds Cov_{ν.tilted(s f)}(g,k) = thirdCentral(...)(g,k,f)`.
- Response defect `responseDefect h t = D(ρ_t ‖ Pfam(Φ(ρ_t)))`-type quantity with `deriv_deriv_responseDefect_zero_eq_residual`
  (`Δ''(0) = Var(h − regressor)`), and `ResponseDefectEvolution.deriv_deriv_responseDefect` at every `t`:
  `ℰ'' = Var_{ρ_t}h − |q'|²_F + Cov_{ρ_t}((h−Eh)², t h + ⟨θ_t,S⟩)`.

## Second-order material already in the seabed
- `CovarianceFrechet`: `hasFDerivAt_integral_family` (`θ ↦ E_{Pfam θ} φ` Fréchet-differentiable with derivative
  `−Cov_θ(φ, ⟨·,S⟩)`), `hasFDerivAt_lawCov_family` (derivative of `θ ↦ Cov_θ(f,g)` is `−κ_θ(f,g,⟨·,S⟩)`), `hasFDerivAt_famDens`,
  `thirdVec S ν θ η v`, `thirdOp θ : W →L (W →L W)` with `hasFDerivAt_chartDeriv : HasFDerivAt (CD) (thirdOp θ₀) θ₀`,
  `hasFDerivAt_inverse_response` (derivative of `w ↦ (CDE (θr(M+w)))⁻¹`), `inverse_response_deriv_apply`, `thirdVec_eq_respCov`,
  `hasFDerivAt_responseScore_response`, `hasFDerivAt_famDens_responseScore`.
- `SmoothFamily`: `contDiff_famNum`, `contDiff_meanMap : ContDiff ℝ ∞ mean`, `contDiff_chartDeriv`, `contDiff_chartDerivEquiv_symm`
  (so `θr` is `C^∞` on the open moment body by the inverse function theorem; `MeanMapChart.hasStrictFDerivAt_meanMapInverse`).
- `AtlasVelocityDerivative`/`AtlasHessian`/`AtlasSkewness` (along the straight mean path `m_s = (1−s)m₀ + s m₁`):
  `cumulantVec`, `cumulantOp s`, `hasDerivAt_chartDeriv_atlas`, `hasDerivAt_atlasVel` (second derivative of `θr(m_s)`: the
  atlas "bend" `atlasBend`, `atlasAccel_eq_neg_atlasBend`), `atlasHess`, `hasDerivAt_atlasCurv` (derivative of the Fisher speed
  along the mean path is a third cumulant), `toReal_klDiv_responseProjection_sub_symm_eq_skew`.
- `ChartPathDerivatives`/`ContractionIdentity` (older joint-chart layer with `Option ι`): `natCum3`, `cum3Mat`, `respHess`
  (a "response Hessian" matrix), `hasDerivAt_natb_path`, `hasDerivAt_natVarH_path`.
- `ResponseSubmersionCalculus`: `velLin g : bddSpace X →ₗ W` (linear in the direction `k`), `horLin`, `velQuotEquiv : bddSpace ⧸ ker ≃ W`.
- `CoefficientTiltDifferentiation`: `hasDerivAt_integral_tilted_dirLoss` (derivative of `t ↦ E_{ν.tilted(t g)} φ` is `Cov(φ,g)`).

## Questions
Q1. Restate programme B as six modules ADAPTED to the seabed: for each, the name, the exact Lean-flavoured statements in the
conventions above (sign of θ!), the proof route, and which existing declarations it rests on. In particular:
  (a) `ResponseHessian`: the second derivative of `t ↦ responseOf (g + t k)` (or of the two-parameter `(s,t) ↦ responseOf (g + s k + t ℓ)`)
  at `0`, as an explicit element of `W`: state it with `thirdCentral`/`thirdVec`, `forcing`, `responseVel` and `CDE`. Please derive
  it by twice differentiating the moment-matching identity `mean (responseOf (g + t k)) = E_{ρ_{g+tk}} S` and give the
  sign-correct formula. Is the natural Lean object a `HasDerivAt` of `t ↦ responseVel (g + t k) ℓ` (velocity field along the
  journey) — i.e. the derivative of `t ↦ (CDE (responseOf(g+tk)))⁻¹ (forcing (g+tk) ℓ)` via the product rule with
  `hasFDerivAt_inverse_response` + `hasDerivAt_lawCov_tilted`?
  (b) `ResponseMixtureAffine`: the mixture journey has `mean(mixResponse t)` affine in `t` (trivial) — what is the NON-trivial
  statement? Presumably the second derivative of `mixResponse` equals `−(CDE)⁻¹ ∘ (D CD)[v,v]` with `v` the velocity, i.e.
  `atlasBend`-type: is this already `AtlasVelocityDerivative.hasDerivAt_atlasVel` and only needs re-expression, or is there a
  genuinely new claim ("zero mixture covariant Hessian" = the mean-coordinate second derivative vanishes) that we should state
  as: for the mixture journey, `d²/dt² [mean ∘ mixResponse] = 0` while `d²/dt² mixResponse = −CDE⁻¹ thirdOp[v,v]`?
  (c) `ResponseExponentialDefect`: for the e-journey `ρ_t = ν.tilted(t h)` the second derivative of `t ↦ responseOf(t h)` is
  `CDE⁻¹(κ_{ρ_t}(S,h,h) − κ_{Pfam Φ}(S,⟨a,S⟩,⟨a,S⟩))`-type (with signs); please write the exact statement and the
  interpretation as "defect of the e-connection under Φ", WITHOUT any connection formalism (we have no manifold/connection API —
  everything must be stated as derivatives along explicit journeys).
  (d) `ResponseFisherCurvature`: what is the cleanest connection-free statement? (E.g. the derivative of the pulled-back form
  along the journey, `d/dt pullbackForm`, as a combination of third cumulants — vs. the true Riemann curvature, which needs
  Christoffel symbols; is a "curvature" statement realistic here, or should this module be "variation of the pull-back
  form" only?)
  (e) `ResponseHigherDefectVariation`: the third derivative `Δ'''(0)` of the initial defect `t ↦ D(ρ_t ‖ Pfam(Φ(ρ_t)))` along
  `ρ_t = ν.tilted(t h)` starting at the matched point — give the formula in terms of `thirdCentral` of `h − regressor` and
  the response velocity; which of `deriv_deriv_responseDefect` (every-t formula) inputs are needed.
Q2. Which of the six are genuinely new theorems vs restatements of `CovarianceFrechet`/`AtlasVelocityDerivative`? Drop or merge
the restatements; propose replacements of equal depth (candidates: (i) a global `C^∞`/`C²` statement `responseOf` is `C²` in
the data direction on `bddSpace`; (ii) the second variation of the journey length; (iii) the "Hessian is symmetric"
identity `D²Φ[h,k] = D²Φ[k,h]` proved from the explicit formula (a nontrivial cumulant symmetry); (iv) Hessian of the
canonical e-journey at `t=0` — the direction in which the response bends away from the straight natural path — with the
sign controlled by skewness; (v) the second-order expansion of the response `Φ(g + t k) = Φ(g) + t v + t²/2 a + o(t²)`
as a `HasStrictFDerivAt`/Taylor statement).
Q3. Give the single headline theorem of programme B for the note (one displayed formula) and a one-paragraph statement of
why it is the natural second-order counterpart of "the response form is the Fisher form" (round 26) and of the
submersion/horizontal-lift picture (round 85).
Be concrete; flag any formula whose sign you are not sure of; end with the ranked list of six modules to formalise next.
