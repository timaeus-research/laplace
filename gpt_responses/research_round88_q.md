# Round 88 — the response-map section after round 87: audit, the stratification theorem, and what next

You are Astra, research advisor on the Lean formalisation (laplace seabed, `Laplace/Multi/*`, Lean 4.33 + Mathlib) of the
germbij note on the response map `q ↦ Φ(q)` over the data manifold. In round 87 you ranked six modules; ALL SIX have
now been formalised (sorry-free, warning-free). This round: (1) audit them for overclaims or errors of substance,
(2) advise on two candidate global theorems (the stratification of the completion by face charts, and the
featureless→data tilt segment as the canonical journey), (3) rank the next batch.

Conventions (unchanged): `S : J → X → ℝ` bounded statistics, `ν` featureless law, `W = dirSpan ν 1 S`, `Pfam θ` the
family, `θr M` the response chart (inverse mean map), `CDE θ` the chart derivative equivalence on `W`,
`FisherCompletion hS ν = Ŵ`, `completionLaw hS ν x = Q_x`, `rootDensExt hS ν x = Ψ_x ∈ L²(ν)` (unit vector, ½-Lipschitz),
`forcing S ν g k = Cov_{ν.tilted g}(S, k)`, `responseOf hS ν g = Φ(g) = θr(E_{ρ_g} S)`,
`responseVel hS ν hg hk = DΦ_g[k] = (CDE Φ(g)).symm (forcing g k)`, `pullbackForm = |DΦ_g[k]|²_F`,
`samplingOp θ p = ι ∘ (CDE θ).symm ∘ p` for a retraction `p : (J → ℝ) →ₗ W`, `samplingEnergy θ p z = −⟨samplingOp z, z⟩`,
`sampleResponse S Xs n ω = (1/n) Σ S(X_i)`, `faceEmbed hS ν μ' hle x₀ v₀ w = tiltExt (w − v₀) x₀`, `faceEmbedExt` its
1-Lipschitz extension `Ŵ' → Ŵ`, `meanExt`, `momentBody`, `intrinsicInterior`, `minimalFacePoly V M`.

## 1. What landed in round 87 (statements, all proved)

### 1.1 `SeedIndependentAtlas` (your rank 1)
- `faceDir_add`, `faceDir_self`, `faceEmbed_self : j(v₀) = x₀`.
- `tiltExt_faceEmbed : tiltExt (faceDir w w') (faceEmbed x₀ v₀ w) = faceEmbed x₀ v₀ w'` (finite equivariance).
- `faceEmbedExt_eq_iff (hx₀ hx₀') : faceEmbedExt x₀ v₀ = faceEmbedExt x₀' v₀' ↔ x₀' = tiltExt (faceDir v₀ v₀') x₀`.
- `faceEmbedExt_eq_of_faceEmbed_eq : faceEmbed x₀ v₀ w = faceEmbed x₀' v₀' w (one w) → faceEmbedExt x₀ v₀ = faceEmbedExt x₀' v₀'`.
- `faceEmbedExt_transport : faceEmbedExt (faceEmbed x₀ v₀ v₀') v₀' = faceEmbedExt x₀ v₀`.
- `faceEmbedExt_eq_of_completionLaw_unique` / `faceEmbedExt_eq_of_meanExt_unique`: one singleton ambient fibre over one
  finite sub-model law (resp. mean) ⇒ all admissible seed pairs give the same extension.
- `faceEmbedExt_injective (huniq : ∀ y z, Q'_y = Q'_z → y = z) : Injective faceEmbedExt`.
- `exists_charged_vertex_on_face`, `meanMap_faceMeasure_mem_intrinsicInterior`.
- `faceEmbedExt_eq_of_charged_face`: charged polytope (`momentBody ν = convexHull V`, all vertices charged), exposed face
  `{dirLoss S u = β}` with `∀ v ∈ V, ⟨u,v⟩ ≤ β`, `0 < ν(face)`, sub-model `faceMeasure ν face`: every seed pair gives the
  same `faceEmbedExt` (via `meanExt_eq_face_unique` at the finite face mean `m_F(v₀)`).

### 1.2 `ResponseProductAffinity` (rank 2 + the tail theorem)
- `rootLaw μ f := μ.withDensity (ofReal (f·f))` for `f ∈ L²(μ)`; `completionLaw x = rootLaw ν Ψ_x` (rfl).
- `integral_rootLaw_sub_le (‖f‖=‖g‖=1) (0 ≤ φ ≤ 1 measurable) : ∫φ d(f²μ) − ∫φ d(g²μ) ≤ ‖f − g‖`.
- `testing_error_ge : (1 − ‖f−g‖)/2 ≤ (∫φ d(f²μ) + ∫(1−φ) d(g²μ))/2`.
- `prodRoot μ n f = ∏_i f(z_i) ∈ L²(μ^{⊗n})`, `inner_prodRoot : ⟪R_f, R_g⟫ = (∫ f g)^n`, `norm_sub_prodRoot_sq : ‖R_f − R_g‖² = 2 − 2A^n`,
  `norm_sub_prodRoot_sq_le : ‖R_f − R_g‖² ≤ n ‖f − g‖²` (Bernoulli with |A| ≤ 1), `norm_sub_prodRoot_le : ≤ √n ‖f−g‖`,
  `rootLaw_prodRoot : rootLaw μ^{⊗n} (R_f) = (rootLaw μ f)^{⊗n}` (Measure.pi_eq on boxes).
- `sampleLaw hS ν n x := Measure.pi (fun _ ↦ Q_x)`; `integral_sampleLaw_sub_le : ∫φ dQ_x^{⊗n} − ∫φ dQ_y^{⊗n} ≤ √n d̂(x,y)/2`;
  `testing_error_sampleLaw_ge`.
- TAIL THEOREM `testing_error_pathEndpoint_ge`: along a W-path with integrable Fisher speed, `R(t) = ∫_t^∞ speed`,
  every test on n samples between `Q_{x_t}^{⊗n}` and `Q_{x_∞}^{⊗n}` has error ≥ (1 − √n R(t)/2)/2.

### 1.3 `ResponseJourneyResolution` (rank 3)
- `fisherDist_le_sqrt_mul_of_segment (hΛ : ∀ t ∈ [0,1], ∀ w, fisherVar (x + t(y−x)) w ≤ Λ ⟨w,w⟩) : d_F(x,y) ≤ √Λ √⟨y−x,y−x⟩`.
- `fisherDist_lt_of_dotJ_lt : √Λ r < δ ∧ ⟨y−x,y−x⟩ < r² ⇒ d_F(x,y) < δ` (patch clearance, segment condition explicit).
- `fisherDist_coeffResponse_le : d_F(Φ(g_{t₁}), Φ(g_{t₂})) ≤ ∫_{t₁}^{t₂} √G^{resp}` for coefficient journeys `g_t = ⟨a(t), h⟩`.
- `fisherDist_coeffResponse_lt_of_length_lt : L < ρ₀ + ρ₁ ⇒ d_F < ρ₀ + ρ₁` (no disjoint-ball certificate).
- `measureReal_sampleResponse_notMem_fisherBall_le`: intrinsic confidence radius, `P(M̂ ∉ B_F(θ(m_D), √(Λ/λ) r)) ≤ tr(R C_D)/(n r²)`.
- `fisherBall`, `ballClassifier` (decide class 0 iff M̂ ∈ first ball), `measureReal_ballClassifier_ne_true_le`,
  `measureReal_ballClassifier_ne_false_le` (needs disjointness), `disjoint_fisherBall (ρ₀ + ρ₁ ≤ d_F(θ₀,θ₁))`.

### 1.4 `ResponseLawContinuity` (rank 4)
- geometry as a function of the density `q` (admissible: AEMeasurable, ≥ 0, integrable, ∫ q = 1): `densMean`, `densForcing`,
  `densResponse = θr (densMean)`, `densVel q p k = (CDE (densResponse q)).symm (p (densForcing q k))`, `densBilin`, `densEffDim`.
- `norm_densMean_sub_le : ‖m(q₁) − m(q₂)‖ ≤ B ‖q₁−q₂‖₁`; `norm_densForcing_sub_le : ≤ 3BK‖q₁−q₂‖₁`; `abs_densCov_stat_sub_le`.
- along any filter with `‖q_n − q₀‖₁ → 0` and `densMean q₀` interior: `tendsto_densMean`, `tendsto_densForcing`,
  `tendsto_densCov_stat`, `tendsto_densResponse`, `tendsto_densVel`, `tendsto_densBilin`, `tendsto_densEffDim`.

### 1.5 `ResponseHellingerAtlas` (rank 5)
- `tendsto_fisherDist_iff_hellingerDist`: on a coercive convex patch of interior means, Fisher convergence of responses ⇔
  Hellinger convergence of laws (from the sandwich `√λ d_F ≤ 2B H ≤ B d_F`); `tendsto_rootDensLp_iff_fisherDist`.
- `hellingerExt x y = dist Ψ_x Ψ_y`, `hellingerExt_coe`, `hellingerExt_le : ≤ d̂/2`, `tendsto_rootDensExt`,
  `tendsto_integral_completionLaw` (completion convergence ⇒ TV convergence of laws).
- `isClosedEmbedding_rootDensExt [CompactSpace Ŵ] (huniq : Q_x = Q_y → x = y)`, `tendsto_iff_tendsto_rootDensExt`.

### 1.6 `ResponseSubmersionCalculus` (rank 6)
- `bddSpace X` (bounded measurable contrasts, a Submodule of `X → ℝ`), `forcingLin : bddSpace →ₗ W`, `velLin = (CDE Φg).symm ∘ forcingLin`.
- `mem_ker_velLin_iff : k ∈ ker velLin ↔ forcing g k = 0`; `mem_ker_velLin_iff' : ↔ ∀ i, Cov(S i, k) = 0`.
- `velLin_surjective`; `horLin : W →ₗ bddSpace` (canonical horizontal lift), `velLin_horLin`, `horLin_injective`,
  `horProj = horLin ∘ velLin`, `isProj_horProj`, `isCompl_range_horLin_ker_velLin : IsCompl (range horLin) (ker velLin)`.
- `lawCov_horizontalLift_of_forcing_eq_zero` (horizontal ⟂ invisible), `forcing_residual_eq_zero`,
  `lawCov_self_eq_horizontal_add_residual : Var k = Var hor(DΦ[k]) + Var(k − hor)` (any data law),
  `lawCov_self_eq_dotJ_add_residual : Var k = ⟨C⁻¹ Dm v, Dm v⟩ + Var(residual)`, `velQuotEquiv : bddSpace ⧸ ker velLin ≃ W`.

## 2. Questions

### Q1. Audit
For each of 1.1–1.6: is anything overclaimed, mis-stated or vacuous? In particular: (a) in 1.2 the testing bound uses the
crude `‖f+g‖ ≤ 2`; is `TV ≤ H` the right constant to advertise, and is the Bernoulli step `2 − 2A^n ≤ n(2 − 2A)` the standard
route or is there a sharper `H_n² ≤ n H²`-type statement we should cite? (b) In 1.3 the classifier's error bounds only
use ball-exit probabilities; is "sufficient separation theorem" the right name? (c) In 1.4 we parametrised by the
density and used a retraction `p` in `densVel` to avoid proving `Cov_D(S,k) ∈ W` for general `D ≪ ν` (it IS in `W`,
but the proof needs an integral-in-closed-subspace argument); is this a defect for the note? (d) In 1.5 is the
conditional package stated the way you would state it?

### Q2. The stratification theorem
Your round-87 "final atlas statement": for a charged polytope, every point of the polytope lies in the relative
interior of a unique face, hence `Ŵ = ⊔_F j_F(W_F)` with `j_F(W_F) = {x : meanExt x ∈ ri F}`. We have:
`mem_intrinsicInterior_minimalFacePoly` (M ∈ ri(minimalFacePoly V M)), `exists_exposing_minimalFacePoly` (every minimal
face is exposed by some (u, β) with the tight vertices exactly the charged ones), `meanExt_eq_face_unique` (singleton
fibre over charged face interiors — needs the face exposed by (u, β) and `M ∈ intrinsicInterior (momentBody (faceMeasure
ν {dirLoss u = β}))`), `exists_meanExt_eq_of_mem_ri_face` (one accessible point of ri(face) ⇒ all of ri(face) accessible),
`faceEmbedExt_eq_of_charged_face` (canonical `j_F`), `completionLaw_faceEmbedExt`, `meanExt_faceEmbedExt`,
`faceEmbedExt_faceEmbedExt` (chain), `meanMap_faceMeasure_mem_intrinsicInterior`. What is missing is
(i) the identification `intrinsicInterior (momentBody (faceMeasure ν face)) = ri(F)` for the face polytope `F = convexHull
(V ∩ {⟨u,·⟩ = β})` (we have `momentBody_faceMeasure_subset_hyperplane` and `momentBody_faceMeasure_subset`), (ii) that
every completion point over `M ∈ ri F` is in the image of `j_F` (from fibre uniqueness + `completionLaw_faceEmbed`),
(iii) accessibility of each face interior (is it automatic for charged polytopes? We have the *conditional* results:
accessible iff normal ray has finite Fisher length, `Σ √a_k < ∞` for facets). Please give the precise statement you
would prove and its dependency order; say which parts are unconditional for charged polytopes and which need the
accessibility hypothesis (per face). Is "`Ŵ = ⊔_F j_F(W_F)` over the ACCESSIBLE faces" the honest theorem?

### Q3. The featureless→data journey as the canonical journey
The user's directive is to map responses "from the featureless distribution of maximal entropy to the actual data
distribution". The obvious canonical journey is the tilt segment `g_t = t·log q` (q = dD/dν bounded away from 0 and ∞),
`ρ_0 = ν`, `ρ_1 = D`, a coefficient journey with `h = log q`, `a(t) = t`. Then everything landed applies: the response path
`t ↦ Φ(t log q)` is C¹ (`hasDerivAt_coeffResponse`), its length `L = ∫_0^1 √G^{resp}_{t log q}(log q)`, `d_F(0, Φ(D)) ≤ L`
(`fisherDist_coeffResponse_le`), the forms are continuous along it, the noise floor and the testing bounds apply at every t.
Is this the right canonical journey (it is the exponential/geodesic segment in the data manifold, i.e. the e-geodesic
from ν to D)? What are the clean theorems specific to it — e.g. (a) at t = 0 the response velocity is the regression of
log q on S (`ResponseAtFeaturelessLaw` has `Var_ν h = |θ'_0|²_F + Var(h − regressor)`), (b) `Φ(t log q)` vs the m-geodesic
(mixture) `(1−t)ν + tD` whose response is `θr((1−t)m_ν + t m_D)`: which journey has smaller response length, and is there
an inequality? (c) monotonicity of `t ↦ D(ρ_t‖ν)` or of the response defect along the e-segment? Please rank these.

### Q4. Next six
Rank the next six modules by depth × reachability, with one-line deliverables. Candidates: the stratification theorem
(Q2), the canonical featureless→data journey (Q3), `Cov_D(S,k) ∈ W` for general `D ≪ ν` (closing the retraction in 1.4),
sharper TV/Hellinger constants, second-order / curvature of the response map (you said "new project" — confirm), a
"chamber atlas" statement (the frozen-margin hypothesis `hell` of the resolution theorems discharged from patch
clearance `fisherDist_lt_of_dotJ_lt`), the response map on mixtures (m-geodesics), and anything you consider missing
from the six-part shape you recommended (1 projection, 2 infinitesimal geometry, 3 sampling/resolution, 4 boundary
geometry, 5 journeys, 6 what finite samples see).

Be concrete: exact statements in the seabed's conventions, hypothesis lists, and the dependency order. End with the
single theorem you would put last in the note.
