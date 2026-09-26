# Research round 72: after rigidity and the boundary-ray formula — the next deep step

## Landed since round 71 (laplace `Laplace/Multi/*`, sorry-free, warning-free, pushed; NOT mirrored)
Your round-71 ranks 1 and 3 are done, and rank 2's first lemma turned out to exist already:
- **ExtremeMeanSupport** (rigidity I): `conditional_mean_eq_of_extreme` (a `ν`-dominated law with extreme mean has all its
  non-trivial conditional means equal to the mean), `ae_statPoint_eq_of_mean_extreme` (AN EXTREME MEAN FORCES CONCENTRATION ON
  ITS FIBRE, by the coordinate half-space split you proposed), `statFibre_pos_of_mean_extreme`, `norm_sub_eq_two_of_mean_extreme`
  (`L¹` densities over distinct extreme points are at distance exactly 2).
- **CompactMeanLiftRigidity** (rigidity II): `finite_extremePoints_of_compact_mean_lift` (2-separation vs compactness),
  `exists_charged_generators_of_compact_mean_lift` (Krein–Milman + finite hull closed), `exists_charged_generators_of_continuous_section`,
  **`exists_charged_polytope_iff_exists_compact_mean_lift`**: `(∃ V finset, momentBody = conv V ∧ ∀ v ∈ V, ν{S=v} > 0) ↔ (∃ K compact ⊆
  probL1 ν, meanL1 '' K = momentBody)`.
- **BoundaryRayFormula** (rank 3): along `θ − t u` with `⟨u,S⟩ ≤ β` a.e., charged fibre `F = {⟨u,S⟩ = β}`, slack `g = β − ⟨u,S⟩`:
  `famZ_ray : Z(θ − tu) = e^{tβ}(A + B_t)`, `famDens_ray`, **`integral_abs_famDens_ray_sub_faceDens : ‖p_{θ−tu} − 1_F w/A‖₁ = 2B_t/(A+B_t)`**
  for every `t`, `tendsto_offFaceMass` (DCT), `familyMeasure_faceMeasure_eq` (the face law = exponential family of `ν(·|S ∈ F)`),
  **`exists_ray_tendsto_responseProjection`** (every `M ∈ ri (momentBody (faceMeasure ν F))` with `u·M = β` is the TV-limit of an
  explicit natural ray with that exact rate).
- Rank 2, first lemma: the seabed already had `compl_eq_zero_of_mean_face` (a law whose mean lies on a supporting hyperplane is
  carried by the face), so `M ∈ F ↔ μ{S ∈ F} = 1` is available for exposed hyperplane faces.
- Interior Fisher/Hessian facts already in the seabed: `hessian_rateFun_chart_eq` (DualFisherMetric: the Hessian of the rate in
  chart coordinates on `dirSpan μ π S` equals the inverse covariance form), `featCov_mulVec_dualHessian` (`D²_M J = C⁻¹`),
  `fisherInformation_eq_responseForm` (score covariance = response form); all for a general reference measure `μ`, hence they
  instantiate verbatim on `faceMeasure ν F`, and `genRate_face_eq` (`𝓘 = −log ν(F) + 𝓘_F`) transports the constant. So the
  "stratified Fisher structure" is essentially an instantiation; the genuinely new pieces of your rank 2 are
  `momentBody (faceMeasure ν F) = F` for a polytope face with charged generators, the essential support `q_M ∼ ν|_{S∈F_M}`,
  and the uniform bound `dq_M/dν ≤ 1/min_v ν{S=v}`.

## The whole picture now (charged polytope `P = conv V`, general `X`)
`M ↦ [dq_M/dν] ∈ L¹(ν)` continuous on all of `P`; `P ≃ₜ completedFamilyL1`; strong deformation retraction of ALL `L¹` probability
densities onto it, mean-preserving; the rate is continuous on `P`; the completed family is the closure of the interior
exponential family; RIGIDITY: these hypotheses are necessary for any compact/continuous absolutely-continuous mean lift; interior:
analytic response atlas, Bell tower of jets, sharp cubic remainder, explicit natural-parameter radius `log(3/2)/L` with
`‖p(s+t) − Taylor_N‖₁ ≤ 3(|t|/ρ)^{N+1}`; boundary rays with exact TV rate `2B_t/(A+B_t)`.

## Questions
1. Re-rank what remains for the user's direction ("map the space of responses across the data manifold, from the featureless
   distribution to the data distribution, with maximum beauty and depth"), with precise statements and seabed routes for the top two.
   Candidates we see: (a) the polytope face lattice in Lean (`conv V ∩ {u·y = β} = conv (V.filter (u·v = β))` when `u·v ≤ β` on `V`;
   `momentBody (faceMeasure ν F) = F`; essential support of `q_M` = face fibre of the minimal face; the uniform density bound
   `1/m_*`); (b) the facewise delta method and CLT (`√n(q_{M̂_n} − q_M) ⇒ Dq_M[G]`, `G ∼ N(0, Cov|_{V_F})`; Cramér–Wold; Mathlib's
   multivariate CLT status?); (c) a quantitative interior-to-boundary statement: given the exact ray formula, is there a clean
   statement of the "boundary layer" `∫_{0 < g ≤ r} w dν ≤ K r^α ⇒ B_t = O(t^{−α})` and its converse (Tauberian)?; (d) the capstone
   `ResponseAtlas` structure (what fields, in what order; is it worth writing now?); (e) something we have not seen — e.g. a
   canonical **metric** on the completed family (the `L¹`/TV metric vs the Fisher–Rao/information metric on `ri P` degenerating
   at faces — is there a theorem about the completion as a metric completion, or about geodesics reaching the boundary in finite
   Fisher–Rao length, cf. our earlier `2 arccos ρ ≤ length` bound?), or a **duality**: the completed family as the image of the
   polytope under the Legendre map, with the faces as the "points at infinity" of the natural parameter space (a compactification
   theorem for the natural-parameter space: `Θ ∪ {faces}` ≃ `P`?).
2. For the top candidate give the lemma chain and the single hardest lemma; for the second the minimal first module.
Answer in ≤ 3000 words; be concrete about Lean shapes.
