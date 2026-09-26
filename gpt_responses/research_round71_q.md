# Research round 71: after the general-`X` polyhedral completion — what is the deepest next step?

## Landed since round 70 (laplace `Laplace/Multi/*`, sorry-free, warning-free, pushed; NOT mirrored)
Your round-70 five-module plan was executed verbatim, plus the ambient retraction:
1. **PolyhedralVertexWitness**: `statFibre S v = {S = v}`; vertex densities `h_a = Σ_v a_v 1_{S=v}/ν{S=v}`, vertex laws
   `L(a) = ν.withDensity (ofReal ∘ h_a)`: probability, mean `Σ a_v v`, bounded (`h_a ≤ Σ_v 1/ν{S=v}`), `klDiv ≠ ⊤` (via
   `x log x` bounded on `[0, C]`), `Finset.mem_convexHull'` ↔ simplex weights; **every point of a charged polytope has finite
   rate** (`genRate_ne_top_of_mem_momentBody_polytope`).
2. **PolyhedralVertexSection**: the finite completion on the vertex type `↥V` with features `v ↦ v_j` and the uniform reference
   gives `vertexSection : P → Δ_V`, continuous on `P`, `Σ a_v(M) v = M`.
3. **ProjectionDensityBounds**: `exists_projection_density_bounds` (`q_M = f ν`, `f = 1_A e^{−⟨θ,S⟩}/(Z ν(A))`, `c 1_A ≤ f ≤ C 1_A`,
   from `responseProjection_eq_of_exposedChain`); **domination** `δ h ≤ f` a.e. for any feasible bounded-density finite-entropy
   law `hν` (Pythagoras ⇒ `KL(r‖q_M) < ∞` ⇒ `r ≪ q_M` ⇒ `h = 0` a.e. off `A`).
4. **PolyhedralRecovery**: general `KL(gν‖ν) = ∫ g log g` for bounded densities; `exists_recovery` (`g_n = f + h_{a(M_n)} − h_{a(M)}`
   with `f := max(f₀, δ h_{a(M)})` pointwise dominated; eventually `≥ 0`, mass 1, mean `M_n`, `|g_n − f| ≤ ε_n → 0`,
   `KL(g_n ν‖ν) → 𝓘(M)` by DCT); **`continuousOn_genRate_momentBody`** (rate continuous on the whole closed moment body).
5. **PolyhedralCompletion**: Pinsker in `L¹` form `(∫|p−q|)²/2 ≤ KL(pν‖qν)`; `projL1 M = [(dq_M/dν).toReal] ∈ L¹(ν)` for EVERY `M`;
   `KL(g_n ν‖q_{M_n}) = KL(g_n ν‖ν) − 𝓘(M_n) → 0` ⇒ **`continuousOn_projL1_momentBody`** (`M ↦ [dq_M/dν]` continuous in `L¹`
   on the closed moment body); `completedFamilyL1 = projL1 '' P` compact, **`completedHomeomorphL1 : P ≃ₜ completedFamilyL1`**
   (inverse = mean map `meanL1 f = (∫ S_j f dν)_j`), **`closure_image_intrinsicInterior`** (closure of the interior family).
6. **PolyhedralRetraction**: `probL1 ν` = all probability densities in `L¹(ν)`; `meanL1_mem_momentBody` (mean of any density in the
   moment body, via monotonicity of `essRange` under `≪`); `retractL1 f = projL1 (meanL1 f)`: continuous on `probL1`, mean-preserving,
   idempotent, fixed points = completed family; `deformationL1 t f = (1−t) f + t R f`: strong deformation retraction, mean-preserving,
   `R ∘ H_t = R`, continuous on `ℝ × probL1`.
Also landed (round 69 rank 2): `NaturalParameterMajorant` (`Σ_{k≤N} ρ^k‖p^{(k)}‖₁/k! ≤ 3`) and `NaturalParameterTaylor`
(`‖p(s+t) − Taylor_N‖₁ ≤ 3(|t|/ρ)^{N+1}` for all `s,t`; `L¹` Taylor series converges for `|t| < ρ = log(3/2)/L`).

## What exists that the next steps could use
`genRate_face_eq` / `responseProjection_faceMeasure` (exposed hyperplane faces), `ExposedChain`, `FisherInformation` (interior:
response form = Fisher information = covariance of the statistic), `NaturalGradientAtlas`, `PinskerEvent/Observable`, the analytic
atlas (`AnalyticChart`), `PointwiseJets`/Bell tower, `EmpiricalProjection` (a.s. convergence of the empirical response),
`EmpiricalTotalVariation`, `QuantitativeJets`/`CubicRemainder`, `MomentPolytope` (finite-`X` LP/polytope facts), `FiniteMinimalFace`
(Csiszár support for finite `X`), `intrinsicInterior`/`momentBody` API, `atlas_mem_intrinsicInterior` (straight rays from `m₀`).

## Questions
1. **Re-rank** what remains for the user's direction ("map the space of responses across the data manifold, from the featureless
   distribution to the data distribution, with maximum beauty and depth"), with precise statements and seabed routes for the top two:
   (a) **facewise geometry on the charged polytope**: the face lattice `M ∈ F ↔ q_M{S ∈ F} = 1` (for every feasible law), the
       minimal-face identification `supp q_M = {S ∈ F_M}` (Csiszár for general `X`: does it follow from our domination lemma +
       the vertex section, or does it need the exposing functional?), the uniform bound `dq_M/dν ≤ 1/min_v ν{S=v}` on the whole
       polytope, and the **stratified Fisher structure** `D²𝓘_F = Cov|_{V_F}⁻¹` on each open face (`momentBody (faceMeasure ν {S ∈ F})
       = F` needs the charged generators of `F`);
   (b) the **boundary-ray formula** `‖q_t − q_F‖₁ = 2B_t/(A + B_t)` for `q_t ∝ w e^{−tg}ν` with `g ≥ 0` exposing `F` — is there a
       cleaner statement in the charged-polytope setting (e.g. along the straight ray `M_s = m₀ + s(M − m₀)` towards a boundary
       point `M`, the exact TV distance `‖q_{M_s} − q_M‖₁` or its rate, given that natural rays and response rays differ)?
   (c) the **reconstruction CLT** (deterministic delta lemma `‖[q_{M+h}] − [q_M] − Dp_M h‖₁ = o(‖h‖)` — already available from
       the analytic atlas? — then the real CLT for `√n(M̂_n − M)` coordinatewise; is a multivariate CLT needed, and does Mathlib
       (Sept 2026) have one?);
   (d) the **capstone** `ResponseAtlas` structure — now that the boundary is understood for general `X`, is there a single
       statement worth writing ("the response atlas of a charged polytope": `P ≃ₜ completedFamily`, analytic on `ri P`, strong
       deformation retraction of `probL1`, explicit natural-parameter radius, rate continuous with `D²𝓘 = Fisher` on faces)?
   (e) **beyond polytopes**: for a general moment body (not polyhedral), what is the right hypothesis for continuity of the
       completion up to the boundary — is the vertex-charged condition replaceable by "every exposed point is charged" or by a
       strictly convex + charged-boundary condition, and is the failure in general (your `cos(1/n), sin(1/n)` example) the whole
       story? Is there a **quantitative** version (modulus of continuity of `M ↦ q_M` in TV in terms of `min_v ν{S=v}` and the
       geometry of `P`)?
2. For your top candidate: lemma chain + the single hardest lemma; for the second: the minimal first module.
Answer in ≤ 3000 words; be concrete about Lean shapes.
