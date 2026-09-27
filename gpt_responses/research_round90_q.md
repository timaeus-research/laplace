# Round 90 — the response-map section is complete: what is the next programme?

You are Astra, research advisor on the Lean formalisation (laplace seabed, `Laplace/Multi/*`) of the germbij note on
the response map over the data manifold. In round 89 you declared the response-map section complete at its scope, and
the closing items landed (`ResponseAtlasClosure`: `meanExt_injective`/`completionLaw_injective` on charged polytopes,
`huniq` discharged in the Hellinger package and in `faceEmbedExt_injective_of_charged_face`, `faceMeasure_charged`
(face models are charged polytope models), `iUnion_faceStratum` / `faceStratum_eq_range` (`Ŵ = ⋃_{F accessible} X_F`,
`X_F = range j_F`), `journey_defect_curvature_zero`, and the closing `affinityExt_pathEndpoint_ge` /
`testing_error_pathEndpoint_ge_sqrt`). Rounds 84–89 landed ~45 modules covering your six-part shape.

The standing directive from the user is to keep formalising, prioritising new mathematics, and to choose work that
"maps the space of responses across the data manifold, ideally all the way from the featureless distribution to the
actual data distribution, with maximum beauty and depth". Please define the next programme.

## Candidate programmes

### A. Unconditional stratification for finite-range statistics
Claim: if `S` has finite essential range (e.g. finite `X`, or `statPoint S` takes finitely many values ν-a.e.), then every
nonempty face of the moment polytope is accessible, hence `Ŵ = ⨆_{ALL nonempty faces F} j_F(W_F)`, with the closure
relations of the face lattice reflected in the completion. What the seabed has:
- `raySpeedSq S ν θ u t := Var_{P_{θ − t u}}⟨u,S⟩` (FisherAccessibility), `continuous_raySpeedSq`,
  `lintegral_sqrt_raySpeedSq_lt_top_of_path`, `lintegral_sqrt_raySpeedSq_lt_top_iff_tilt` (RayTiltInvariance: ray finiteness is
  invariant under bounded tilts of the base point), `measureReal_family_ray_faceFibre`,
  `tendsto_measureReal_family_ray_faceFibre` (FaceMassConcentration: mass concentrates on the face along the normal ray).
- FACET theorems: `exists_meanExt_eq_iff_ray` / `facet_fisher_access_iff` (FacetCompletionAccess/FacetFisherAccess), stated
  with a transversality hypothesis `hT : ∀ w ∈ W, ⟨w,u⟩ = 0 → …` (the facet condition `T' = W ∩ u^⊥`) and a vertex `z` off the
  face; `forall_exists_meanExt_eq_of_facet` (one facet point accessible ⇒ all of ri(facet) accessible).
- General faces: `NormalConeCauchyCoalescence` (`completion_limit_eq_of_normalCone`: face-concentrating Fisher-Cauchy
  sequences with normal-cone offsets have the same limit), `exists_meanExt_eq_of_mem_ri_face` (AccessibleFaceStrata: one
  accessible point of ri(face) ⇒ all), `exists_meanExt_eq_faceFamily` (tilt action on face laws),
  `completionLaw_pathEndpoint_eq` (endpoint law = Π(lim m)), `momentBody_faceMeasure_eq`, `meanMap_faceMeasure_mem_intrinsicInterior`.
- What is missing, as far as I can see: (i) the exponential decay `raySpeedSq θ u t ≤ C e^{−2 gap t}` for finite-range `S`
  (gap = β − max{⟨u,v⟩ : v ∈ V, ⟨u,v⟩ < β}), giving integrable `√raySpeedSq` on `[0,∞)` for EVERY exposed face; (ii) that a
  normal ray of finite Fisher length converges in `Ŵ` to a point whose extended mean lies in ri(F) — for facets this is in
  the seabed; for a general exposed face `F = conv(tight V)` with `u` its exposing vector, does the ray `θ − t u` have limiting mean
  `E_{P^F_{θ|F}} S ∈ ri F`? (iii) the assembly `Ŵ = ⨆_{F} j_F(W_F)` over all nonempty faces, plus closure relations
  (`closure (X_F) ⊇ X_E` for faces `E ⊆ F`? which direction is true, and is it provable from the tilt action?).
Please give the precise theorem list and dependency order, and say which of (i)–(iii) are routine and which need care
(e.g. general faces vs facets in (ii); the role of `hT`).

### B. Second-order calculus of the response map
The Hessian of `Φ` (or of `θr`), the second variation of the pull-back form along journeys, curvature of the response
chart's Fisher metric in natural coordinates, the initial defect expansion beyond `Δ''(0)` (already have `Δ''(0) =
Var(h − h_reg)`, `ℰ'' = Var_{ρ_t}h − |q'|²_F + Cov_{ρ_t}((h−Eh)², t h + ⟨θ_t,S⟩)` at every t in `ResponseDefectEvolution`), and
the e/m dual-connection picture: the exponential journey is e-flat, the mixture journey is m-flat; the response chart
`θr` sends m-geodesics in mean space to the natural-coordinate images — is there a clean theorem of the form "the
response map intertwines the mixture (m-)connection of the data manifold with the mixture connection of the family, and
sends the exponential (e-)connection to a connection with an explicit defect term"? What are the six modules?

### C. Other
Anything you consider deeper for the directive: e.g. (1) a global "quotient theorem": the response map is the quotient of
the (bounded-tilt) data manifold by the invisible directions, as a global statement (we have the linear-algebraic
`velQuotEquiv` and the fibre equivalence `D ∼ D' ⇔ Φ(D) = Φ(D')`); (2) the response map on several data laws (a family of
journeys, the atlas as the image of the whole data manifold); (3) the tail theorem's converse (if `R(t)` is large then n
samples CAN see the tail, under coercivity), turning the closing statement into a two-sided resolution theorem;
(4) anything else.

## Questions
Q1. Rank the programmes A, B, C(1–4) by depth × reachability given the seabed, with a one-paragraph rationale each.
Q2. For the top programme, give six modules (name, one-line deliverable, exact statement in the seabed's conventions,
dependency order, the existing lemmas each rests on). Flag the statements you are not sure are true.
Q3. For programme A specifically: is (ii) true for general exposed faces of a charged polytope with finite-range `S`, and
what is the cleanest route (ray + tilt action, or the path-endpoint theorem `tendsto_pathEndpoint` + `completionLaw_pathEndpoint_eq`
+ `momentBody_faceMeasure_eq`)?
Be concrete; end with the single ranked list of what to formalise next.
