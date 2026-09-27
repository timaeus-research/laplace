# Round 87: the response-map section is nearly closed — what remains, and what is the note's final shape?

## Landed since round 86 (all sorry-free; `Laplace/Multi/*`, timaeus-research/laplace, main)

Your round-86 ranking, with what each became:

1. `FaceEmbedExtension` + `FaceChainAccessibility` (rank 1). The embedding is now for an arbitrary SUB-MODEL `μ'`
   (probability law with `dirSpan μ' ≤ dirSpan ν`; faces are the instance via `dirSpan_faceMeasure_le`), seed
   `x₀` with `Q_{x₀} = P'_{v₀}`, `v₀ ∈ W'`: `j(w) = tiltExt (w − v₀) x₀`, `Q_{j w} = P'_w`, nonexpansive
   (`dist_faceEmbed_le`); `1`-Lipschitz extension `ĵ : Ŵ' → Ŵ` (`faceEmbedExt`), MEAN COMPATIBILITY `meanExt ∘ ĵ = meanExt'`
   (by density), ACCESSIBILITY TRANSFER; LAW COMPATIBILITY AT COMPLETION POINTS `Q_{ĵ y} = Q'_y` (by density through
   indicator integrals); EQUIVARIANCE `ĵ (tiltExt' h y) = tiltExt h (ĵ y)`; CHAIN COMPATIBILITY `ĵ_A ∘ ĵ^A_E = ĵ_E` with
   the transported seed `ĵ_A y₀`; nested faces are nested sub-models (`(ν_A)_E = ν_E`, `W_E ⊆ W_A`). NOT done: seed
   independence.
2. `CoefficientTiltDifferentiation` + `ResponseTiltPathBudget` (rank 2): for `g_t = ⟨a(t), h⟩`, `a ∈ C¹` with `a'`
   continuous, `d/dt E_{ρ_t} φ = Cov_{ρ_t}(φ, ġ_t)` (dominated differentiation + quotient rule), the response path
   `t ↦ Φ(g_t)` is `C¹` with velocity `responseVel` (chart's strict derivative), the velocity is continuous, the Fisher
   speed is `√(G^{resp}_{g_t}(ġ_t))`, and the LENGTH BUDGET FOR JOURNEYS THROUGH DATA holds
   (`tendsto_coeffResponse_endpoint`: integrable speed ⇒ endpoint in `Ŵ`, tail bound, data means → extended mean).
3. `ResponseFormContinuity` (rank 3, along coefficient paths): forcings, response velocities, `G_{g_t}(k,ℓ)`,
   `G_{g_t}(ġ_t)`, and `d_eff(t)` are continuous in `t`. NOT done: the `L¹`-in-the-law form.
4. (rank 4 `ResponseSubmersionCalculus`): partially covered — linearity of `DΦ_g`, kernel `= {b_g(k) = 0}`, onto,
   canonical variance-minimising lift, matched decomposition; no separate module.
5. `ResponseNoiseCalibration` (rank 5): the Fisher form is an inner product on `W` (`fisherCore`, via a type synonym
   `FisherSpace` because `W ⊆ J → ℝ` carries the sup norm), Fisher-orthonormal basis, `d_eff(D) = ∑_i Var_D⟨e_i,S⟩`,
   hence `Var_D⟨w,S⟩ ≤ κ Var_{P_θ}⟨w,S⟩ ∀w ⇒ d_eff(D) ≤ κ dim W` (`effDim_le_of_relCov`).
6–8: `ResponseHellingerAtlas`, `ResponseProductAffinity`, `ResponsePatchMargins`: NOT done.

Whole response-map layer now (rounds 82–86): pull-back form (+ bilinear, + horizontal lift, + matched submersion
identity), Fisher-normalised sampling trace identity and calibration, chamber resolution (frozen, intrinsic, two-class
separation), local testing sandwich, completion laws `Q_x = Π(meanExt x)`, `L¹` compactification, data-manifold
response law, uniqueness of fibres over charged face interiors, bounded-tilt action, accessible face strata,
coherent nonexpanding boundary atlas (law/mean/nonexpansion/chain), length budget on `W`-paths and for coefficient
journeys, continuity of the forms along journeys.

The standing direction is unchanged (responses across the data manifold from the featureless law, with maximum
beauty and depth; the resolution story).

## Questions

### Q1. Seed independence and the final atlas statement
For two seeds `x₀, x₀'` with `Q_{x₀} = P'_{v₀}`, `Q_{x₀'} = P'_{v₀'}` (`v₀, v₀' ∈ W'`), when do the embeddings
`ĵ, ĵ'` coincide? On `W'`, `ĵ w` and `ĵ' w` both have law `P'_w`; equality of the completion POINTS needs the
uniqueness of fibres — available only over charged face interiors of the moment polytope
(`meanExt_eq_face_unique`, with polytope hypotheses `V, hpoly, hcharged`) and over vertices. Is "seed independence on
the face-interior strata of a charged polytope" the right statement, and is there a polytope-free formulation (e.g.
via the tilt action: `x₀' = tiltExt (v₀' − v₀) x₀` if and only if …)? Then state the FINAL atlas theorem for the note.

### Q2. What is genuinely missing for the note's response-map section?
Rank what remains: `ResponseHellingerAtlas` (Hellinger topology of the projected-law atlas vs the Fisher completion
topology), `ResponseProductAffinity` (small-`nδ²` product-affinity closeness), `ResponsePatchMargins` (Euclidean
clearance sufficient condition `√Λ r < δ`), the `L¹`-in-the-law continuity of the forms, seed independence, a
polished `ResponseSubmersionCalculus` package, or something new you now see (e.g. the "invisible tangent space" as
a subspace of scores and its complement, the response map as a quotient by an explicit equivalence relation on data
laws, curvature/second-order terms, or a statement connecting the resolution floor `√(d_eff/n)` with the
length-budget tail `∫_t^∞ √G^{resp}` — "how far along a journey can `n` samples see?").

### Q3. "How far along a journey can `n` samples see?"
Combine the length budget with the noise floor: along a journey `g_t`, the response moves by at most
`L(t₁,t₂) = ∫_{t₁}^{t₂} √G^{resp}` and the sampling noise at any point is `√(d_eff/n)` in the frozen metric (with the
frozen → intrinsic transfer `√(Λ/λ)`). Is there a clean theorem "two times `t₁ < t₂` on the journey are resolved by `n`
samples iff/only if `d_F(Φ(g_{t₁}), Φ(g_{t₂})) ≳ √(κ dim W/n)`, and `d_F ≤ L(t₁,t₂)`", i.e. the journey is resolvable at
scale `n^{−1/2}` in Fisher length? State it precisely with the landed pieces (two-class theorem + length bound).

### Q4. Corrections
Any of the landed statements you would restate? In particular the `FisherSpace` synonym construction (instances built
as structure updates over the synonym's module) — is there a cleaner standard idiom you'd recommend, and is the
sub-model generalisation of the face embedding (any `μ'` with `W' ⊆ W`, no face structure) sound as stated — it only
needs positivity of the data variances of `ν` on `W`, correct?

### Q5. Ranked list
Rank the next 6 modules by depth × reachability, and say explicitly if you consider the response-map section
COMPLETE for the note after them (what the note should claim, and what it should explicitly NOT claim).
