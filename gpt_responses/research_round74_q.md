# Research round 74: after the atlas — the deepest next theorem about the response map over the data manifold

## Landed since round 73 (laplace `Laplace/Multi/*`, sorry-free, warning-free, pushed; your route (b) executed verbatim)
- **PolytopeMinimalFace**: for `P = conv V`, `T_M = {v : a_v(M) > 0}` (vertex section), `F_M = conv T_M`:
  `minimalFace_vertexStat_eq` (the abstract minimal face = `F_M`), `isExtreme_minimalFacePoly`, `minimalFacePoly_subset_of_isExtreme`,
  `vertexSection_pos_iff_mem_minimalFacePoly` (Csiszár for polytopes), **`mem_intrinsicInterior_minimalFacePoly`** (`M ∈ ri F_M`;
  proof: the seabed's supporting-functional criterion — a functional maximised at `M = Σ_T a_v v` is constant on `T`),
  `disjoint_uncharged_affineSpan` (`conv(V∖T) ∩ aff F_M = ∅`: a point of `aff F_M` is an endpoint of an open segment through `M`
  inside `P`, hence on `F_M` by extremality, contradicting absorption), **`exists_exposing_minimalFacePoly`**
  (`∃ u β, ⟨u,v⟩ ≤ β on V, ⟨u,M⟩ = β, (⟨u,v⟩ = β ↔ v ∈ T_M), F_M = conv{v ∈ V : ⟨u,v⟩ = β}` via
  `geometric_hahn_banach_compact_closed` separating `conv(V∖T)` from `aff F_M`, and "a functional bounded below on an affine
  subspace is constant"), `exists_minimalFacePoly_eq_inter_hyperplane` (`F_M = P ∩ {⟨u,·⟩ = β}`).
- **PolytopeProjectionSupport**: `exists_exposing_polytope` (every `M ∈ P` has exposing data with a tight charged vertex, a
  charged face fibre, `M ∈ ri` of the tight hull, and the face identity), **`exists_ray_tendsto_responseProjection_of_mem_polytope`**
  (EVERY `q_M` on a charged polytope is the TV-limit of an explicit natural ray with the exact rate `2B_t/(A+B_t)`),
  `responseProjection_compl_faceFibre_eq_zero` (essential support), `responseProjection_eq_faceMeasure_of_mem_polytope`
  (`q_M` = projection of `ν(·|⟨u,S⟩=β)`), **`ae_projDens_le_of_mem_polytope`** (`dq_M/dν ≤ 1/m` when every vertex fibre has mass
  `≥ m`; the weight `e^{−⟨θ,S⟩}` on the face peaks at a tight vertex whose fibre sits in the normaliser), `exists_uniform_projDens_bound`,
  **`tendsto_integral_abs_projDens_sub_pow`** (`L^p` continuity for every finite `p`).
- **PolytopeFaceOrder**: `minimalFaceFibre V S M = {x : S x ∈ F_M}`, `responseProjection_absolutelyContinuous_restrict`
  (`q_M ≪ ν|_{Φ_M}`), `restrict_minimalFaceFibre_absolutelyContinuous` (`ν|_{Φ_M} ≪ q_M`, via `q_M = ν_F.tilted(−⟨θ,S⟩)` and
  Mathlib's `absolutelyContinuous_tilted`), **`responseProjection_absolutelyContinuous_iff`** (`q_M ≪ q_N ↔ F_M ⊆ F_N`),
  `responseProjection_equivalent_iff` (mutual a.c. ↔ `F_M = F_N`: the strata are the faces), the order read off the vertex section.
- **ResponseAtlas** (capstone, thin): `exists_faceMeasure_tilted_eq_responseProjection` (facewise exponential representation),
  `structure ChargedPolytopeAtlas hS ν V : Prop` with fields strata / charged_iff / exposed / facewise_exponential / support /
  face_order / density_bound / homeomorph (`P ≃ₜ` completed family in `L¹`, `e M = dq_M/dν`) / compact / hellinger / lp / ray;
  `chargedPolytopeAtlas hpoly hcharged`, and `exists_chargedPolytopeAtlas_of_compact_mean_lift` (rigidity).
- Also in the seabed (earlier): mean-map charts on the relative interior (`MeanMapChart`, `GlobalChart`, `IntrinsicLegendre`:
  `M ↦ θ(M)` is a homeomorphism `ri(momentBody) ≃ Θ`, with `D²log Z = Cov(S)` positive definite on the direction space),
  `NaturalParameterMajorant`/`Taylor` (factorial bounds and explicit analyticity radius in natural coordinates), `FisherInformation`
  (response form = Fisher information), the three scales of thermodynamic distance, `BoundaryLayerBounds`, `FisherAccessibility`
  (`Var_{p_t}⟨u,S⟩ ≤ 16B_{t/2}/(At²)`, polynomial layer ⇒ finite Fisher length), `HellingerComparison`.

## The standing directive (user, verbatim)
"make sure we are tackling core features of the change in posterior expectation values with the change in the data
distribution that allow us to 'map' the space of responses across the data manifold (ideally, all the way from the
'featureless' distribution of maximal entropy to our actual data distribution). What would it take to do this with maximum
beauty and depth?"

## Questions
1. With the stratified atlas landed, rank (with a one-paragraph Lean route each, naming Mathlib pieces where you can) the
   candidates for the next DEEP theorem, judged by the directive above — the change of posterior expectations `⟨f⟩_{q_M}` as
   `M` moves across strata from the featureless response `M₀ = E_ν S` (the maximal-entropy point, `q_{M₀} = ν`) to a
   boundary response:
   (A) **Natural-parameter convergence by face flags**: characterise `θ_n → ∞` with `M(θ_n) → M ∈ ri F` (normal divergence
       selecting `F`, convergence of the effective tangential parameter in `Θ_F`), and the iterated version for flags
       `F_1 ⊃ F_2 ⊃ …`; the topology of `⨆_F Θ_F ↔ P`. Which precise statement is the right first theorem, and is the
       "normal part → +∞ along the polar cone of `F`" formulation provable from what we have (exposed faces + `M ∈ ri F` +
       the ray formula)?
   (B) **Susceptibilities across strata**: for bounded `f`, `M ↦ ⟨f⟩_{q_M}` is continuous on `P` (from `L¹`), differentiable on
       each `ri F` with derivative `Cov_{q_M}(f, S)·Cov_{q_M}(S)^{-1}` on `L_F`; what happens to the susceptibility as `M` approaches
       a subface — rates in terms of the boundary layer (`H(r) ~ r^α`), blow-up exponents, and the sharp form of "the response
       map is Lipschitz in Hellinger but not in the mean parameter near a face". Is there a clean theorem: along the natural ray,
       `d⟨f⟩/dt = −Cov_{p_t}(f,⟨u,S⟩)` with `|·| ≤ ‖f‖_∞ · 4√(B_{t/2}/A)/t`, and `dM_u/dt = −Var`, so `d⟨f⟩/dM_u` is a ratio whose
       behaviour is governed by the layer? Which formulation is deepest yet landable?
   (C) **Fisher completion vs topological completion** (your §4): the sharp 1-D example `ν = p₀δ₀ + p₁δ₁ + c·1_{(0,e^{-1})}
       dx/(x log²(1/x))`, `H(r) = c/log(1/r)`, infinite Fisher length despite TV/Hellinger convergence. What is the cleanest
       general classification theorem (e.g. "the natural ray to `F` has finite Fisher length iff `∫₀ √(H(r))/r dr < ∞`" or a
       Laplace-transform criterion `∫^∞ √(B_{t/2})/t dt < ∞`), is it true in that form, and what is the Lean route from
       `raySpeedSq_le_offFaceMass` plus a matching LOWER bound `Var_{p_t}⟨u,S⟩ ≥ c·B_{2t}/(A t²)`-type?
   (D) **Uniform CLT near stratum changes** (your remark): what is the statement, and is it within reach given the atlas?
   (E) Anything else you consider more fundamental for "mapping the responses from the featureless law to the data law".
2. For your rank-1 item give the precise Lean-shaped statement(s), the hypotheses you would take (which of our objects:
   `faceMeasure`, `famDens`, `raySpeedSq`, `layerMass`, `tiltMass`, `minimalFacePoly`, `vertexSection`, `meanMap` charts),
   and the two or three lemmas that carry the proof.
3. Sanity-check the claim "`dq_M/dν ≤ 1/m_*`" as we formalised it: `m` is a lower bound on ALL vertex fibre masses `ν(S = v)`,
   `v ∈ V`, and the bound holds for every `M ∈ P` with the same `m`. Correct? Any sharper uniform bound available for free?
