# Round 83: after uniqueness in every codimension — existence, and the global response map

## Context (same seabed as rounds 80–82)

Bounded statistics `S : J → X → ℝ`, featureless law `ν` (probability), family `P_θ = e^{−⟨θ,S⟩} ν / Z(θ)`,
direction space `W = dirSpan ν 1 S`, Fisher norm `|w|²_{F,θ} = Var_{P_θ}⟨w,S⟩`, intrinsic distance `d_F` on `W`
(inf of lengths of flat C¹ paths), completion `Ŵ` (a metric completion of `W`), `meanExt : Ŵ → ℝ^J` (Lipschitz
extension of the mean map), every point of `Ŵ` is a law `Q_x = Ψ̄(x)² ν ≪ ν` with mean `meanExt x`.

Polyhedral setting: `V : Finset (J → ℝ)`, `hpoly : momentBody ν 1 S = convexHull V`, `hcharged : ∀ v ∈ V,
0 < ν{S = v}`. Exposed face event `A = {⟨u,S⟩ = β}` with `∀ v ∈ V, ⟨u,v⟩ ≤ β`. Face family `P^A_v =
e^{−⟨v,S⟩} ν(·|A)/Z_A(v)`, face direction space `W_A`, face natural coordinate `faceTheta`.

## Landed since round 82 (all sorry-free, Lean 4 + Mathlib, `timaeus-research/laplace`, `Laplace/Multi/*`)

Your round-82 ranked list, items 1–6 all landed, plus the general-face normal form:

1. `NormalShiftBoundaryCost`: for `h` with `⟨h,S⟩ = c` a.e. on `A`, `⟨h,S⟩ ≥ c` a.e., `|⟨h,S⟩ − c| ≤ B`:
   `d_F(θ, θ + h) ≤ B √(P_θ(A^c))`  (fisherDist_add_normal_le).
2. `FaceMassHellinger`: `|√P_θ(A) − √P_η(A)| ≤ H(θ,η)`; a path of length ≤ 1/2 from a point with `P(A) ≥ 3/4`
   stays in `P(A) ≥ 1/4`, and its translate by a normal-cone vector has at most twice its length.
3. `NormalConeCauchyCoalescence`: sequences `v + a_n`, `v + b_n` with `a_n, b_n` normal to a measurable `A`
   (a.e. constant on `A`, ≥ that constant a.e., bounded), both Fisher-Cauchy, `P(A) → 1` for both ⇒
   `d_F(θ_n, η_n) → 0`, hence equal completion limits (translated grid, exactly as you prescribed).
4. `ResponseAtFeaturelessLaw`: `θ'_0` = basepoint velocity, `P_{θ_0} = ν`, `|θ'_0|²_F = Var_ν(regressor)`,
   `Var_ν h = |θ'_0|²_F + Var_ν(h − regressor)`, residual ⊥ every `⟨e,S⟩`, regressor = best visible approximation.
5. `FaceResponsePythagoras`: for `A` charged exposed, `Q ≪ ν` probability with mean `m_A(v)`:
   `D(Q‖ν) = D(Q‖P^A_v) + D(P^A_v‖ν)` in `ℝ≥0∞`; `P^A_v` has finite information and is the unique information
   projection (equal information ⇒ `Q = P^A_v`).
6. `ResponsePullbackMetric`: along `ρ_t ∝ e^{th} ν`: `|θ'_t|²_F = Cov_{ρ_t}(⟨−θ'_t,S⟩, h)`;
   `(|θ'_t|²_F)² ≤ Var_{ρ_t}⟨θ'_t,S⟩ · Var_{ρ_t} h`; hence `|θ'_t|²_F ≤ (Var_{ρ_t}⟨θ'_t,S⟩ / Var_{P_{θ_t}}⟨θ'_t,S⟩)
   Var_{ρ_t} h` and contraction `|θ'_t|²_F ≤ Var_{ρ_t} h` at a matched law `ρ_t = P_{θ_t}`.
7. `VertexFibreUnique`: means → exposed charged vertex `M` ⇒ eventually `⟨θ_n, w − M⟩ ≥ 0` ∀ vertices
   (forward vertex gap) and `P_{θ_n}{S = M} → 1` ⇒ **the completion fibre over a charged vertex is one point**.
8. `FaceFibreUnique`: `A` exposed, `z₀ ∈ V` a charged vertex of the minimal face of `M` on `A`,
   `M ∈ ri(momentBody ν(·|A))`: for means → `M`, tangential coordinates `τ_n = faceTheta θ_n → v_M`
   (face means converge by L¹ convergence of conditioned laws; face mean map is a chart), normal parts
   `a_n = θ_n − τ_n` are invisible on the face with a.e. constant `⟨a_n, z₀⟩`, outside-vertex gaps
   `⟨a_n, w − z₀⟩ → +∞`, so `a_n` eventually in the normal cone; `P_{θ_n}(A) → 1`; replacing `τ_n` by `v_M`
   costs `K‖τ_n − v_M‖ → 0`; coalescence with base `v_M` ⇒ **the completion fibre over every charged face
   interior is at most one point** (`meanExt_eq_face_unique`), every codimension, no normal ray.

Also available (rounds 80–81): facet accessibility criterion (∃ completion point over `M ∈ ri F` (facet) ⇔
normal ray finite ⇔ Σ√(shell masses) < ∞), the completion law over an accessible facet point = `P^A_{v_M}`,
data-path endpoint theorem (limit in `Ŵ` ⇔ finite response length), `rayTail`, `dist_ray_completion_le`,
`fisherDist_ray_le_rayTail`, Hellinger embedding at accessible facet points, `completionLaw_face_eq_one`.

The user's standing direction: "tackle core features of the change in posterior expectation values with the
change in the data distribution that allow us to *map* the space of responses across the data manifold
(ideally, all the way from the featureless distribution of maximal entropy to our actual data distribution).
What would it take to do this with maximum beauty and depth?"

## Questions

### Q1. Existence (accessibility) in codimension ≥ 2 — the next sufficient theorem

Uniqueness is done in every codimension. Existence is known only for facets (normal ray) and you showed interior
normal rays fail in codimension 2 (charged-square groups). You proposed **face-chain accessibility**: a
finite-length approach to a face followed by a finite-length approach inside its face family lifts to a
finite-length interior approach under normal-translation control. Please give:

(a) a precise statement in seabed terms. Candidate: let `F₁ ⊃ F₂` be faces (`A₁ = {⟨u₁,S⟩=β₁}` a facet event,
`A₂ = A₁ ∩ {⟨u₂,S⟩=β₂}` a face of it), `M ∈ ri F₂`. Suppose (i) the normal ray of `A₁` from some `v₁ ∈ W_{A₁}`
has finite Fisher length (facet accessibility), and (ii) inside the face family on `ν(·|A₁)` the normal ray of
`A₂` towards `M` has finite face-Fisher length. Conclusion: `M` is accessible in `Ŵ` (∃ x with `meanExt x = M`),
and the law is `P^{A₂}_{v_M}`. Is this true as stated? What exactly is the "normal-translation control"
hypothesis, and is it automatic from `NormalTiltFisherComparison` (`Var_{P_{θ+a}} ≤ Var_{P_θ}/P_θ(A)`) when the
first ray keeps `P(A₁)` bounded below?

(b) a proof route using: `fisherDist_add_le_integral_div_sqrt` (translated path costs `1/√q`),
`fisherDist_ray_le_rayTail`, the face family's own Fisher geometry (`W_{A₁}`, its normal ray), and the
comparison between the face-family Fisher form at `v` and the full family's Fisher form at `v − r u₁` for large
`r` (is `Var_{P_{v − r u₁}}⟨w,S⟩ → Var_{P^{A₁}_v}⟨w,S⟩` as `r → ∞`, uniformly on compacts in `v`? we have
`tendsto_rootDensLp_ray` in L²).

(c) the multiscale alternative: is there a clean sufficient criterion for accessibility along a *path* that
alternates normal tilts (your charged-square construction), stated as a summability condition over a
two-dimensional array of shells? Or is face-chain the right level of generality for now?

### Q2. The global response map, from the featureless law to the data law

We now have two maps on the closed moment body: the variational law `M ↦ Q_M` (defined at every face-family
mean, `FaceResponsePythagoras`), and the completed Fisher response `x ↦ Q_x` on `Ŵ` (defined on accessible means,
unique over face interiors). For the "map of responses across the data manifold" what is the deepest
statement to formalise next? Candidates:

(i) **Continuity of the variational response in the mean**: `M ↦ Q_M` is continuous from the closed moment body
(polyhedral) into `L¹(ν)` or Hellinger *on each open face*, and jumps across faces (the law changes support).
Is there a clean statement of the jump: `H(Q_M, Q_{M'})² → 2 − 2√(ν(A')/ν(A))·(…)` as `M' → M` from a lower face?
Or a total-variation formula for the jump in terms of face masses?

(ii) **The response curve of the data path as a curve of laws** `t ↦ Q_{[θ_t]}`, `t ∈ [0,∞]`: at `t = 0` it is
`ν`; it moves with speed `|θ'_t|_F`; its endpoint is `P^A_{v_M}`. Statement of "monotone information":
is `t ↦ D(Q_{[θ_t]} ‖ ν)` monotone along the data path? (For the interior part `D(P_{θ_t}‖ν) = 𝓘(m_t)`, the
rate function at the data response mean; is `t ↦ 𝓘(m(ρ_t))` monotone in `t` for `ρ_t ∝ e^{th}ν`? We have the
derivative `d/dt 𝓘(m_t) = ⟨θ_t, −b_t⟩`-type identities.)

(iii) **Length budget**: `FacetResponseLengthBudget` — bound the response length `∫_0^∞ |θ'_t|_F dt` by the data
length plus the ray-plus-log term (you said "land the ray-plus-log bound" in round 82 §Q3.3). Please restate
the sharp form you have in mind, given `eventually_dataRay_estimates` (√responseSpeedSq ≤ C₁‖dataCov‖ +
C₂ √raySpeedSq·|depthVel| and √raySpeedSq·(−depthVel)₊ ≤ C₃∫(H−h)dρ_t + C₄‖dataCov‖).

(iv) **Hellinger–Fisher local Lipschitz continuity of the response map** (`ResponseLocalHellingerLipschitz`):
`d_F(Φ(Q), Φ(R)) ≤ (2B/√λ) H(Q,R)` where `C_{θ(m)} ⪰ λ I` on a convex mean neighbourhood — with the seabed's
`meanMapHomeomorph` and `hasStrictFDerivAt_invFun_meanMap`, how should `λ` be packaged (min eigenvalue of the
covariance on `W`, or a coercivity hypothesis `fisherVar θ w ≥ λ‖w‖²` on a set of `θ`)?

Which of (i)–(iv) is the *core* of "mapping responses across the data manifold"? What is missing from this list
that you consider deeper (e.g. a Riemannian/stratified structure theorem for `Ŵ`: the completion over the
polytope is the disjoint union over faces of the face families, glued by the face-mass-to-one topology)?

### Q3. Ranked list

Rank 8–10 modules (≤300 lines each) for the next stretch, each with a one-line statement in seabed terms and
a two-line proof route. Mark which are "beautiful and deep" in the user's sense versus infrastructure.

### Q4. Sanity of the landed statements

Any of the eight landed statements above that you think is weaker than it should be, or where a hypothesis is
unnatural (e.g. `z₀ ∈ minimalFacePoly V M` in `FaceFibreUnique`, the finite-vertex charged-polytope setting),
and the cheapest strengthening.
