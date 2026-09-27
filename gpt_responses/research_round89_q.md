# Round 89 — after rounds 87 and 88: is the response-map section complete, and what is its final shape?

You are Astra, research advisor on the Lean formalisation (laplace seabed, `Laplace/Multi/*`) of the germbij note on
the response map `q ↦ Φ(q)` over the data manifold. ALL SIX modules you ranked in round 88 are now formalised
(sorry-free, warning-free), on top of the six of round 87. This round: audit round 88, then decide whether the
response-map section is complete for the note and what (if anything) is worth one more batch.

Conventions unchanged (see rounds 87–88): `S` bounded statistics, `ν` featureless, `W = dirSpan`, `θr` response chart,
`CDE θ` chart-derivative equivalence on `W`, `Ŵ` the Fisher completion, `Q_x` completion laws, `Ψ_x ∈ L²(ν)` root
densities, `forcing`, `responseOf`, `responseVel`, `pullbackForm`, `samplingOp/samplingEnergy`, `sampleResponse`,
`faceEmbed`/`faceEmbedExt`, `meanExt`, `momentBody`, `intrinsicInterior`, `minimalFacePoly V M`, `faceMeasure ν E`.

## 1. What landed in round 88

### 1.1 `AccessibleFaceStratification` (rank 1)
- `minimalFacePoly_eq_of_mem_intrinsicInterior : N ∈ ri(F_M) → F_N = F_M` (M, N in the polytope), and the iff
  `mem_intrinsicInterior_minimalFacePoly_iff : N ∈ ri(F_M) ↔ F_N = F_M`.
- `momentBody_faceMeasure_eq : momentBody (faceMeasure ν {⟨u,S⟩ = β}) = conv{v ∈ V : ⟨u,v⟩ = β}` (charged polytope,
  exposed face with a tight vertex): tight vertices stay charged after conditioning (`tight_vertex_mem_momentBody_faceMeasure`),
  upper inclusion by the hyperplane cut.
- Seed bridge `completionLaw_eq_faceFamily_faceThetaOf : meanExt x = M ∈ ri(momentBody ν_E) → Q_x = P^E_{θ_E(M)}`.
- `faceChart (hx₀ : meanExt x₀ ∈ ri(momentBody ν_E)) : W_E → Ŵ := faceEmbed … x₀ (θ_E(meanExt x₀))`;
  `completionLaw_faceChart : Q_{j w} = P^E_w`; `meanExt_faceChart : meanExt (j w) = m_E(w)`; `meanExt_faceChart_mem`;
  `eq_of_meanExt_eq_of_mem_ri` (fibre over a face-interior mean is a single point; uses a charged tight vertex from
  `exists_charged_vertex_on_face`); `range_faceChart : range j = {x : meanExt x ∈ ri(momentBody ν_E)}`;
  `range_faceChart_eq_ri_face : = {x : meanExt x ∈ ri(conv(tight V))}`; `faceChart_injective`; `faceChart_eq` (seed
  independence of the finite chart).
- `stratum x := {y : F_{meanExt y} = F_{meanExt x}}`, `stratum_eq_or_disjoint`, `iUnion_stratum = univ`,
  `exists_faceChart_range_eq (x) : ∃ u β z₀ (hz₀V hz₀β) (hx₀ : meanExt x ∈ ri(momentBody ν_{E(u,β)})),
    (∀ v ∈ V, ⟨u,v⟩ ≤ β) ∧ F_{meanExt x} = conv(tight) ∧ range (faceChart hx₀) = stratum x`.
  I.e. `Ŵ = ⨆_{F accessible} j_F(W_F)`, each stratum being the image of the canonical chart of the minimal face of its
  extended mean, accessible by the point itself. Nothing claimed about accessibility of every face or frontier conditions.

### 1.2 `CanonicalDataJourney` (rank 2)
- `logDens q = log q`; `bdd_logDens (c ≤ q ≤ C, c > 0)`; `journeyLaw_zero : ν.tilted(0·log q) = ν`;
  `journeyLaw_one (∫q = 1) : ν.tilted(1·log q) = q ν`.
- `responseOf_eq_dataTheta : responseOf (t log q) = dataTheta hh t` (the seabed's data path);
  `coeffResponse_unit` (a one-coefficient journey); `journeyResponse_zero : Φ(ρ_0) = 0`; `journeyResponse_one : Φ(ρ_1) = θr(E_D S)`;
  `hasDerivAt_journeyResponse : d/dt Φ(t log q) = responseVel (t log q) (log q)`;
  `fisherDist_journey_le`, `fisherDist_zero_dataResponse_le : d_F(0, θr(E_D S)) ≤ ∫_0^1 √(pullbackForm (t log q)(log q))`.
- `journeyLaw_zero_matched`; `lawCov_logDens_eq_fisherVar_add_residual : Var_ν(log q) = |DΦ_0[log q]|²_{F,0} + Var_ν(log q − hor_0 DΦ_0[log q])`.
- `hasDerivAt_klDiv_journey : d/dt D(ρ_t‖ν) = t Var_{ρ_t}(log q)`; `monotoneOn_klDiv_journey` on `[0,∞)`;
  `klDiv_journey_le : D(ρ_t‖ν) ≤ D(D‖ν)` for `t ∈ [0,1]`.

### 1.3 `AbsolutelyContinuousForcing` (rank 3)
- `covVec_mem_dirSpan : (Cov_D(S_i,k))_i ∈ W` for every `D ≪ ν` and bounded `k` (vector integral of the a.e. `W`-valued
  `k(x)(S(x) − E_D S)` via `Convex.integral_mem`).
- `densForcing_mem_dirSpan`, `retraction_densForcing`, `densVel_eq_symm`, `densVel_eq` (retraction-free density velocity),
  `densForcing_tiltDens`, `densResponse_tiltDens`, `densVel_tiltDens` (density objects = tilt objects at `q = e^g/Z`, all `rfl`).

### 1.4 `ResponseChamberClearance` (rank 4)
- `mem_of_fisherClearance` (Fisher δ-ball in a coefficient chamber + segment bound Λ + √Λ r < δ ⇒ Euclidean r-ball in the chamber).
- `frozen_margin_of_euclidean_clearance : (∀ z ∈ W, ⟨z,z⟩ < r² → M + z ∈ U) → ∀ z ∈ W, q_θ(z) < (r/√Λ)² → M + z ∈ U`
  (from `‖z‖₂² ≤ Λ q_θ(z)`).
- `measureReal_sampleResponse_notMem_fisherBall_le_of_clearance : P(M̂ ∉ B_F(θ(m_D), r/√λ)) ≤ Λ · tr(R C_D)/(n r²)` under
  Euclidean clearance r, coercivity λ on the chamber, bound Λ at the response.

### 1.5 `MixtureResponseJourney` (rank 5)
- `mem_intrinsicInterior_segment` (segment between relative-interior points is relative-interior, via the supporting-functional criterion).
- `mixLaw t = ofReal(1−t)•ν + ofReal t•D`; `mean_mixLaw : m_t = m_ν + t(m_D − m_ν)`; `mixResponse t := θr(m_t)`;
  `mixResponse_eq`; `mixResponse_zero = 0`; `mixResponse_one = θr m_D`;
  `hasDerivAt_mixResponse : Φ(D_t)' = (CDE Φ(D_t)).symm (m_D − m_ν)` for `t ∈ [0,1]` (m_D interior);
  `fisherDist_mixResponse_le : d_F(0, θr m_D) ≤ ∫_0^1 |(CDE θ_t).symm (m_D − m_ν)|_{F,θ_t} dt` (clamp path + change of variables).

### 1.6 `SharpAffinityTesting` (rank 6)
- `integral_abs_mul_self_sub_le_sqrt : ∫|f² − g²| ≤ 2√(1 − A²)`; `integral_rootLaw_sub_le_sqrt : ∫φ d(f²μ) − ∫φ d(g²μ) ≤ √(1 − A²)`;
  `testing_error_ge_sqrt`; `affinityExt x y = ∫Ψ_xΨ_y`, `affinityExt_eq (= 1 − H²/2)`, `affinityExt_ge (≥ 1 − d̂²/8)`;
  `integral_sampleLaw_sub_le_sqrt : ≤ √(1 − A^{2n})`; `testing_error_sampleLaw_ge_sqrt : err ≥ (1 − √(1 − A(x,y)^{2n}))/2`.

## 2. Questions

### Q1. Audit
Anything overclaimed or mis-stated in 1.1–1.6? Specifically: (a) is `exists_faceChart_range_eq` the right formal shape of
"`Ŵ = ⨆_{F accessible} j_F(W_F)`", or should the theorem be stated as a `Set`-level `iUnion` over faces with an explicit
`Accessible F` predicate? (b) In 1.2 the KL monotonicity is on `[0,∞)` — fine? (c) In 1.5 the length bound's integrand
mentions `θ_t = mixResponse t`, defined for all `t` but only meaningful on `[0,1]`; the integral is over `[0,1]` — ok?
(d) Is there any hidden dependence on a choice in `faceChart` (it is seeded at the given accessible point; `faceChart_eq`
removes it) that the note should mention?

### Q2. Is the response-map section complete?
Against your recommended six-part shape (1 response as projection, 2 infinitesimal geometry, 3 sampling and resolution,
4 boundary geometry, 5 journeys through data, 6 what finite samples can see): list, for each part, the landed theorems
that carry it and any genuine gap. Which of the following are worth doing, ranked (deliverables one line each), and which
should be explicitly declined:
- the global mean-injectivity corollary of the stratification (two completion points with equal extended means coincide,
  charged polytope, no accessibility) and hence law-injectivity `Q_x = Q_y → x = y` — this would discharge the `huniq`
  hypothesis of the Hellinger package and of `faceEmbedExt_injective`;
- per-face accessibility for finitely supported statistics (finite support ⇒ exponential normal-ray decay ⇒ finite tail
  length ⇒ every face accessible ⇒ decomposition over ALL nonempty faces);
- the stratification's chain compatibility (`j_F ∘ j^F_E = j_E` for `E ⊆ F` faces of the polytope, from `faceEmbedExt_faceEmbedExt`
  and `faceMeasure_faceMeasure_of_subset`);
- the exponential-vs-mixture comparison in one response dimension (monotone paths have equal length);
- a `Ŵ`-level version of the journey theorems (journeys as maps into the completion rather than into `W`);
- the initial defect expansion `Δ''(0) = Var_ν(h − h_reg)` restated for the canonical journey (already exists as
  `deriv_deriv_responseDefect_zero_eq_residual` for general `h`);
- anything from the six-part shape you consider missing.

### Q3. The note's closing
You said to end with the tail theorem. Given the sharp affinity form, should the closing statement be the exact
`err ≥ (1 − √(1 − A^{2n}))/2` with `A ≥ 1 − R(t)²/8`, or the linearised `err ≥ (1 − √n R(t)/2)/2`? Write the closing
paragraph as you would put it in the note (one paragraph, theorem-statement level, with the caveat about response-family
laws versus data laws).

Be concrete; end with the single ranked list of what to do next (or "stop here" if the section is complete).
