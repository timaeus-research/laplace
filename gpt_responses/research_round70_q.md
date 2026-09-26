# Research round 70: the general-`X` polyhedral completion — fixing the Lean shape before building

## Landed since round 69 (laplace `Laplace/Multi/*`, sorry-free, pushed; NOT mirrored)
Your rank-2 route worked verbatim, in two modules:
- **NaturalParameterMajorant**: `Z(t)•p(t) = w(t)`, `‖w^{(k)}‖₁ ≤ L^k Z`, `|Z^{(j)}| ≤ L^j Z`, Leibniz in `L¹`, the recurrence
  `b_k ≤ L^k + Σ C(k,j)L^j b_{k−j}`, the numerical lemma `Σ_{k≤N} ρ^k b_k/k! ≤ 3`, hence `‖p^{(k)}(t)‖₁ ≤ 3 k! ρ^{−k}` for all `t`.
- **NaturalParameterTaylor**: `‖p(s+t) − Σ_{k≤N} p^{(k)}(s)t^k/k!‖₁ ≤ 3(|t|/ρ)^{N+1}` for ALL `s, t` (norm duality against bounded
  test functions + scalar Lagrange remainder; reflection `v ↦ −v` for `t < 0`), so the `L¹` Taylor series converges on `|t| < ρ`
  (`tendsto_taylor_natCurve`), and the same for every bounded observable's response.

## What the seabed ALREADY has for general `X` (probability space, bounded features `S : J → X → ℝ`, reference `ν`)
- `genRate ν S M = ⨆_q ofReal(q·M − featCgf ν S q)` (dual rate); `responseProjection hS ν M` = the unique Pythagorean minimiser
  (`exists_pythagorean_minimiser`: mean `M`, `klDiv q_M ν = genRate`, `klDiv ρ ν = klDiv ρ q_M + genRate` for every feasible `ρ`);
  `information_decomposition`.
- `momentBody ν 1 S = closure (convexHull (essRange ν 1 S))`; on `intrinsicInterior (momentBody)` the projection is the bounded
  tilt `ν.tilted (−dirLoss S θ)` (`responseProjection_eq_tilted`) and the analytic atlas lives there.
- **Exposed faces**: `faceMeasure ν F = (ν F)⁻¹ • ν.restrict F`; for a supporting functional `u` with `dirLoss S u ≤ β` a.e. and
  `ν.real {dirLoss S u = β} > 0` and `u·M = β`: `genRate_face_eq : 𝓘(M) = −log ν(F) + 𝓘_F(M)` and
  `responseProjection_faceMeasure : q_M(ν) = q_M(faceMeasure ν F)`.
- **Exposed chains** (`ExposedChain ν S M A n`, iterated exposed faces): `exists_exposedChain` (every finite-rate `M` lies in the
  relative interior of the moment body of some iterated conditioned law) and `responseProjection_eq_of_exposedChain`
  (`q_M = familyMeasure (faceMeasure ν A) … θ` with `θ ∈ dirSpan (faceMeasure ν A) 1 S`); corollary
  `responseProjection_eq_withDensity_comp` (the density of `q_M` is a function of `S`).
- **Stability**: `lowerSemicontinuous_genRate`; **`tendsto_integral_responseProjection_of_tendsto_genRate`**: if `M_i → M₀`, rates
  eventually finite and `𝓘(M_i) → 𝓘(M₀)`, then `∫F dq_{M_i} → ∫F dq_{M₀}` for every bounded `F` (proved via Pythagoras + a
  Pinsker-type bound; `PinskerEvent`/`PinskerObservable` give `|∫F dq − ∫F dq'| ≤ L√(2 KL)`); segment versions
  (`tendsto_genRate_segment`, `tendsto_integral_responseProjection_segment_of_ne_top`).
- `EmpiricalTotalVariation`: TV norm of `L¹` densities, `reconstructionL1 hS ν M = [dq_M/dν] ∈ L¹(ν)`.
- **Finite completion** (round 68, finite `X`): `vecMeasure`, `qStarVec hS ν M x = q*(M){x}`, `continuousOn_qStarVec` on the polytope,
  Csiszár `qStarVec M x > 0 ↔ S(x) ∈ minimalFace M`, `retract`, `completedHomeomorph`, deformation retraction, closure statement.

## The plan I am about to execute (your round-69 rank 1), in Lean terms — please check it
Hypotheses: `V : Finset (J → ℝ)`, `hV : momentBody ν 1 S = convexHull ℝ (V : Set (J → ℝ))`,
`hcharged : ∀ v ∈ V, 0 < ν.real {x | statPoint S x = v}` (`statPoint S x = fun j ↦ S j x`).
1. **PolyhedralVertexWitness**: `vertexLaw a := Σ_{v ∈ V} a v • faceMeasure ν {statPoint S = v}` for `a ∈ stdSimplex ℝ V`;
   probability, mean `Σ a v • v`, density `Σ a_v 1_{S=v}/ν{S=v}` bounded, hence `klDiv (vertexLaw a) ν ≠ ⊤` (via
   `klDiv_ne_top_iff`: `≪` + integrable llr) and **`genRate ν S M ≠ ⊤` for every `M ∈ momentBody`** (`genRate_le_klDiv`).
2. **PolyhedralVertexSection**: the finite completion applied to the finite type `V` with features `S' j v := v j` and the uniform
   reference gives `a : (J → ℝ) → (V → ℝ)`, `a(M) ∈ stdSimplex`, `Σ a_v(M) • v = M`, continuous on the polytope, and
   `a_v(M) > 0 ↔ v ∈ minimalFace M` (Csiszár). Also: the minimal face of the polytope is exposed by some `u` (finite `V`), so
   `q_M = q_M(faceMeasure ν {S ∈ F_M})` and `q_M ≥ c·ν` on `{S ∈ F_M}` for some `c > 0` (bounded tilt on the face, via the exposed
   chain / `responseProjection_eq_of_exposedChain`); in particular `q_M ≥ c·ν` on every charged vertex fibre `{S = v}`, `v ∈ F_M`.
3. **PolyhedralRecovery**: for `M_n → M` in the polytope, `b_n := q_M + vertexLaw'(a(M_n) − a(M))` (signed) is eventually a
   probability measure with mean `M_n` (negative corrections only on fibres of `F_M` where `q_M ≥ c ν` and the corrections
   `→ 0` in sup norm), `‖db_n/dν − dq_M/dν‖_∞ → 0`, `klDiv b_n ν → 𝓘(M)` (bounded densities, continuity of `x log x`), hence
   `limsup 𝓘(M_n) ≤ 𝓘(M)`; with `lowerSemicontinuous_genRate`: **`𝓘` continuous on the polytope**.
4. **PolyhedralCompletion**: from 3 and `tendsto_integral_responseProjection_of_tendsto_genRate`: `M ↦ q_M` continuous for
   bounded observables; TV: `klDiv b_n q_{M_n} = klDiv b_n ν − 𝓘(M_n) → 0` (Pythagoras), Pinsker `‖b_n − q_{M_n}‖_TV → 0`,
   `‖b_n − q_M‖_TV → 0`, so **`M ↦ [q_M] ∈ L¹(ν)` is continuous on the whole polytope**; then compactness of the completed family,
   homeomorphism with the polytope, closure of the interior family, retraction/deformation retraction on `ν`-dominated laws with
   bounded density (or on `L¹` densities), mirroring the finite modules.

## Questions
1. Is this the right decomposition, and is anything in 1–4 wrong or avoidable? In particular:
   (a) Is `q_M ≥ c·ν` on the face preimage the right way to make the signed correction legal, and is the exposed-chain machinery
       (`responseProjection_eq_of_exposedChain`, `θ ∈ dirSpan (faceMeasure ν A)`) enough to get the bounded-below density on
       `{S ∈ F_M}` without a new face-restriction lemma? (For a polytope face `F`, `{S ∈ F} = {dirLoss S u = β}` for an exposing `u`,
       so a single exposed step suffices — correct?)
   (b) For step 3, do we need `a(M_n) → a(M)` only (continuity of the vertex section) or also the support statement
       `a_v(M) > 0 ↔ v ∈ F_M`? (The corrections `a_v(M_n) − a_v(M)` can be negative only where `a_v(M) > 0`, i.e. `v ∈ F_M`, where
       `q_M ≥ cν` on the fibre — so both, I think.)
   (c) `klDiv b_n ν → 𝓘(M)`: the densities `f_n = dq_M/dν + Σ_v (a_v(M_n) − a_v(M)) 1_{S=v}/ν{S=v}` are uniformly bounded with
       `f_n → f` in sup norm; `∫ f_n log f_n → ∫ f log f` by dominated convergence (or uniform continuity of `x log x` on `[0, C]`).
       Any cleaner route (e.g. convexity/upper bound `klDiv(b_n‖ν) ≤ (1−ε_n) klDiv(q_M‖ν) + …`)?
   (d) TV continuity in step 4: Pinsker for `klDiv b_n q_{M_n}` needs `b_n ≪ q_{M_n}`; this follows from the Pythagorean identity
       (`klDiv b_n ν = klDiv b_n q_{M_n} + 𝓘(M_n)` finite). Is there a slicker way to get `[q_{M_n}] → [q_M]` in `L¹` from the
       observable statement plus uniform integrability (densities of `q_{M_n}` are NOT uniformly bounded near the boundary)?
2. Which single lemma is now the hardest, given the seabed pieces above? Estimate the module count.
3. The alternative first step is your rank 3 (facewise Fisher geometry `D²𝓘_F = Cov|_{V_F}⁻¹`, face lattice `M ∈ F ↔ q_M{S ∈ F} = 1`,
   boundary-ray formula `‖q_t − q_F‖₁ = 2B_t/(A+B_t)`). Which of these is essentially free from the seabed (`genRate_face_eq`,
   `responseProjection_faceMeasure`, the interior Fisher identity `FisherInformation`), and should any of it be built BEFORE the
   completion (e.g. because the completion proof uses the face lattice)?
4. Anything in the plan that would be more beautiful stated differently (e.g. stating the completion for `ν`-dominated laws with
   the `L¹` density topology as the ambient space of the retraction, or working with the push-forward `S_*ν` on the polytope and
   identity features, since `dq_M/dν` is a function of `S`)?
Answer in ≤ 3000 words; be concrete about Lean shapes and name the Mathlib lemmas you rely on (klDiv, Pinsker, convex hulls of finsets).
