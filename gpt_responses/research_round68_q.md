# Research round 68: face completion on a finite alphabet — the Lean route to continuity of the completed family

## Landed since round 67 (laplace `Laplace/Multi/*`, sorry-free, pushed)
- **AnalyticTilt** (your route (b) through `A = C(K, ℝ)`): `weightL1 θ = T_g(exp_A(featureCLM θ))`, hence `θ ↦ [g e^{−⟨θ,S⟩}]`,
  `famNum`, `famZ` real-analytic. **AnalyticChart**: mean map, Jacobian, chart, covariance operator and its inverse `C^ω`;
  `chartVInv` analytic on its open domain by grade-ω `ContDiffAt.to_localInverse` + identification through
  `chartVInv ∘ chartV = id` (exactly your argument); `z ↦ θ(m₀+z)` and `z ↦ [q_{M+z}]` `AnalyticOnNhd` on the open interior
  displacements; `s ↦ [q_{M_s}]` and every bounded-observable response real-analytic on the interior atlas domain. Round-67 rank 1
  DONE (qualitative).
- **PointwiseJets** (your rank 4, structural): `p^{(k)}(s) = [x ↦ ∂_s^k q_{M_s}(x)]` for every `k` at every interior atlas point
  (induction through the L¹-pointwise principle); Bell tower `B_{k+1} = ∂_s B_k + ℓ_s B_k`, `B_1 = ℓ`; pointwise invisible tower.
- Earlier: ThirdJet, QuantitativeJets (`‖p^{(k)}‖₁` bounds), CubicRemainder (Lagrange `1/3!` by norm duality).

## What the seabed already has for the boundary (general `ν`, bounded `S`)
- `EntropyCompletion.exists_unique_entropy_minimiser (hfin : genRate ν S M ≠ ⊤) : ∃! ρ, IsProbabilityMeasure ρ ∧ E_ρ S = M ∧
  klDiv ρ ν = genRate ν S M` (strong induction on the affine dimension through positive-mass exposed faces);
  `entropyProj_eq_genRate`. The minimiser is `responseProjection hS ν M` (defined for every `M`, meaningful when finite rate).
- `BoundaryCompletion.boundary_completion`: for finite-rate `M` (interior or not) the straight atlas `M_s = m₀ + s(M − m₀)` is
  interior for `s < 1`, `KL(Q_* ‖ Q_s) = ∫_s^1 (1−u) κ_u du → 0` as `s ↑ 1` (`tendsto_klDiv_responseProjection_atlas`), every
  bounded observable's response converges to the endpoint (`tendsto_integral_atlas_endpoint`), Pythagoras
  `KL(ρ‖ν) = KL(ρ‖Q_*) + 𝓘(M)` for every law `ρ` with response `M`.
- `ExposedFace`/`NullFace`/`FaceLimit`/`FaceTotalVariation`/`FaceInfinite`: `𝓘(M) = −log p_F + 𝓘_F(M)` on a positive-mass exposed
  face; the ray `P_{sv}` converges in TV to the conditional law `Q_F` with cost `−log Q(F)`; null faces cost `+∞`.
- `MomentPolytope` (finite alphabet, positive weights `π`, nondegenerate `S`): `range meanMap = interior (convexHull (range S))`;
  `FiniteEndpoint`: natural rays converge to the prior conditioned on the ground face.
- `AtlasRefinement.responseProjection_mean_familyMeasure`: on interior means the projection is the family member.

## Mathlib inventory (checked): Carathéodory (`convexHull_eq_union`), `convexHull` of finite sets, `IsCompact` of the simplex
(`stdSimplex`), `LowerSemicontinuous`/`UpperSemicontinuous`, `IsCompact.exists_isMinOn`, `Filter.Tendsto` on subsequences
(`IsCompact.tendsto_subseq`), `klDiv` (ENNReal) with `klDiv_eq_zero_iff`, Pinsker (`ProbabilityTheory.tvDist`? we use the sign
observable), finite-support measures on `Fintype X` with `Measure.count`; NO Hoffman lemma, NO polyhedral lower hemicontinuity,
NO Gale–Klee–Rockafellar (upper semicontinuity of finite convex functions on polytopes), NO "polytope is locally its tangent cone".

## The target (your rank 2)
Finite `X`, positive weights `w`, `C = conv S(X)`. The completed family `q*(m) = responseProjection m` for `m ∈ C` (every `m ∈ C`
has finite rate on a finite alphabet with positive weights — all faces have positive mass). Wanted: (1) **continuity** of
`m ↦ q*(m)` on `C` (in TV = ℓ¹ on the finite simplex); (2) `supp q*(m) = {x : S(x) ∈ F_m}` with `F_m` the minimal face; (3) the
completed family = closure of the interior family, homeomorphic to `C` via the moment map; (4) `R(p) = q*(E_p S)` is a
continuous moment-preserving retraction of the simplex onto the completed family; (5) `H_t(p) = (1−t)p + tR(p)` is a strong
deformation retraction (`E_{H_t p} S = E_p S` ⇒ `R ∘ H_t = R`).

## Questions
1. **Continuity of `q*` on the closed polytope — the Lean route.** By uniqueness + compactness of the simplex, continuity of `q*`
   follows from continuity of the value function `𝓘` on `C` (any limit point `q` of `q*(m_n)` has `E_q S = m` and
   `KL(q‖w) ≤ liminf 𝓘(m_n) = 𝓘(m)`, so `q = q*(m)`); lower semicontinuity of `𝓘` is free (sup of affine functions). The crux is
   **upper semicontinuity of `𝓘` at boundary points of `C`**, equivalently a recovery sequence: for `m_n → m` in `C`, feasible
   `q'_n` with `E_{q'_n} S = m_n` and `q'_n → q*(m)`. Which route is cheapest in Lean?
   (a) the local conicity of polytopes (`C ∩ B(m,r) = (m + T_mC) ∩ B(m,r)`) giving `m + λ(m_n − m) ∈ C` for `λ ≤ r/|m_n − m|`,
       then `q'_n = (1−ε_n) q*(m) + ε_n q*(m + (m_n−m)/ε_n)`-type convex corrections with `ε_n → 0` (needs a bound on
       `KL` of the correction — fine since all `KL(q‖w) ≤ −log w_min`);
   (b) a direct Hoffman-type lifting for the moment map on the simplex;
   (c) the exposed-face induction of `EntropyCompletion` run "with parameters": show `𝓘` is continuous on each closed face by
       induction on the face dimension, using `𝓘(m) = −log p_F + 𝓘_F(m)` on the face and continuity of the interior chart
       (`meanMap` is a homeomorphism onto the relative interior — we have `MeanMapEmbedding`), plus a boundary matching at
       the relative boundary of each face;
   (d) something through the rays: for `m_n → m`, compare `q*(m_n)` with the atlas laws `Q_{s}` of the ray to `m`
       (`BoundaryCompletion`) using the Pythagoras identity `KL(q*(m_n)‖w) = KL(q*(m_n)‖Q_s) + 𝓘(M_s)`… — is there a clean
       inequality giving `limsup 𝓘(m_n) ≤ 𝓘(m)` from convexity of `𝓘` along segments `[m_n, m]` and the ray?
   (e) a purely convex-analytic fact we could prove once: a convex function on a polytope `C ⊂ ℝ^d` that is finite on `C`
       and lower semicontinuous is continuous on `C` (GKR); is there a short proof for polytopes (e.g. by induction on the
       dimension using barycentric subdivision / the `convexHull_eq_union` Carathéodory representation)?
   Please give the recommended route with the precise lemma chain and the Lean skeleton (statements), flagging the single
   hardest lemma.
2. **Support = minimal face.** With continuity in hand, is (2) a corollary of the seabed's exposed-face induction (the minimiser is
   a bounded tilt of `w` conditioned on the minimal face), i.e. `q*(m)(x) > 0 ↔ S(x) ∈ F_m`? Precise statement and route.
3. **The retraction and the deformation.** Given (1), (4) and (5) are compositions (`p ↦ E_p S` is linear; `H_t` is a convex
   combination). Please write the precise Lean-level statements (types: `X` finite, laws as `X → ℝ` in `stdSimplex ℝ X` or as
   `Measure X` absolutely continuous w.r.t. `count`?) that make the "strong deformation retraction of the simplex onto the
   completed family, fibrewise moment-preserving" cleanest to state and to prove.
4. **Ranking vs the explicit radius.** Your rank-3 natural-parameter theorem (radius `log(3/2)/L`, `Σ‖A_n‖ρ^n ≤ 3`, remainder
   `3(t/ρ)^{N+1}`) — is it still worth doing after the qualitative analytic atlas, or should the next module be face completion
   outright? If face completion, what is the minimal first module (the value-function continuity?) so that progress lands in
   pieces. Answer in ≤ 3000 words.
